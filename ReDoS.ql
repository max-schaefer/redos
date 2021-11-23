/**
 * A simple ReDoS-vulnerability detector in QL.
 *
 * This analysis is purely intended for educational purposes to demonstrate
 * the essence of ReDoS detection. It only supports very simple regexes
 * and is very slow. Battle-tested, scalable implementations of
 * ReDoS detection in QL that support the full regex syntax of various
 * popular programming languages are available in the [CodeQL
 * repository](https://github.com/github/codeql).
 */

/**
 * A regular expression to be analysed.
 */
class Regex extends string {
  Regex() {
    // this one is vulnerable:
    this = "'(\\\\.|[^'])*'"
    or
    // this one is not:
    this = "'(\\\\.|[^\\\\'])*'"
  }
}

// *******************************
// Parsing of regular expressions.
// *******************************
/**
 * A printable ASCII character.
 */
class Char extends string {
  Char() { this = [32 .. 127].toUnicode() }

  predicate isMetaChar() { this = ".()[]|*+?".charAt(_) }
}

/**
 * A token in a regular expression, which is either a backslash escape sequence,
 * or a plain (non-backslash) character.
 *
 * `index` is the logical index among all tokens in `regex`, starting from zero,
 * while `start` is the character offset of the start of the token. `raw` it the
 * raw source text of the token, while `cooked` is the character the token
 * represents; it the same as `raw` if `raw` is not a backslash escape sequence,
 * or the escaped character if it is.
 */
predicate token(Regex regex, int index, int start, string raw, Char cooked) {
  tokenStart(regex, index, start) and
  exists(Char c | c = regex.charAt(start) |
    if c = "\\"
    then (
      cooked = regex.charAt(start + 1) and
      raw = "\\" + cooked
    ) else (
      cooked = c and
      raw = c
    )
  )
}

/**
 * Holds if the `index`th token in `regex` starts at character offset `start`.
 */
predicate tokenStart(Regex regex, int index, int start) {
  index = 0 and
  start = 0
  or
  exists(string raw | token(regex, index - 1, start - raw.length(), raw, _))
}

/**
 * Holds if a character class starts at token index `start` in `regex` and
 * extends at least until `end`, but possibly further.
 */
predicate charClassPrefix(Regex regex, int start, int end) {
  token(regex, start, _, "[", _) and
  end = start + 1
  or
  charClassPrefix(regex, start, end - 1) and
  not token(regex, end - 1, _, "]", _)
}

/**
 * A constituent term of a regular expression to be analysed.
 */
newtype TRegexTerm =
  /** A constant character, matching only itself. */
  MkConst(Regex regex, int start, Char c) {
    exists(string raw | token(regex, start, _, raw, c) and not raw.(Char).isMetaChar())
  } or
  /** A dot character, matching any character. */
  MkDot(Regex regex, int start) { token(regex, start, _, ".", _) } or
  /** A character class, matching a set of characters. */
  MkCharacterClass(Regex regex, int start, int bodyStart, int end, boolean negated) {
    charClassPrefix(regex, start, end) and
    token(regex, end, _, "]", _) and
    (
      if token(regex, start + 1, _, "^", _)
      then (
        bodyStart = start + 2 and
        negated = true
      ) else (
        bodyStart = start + 1 and
        negated = false
      )
    )
  } or
  /** A group, used to override operator precedence. */
  MkGroup(Regex regex, int start, int end, RawRegexTerm body) {
    token(regex, start, _, "(", _) and
    covers(body, regex, start + 1, end - 1) and
    token(regex, end, _, ")", _)
  } or
  /** A Kleene-star quantified term. */
  MkQuant(Regex regex, int start, int end, TQuantifiable body, string quant) {
    covers(body, regex, start, end - 1) and
    token(regex, end, _, quant, _) and
    quant in ["*"]
  } or
  /** A sequence of two terms. */
  MkSeq(Regex regex, int start, int end, TQuantifiable left, TChoice right) {
    exists(int mid |
      covers(left, regex, start, mid) and
      covers(right, regex, mid + 1, end)
    )
  } or
  /** A choice between two terms. */
  MkAlt(Regex regex, int start, int end, TChoice left, RawRegexTerm right) {
    exists(int mid |
      covers(left, regex, start, mid) and
      token(regex, mid + 1, _, "|", _) and
      covers(right, regex, mid + 2, end)
    )
  }

/** An atom that matches a single character. */
class TAtom = MkConst or MkDot or MkCharacterClass;

/** A term that may be the operand of a quantifier. */
class TQuantifiable = TAtom or MkGroup or MkQuant;

/** A term that may be the operand of a choice. */
class TChoice = TQuantifiable or MkSeq;

/** Holds if `term` covers the tokens at index `start` to `end` (inclusive) of `regex`. */
predicate covers(TRegexTerm term, Regex regex, int start, int end) {
  term = MkConst(regex, start, _) and
  end = start
  or
  term = MkDot(regex, start) and
  end = start
  or
  term = MkCharacterClass(regex, start, _, end, _)
  or
  term = MkGroup(regex, start, end, _)
  or
  term = MkSeq(regex, start, end, _, _)
  or
  term = MkAlt(regex, start, end, _, _)
  or
  term = MkQuant(regex, start, end, _, _)
}

/** A regex term, wrapped in a class. */
class RawRegexTerm extends TRegexTerm {
  /** Gets the `i`th child term of this term. */
  RawRegexTerm getChild(int i) {
    this = MkGroup(_, _, _, result) and i = 0
    or
    this = MkSeq(_, _, _, result, _) and i = 0
    or
    this = MkSeq(_, _, _, _, result) and i = 1
    or
    this = MkAlt(_, _, _, result, _) and i = 0
    or
    this = MkAlt(_, _, _, _, result) and i = 1
    or
    this = MkQuant(_, _, _, result, _) and i = 0
  }

  /** Gets a textual representation of this term as an s-expression. */
  string toString() {
    exists(string c |
      this = MkConst(_, _, c) and
      result = "(Atom " + c + ")"
    )
    or
    this = MkDot(_, _) and
    result = "(Dot)"
    or
    exists(Regex regex, int bodyStart, int end, boolean negated |
      this = MkCharacterClass(regex, _, bodyStart, end, negated) and
      result =
        "(CharacterClass " + negated + " " +
          concat(int i, string c |
            i in [bodyStart .. end - 1] and token(regex, i, _, _, c)
          |
            c order by i
          ) + ")"
    )
    or
    exists(RawRegexTerm body | this = MkGroup(_, _, _, body) | result = "(Group " + body + ")")
    or
    exists(RawRegexTerm left, RawRegexTerm right | this = MkSeq(_, _, _, left, right) |
      result = "(Seq " + left + " " + right + ")"
    )
    or
    exists(RawRegexTerm left, RawRegexTerm right | this = MkAlt(_, _, _, left, right) |
      result = "(Alt " + left + " " + right + ")"
    )
    or
    exists(RawRegexTerm body, string quant | this = MkQuant(_, _, _, body, quant) |
      result = "(Quant " + quant + " " + body + ")"
    )
  }
}

// ************************************
// Syntax trees for regular expressions
// ************************************
/** A regex term that forms part of a successful parse of a regular expression. */
class RegexTerm extends RawRegexTerm {
  RegexTerm() {
    exists(Regex regex, int end |
      covers(this, regex, 0, end) and
      not token(regex, end + 1, _, _, _)
    )
    or
    this = any(RegexTerm rt).getChild(_)
  }

  /** Gets an atom that may be matched first in the process of matching this term. */
  Atom getFirst() { none() }

  /** Gets an atom that may be matched last in the process of matching this term. */
  Atom getLast() { none() }

  /** Holds if this term may match the empty string. */
  predicate isNullable() { none() }
}

/** An atomic regex term. */
class Atom extends RegexTerm, TAtom {
  /** Holds if this term matches character `c`. */
  predicate matches(Char c) { none() }

  /**
   * Holds if `witness` is the lexicographically least character matched both by
   * this term and `that` term.
   */
  predicate compatibleWith(Atom that, Char witness) {
    witness = min(Char c | this.matches(c) and that.matches(c))
  }

  override Atom getFirst() { result = this }

  override Atom getLast() { result = this }
}

/** A `.` term matching any character. */
class Dot extends Atom, MkDot {
  override predicate matches(Char c) { any() }
}

/** A constant term matching only itself. */
class Const extends Atom, MkConst {
  override predicate matches(Char c) { this = MkConst(_, _, c) }
}

/** A character class, either negated or not, matching a set of characters. */
class CharacterClass extends Atom, MkCharacterClass {
  boolean negated;

  CharacterClass() { this = MkCharacterClass(_, _, _, _, negated) }

  /**
   * Gets an element of this character class, either representing a character matched,
   * or a character not matched by this class.
   */
  Char getAnElement() {
    exists(Regex regex, int bodyStart, int end |
      this = MkCharacterClass(regex, _, bodyStart, end, _) and
      token(regex, [bodyStart .. end - 1], _, _, result)
    )
  }
}

/** A non-negated character class. */
class PositiveCharacterClass extends CharacterClass {
  PositiveCharacterClass() { negated = false }

  override predicate matches(Char c) { c = getAnElement() }
}

/** A negated character class. */
class NegativeCharacterClass extends CharacterClass {
  NegativeCharacterClass() { negated = true }

  override predicate matches(Char c) { not c = getAnElement() }
}

/** A group term. */
class Group extends RegexTerm, MkGroup {
  RegexTerm getBody() { result = getChild(0) }

  override Atom getFirst() { result = this.getBody().getFirst() }

  override Atom getLast() { result = this.getBody().getLast() }

  override predicate isNullable() { this.getBody().isNullable() }
}

/** A quantified term. */
class Quant extends RegexTerm, MkQuant {
  RegexTerm getBody() { result = getChild(0) }

  override Atom getFirst() { result = this.getBody().getFirst() }

  override Atom getLast() { result = this.getBody().getLast() }

  override predicate isNullable() { any() }
}

/** A sequence term. */
class Seq extends RegexTerm, MkSeq {
  RegexTerm getLeft() { result = getChild(0) }

  RegexTerm getRight() { result = getChild(1) }

  override Atom getFirst() {
    result = this.getLeft().getFirst()
    or
    this.getLeft().isNullable() and result = this.getRight().getFirst()
  }

  override Atom getLast() {
    result = this.getRight().getLast()
    or
    this.getRight().isNullable() and result = this.getLeft().getLast()
  }

  override predicate isNullable() { this.getLeft().isNullable() and this.getRight().isNullable() }
}

/** A choice term. */
class Alt extends RegexTerm, MkAlt {
  RegexTerm getLeft() { result = getChild(0) }

  RegexTerm getRight() { result = getChild(1) }

  override Atom getFirst() {
    result = this.getLeft().getFirst()
    or
    result = this.getRight().getFirst()
  }

  override Atom getLast() {
    result = this.getLeft().getLast()
    or
    result = this.getRight().getLast()
  }

  override predicate isNullable() { this.getLeft().isNullable() or this.getRight().isNullable() }
}

// ****************
// NFA construction
// ****************
/** A state in an NFA built from a regex. */
newtype TState =
  /** A state corresponding to an atomic regex term. */
  MkAtomState(Atom a) or
  /** An accepting state. */
  MkAcceptState()

/** An NFA state wrapped in a class. */
class State extends TState {
  string toString() {
    exists(Atom a | this = MkAtomState(a) | result = a.toString())
    or
    this = MkAcceptState() and result = "Accept"
  }
}

/** Holds if there is a transition from `pred` to `succ` in the NFA. */
predicate transition(State pred, State succ) {
  exists(Seq seq |
    pred = MkAtomState(seq.getLeft().getLast()) and
    succ = MkAtomState(seq.getRight().getFirst())
  )
  or
  exists(Quant q |
    pred = MkAtomState(q.getLast()) and
    succ = MkAtomState(q.getFirst())
  )
  or
  exists(RegexTerm root |
    pred = MkAtomState(root.getLast()) and
    not root = any(RegexTerm rt).getChild(_) and
    succ = MkAcceptState()
  )
}

// ************************
// Product NFA construction
// ************************
/** A pair of NFA states. */
newtype StatePair = MkStatePair(State s1, State s2)

/**
 * Holds if there is a parallel transition from `pred` to `succ` in the product NFA,
 * and `witness` is a character accepted by both constituent transitions.
 */
predicate parallelTransition(StatePair pred, StatePair succ, Char witness) {
  exists(Atom a, Atom b, State succ1, State succ2 |
    pred = MkStatePair(MkAtomState(a), MkAtomState(b)) and
    transition(MkAtomState(a), succ1) and
    transition(MkAtomState(b), succ2) and
    a.compatibleWith(b, witness) and
    succ = MkStatePair(succ1, succ2)
  )
}

/**
 * Holds if there is a transition from `pred` to `succ` in the product NFA.
 */
predicate parallelTransition(StatePair pred, StatePair succ) { parallelTransition(pred, succ, _) }

/** Gets the shortest distance from `start` to `end` in the product NFA. */
int parallelDistance(StatePair start, StatePair end) =
  shortestDistances(isStatePair/1, parallelTransition/2)(start, end, result)

/** A trivial auxiliary predicate required for the least-distance computation. */
predicate isStatePair(StatePair s) { any() }

/**
 * Holds if there is a path from `start` to `end` in the product NFA, whose edge
 * labels concatenate to `witness`.
 */
predicate parallelPath(StatePair start, StatePair end, string witness) {
  start = end and witness = ""
  or
  exists(string prefix, StatePair pred, Char c |
    parallelPath(start, pred, prefix) and
    parallelTransition(pred, end, c) and
    witness = prefix + c and
    witness.length() <= parallelDistance(start, end)
  )
}

/**
 * Holds if `pred` is a pump state, that is, there is a transition from `(pred, pred)`
 * to `succ` in the product NFA, and `succ` is not a pair with identical components.
 */
predicate pumpState(State pred, StatePair succ, Char witness) {
  exists(State succ1, State succ2 |
    parallelTransition(MkStatePair(pred, pred), MkStatePair(succ1, succ2), witness) and
    succ1 != succ2 and
    succ = MkStatePair(succ1, succ2)
  )
}

from State pred, StatePair succ, Char fst, string rest
where
  pumpState(pred, succ, fst) and
  parallelPath(succ, MkStatePair(pred, pred), rest)
select pred, fst + rest
