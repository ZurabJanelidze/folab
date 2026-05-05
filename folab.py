"""
fol.py

Clean proof-checking engine for bracket-language first-order logic.

This file contains only the proof engine. It contains no Anvil, Streamlit,
Gradio, or demo code. It is meant to be imported by a separate interface module.

Main user-facing classes:

    FirstOrderLanguage
    Proof

Typical use:

    from fol import FirstOrderLanguage, Proof

    L = FirstOrderLanguage(
        variables=["x", "y"],
        operations=["0"],
        relations=["P[]", "Q[]"],
    )

    P = Proof(L)
    G = Proof(P, goal="for every [x] we have [[P[x]] implies [P[x]]]")
    G.assume("x")
    H = Proof(G, goal="[P[x]] implies [P[x]]")
    H.assume("P[x]")
    H.conclude("P[x]")
    G.goal(H)
    P.goal(G)

Important correction:
    Equality introduction no longer creates variables. A line such as [x]=[x]
    is accepted only if x is already active. A variable is active if it is
    contextual, or if it has been introduced by an explicit object-assumption
    line such as ASSUME x inside the current proof path.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Optional, Literal


LineKind = Literal["assumption", "object_assumption", "conclusion", "goal"]


class ProofError(Exception):
  """Raised when a proof line is not valid."""


class SyntaxErrorFOL(Exception):
  """Raised when an expression is not syntactically valid."""


# ---------------------------------------------------------------------------
# Basic string and bracket utilities
# ---------------------------------------------------------------------------


def norm(s: str) -> str:
  """Normalize harmless whitespace while preserving the bracket language."""
  return " ".join(str(s).strip().split())


def count_placeholders(template: str) -> int:
  return norm(template).count("[]")


def matching_pairs(s: str) -> dict[int, int]:
  """Return a dictionary from opening-bracket positions to matching closings."""
  stack: list[int] = []
  pairs: dict[int, int] = {}

  for i, ch in enumerate(s):
    if ch == "[":
      stack.append(i)
    elif ch == "]":
      if not stack:
        raise SyntaxErrorFOL(
          f"Unmatched closing bracket at position {i} in {s!r}."
        )
      j = stack.pop()
      pairs[j] = i

  if stack:
    raise SyntaxErrorFOL(
      f"Unmatched opening bracket at position {stack[-1]} in {s!r}."
    )

  return pairs


def is_expression(s: str) -> bool:
  try:
    matching_pairs(norm(s))
    return True
  except SyntaxErrorFOL:
    return False


def is_atomic_expression(s: str) -> bool:
  """
    A non-empty expression whose brackets, if any, are all placeholders [].
    """
  s = norm(s)

  if not s:
    return False

  try:
    pairs = matching_pairs(s)
  except SyntaxErrorFOL:
    return False

  for i, j in pairs.items():
    if j != i + 1:
      return False

  return True


def decompose_top_level(expr: str) -> tuple[str, list[str]]:
  """
    Decompose an expression into its root atomic template and immediate children.

    Examples:
        '[[x]+[y]]=[z]' -> ('[]=[]', ['[x]+[y]', 'z'])
        '[x]+[y]'       -> ('[]+[]', ['x', 'y'])
        'P[x]'          -> ('P[]', ['x'])
        'x'             -> ('x', [])
    """
  expr = norm(expr)
  pairs = matching_pairs(expr)

  out: list[str] = []
  children: list[str] = []

  i = 0
  while i < len(expr):
    if expr[i] == "[":
      j = pairs[i]
      out.append("[]")
      children.append(expr[i + 1 : j])
      i = j + 1
    else:
      out.append(expr[i])
      i += 1

  return norm("".join(out)), [norm(c) for c in children]


def fill_template(template: str, children: Iterable[str]) -> str:
  """Fill placeholders of an atomic template with bracketed children."""
  result = norm(template)
  children = list(children)

  if result.count("[]") != len(children):
    raise SyntaxErrorFOL(
      f"Wrong number of children for template {template!r}."
    )

  for child in children:
    result = result.replace("[]", f"[{norm(child)}]", 1)

  return norm(result)


def bracketed_occurrences(expr: str, content: str) -> list[tuple[int, int]]:
  """Positions of matching bracket pairs whose inside is exactly content."""
  expr = norm(expr)
  content = norm(content)
  pairs = matching_pairs(expr)

  found: list[tuple[int, int]] = []
  for i, j in sorted(pairs.items()):
    if norm(expr[i + 1 : j]) == content:
      found.append((i, j))

  return found


# ---------------------------------------------------------------------------
# First-order language
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FirstOrderLanguage:
  """
    A first-order language in bracket notation.

    variables:
        bracketless atomic expressions, e.g. ["x", "y", "z"].

    operations:
        atomic templates for operations, e.g. ["0", "[]+[]", "S[]"].

    relations:
        atomic templates for relations. Equality []=[] is included automatically
        unless already supplied.

    Logical constructors are fixed:
        true, false,
        [] and [],
        [] or [],
        [] implies [],
        for every [] we have [],
        there exists [] such that [].
    """

  variables: tuple[str, ...]
  operations: tuple[str, ...]
  relations: tuple[str, ...]

  TRUE: str = "true"
  FALSE: str = "false"
  AND: str = "[] and []"
  OR: str = "[] or []"
  IMPLIES: str = "[] implies []"
  FORALL: str = "for every [] we have []"
  EXISTS: str = "there exists [] such that []"
  EQ: str = "[]=[]"

  def __init__(
    self,
    variables: Iterable[str],
    operations: Iterable[str] = (),
    relations: Iterable[str] = (),
  ) -> None:
    vars_n = tuple(norm(v) for v in variables)
    ops_n = tuple(norm(o) for o in operations)

    rels = [norm(r) for r in relations]
    if self.EQ not in rels:
      rels.insert(0, self.EQ)
    rels_n = tuple(rels)

    object.__setattr__(self, "variables", vars_n)
    object.__setattr__(self, "operations", ops_n)
    object.__setattr__(self, "relations", rels_n)

    self._validate_language()

  @property
  def logical_constructors(self) -> tuple[str, ...]:
    return (
      self.TRUE,
      self.FALSE,
      self.AND,
      self.OR,
      self.IMPLIES,
      self.FORALL,
      self.EXISTS,
    )

  def _validate_language(self) -> None:
    classes = [
      self.variables,
      self.operations,
      self.relations,
      self.logical_constructors,
    ]

    names: list[str] = []
    for cls in classes:
      for item in cls:
        if not is_atomic_expression(item):
          raise SyntaxErrorFOL(f"Not an atomic expression: {item!r}")
        names.append(item)

    if len(set(names)) != len(names):
      duplicates = sorted({x for x in names if names.count(x) > 1})
      raise SyntaxErrorFOL(
        f"Language classes are not pairwise disjoint: {duplicates}"
      )

    for v in self.variables:
      if "[" in v or "]" in v:
        raise SyntaxErrorFOL(f"Variable must be bracketless: {v!r}")

  def arity(self, template: str) -> int:
    return count_placeholders(norm(template))

    # ----------------------------- Terms ----------------------------------

  def is_variable(self, expr: str) -> bool:
    return norm(expr) in self.variables

  def is_constant(self, expr: str) -> bool:
    e = norm(expr)
    return e in self.operations and self.arity(e) == 0

  def is_term(self, expr: str) -> bool:
    expr = norm(expr)

    if self.is_variable(expr) or self.is_constant(expr):
      return True

    try:
      template, children = decompose_top_level(expr)
    except SyntaxErrorFOL:
      return False

    return (
      template in self.operations
      and self.arity(template) == len(children)
      and all(self.is_term(c) for c in children)
    )

  def term_variables(self, term: str) -> set[str]:
    term = norm(term)

    if not self.is_term(term):
      raise SyntaxErrorFOL(f"Not a term: {term!r}")

    if self.is_variable(term):
      return {term}

    if self.is_constant(term):
      return set()

    _, children = decompose_top_level(term)

    out: set[str] = set()
    for c in children:
      out |= self.term_variables(c)

    return out

  def substitute_in_term(self, term: str, x: str, U: str) -> str:
    term = norm(term)
    x = norm(x)
    U = norm(U)

    if not self.is_term(term):
      raise SyntaxErrorFOL(f"Not a term: {term!r}")

    if not self.is_variable(x):
      raise SyntaxErrorFOL(f"Not a variable: {x!r}")

    if not self.is_term(U):
      raise SyntaxErrorFOL(f"Not a term: {U!r}")

    if term == x:
      return U

    if self.is_constant(term):
      return term

    template, children = decompose_top_level(term)
    new_children = [self.substitute_in_term(c, x, U) for c in children]
    return fill_template(template, new_children)

    # ---------------------------- Formulas --------------------------------

  def is_formula(self, expr: str) -> bool:
    expr = norm(expr)

    if expr in (self.TRUE, self.FALSE):
      return True

    try:
      template, children = decompose_top_level(expr)
    except SyntaxErrorFOL:
      return False

      # Nullary relation, such as A, B, C if declared as relations.
    if template in self.relations and self.arity(template) == 0 and not children:
      return True

      # Atomic formula from relation.
    if template in self.relations:
      return (
        len(children) == self.arity(template)
        and all(self.is_term(c) for c in children)
      )

      # Binary logical constructors.
    if template in (self.AND, self.OR, self.IMPLIES):
      return (
        len(children) == 2
        and self.is_formula(children[0])
        and self.is_formula(children[1])
      )

      # Quantifiers.
    if template in (self.FORALL, self.EXISTS):
      return (
        len(children) == 2
        and self.is_variable(children[0])
        and self.is_formula(children[1])
      )

    return False

  def free_variables(self, formula: str) -> set[str]:
    formula = norm(formula)

    if not self.is_formula(formula):
      raise SyntaxErrorFOL(f"Not a formula: {formula!r}")

    if formula in (self.TRUE, self.FALSE):
      return set()

    template, children = decompose_top_level(formula)

    if template in self.relations:
      out: set[str] = set()
      for c in children:
        out |= self.term_variables(c)
      return out

    if template in (self.AND, self.OR, self.IMPLIES):
      return self.free_variables(children[0]) | self.free_variables(children[1])

    if template in (self.FORALL, self.EXISTS):
      binder, scope = children
      return self.free_variables(scope) - {binder}

    raise SyntaxErrorFOL(f"Cannot compute free variables of: {formula!r}")

  def substitute_in_formula(self, formula: str, x: str, U: str) -> str:
    """
        Safe substitution A[U/x], replacing free occurrences of x by U.

        Raises ProofError if a free variable of U would be captured.
        """
    formula = norm(formula)
    x = norm(x)
    U = norm(U)

    if not self.is_formula(formula):
      raise SyntaxErrorFOL(f"Not a formula: {formula!r}")

    if not self.is_variable(x):
      raise SyntaxErrorFOL(f"Not a variable: {x!r}")

    if not self.is_term(U):
      raise SyntaxErrorFOL(f"Not a term: {U!r}")

    return self._subst_formula_rec(formula, x, U)

  def _subst_formula_rec(self, formula: str, x: str, U: str) -> str:
    if formula in (self.TRUE, self.FALSE):
      return formula

    template, children = decompose_top_level(formula)

    if template in self.relations:
      new_children = [self.substitute_in_term(c, x, U) for c in children]
      return fill_template(template, new_children)

    if template in (self.AND, self.OR, self.IMPLIES):
      return fill_template(
        template,
        [
          self._subst_formula_rec(children[0], x, U),
          self._subst_formula_rec(children[1], x, U),
        ],
      )

    if template in (self.FORALL, self.EXISTS):
      binder, scope = children

      if binder == x:
        return formula

      if binder in self.term_variables(U) and x in self.free_variables(scope):
        raise ProofError(
          f"Unsafe substitution: variable {binder!r} in {U!r} "
          f"would be captured in {formula!r}."
        )

      new_scope = self._subst_formula_rec(scope, x, U)
      return fill_template(template, [binder, new_scope])

    raise SyntaxErrorFOL(f"Cannot substitute in formula: {formula!r}")

  def is_safe_substitution_result(
    self,
    source: str,
    target: str,
    x: str,
    U: str,
  ) -> bool:
    try:
      return self.substitute_in_formula(source, x, U) == norm(target)
    except (ProofError, SyntaxErrorFOL):
      return False

    # ---------------------- Equality replacement --------------------------

  def equality_sides(self, eq_formula: str) -> Optional[tuple[str, str]]:
    eq_formula = norm(eq_formula)

    try:
      template, children = decompose_top_level(eq_formula)
    except SyntaxErrorFOL:
      return None

    if (
      template == self.EQ
      and len(children) == 2
      and all(self.is_term(c) for c in children)
    ):
      return children[0], children[1]

    return None

  def possible_equal_replacements(self, formula: str, old: str, new: str) -> set[str]:
    """
        All formulas obtained by safely replacing one bracketed occurrence of
        old by new.
        """
    formula = norm(formula)
    old = norm(old)
    new = norm(new)

    if not self.is_formula(formula):
      raise SyntaxErrorFOL(f"Not a formula: {formula!r}")

    if not self.is_term(old) or not self.is_term(new):
      raise SyntaxErrorFOL("Equality replacement requires terms.")

    return self._replace_in_formula_rec(formula, old, new, bound=set())

  def _replace_in_formula_rec(
    self,
    formula: str,
    old: str,
    new: str,
    bound: set[str],
  ) -> set[str]:
    if formula in (self.TRUE, self.FALSE):
      return set()

    template, children = decompose_top_level(formula)
    results: set[str] = set()

    if template in self.relations:
      for i, child in enumerate(children):
        for new_child in self._replace_in_term_rec(child, old, new, bound):
          new_children = children[:]
          new_children[i] = new_child
          candidate = fill_template(template, new_children)
          if self.is_formula(candidate):
            results.add(candidate)
      return results

    if template in (self.AND, self.OR, self.IMPLIES):
      for side in (0, 1):
        for new_side in self._replace_in_formula_rec(
          children[side], old, new, bound
        ):
          new_children = children[:]
          new_children[side] = new_side
          results.add(fill_template(template, new_children))
      return results

    if template in (self.FORALL, self.EXISTS):
      binder, scope = children
      for new_scope in self._replace_in_formula_rec(
        scope, old, new, bound | {binder}
      ):
        results.add(fill_template(template, [binder, new_scope]))
      return results

    return set()

  def _replace_in_term_rec(
    self,
    term: str,
    old: str,
    new: str,
    bound: set[str],
  ) -> set[str]:
    results: set[str] = set()

    if term == old:
      if self.term_variables(new) & bound:
        return set()
      results.add(new)

    if self.is_variable(term) or self.is_constant(term):
      return results

    template, children = decompose_top_level(term)

    if template in self.operations:
      for i, child in enumerate(children):
        for new_child in self._replace_in_term_rec(child, old, new, bound):
          new_children = children[:]
          new_children[i] = new_child
          candidate = fill_template(template, new_children)
          if self.is_term(candidate):
            results.add(candidate)

    return results

    # -------------------------- Reformulation -----------------------------

  def possible_reformulations(self, formula: str, new_var: str) -> set[str]:
    """
        All formulas obtained by renaming one binding occurrence and all
        occurrences bound by it to a completely fresh variable new_var.
        """
    formula = norm(formula)
    new_var = norm(new_var)

    if not self.is_formula(formula):
      raise SyntaxErrorFOL(f"Not a formula: {formula!r}")

    if not self.is_variable(new_var):
      raise SyntaxErrorFOL(f"Not a variable: {new_var!r}")

    if new_var in self._all_variables_in_formula(formula):
      return set()

    return self._reformulations_rec(formula, new_var)

  def _all_variables_in_formula(self, formula: str) -> set[str]:
    if formula in (self.TRUE, self.FALSE):
      return set()

    template, children = decompose_top_level(formula)

    if template in self.relations:
      out: set[str] = set()
      for c in children:
        out |= self.term_variables(c)
      return out

    if template in (self.AND, self.OR, self.IMPLIES):
      return self._all_variables_in_formula(children[0]) | self._all_variables_in_formula(
        children[1]
      )

    if template in (self.FORALL, self.EXISTS):
      return {children[0]} | self._all_variables_in_formula(children[1])

    return set()

  def _reformulations_rec(self, formula: str, new_var: str) -> set[str]:
    if formula in (self.TRUE, self.FALSE):
      return set()

    template, children = decompose_top_level(formula)
    results: set[str] = set()

    if template in self.relations:
      return results

    if template in (self.AND, self.OR, self.IMPLIES):
      for side in (0, 1):
        for new_side in self._reformulations_rec(children[side], new_var):
          new_children = children[:]
          new_children[side] = new_side
          results.add(fill_template(template, new_children))
      return results

    if template in (self.FORALL, self.EXISTS):
      binder, scope = children

      # Reformulate this binder.
      new_scope = self._rename_bound_occurrences(scope, binder, new_var)
      results.add(fill_template(template, [new_var, new_scope]))

      # Or reformulate a smaller binder inside the scope.
      for new_inner in self._reformulations_rec(scope, new_var):
        results.add(fill_template(template, [binder, new_inner]))

      return results

    return results

  def _rename_bound_occurrences(self, formula: str, old: str, new: str) -> str:
    """
        Rename occurrences bound by the current binder old, stopping at shadowing
        binders for old.
        """
    if formula in (self.TRUE, self.FALSE):
      return formula

    template, children = decompose_top_level(formula)

    if template in self.relations:
      return fill_template(
        template,
        [self._rename_in_term(c, old, new) for c in children],
      )

    if template in (self.AND, self.OR, self.IMPLIES):
      return fill_template(
        template,
        [
          self._rename_bound_occurrences(children[0], old, new),
          self._rename_bound_occurrences(children[1], old, new),
        ],
      )

    if template in (self.FORALL, self.EXISTS):
      binder, scope = children

      if binder == old:
        return formula

      return fill_template(
        template,
        [binder, self._rename_bound_occurrences(scope, old, new)],
      )

    return formula

  def _rename_in_term(self, term: str, old: str, new: str) -> str:
    if term == old:
      return new

    if self.is_variable(term) or self.is_constant(term):
      return term

    template, children = decompose_top_level(term)
    return fill_template(
      template,
      [self._rename_in_term(c, old, new) for c in children],
    )


# ---------------------------------------------------------------------------
# Proof objects
# ---------------------------------------------------------------------------


@dataclass
class Line:
  number: str
  kind: LineKind
  formula: str
  rule: str = ""
  note: str = ""
  proved: bool = False


class Proof:
  """
    A Fitch-style proof object.

    Commands:
        P.assume("...")
        P.conclude("...")
        P.goal(subproof)

    A subproof with a goal is created as:
        G = Proof(P, goal="...")
    """

  def __init__(
    self,
    language_or_parent: FirstOrderLanguage | "Proof",
    *,
    goal: Optional[str] = None,
    parent: Optional["Proof"] = None,
    name: str = "Proof",
    print_steps: bool = True,
  ) -> None:
    if isinstance(language_or_parent, Proof):
      parent = language_or_parent
      language = parent.language
    else:
      language = language_or_parent

    self.language = language
    self.parent = parent
    self.goal_formula = norm(goal) if goal else None
    self.name = name
    self.lines: list[Line] = []
    self.print_steps = print_steps
    self._next_number = 1
    self._prefix = ""
    self._goal_line: Optional[Line] = None

    if self.goal_formula is not None:
      self._require_formula(self.goal_formula)

      if self.parent is None:
        self._goal_line = self._add_line("goal", self.goal_formula)
        self._prefix = self._goal_line.number
        self._next_number = 1
      else:
        self._goal_line = self.parent._add_line("goal", self.goal_formula)
        self._prefix = self._goal_line.number

    # ----------------------------- Display --------------------------------

  @property
  def depth(self) -> int:
    d = 0
    p = self.parent

    while p is not None:
      d += 1
      p = p.parent

    return d

  def _print(self, text: str) -> None:
    if self.print_steps:
      print("  " * self.depth + text)

  def _make_number(self) -> str:
    local = str(self._next_number)
    return f"{self._prefix}.{local}" if self._prefix else local

  def _add_line(
    self,
    kind: LineKind,
    formula: str,
    rule: str = "",
    note: str = "",
  ) -> Line:
    line = Line(self._make_number(), kind, norm(formula), rule, note)
    self._next_number += 1
    self.lines.append(line)

    label = {
      "assumption": "Assume",
      "object_assumption": "Assume",
      "conclusion": "Conclude",
      "goal": "Goal",
    }[kind]

    suffix = f"    ({rule})" if rule else ""
    self._print(f"{line.number}. {label}: {line.formula}{suffix}")

    return line

    # ---------------------------- Context ---------------------------------

  def available_formulas(self) -> list[str]:
    formulas: list[str] = []

    if self.parent is not None:
      formulas.extend(self.parent.available_formulas())

    for line in self.lines:
      if line.kind in ("assumption", "conclusion") or (
        line.kind == "goal" and line.proved
      ):
        formulas.append(line.formula)

    return formulas

  def local_assumptions(self) -> list[str]:
    return [line.formula for line in self.lines if line.kind == "assumption"]

  def local_object_assumptions(self) -> list[str]:
    return [line.formula for line in self.lines if line.kind == "object_assumption"]

  def object_assumptions_on_active_path(self) -> set[str]:
    """
        Object variables introduced by explicit object-assumption lines on the
        current active proof path.
        """
    out: set[str] = set()

    if self.parent is not None:
      out |= self.parent.object_assumptions_on_active_path()

    for line in self.lines:
      if line.kind == "object_assumption":
        out.add(line.formula)

    return out

  def local_conclusions(self) -> list[str]:
    """
        Local conclusions include ordinary conclusion lines and proved goal lines.
        """
    return [
      line.formula
      for line in self.lines
      if line.kind == "conclusion" or (line.kind == "goal" and line.proved)
    ]

  def contextual_variables(self) -> set[str]:
    """
        Variables occurring freely in currently available formulas.
        """
    out: set[str] = set()

    for f in self.available_formulas():
      if self.language.is_formula(f):
        out |= self.language.free_variables(f)

    return out

  def active_variables(self) -> set[str]:
    """
        Variables currently usable as names of available objects.

        This includes:
        1. contextual variables, from available formulas;
        2. variables introduced by explicit object-assumption lines on the
           current active proof path.
        """
    return set(self.contextual_variables()) | self.object_assumptions_on_active_path()

  def _in_context(self, formula: str) -> bool:
    return norm(formula) in self.available_formulas()

  def _require_formula(self, formula: str) -> None:
    if not self.language.is_formula(formula):
      raise ProofError(f"Not a formula in this language: {formula!r}")

    # -------------------------- User commands -----------------------------

  def assume(self, item: str) -> Line:
    """
        Add an assumption line.

        If item is a formula, this is an ordinary formula assumption.
        If item is a declared variable, this is an object-assumption line,
        meaning that the variable is introduced as a local arbitrary object.
        """
    item = norm(item)

    if self.language.is_formula(item):
      return self._add_line("assumption", item, rule="assumption")

    if self.language.is_variable(item):
      if item in self.active_variables():
        raise ProofError(
          f"Variable {item!r} is already active and cannot be introduced again."
        )
      return self._add_line(
        "object_assumption",
        item,
        rule="assumption",
      )

    raise ProofError(
      f"Assumption must be either a formula or a declared variable: {item!r}"
    )

  def conclude(self, formula: str, *, rule: Optional[str] = None, **kwargs: str) -> Line:
    formula = norm(formula)
    self._require_formula(formula)
    used_rule = self._check_conclusion(formula, rule=rule, **kwargs)
    return self._add_line("conclusion", formula, rule=used_rule)

  def goal(self, subproof: "Proof") -> Line:
    if subproof.parent is not self:
      raise ProofError("The supplied subproof must have this proof as its parent.")

    if subproof.goal_formula is None or subproof._goal_line is None:
      raise ProofError("The supplied proof object has no goal line.")

    self._check_goal_subproof(subproof)

    subproof._goal_line.proved = True
    subproof._goal_line.rule = "goal/subproof"

    self._print(f"✓ Goal {subproof._goal_line.number} proved: {subproof.goal_formula}")

    return subproof._goal_line

    # -------------------------- Rule checking -----------------------------

  def _check_conclusion(self, formula: str, *, rule: Optional[str], **kwargs: str) -> str:
    if rule is not None:
      return self._check_named_rule(formula, rule, **kwargs)

    for checker in (
      self._auto_reiteration,
      self._auto_true_intro,
      self._auto_false_elim,
      self._auto_and_intro,
      self._auto_and_elim,
      self._auto_or_intro,
      self._auto_imp_elim,
      self._auto_or_elim,
      self._auto_eq_intro,
      self._auto_forall_elim,
      self._auto_exists_intro,
      self._auto_exists_elim,
      self._auto_eq_elim,
      self._auto_reformulation,
      self._auto_double_negation,
    ):
      rule_name = checker(formula)
      if rule_name:
        return rule_name

    raise ProofError(f"Cannot justify conclusion: {formula}")

  def _check_named_rule(self, formula: str, rule: str, **kwargs: str) -> str:
    """
        Named rules are optional. The interface normally uses automatic rule
        detection, but named rules are kept for debugging and advanced scripts.
        """
    rule = norm(rule).lower()

    if rule in {"forall_elim", "universal_elim"}:
      source = norm(kwargs.get("source", ""))
      var = norm(kwargs.get("var", ""))
      term = norm(kwargs.get("term", ""))

      if not source or not var or not term:
        raise ProofError("forall_elim requires source=..., var=..., term=...")

      if not self._in_context(source):
        raise ProofError("Universal source formula is not in the context.")

      if not self.language.is_term(term):
        raise ProofError(f"Not a term: {term!r}")

      if not self.language.term_variables(term) <= self.active_variables():
        raise ProofError(
          "Every variable of the substituting term must be active."
        )

      scope = source_scope_of_forall(source, self.language, var)

      if not self.language.is_safe_substitution_result(scope, formula, var, term):
        raise ProofError("The claimed formula is not the safe universal instance.")

      return "universal elimination"

    if rule in {"exists_intro", "existential_intro"}:
      source = norm(kwargs.get("source", ""))
      var = norm(kwargs.get("var", ""))
      term = norm(kwargs.get("term", ""))

      if not source or not var or not term:
        raise ProofError("exists_intro requires source=..., var=..., term=...")

      if not self._in_context(source):
        raise ProofError("Existential-introduction source is not in the context.")

      template, children = decompose_top_level(formula)

      if template != self.language.EXISTS or len(children) != 2:
        raise ProofError("Conclusion is not existential.")

      bound_var, scope = children

      if var != bound_var:
        raise ProofError(
          "var=... must be the variable bound by the existential conclusion."
        )

      if not self.language.is_safe_substitution_result(scope, source, var, term):
        raise ProofError("The source is not the required safe instance A[U/x].")

      if not self.language.term_variables(term) <= self.active_variables():
        raise ProofError("Every variable of the witnessing term must be active.")

      return "existential introduction"

    if rule in {"exists_elim", "existential_elim", "witness"}:
      source = norm(kwargs.get("source", ""))
      var = norm(kwargs.get("var", ""))
      witness = norm(kwargs.get("witness", ""))

      if not source or not var or not witness:
        raise ProofError("exists_elim requires source=..., var=..., witness=...")

      if not self._in_context(source):
        raise ProofError("Existential source formula is not in the context.")

      if witness in self.active_variables():
        raise ProofError("The witness variable must be fresh, not already active.")

      template, children = decompose_top_level(source)

      if template != self.language.EXISTS or len(children) != 2:
        raise ProofError("Source is not existential.")

      bound_var, scope = children

      if var != bound_var:
        raise ProofError(
          "var=... must be the variable bound by the existential source."
        )

      if self.language.substitute_in_formula(scope, var, witness) != formula:
        raise ProofError("Conclusion is not the witness instance A[y/x].")

      return "existential elimination"

    if rule in {"equality_elim", "eq_elim", "substitution_of_equals"}:
      equality = norm(kwargs.get("equality", ""))
      source = norm(kwargs.get("source", ""))

      if not equality or not source:
        raise ProofError("equality_elim requires equality=... and source=...")

      if not self._in_context(equality) or not self._in_context(source):
        raise ProofError(
          "Equality and source formula must both be in the context."
        )

      sides = self.language.equality_sides(equality)

      if sides is None:
        raise ProofError("equality=... is not an equality formula.")

      T, U = sides
      possible = self.language.possible_equal_replacements(source, T, U)
      possible |= self.language.possible_equal_replacements(source, U, T)

      if formula not in possible:
        raise ProofError(
          "Formula is not obtained by a safe replacement of equals."
        )

      return "equality elimination"

    if rule in {"reformulation", "alpha", "alpha_conversion"}:
      source = norm(kwargs.get("source", ""))
      new_var = norm(kwargs.get("new_var", ""))

      if not source or not new_var:
        raise ProofError("reformulation requires source=... and new_var=...")

      if not self._in_context(source):
        raise ProofError("Reformulation source is not in the context.")

      if new_var in self.active_variables():
        raise ProofError("The new variable must not already be active.")

      if formula not in self.language.possible_reformulations(source, new_var):
        raise ProofError("Formula is not an allowed reformulation of the source.")

      return "reformulation"

    raise ProofError(f"Unknown named rule: {rule}")

    # ---------------------------- Auto rules ------------------------------

  def _auto_reiteration(self, formula: str) -> Optional[str]:
    return "tautology" if self._in_context(formula) else None

  def _auto_true_intro(self, formula: str) -> Optional[str]:
    return "true introduction" if formula == self.language.TRUE else None

  def _auto_false_elim(self, formula: str) -> Optional[str]:
    return (
      "false elimination"
      if self.language.FALSE in self.available_formulas()
      else None
    )

  def _auto_and_intro(self, formula: str) -> Optional[str]:
    try:
      template, children = decompose_top_level(formula)
    except SyntaxErrorFOL:
      return None

    if template == self.language.AND and len(children) == 2:
      if self._in_context(children[0]) and self._in_context(children[1]):
        return "conjunction introduction"

    return None

  def _auto_and_elim(self, formula: str) -> Optional[str]:
    for ctx in self.available_formulas():
      try:
        template, children = decompose_top_level(ctx)
      except SyntaxErrorFOL:
        continue

      if template == self.language.AND and formula in children:
        return "conjunction elimination"

    return None

  def _auto_or_intro(self, formula: str) -> Optional[str]:
    try:
      template, children = decompose_top_level(formula)
    except SyntaxErrorFOL:
      return None

    if template == self.language.OR and len(children) == 2:
      if self._in_context(children[0]) or self._in_context(children[1]):
        return "disjunction introduction"

    return None

  def _auto_imp_elim(self, formula: str) -> Optional[str]:
    context = self.available_formulas()

    for ctx in context:
      try:
        template, children = decompose_top_level(ctx)
      except SyntaxErrorFOL:
        continue

      if template == self.language.IMPLIES and len(children) == 2:
        antecedent, consequent = children
        if consequent == formula and antecedent in context:
          return "implication elimination"

    return None

  def _auto_or_elim(self, formula: str) -> Optional[str]:
    context = self.available_formulas()
    ors: list[tuple[str, str]] = []
    implications: set[tuple[str, str]] = set()

    for ctx in context:
      try:
        template, children = decompose_top_level(ctx)
      except SyntaxErrorFOL:
        continue

      if template == self.language.OR and len(children) == 2:
        ors.append((children[0], children[1]))

      if template == self.language.IMPLIES and len(children) == 2:
        implications.add((children[0], children[1]))

    for A, B in ors:
      if (A, formula) in implications and (B, formula) in implications:
        return "disjunction elimination"

    return None

  def _auto_eq_intro(self, formula: str) -> Optional[str]:
    sides = self.language.equality_sides(formula)

    if sides is not None and sides[0] == sides[1]:
      T = sides[0]
      if self.language.term_variables(T) <= self.active_variables():
        return "equality introduction"

    return None

  def _auto_forall_elim(self, formula: str) -> Optional[str]:
    """
        Automatically detect universal elimination.
        """
    for ctx in self.available_formulas():
      try:
        template, children = decompose_top_level(ctx)
      except SyntaxErrorFOL:
        continue

      if template != self.language.FORALL or len(children) != 2:
        continue

      x, scope = children
      witnesses = self._infer_substitution_terms(scope, formula, x)

      for U in witnesses:
        if U is None:
          return "universal elimination"

        if (
          self.language.is_term(U)
          and self.language.term_variables(U) <= self.active_variables()
        ):
          try:
            if self.language.substitute_in_formula(scope, x, U) == formula:
              return "universal elimination"
          except (ProofError, SyntaxErrorFOL):
            continue

    return None

  def _auto_exists_intro(self, formula: str) -> Optional[str]:
    """
        Automatically detect existential introduction.
        """
    try:
      template, children = decompose_top_level(formula)
    except SyntaxErrorFOL:
      return None

    if template != self.language.EXISTS or len(children) != 2:
      return None

    x, scope = children

    for ctx in self.available_formulas():
      witnesses = self._infer_substitution_terms(scope, ctx, x)

      for U in witnesses:
        if U is None:
          continue

        if (
          self.language.is_term(U)
          and self.language.term_variables(U) <= self.active_variables()
        ):
          try:
            if self.language.substitute_in_formula(scope, x, U) == ctx:
              return "existential introduction"
          except (ProofError, SyntaxErrorFOL):
            continue

    return None

  def _auto_exists_elim(self, formula: str) -> Optional[str]:
    """
        Automatically detect the current witness form of existential elimination.
        The witness variable must be fresh, i.e. not already active.
        """
    for ctx in self.available_formulas():
      try:
        template, children = decompose_top_level(ctx)
      except SyntaxErrorFOL:
        continue

      if template != self.language.EXISTS or len(children) != 2:
        continue

      x, scope = children
      witnesses = self._infer_substitution_terms(scope, formula, x)

      for y in witnesses:
        if y is None:
          continue

        if self.language.is_variable(y) and y not in self.active_variables():
          try:
            if self.language.substitute_in_formula(scope, x, y) == formula:
              return "existential elimination"
          except (ProofError, SyntaxErrorFOL):
            continue

    return None

  def _auto_eq_elim(self, formula: str) -> Optional[str]:
    """
        Automatically detect equality elimination/substitution of equals.
        """
    context = self.available_formulas()
    equalities: list[tuple[str, str]] = []

    for ctx in context:
      sides = self.language.equality_sides(ctx)
      if sides is not None:
        equalities.append(sides)

    for T, U in equalities:
      for source in context:
        try:
          possible = self.language.possible_equal_replacements(source, T, U)
          possible |= self.language.possible_equal_replacements(source, U, T)
        except (ProofError, SyntaxErrorFOL):
          continue

        if formula in possible:
          return "equality elimination"

    return None

  def _auto_reformulation(self, formula: str) -> Optional[str]:
    """
        Automatically detect safe reformulation of one bound variable.
        """
    for source in self.available_formulas():
      for new_var in self.language.variables:
        if new_var in self.active_variables():
          continue

        try:
          if formula in self.language.possible_reformulations(source, new_var):
            return "reformulation"
        except (ProofError, SyntaxErrorFOL):
          continue

    return None

  def _auto_double_negation(self, formula: str) -> Optional[str]:
    target = fill_template(
      self.language.IMPLIES,
      [
        fill_template(self.language.IMPLIES, [formula, self.language.FALSE]),
        self.language.FALSE,
      ],
    )

    return "double negation elimination" if self._in_context(target) else None

    # ---------------------- Substitution inference ------------------------

  def _infer_substitution_terms(
    self,
    pattern: str,
    instance: str,
    x: str,
  ) -> set[Optional[str]]:
    """
        Infer terms U such that pattern[U/x] could equal instance.

        Returns {None} only when x is not free in the pattern and the formula is
        already identical to the instance.
        """
    pattern = norm(pattern)
    instance = norm(instance)
    x = norm(x)

    if pattern == instance and x not in self.language.free_variables(pattern):
      return {None}

    bindings: set[str] = set()

    if self._match_formula_instance(pattern, instance, x, bindings):
      return bindings

    return set()

  def _match_formula_instance(
    self,
    pattern: str,
    instance: str,
    x: str,
    bindings: set[str],
  ) -> bool:
    if not self.language.is_formula(pattern) or not self.language.is_formula(instance):
      return False

    if pattern in (self.language.TRUE, self.language.FALSE):
      return pattern == instance

    try:
      p_template, p_children = decompose_top_level(pattern)
      i_template, i_children = decompose_top_level(instance)
    except SyntaxErrorFOL:
      return False

    if p_template != i_template or len(p_children) != len(i_children):
      return False

    if p_template in self.language.relations:
      for p_child, i_child in zip(p_children, i_children):
        if not self._match_term_instance(p_child, i_child, x, bindings):
          return False
      return True

    if p_template in (self.language.AND, self.language.OR, self.language.IMPLIES):
      return all(
        self._match_formula_instance(p_child, i_child, x, bindings)
        for p_child, i_child in zip(p_children, i_children)
      )

    if p_template in (self.language.FORALL, self.language.EXISTS):
      p_var, p_scope = p_children
      i_var, i_scope = i_children

      if p_var != i_var:
        return False

      if p_var == x:
        return p_scope == i_scope

      return self._match_formula_instance(p_scope, i_scope, x, bindings)

    return False

  def _match_term_instance(
    self,
    pattern: str,
    instance: str,
    x: str,
    bindings: set[str],
  ) -> bool:
    if not self.language.is_term(pattern) or not self.language.is_term(instance):
      return False

    if pattern == x:
      bindings.add(instance)
      return True

    if self.language.is_variable(pattern) or self.language.is_constant(pattern):
      return pattern == instance

    try:
      p_template, p_children = decompose_top_level(pattern)
      i_template, i_children = decompose_top_level(instance)
    except SyntaxErrorFOL:
      return False

    if p_template != i_template or len(p_children) != len(i_children):
      return False

    return all(
      self._match_term_instance(p_child, i_child, x, bindings)
      for p_child, i_child in zip(p_children, i_children)
    )

    # --------------------------- Goal checks ------------------------------

  def _check_goal_subproof(self, subproof: "Proof") -> None:
    goal = subproof.goal_formula
    assert goal is not None

    template, children = decompose_top_level(goal)

    # Implication introduction.
    if template == self.language.IMPLIES and len(children) == 2:
      A, B = children
      assumptions = subproof.local_assumptions()

      if assumptions != [A]:
        raise ProofError(
          "Implication-introduction subproof must have A as its "
          "only assumption line."
        )

      if B not in subproof.local_conclusions():
        raise ProofError("Implication-introduction subproof must conclude B.")

        # Free variables of the implication goal must be active in the
        # parent proof.
      if not self.language.free_variables(goal) <= self.active_variables():
        raise ProofError(
          "Free variables of the implication goal must be active."
        )

      return

      # Universal introduction.
    if template == self.language.FORALL and len(children) == 2:
      x, A = children
      parent_active = self.active_variables()
      free_A = self.language.free_variables(A)

      if not (free_A - {x}) <= parent_active:
        raise ProofError(
          "All free variables of A except the quantified variable "
          "must already be active."
        )

      if x in parent_active:
        raise ProofError(
          "The universal variable must not already be active in the "
          "surrounding proof."
        )

      if subproof.local_assumptions():
        raise ProofError(
          "Universal-introduction subproof must not introduce formula assumptions."
        )

      if subproof.local_object_assumptions() != [x]:
        raise ProofError(
          "Universal-introduction subproof must begin by assuming "
          "the quantified variable as its object assumption."
        )

      if A not in subproof.local_conclusions():
        raise ProofError("Universal-introduction subproof must conclude A.")

      return

    # General goal.
    # A general goal may be proved only by a subproof with no assumptions,
    # provided the goal formula appears as a conclusion or proved goal inside it.
    if subproof.local_assumptions():
      raise ProofError("A general-goal subproof must not contain assumptions.")
    
    if goal not in subproof.local_conclusions():
      raise ProofError("The goal formula was not concluded in the subproof.")


# ---------------------------------------------------------------------------
# Helper for named universal elimination
# ---------------------------------------------------------------------------


def source_scope_of_forall(source: str, lang: FirstOrderLanguage, var: str) -> str:
  source = norm(source)

  template, children = decompose_top_level(source)

  if template != lang.FORALL or len(children) != 2:
    raise ProofError("Source is not universal.")

  bound_var, scope = children

  if bound_var != norm(var):
    raise ProofError("var=... must be the variable bound by the universal source.")

  return scope
