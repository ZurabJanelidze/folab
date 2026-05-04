folab
=====

folab is an experimental Python module for building and checking proofs in a bracket-language version of first-order logic.

The project is designed for educational use. A user writes proof steps explicitly, and folab checks whether each new line follows from the current proof context by one of the implemented deduction rules. As the proof is built, the console displays the proof with nested line numbers.

Main idea
---------

The syntax is based on bracket-language expressions. For example:

    []+[]
    []=[]
    [] and []
    [] implies []
    for every [] we have []
    there exists [] such that []

The empty bracket pairs [] serve as placeholders. Inserting terms or formulas into these placeholders produces more complex expressions.

For example:

    [x]+[y]
    [x]=[y]
    [[x]<[y]] and [[y]<[z]]
    for every [x] we have [[x]=[x]]

Features
--------

folab currently supports:

- declaration of a first-order language;
- variables, operations, and relations;
- automatic inclusion of equality []=[];
- fixed logical constructors:
  - true
  - false
  - [] and []
  - [] or []
  - [] implies []
  - for every [] we have []
  - there exists [] such that []
- checking whether expressions are terms or formulas;
- free-variable calculation;
- safe substitution;
- equality replacement;
- reformulation of bound variables;
- Fitch-style proof construction;
- nested goal/subproof numbering;
- automatic detection of applicable deduction rules.

Installation
------------

At present, folab is a standalone Python module. Put folab.py in the same folder as the example file you want to run.

No external Python packages are required.

Quick example
-------------

Create a file called example.py in the same folder as folab.py.

    from folab import FirstOrderLanguage, Proof


    L = FirstOrderLanguage(
        variables=["x", "y", "z"],
        operations=["0", "1", "[]+[]"],
        relations=["A", "B", "C", "[]<[]"],
    )

    P = Proof(L)

    P.assume("[A] and [B]")
    P.conclude("A")
    P.conclude("B")
    P.conclude("[B] and [A]")

Run:

    python example.py

Expected output:

    1. Assume: [A] and [B]    (assumption)
    2. Conclude: A    (conjunction elimination)
    3. Conclude: B    (conjunction elimination)
    4. Conclude: [B] and [A]    (conjunction introduction)

Nested proof example
--------------------

    from folab import FirstOrderLanguage, Proof


    L = FirstOrderLanguage(
        variables=["x"],
        operations=[],
        relations=["A"],
    )

    P = Proof(L)

    G = Proof(P, goal="[A] implies [A]")
    G.assume("A")
    G.conclude("A")

    P.goal(G)

Expected output:

    1. Goal: [A] implies [A]
      1.1. Assume: A    (assumption)
      1.2. Conclude: A    (available formula)
    ✓ Goal 1 proved: [A] implies [A]

Example: universal elimination
------------------------------

    from folab import FirstOrderLanguage, Proof


    L = FirstOrderLanguage(
        variables=["x"],
        operations=["0"],
        relations=[],
    )

    P = Proof(L)

    P.assume("for every [x] we have [[x]=[x]]")
    P.conclude("[0]=[0]")

The second line is detected as an instance of universal elimination.

Example: incidence geometry
---------------------------

The following example uses unary relations for object types and a binary relation for incidence.

    from folab import FirstOrderLanguage, Proof


    def Pt(x):
        return f"Pt[{x}]"

    def Ln(x):
        return f"Ln[{x}]"

    def Inc(x, y):
        return f"[{x}]I[{y}]"

    def Eq(x, y):
        return f"[{x}]=[{y}]"

    def And(A, B):
        return f"[{A}] and [{B}]"

    def Imp(A, B):
        return f"[{A}] implies [{B}]"

    def Forall(x, A):
        return f"for every [{x}] we have [{A}]"

    def Exists(x, A):
        return f"there exists [{x}] such that [{A}]"


    IG = FirstOrderLanguage(
        variables=["l", "p", "q", "u", "v"],
        operations=[],
        relations=["Pt[]", "Ln[]", "[]I[]"],
    )


    def two_points_on_line_body(p, q, l):
        return And(
            And(Pt(p), Pt(q)),
            And(Inc(p, l), Inc(q, l)),
        )


    AX_LINE_HAS_TWO_POINTS = Forall(
        "l",
        Imp(
            Ln("l"),
            Exists(
                "p",
                Exists(
                    "q",
                    two_points_on_line_body("p", "q", "l"),
                ),
            ),
        ),
    )


    LINE_HAS_POINT = Forall(
        "l",
        Imp(
            Ln("l"),
            Exists("p", And(Pt("p"), Inc("p", "l"))),
        ),
    )


    P = Proof(IG)

    P.assume(AX_LINE_HAS_TWO_POINTS)

    G = Proof(P, goal=LINE_HAS_POINT)
    G.conclude(Eq("l", "l"))

    H = Proof(
        G,
        goal=Imp(
            Ln("l"),
            Exists("p", And(Pt("p"), Inc("p", "l"))),
        ),
    )

    H.assume(Ln("l"))

    H.conclude(
        Imp(
            Ln("l"),
            Exists(
                "p",
                Exists(
                    "q",
                    two_points_on_line_body("p", "q", "l"),
                ),
            ),
        )
    )

    H.conclude(
        Exists(
            "p",
            Exists(
                "q",
                two_points_on_line_body("p", "q", "l"),
            ),
        )
    )

    H.conclude(
        Exists(
            "q",
            two_points_on_line_body("u", "q", "l"),
        )
    )

    H.conclude(two_points_on_line_body("u", "v", "l"))

    H.conclude(And(Pt("u"), Pt("v")))
    H.conclude(Pt("u"))

    H.conclude(And(Inc("u", "l"), Inc("v", "l")))
    H.conclude(Inc("u", "l"))

    H.conclude(And(Pt("u"), Inc("u", "l")))

    H.conclude(
        Exists(
            "p",
            And(Pt("p"), Inc("p", "l")),
        )
    )

    G.goal(H)

    G.conclude(
        Imp(
            Ln("l"),
            Exists("p", And(Pt("p"), Inc("p", "l"))),
        )
    )

    P.goal(G)

Proof commands
--------------

The main user-facing commands are:

    P.assume("...")
    P.conclude("...")
    P.goal(subproof)

A line is accepted only if it is syntactically valid and follows from the current context by one of the implemented rules. If not, folab raises an error and the invalid line is not added.

Deduction rules currently implemented
-------------------------------------

The checker currently attempts to detect:

- use of an available formula;
- true introduction;
- false elimination;
- conjunction introduction;
- conjunction elimination;
- disjunction introduction;
- disjunction elimination;
- implication elimination;
- implication introduction through goals/subproofs;
- universal elimination;
- universal introduction through goals/subproofs;
- existential introduction;
- existential elimination using a fresh witness;
- equality introduction;
- equality elimination;
- double-negation elimination;
- reformulation of bound variables.

Syntax notes
------------

The module expects exact bracket-language syntax. For example:

    [A] and [B]
    [A] implies [B]
    for every [x] we have [[x]=[x]]
    there exists [x] such that [[x]<[y]]

Terms and formulas are distinguished by the declared language. For example, if []+[] is declared as an operation, then

    [x]+[y]

is a term. If []<[] is declared as a relation, then

    [x]<[y]

is a formula.

Status
------

folab is experimental. It is meant as a teaching and exploration tool rather than a complete theorem prover. The proof checker is deliberately explicit and conservative, so some valid mathematical arguments may need to be written in a more detailed form before the program accepts them.

Possible future improvements
----------------------------

- Web interface for entering languages and proofs online.
- Better error messages explaining why a line failed.
- Export of completed proofs to LaTeX.
- More robust parsing and pretty-printing.
- A library of examples from algebra, order theory, and incidence geometry.
- Optional classical or intuitionistic proof modes.

License
-------

Choose a license before making the repository public. For an educational open-source project, the MIT License is a simple option.
