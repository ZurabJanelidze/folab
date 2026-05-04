"""
Streamlit interface for folab.

Save this file as app.py in the same GitHub repository/folder as folab.py.
Run locally with:

    streamlit run app.py

The app does not execute arbitrary Python entered by users. Instead, it uses a
small proof-script language:

    ASSUME <formula>
    CONCLUDE <formula>
    GOAL <formula>
    END

A GOAL opens a nested subproof. END closes the current subproof and asks its
parent proof to verify the goal.
"""

from __future__ import annotations

import contextlib
import io
import re
from dataclasses import dataclass
from typing import Callable

import streamlit as st

from folab import FirstOrderLanguage, Proof, ProofError, SyntaxErrorFOL


# -----------------------------------------------------------------------------
# Page setup
# -----------------------------------------------------------------------------

st.set_page_config(
    page_title="folab proof studio",
    page_icon="∴",
    layout="wide",
    initial_sidebar_state="expanded",
)


CUSTOM_CSS = """
<style>
.block-container {padding-top: 1.5rem; padding-bottom: 3rem;}
.folab-title {
    font-size: 2.4rem;
    font-weight: 800;
    letter-spacing: -0.04em;
    margin-bottom: 0.15rem;
}
.folab-subtitle {
    color: #667085;
    font-size: 1.05rem;
    margin-bottom: 1.2rem;
}
.folab-card {
    border: 1px solid rgba(128,128,128,0.20);
    border-radius: 18px;
    padding: 1.05rem 1.15rem;
    background: rgba(128,128,128,0.045);
    margin-bottom: 1rem;
}
.folab-small {
    font-size: 0.88rem;
    color: #667085;
}
.folab-ok {
    border-left: 5px solid #12b76a;
    padding-left: 0.75rem;
}
.folab-bad {
    border-left: 5px solid #f04438;
    padding-left: 0.75rem;
}
code {white-space: pre-wrap;}
</style>
"""

st.markdown(CUSTOM_CSS, unsafe_allow_html=True)


# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------


def split_items(raw: str) -> list[str]:
    """Split comma/newline-separated user input into non-empty strings."""
    parts = re.split(r"[,\n]+", raw)
    return [p.strip() for p in parts if p.strip()]


@dataclass
class ScriptResult:
    ok: bool
    output: str
    error: str | None = None
    line_number: int | None = None
    command: str | None = None


SAMPLE_BASIC = """# Conjunction commutativity
ASSUME [A] and [B]
CONCLUDE A
CONCLUDE B
CONCLUDE [B] and [A]
"""


SAMPLE_NESTED = """# Identity of implication
GOAL [A] implies [A]
ASSUME A
CONCLUDE A
END
"""


SAMPLE_INCIDENCE = """# Incidence geometry: every line has an incident point
# Axiom: every line has two incident points.
ASSUME for every [l] we have [[Ln[l]] implies [there exists [p] such that [there exists [q] such that [[[Pt[p]] and [Pt[q]]] and [[[p]I[l]] and [[q]I[l]]]]]]]

GOAL for every [l] we have [[Ln[l]] implies [there exists [p] such that [[Pt[p]] and [[p]I[l]]]]]
CONCLUDE [l]=[l]

GOAL [Ln[l]] implies [there exists [p] such that [[Pt[p]] and [[p]I[l]]]]
ASSUME Ln[l]
CONCLUDE [Ln[l]] implies [there exists [p] such that [there exists [q] such that [[[Pt[p]] and [Pt[q]]] and [[[p]I[l]] and [[q]I[l]]]]]]
CONCLUDE there exists [p] such that [there exists [q] such that [[[Pt[p]] and [Pt[q]]] and [[[p]I[l]] and [[q]I[l]]]]]
CONCLUDE there exists [q] such that [[[Pt[u]] and [Pt[q]]] and [[[u]I[l]] and [[q]I[l]]]]
CONCLUDE [[Pt[u]] and [Pt[v]]] and [[[u]I[l]] and [[v]I[l]]]
CONCLUDE [Pt[u]] and [Pt[v]]
CONCLUDE Pt[u]
CONCLUDE [[u]I[l]] and [[v]I[l]]
CONCLUDE [u]I[l]
CONCLUDE [Pt[u]] and [[u]I[l]]
CONCLUDE there exists [p] such that [[Pt[p]] and [[p]I[l]]]
END

CONCLUDE [Ln[l]] implies [there exists [p] such that [[Pt[p]] and [[p]I[l]]]]
END
"""


SAMPLE_MONOID = """# Monoid-style associativity instance
# Language should include variables x,y,z,w,p,q,r and operation []*[].
ASSUME for every [p] we have [for every [q] we have [for every [r] we have [[[[p]*[q]]*[r]]=[p]*[[q]*[r]]]]]

CONCLUDE for every [q] we have [for every [r] we have [[[[x]*[q]]*[r]]=[x]*[[q]*[r]]]]
CONCLUDE for every [r] we have [[[[x]*[y]]*[r]]=[x]*[[y]*[r]]]
CONCLUDE [[[x]*[y]]*[z]]=[x]*[[y]*[z]]
"""


EXAMPLES = {
    "Basic: conjunction": SAMPLE_BASIC,
    "Nested: implication identity": SAMPLE_NESTED,
    "Incidence: line has a point": SAMPLE_INCIDENCE,
    "Algebra: associativity instance": SAMPLE_MONOID,
}


DEFAULT_VARIABLES = "x, y, z, w, p, q, r, l, u, v"
DEFAULT_OPERATIONS = "0, 1, []*[]"
DEFAULT_RELATIONS = "A, B, C, []<[], Pt[], Ln[], Pl[], []I[]"


# -----------------------------------------------------------------------------
# Proof-script runner
# -----------------------------------------------------------------------------


def run_proof_script(language: FirstOrderLanguage, script: str) -> ScriptResult:
    """Run the folab proof-script language and capture console output."""
    out = io.StringIO()
    root: Proof | None = None
    stack: list[Proof] = []

    def current() -> Proof:
        if not stack:
            raise ProofError("There is no active proof. This should not happen.")
        return stack[-1]

    try:
        with contextlib.redirect_stdout(out):
            root = Proof(language)
            stack = [root]

            for idx, raw_line in enumerate(script.splitlines(), start=1):
                line = raw_line.strip()
                if not line or line.startswith("#"):
                    continue

                upper = line.upper()

                if upper.startswith("ASSUME "):
                    formula = line[len("ASSUME "):].strip()
                    current().assume(formula)

                elif upper.startswith("CONCLUDE "):
                    formula = line[len("CONCLUDE "):].strip()
                    current().conclude(formula)

                elif upper.startswith("GOAL "):
                    formula = line[len("GOAL "):].strip()
                    sub = Proof(current(), goal=formula)
                    stack.append(sub)

                elif upper == "END":
                    if len(stack) == 1:
                        raise ProofError("END was used, but there is no open subproof to close.")
                    sub = stack.pop()
                    current().goal(sub)

                else:
                    raise ProofError(
                        "Unknown command. Use ASSUME, CONCLUDE, GOAL, END, or # for comments."
                    )

            if len(stack) != 1:
                raise ProofError(
                    f"There are {len(stack)-1} unclosed subproof(s). Add END line(s)."
                )

        return ScriptResult(ok=True, output=out.getvalue())

    except Exception as exc:
        return ScriptResult(
            ok=False,
            output=out.getvalue(),
            error=f"{type(exc).__name__}: {exc}",
            line_number=idx if "idx" in locals() else None,
            command=raw_line if "raw_line" in locals() else None,
        )


# -----------------------------------------------------------------------------
# Sidebar
# -----------------------------------------------------------------------------

with st.sidebar:
    st.markdown("### ∴ folab studio")
    st.caption("Build and check bracket-language first-order proofs.")

    st.divider()

    example_name = st.selectbox("Load example", list(EXAMPLES.keys()))

    if st.button("Load selected example", use_container_width=True):
        st.session_state["script"] = EXAMPLES[example_name]
        if "Incidence" in example_name:
            st.session_state["variables"] = "l, p, q, u, v, x, y, z"
            st.session_state["operations"] = ""
            st.session_state["relations"] = "Pt[], Ln[], Pl[], []I[]"
        elif "Algebra" in example_name:
            st.session_state["variables"] = "x, y, z, w, p, q, r"
            st.session_state["operations"] = "e, []*[]"
            st.session_state["relations"] = "A, B, C"
        else:
            st.session_state["variables"] = DEFAULT_VARIABLES
            st.session_state["operations"] = DEFAULT_OPERATIONS
            st.session_state["relations"] = DEFAULT_RELATIONS
        st.rerun()

    st.divider()
    st.markdown("### Proof-script commands")
    st.code("ASSUME <formula>\nCONCLUDE <formula>\nGOAL <formula>\nEND", language="text")
    st.caption("A goal opens a nested subproof. END closes the current subproof.")


# -----------------------------------------------------------------------------
# Main page
# -----------------------------------------------------------------------------

st.markdown('<div class="folab-title">folab proof studio</div>', unsafe_allow_html=True)
st.markdown(
    '<div class="folab-subtitle">An interactive first-order logic proof checker using bracket-language syntax.</div>',
    unsafe_allow_html=True,
)

if "variables" not in st.session_state:
    st.session_state["variables"] = DEFAULT_VARIABLES
if "operations" not in st.session_state:
    st.session_state["operations"] = DEFAULT_OPERATIONS
if "relations" not in st.session_state:
    st.session_state["relations"] = DEFAULT_RELATIONS
if "script" not in st.session_state:
    st.session_state["script"] = SAMPLE_NESTED

left, right = st.columns([0.38, 0.62], gap="large")

with left:
    st.markdown("### 1. Define the language")
    st.markdown('<div class="folab-card">', unsafe_allow_html=True)
    variables_raw = st.text_area(
        "Variables",
        key="variables",
        height=95,
        help="Comma-separated or one per line. Variables should be bracketless atomic expressions.",
    )
    operations_raw = st.text_area(
        "Operations",
        key="operations",
        height=95,
        help="Examples: 0, 1, []*[], S[]. Constants are nullary operations.",
    )
    relations_raw = st.text_area(
        "Relations",
        key="relations",
        height=105,
        help="Examples: A, B, []<[], Pt[], []I[]. Equality []=[] is included automatically.",
    )
    st.markdown('</div>', unsafe_allow_html=True)

    variables = split_items(variables_raw)
    operations = split_items(operations_raw)
    relations = split_items(relations_raw)

    c1, c2, c3 = st.columns(3)
    c1.metric("Variables", len(variables))
    c2.metric("Operations", len(operations))
    c3.metric("Relations", len(relations) + 1, help="Includes equality automatically")

    try:
        L = FirstOrderLanguage(variables=variables, operations=operations, relations=relations)
        st.success("Language is valid.")
        language_ok = True
    except Exception as exc:
        st.error(f"Language error: {type(exc).__name__}: {exc}")
        L = None
        language_ok = False

    with st.expander("Fixed logical constructors", expanded=False):
        st.code(
            "true\nfalse\n[] and []\n[] or []\n[] implies []\nfor every [] we have []\nthere exists [] such that []",
            language="text",
        )

with right:
    st.markdown("### 2. Write the proof script")
    st.text_area(
        "Proof script",
        key="script",
        height=430,
        help="Use ASSUME, CONCLUDE, GOAL, END. Lines starting with # are ignored.",
    )

    col_run, col_clear = st.columns([0.75, 0.25])
    with col_run:
        run_clicked = st.button("▶ Check proof", type="primary", use_container_width=True)
    with col_clear:
        if st.button("Clear output", use_container_width=True):
            st.session_state.pop("last_result", None)
            st.rerun()

    if run_clicked:
        if not language_ok or L is None:
            st.session_state["last_result"] = ScriptResult(
                ok=False,
                output="",
                error="Cannot run proof: the language declaration is invalid.",
            )
        else:
            st.session_state["last_result"] = run_proof_script(L, st.session_state["script"])


# -----------------------------------------------------------------------------
# Output area
# -----------------------------------------------------------------------------

st.markdown("### 3. Proof output")

result: ScriptResult | None = st.session_state.get("last_result")

if result is None:
    st.info("Click **Check proof** to run the proof checker.")
else:
    if result.ok:
        st.markdown('<div class="folab-ok">', unsafe_allow_html=True)
        st.success("Proof script accepted.")
        st.markdown('</div>', unsafe_allow_html=True)
    else:
        st.markdown('<div class="folab-bad">', unsafe_allow_html=True)
        st.error("Proof script rejected.")
        if result.line_number is not None:
            st.write(f"Failed at script line **{result.line_number}**:")
            st.code(result.command or "", language="text")
        st.write(result.error)
        st.markdown('</div>', unsafe_allow_html=True)

    st.code(result.output or "No proof lines were produced before the error.", language="text")

    st.download_button(
        "Download proof output",
        data=result.output or result.error or "",
        file_name="folab-proof-output.txt",
        mime="text/plain",
        use_container_width=True,
    )


with st.expander("How this app works", expanded=False):
    st.markdown(
        """
This app imports your `folab.py` module and uses its `FirstOrderLanguage` and `Proof` classes.
It does **not** execute arbitrary Python typed by visitors. Instead, it reads a small proof-script language:

```text
ASSUME <formula>
CONCLUDE <formula>
GOAL <formula>
END
```

Each `CONCLUDE` line is passed to `Proof.conclude(...)`, so the module tries to detect which deduction rule applies.
If the line is invalid, `folab` raises an error and the proof stops.
        """
    )

st.caption("folab proof studio · experimental educational interface")
