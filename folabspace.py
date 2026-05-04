"""
folabspace.py

A minimal Streamlit interface for folab.py.

Folder structure:

    folab.py
    folabspace.py
    requirements.txt

requirements.txt should contain:

    streamlit

Run locally with:

    streamlit run folabspace.py

The app uses a small proof-script language:

    ASSUME <formula>
    CONCLUDE <formula>
    GOAL <formula>
    END

A GOAL opens a nested subproof. END closes the current subproof.
"""

from __future__ import annotations

import contextlib
import io
import re
from dataclasses import dataclass

import streamlit as st

from folab import FirstOrderLanguage, Proof


# -----------------------------------------------------------------------------
# Utility functions
# -----------------------------------------------------------------------------


def split_items(text: str) -> list[str]:
    """Split comma-separated or newline-separated input into a clean list."""
    items = re.split(r"[,\n]+", text)
    return [item.strip() for item in items if item.strip()]


@dataclass
class RunResult:
    ok: bool
    output: str
    error: str = ""
    failed_line_number: int | None = None
    failed_line: str = ""


# -----------------------------------------------------------------------------
# Proof-script runner
# -----------------------------------------------------------------------------


def run_script(language: FirstOrderLanguage, script: str) -> RunResult:
    """
    Run a proof script against folab and capture the console output.

    Supported commands:

        ASSUME <formula>
        CONCLUDE <formula>
        GOAL <formula>
        END

    Blank lines and lines beginning with # are ignored.
    """
    output = io.StringIO()
    proof_stack: list[Proof] = []

    try:
        with contextlib.redirect_stdout(output):
            root = Proof(language)
            proof_stack.append(root)

            for line_number, raw_line in enumerate(script.splitlines(), start=1):
                line = raw_line.strip()

                if not line or line.startswith("#"):
                    continue

                active_proof = proof_stack[-1]
                command = line.upper()

                if command.startswith("ASSUME "):
                    formula = line[len("ASSUME ") :].strip()
                    active_proof.assume(formula)

                elif command.startswith("CONCLUDE "):
                    formula = line[len("CONCLUDE ") :].strip()
                    active_proof.conclude(formula)

                elif command.startswith("GOAL "):
                    formula = line[len("GOAL ") :].strip()
                    subproof = Proof(active_proof, goal=formula)
                    proof_stack.append(subproof)

                elif command == "END":
                    if len(proof_stack) == 1:
                        raise ValueError("END was used, but there is no open subproof.")

                    finished_subproof = proof_stack.pop()
                    parent_proof = proof_stack[-1]
                    parent_proof.goal(finished_subproof)

                else:
                    raise ValueError(
                        "Unknown command. Use ASSUME, CONCLUDE, GOAL, END, or # for comments."
                    )

            if len(proof_stack) != 1:
                raise ValueError(
                    f"There are {len(proof_stack) - 1} unclosed subproof(s). Add END line(s)."
                )

        return RunResult(ok=True, output=output.getvalue())

    except Exception as exc:
        return RunResult(
            ok=False,
            output=output.getvalue(),
            error=f"{type(exc).__name__}: {exc}",
            failed_line_number=line_number if "line_number" in locals() else None,
            failed_line=raw_line if "raw_line" in locals() else "",
        )


# -----------------------------------------------------------------------------
# Streamlit page
# -----------------------------------------------------------------------------


st.set_page_config(
    page_title="folabspace",
    page_icon="∴",
    layout="wide",
)

st.title("∴ folabspace")
st.caption("A minimal browser interface for building bracket-language first-order logic proofs.")

left, right = st.columns(2, gap="large")


# -----------------------------------------------------------------------------
# Left side: input
# -----------------------------------------------------------------------------


with left:
    st.subheader("Input")

    st.markdown("**1. First-order language**")

    variables_text = st.text_area(
        "Variables",
        value="x, y, z, A, B, C",
        height=80,
        help="Comma-separated or one per line. Variables must be bracketless atomic expressions.",
    )

    operations_text = st.text_area(
        "Operations",
        value="0, 1, []+[]",
        height=80,
        help="Examples: 0, 1, []*[], S[]. Constants are operations of arity 0.",
    )

    relations_text = st.text_area(
        "Relations",
        value="P[], Q[], []<[]",
        height=80,
        help="Examples: P[], []<[], Pt[], []I[]. Equality []=[] is added automatically.",
    )

    st.markdown("**2. Proof script**")

    default_script = """# Example: implication identity
GOAL [P[x]] implies [P[x]]
ASSUME P[x]
CONCLUDE P[x]
END
"""

    script = st.text_area(
        "Proof script",
        value=default_script,
        height=320,
        help="Use ASSUME, CONCLUDE, GOAL, END. Lines starting with # are ignored.",
    )

    check_button = st.button("Check proof", type="primary", use_container_width=True)


# -----------------------------------------------------------------------------
# Right side: output
# -----------------------------------------------------------------------------


with right:
    st.subheader("Output")

    if not check_button:
        st.info("Enter a language and proof script, then click **Check proof**.")
        st.markdown(
            """
Proof-script commands:

```text
ASSUME <formula>
CONCLUDE <formula>
GOAL <formula>
END
```
            """
        )

    else:
        try:
            variables = split_items(variables_text)
            operations = split_items(operations_text)
            relations = split_items(relations_text)

            language = FirstOrderLanguage(
                variables=variables,
                operations=operations,
                relations=relations,
            )

        except Exception as exc:
            st.error("Language declaration failed.")
            st.code(f"{type(exc).__name__}: {exc}", language="text")
            st.stop()

        result = run_script(language, script)

        if result.ok:
            st.success("Proof accepted.")
        else:
            st.error("Proof rejected.")
            if result.failed_line_number is not None:
                st.write(f"Failed at script line {result.failed_line_number}:")
                st.code(result.failed_line, language="text")
            st.code(result.error, language="text")

        st.markdown("**Console output**")
        st.code(result.output if result.output else "No output produced.", language="text")
