"""Extract benchmark problems from StatLean .lean files.

Reads theorem declarations, extracts statement + imports + context,
replaces proof body with sorry for the benchmark.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from pathlib import Path

import yaml

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent


@dataclass
class Problem:
    """A benchmark problem extracted from a .lean file."""
    problem_id: str
    theorem_name: str
    lean_file: str  # relative to project root
    difficulty: str  # easy, medium, hard, open
    imports: str  # all import lines
    context: str  # section/variable/open declarations before the theorem
    statement: str  # theorem signature (up to `:= by`)
    ground_truth: str  # original proof body (not given to models)
    categories: list[str] = field(default_factory=list)
    api_sections: list[str] = field(default_factory=list)
    keywords: list[str] = field(default_factory=list)
    proof_lines: int = 0  # line count of ground truth proof


def extract_problem(
    lean_file: str,
    theorem_name: str,
    problem_id: str | None = None,
    difficulty: str = "medium",
    categories: list[str] | None = None,
    api_sections: list[str] | None = None,
    keywords: list[str] | None = None,
) -> Problem:
    """Extract a benchmark problem from a .lean file.

    Args:
        lean_file: Path relative to project root
        theorem_name: Name of the theorem to extract
        problem_id: ID for the problem (defaults to theorem_name)
        difficulty: easy/medium/hard/open
        categories: Tactic pattern categories for skill filtering
        api_sections: Mathlib API index sections for skill filtering
        keywords: Additional keywords for skill filtering
    """
    abs_path = PROJECT_ROOT / lean_file
    source = abs_path.read_text()
    lines = source.split("\n")

    # Extract imports (all lines starting with `import`)
    import_lines = []
    for line in lines:
        if line.startswith("import "):
            import_lines.append(line)
        elif line.strip() and not line.startswith("--") and not line.startswith("/-"):
            if not line.startswith("import"):
                break

    # Find the theorem declaration
    decl_pattern = re.compile(
        rf"^(theorem|lemma|def|noncomputable def)\s+{re.escape(theorem_name)}\b"
    )
    decl_line = None
    for i, line in enumerate(lines):
        if decl_pattern.match(line.strip()):
            decl_line = i
            break

    if decl_line is None:
        raise ValueError(f"Theorem '{theorem_name}' not found in {lean_file}")

    # Extract context: everything between imports and the theorem that's
    # needed (open, variable, section, noncomputable, etc.)
    context_lines = []
    for i in range(len(import_lines), decl_line):
        line = lines[i]
        stripped = line.strip()
        # Include structural declarations
        if stripped and (
            stripped.startswith("open ")
            or stripped.startswith("variable ")
            or stripped.startswith("section ")
            or stripped.startswith("end ")
            or stripped.startswith("namespace ")
            or stripped.startswith("noncomputable ")
            or stripped.startswith("set_option ")
            or stripped.startswith("attribute ")
            or stripped.startswith("/-!")  # module docstring
            or stripped.startswith("omit")
            or stripped.startswith("suppress_compilation")
        ):
            context_lines.append(line)
        elif stripped.startswith("--"):
            context_lines.append(line)
        elif not stripped:
            context_lines.append(line)

    # Find statement (from declaration to `:= by` or `:= sorry`)
    # No hardcoded window — scan until proof start or next declaration
    statement_lines = []
    proof_start_line = None
    for i in range(decl_line, len(lines)):
        line = lines[i]
        stripped = line.strip()
        if ":= by" in line:
            idx = line.index(":= by")
            statement_lines.append(line[: idx + 5])  # include `:= by`
            proof_start_line = i
            break
        elif ":= sorry" in line:
            idx = line.index(":= sorry")
            statement_lines.append(line[:idx] + ":= by")
            proof_start_line = i
            break
        elif stripped == "sorry" and i > decl_line:
            proof_start_line = i
            break
        elif i > decl_line and stripped and re.match(
            r"^(theorem|lemma|def|noncomputable|section|end\s|namespace|open\s|#|/-!|attribute|instance|@\[)",
            stripped,
        ):
            # Hit next declaration without finding proof — bail out
            break
        else:
            statement_lines.append(line)

    if proof_start_line is None:
        raise ValueError(f"Could not find proof body for '{theorem_name}' in {lean_file}")

    # Extract proof body (ground truth)
    proof_body_lines = []
    base_indent = len(lines[decl_line]) - len(lines[decl_line].lstrip())

    # Handle single-line proofs (`:= by sorry`, `:= sorry`, `:= by trivial`, etc.)
    if ":= by sorry" in lines[proof_start_line] or ":= sorry" in lines[proof_start_line]:
        proof_body_lines = ["  sorry"]
    elif lines[proof_start_line].strip() == "sorry":
        proof_body_lines = ["  sorry"]
    elif ":= by" in lines[proof_start_line]:
        # Check if there's proof text on the same line after `:= by`
        idx = lines[proof_start_line].index(":= by") + 5
        trailing = lines[proof_start_line][idx:].strip()
        if trailing:
            # Single-line proof like `theorem foo : True := by trivial`
            proof_body_lines = ["  " + trailing]
            # Also collect any continuation lines (multi-line starting on decl line)
            for i in range(proof_start_line + 1, len(lines)):
                stripped = lines[i].strip()
                if not stripped:
                    proof_body_lines.append(lines[i])
                    continue
                current_indent = len(lines[i]) - len(lines[i].lstrip())
                if current_indent <= base_indent and re.match(
                    r"^(theorem|lemma|def|noncomputable|section|end|namespace|open|#|/-|attribute|instance|@)",
                    stripped,
                ):
                    break
                proof_body_lines.append(lines[i])
        else:
            # `:= by` on its own at end of line — proof starts on next line
            for i in range(proof_start_line + 1, len(lines)):
                stripped = lines[i].strip()
                if not stripped:
                    proof_body_lines.append(lines[i])
                    continue
                current_indent = len(lines[i]) - len(lines[i].lstrip())
                if current_indent <= base_indent and re.match(
                    r"^(theorem|lemma|def|noncomputable|section|end|namespace|open|#|/-|attribute|instance|@)",
                    stripped,
                ):
                    break
                proof_body_lines.append(lines[i])
    else:
        # Multi-line proof: collect everything after the `:= by` line
        for i in range(proof_start_line + 1, len(lines)):
            stripped = lines[i].strip()
            if not stripped:
                proof_body_lines.append(lines[i])
                continue

            current_indent = len(lines[i]) - len(lines[i].lstrip())
            # Stop at a new top-level declaration
            if current_indent <= base_indent and re.match(
                r"^(theorem|lemma|def|noncomputable|section|end|namespace|open|#|/-|attribute|instance|@)",
                stripped,
            ):
                break
            proof_body_lines.append(lines[i])

    # Clean trailing blank lines from proof
    while proof_body_lines and not proof_body_lines[-1].strip():
        proof_body_lines.pop()

    # Also collect any helper lemmas/defs that are inside the proof's `where` block
    # or immediately preceding private lemmas
    preceding_helpers = _extract_preceding_helpers(lines, decl_line, base_indent)

    full_context = "\n".join(context_lines).strip()
    if preceding_helpers:
        full_context += "\n\n" + preceding_helpers

    return Problem(
        problem_id=problem_id or theorem_name,
        theorem_name=theorem_name,
        lean_file=lean_file,
        difficulty=difficulty,
        imports="\n".join(import_lines),
        context=full_context,
        statement="\n".join(statement_lines),
        ground_truth="\n".join(proof_body_lines),
        categories=categories or [],
        api_sections=api_sections or [],
        keywords=keywords or [],
        proof_lines=len([l for l in proof_body_lines if l.strip()]),
    )


def _extract_preceding_helpers(
    lines: list[str], decl_line: int, base_indent: int
) -> str:
    """Extract private helper lemmas that appear before the theorem
    but are needed for the proof (e.g., `private lemma`, `private def`).
    """
    helpers = []
    # Look backwards from the declaration for private helpers
    i = decl_line - 1
    while i >= 0:
        stripped = lines[i].strip()
        if not stripped:
            i -= 1
            continue
        # Check if it's a private helper
        if stripped.startswith("private ") or stripped.startswith("local "):
            # Collect the full helper (backwards until we hit blank or another decl)
            helper_lines = [lines[i]]
            j = i + 1
            while j < decl_line:
                if lines[j].strip():
                    current_indent = len(lines[j]) - len(lines[j].lstrip())
                    helper_indent = len(lines[i]) - len(lines[i].lstrip())
                    if current_indent > helper_indent:
                        helper_lines.append(lines[j])
                    else:
                        break
                else:
                    helper_lines.append(lines[j])
                j += 1
            helpers.insert(0, "\n".join(helper_lines))
            i -= 1
        else:
            break

    return "\n\n".join(helpers)


def problem_to_yaml(problem: Problem) -> dict:
    """Convert a Problem to a YAML-serializable dict."""
    return {
        "problem_id": problem.problem_id,
        "theorem_name": problem.theorem_name,
        "lean_file": problem.lean_file,
        "difficulty": problem.difficulty,
        "categories": problem.categories,
        "api_sections": problem.api_sections,
        "keywords": problem.keywords,
        "proof_lines": problem.proof_lines,
    }


def build_prompt_for_problem(
    problem: Problem,
    skill_context: str | None = None,
) -> list[dict]:
    """Build the prompt messages for a model to solve a problem.

    Args:
        problem: The benchmark problem
        skill_context: Optional skill enhancement text (for 'skill' condition)

    Returns:
        List of message dicts for the model adapter.
    """
    messages = []

    # System message
    system_parts = [
        "You are a Lean 4 proof assistant. Your task is to complete a theorem proof.",
        "Write ONLY the proof body (the tactics after `:= by`). Do not repeat the theorem statement.",
        "Do not include `:= by` — start directly with the first tactic.",
        "Do not use `sorry` anywhere in your proof.",
        "Wrap your proof in a ```lean code block.",
    ]

    if skill_context:
        system_parts.append("\n---\n")
        system_parts.append(skill_context)

    messages.append({"role": "system", "content": "\n".join(system_parts)})

    # User message: the problem
    user_parts = [
        "Complete the following Lean 4 theorem proof.\n",
        "### Imports and Context",
        "```lean",
        problem.imports,
        "",
        problem.context,
        "```\n",
        "### Theorem to Prove",
        "```lean",
        problem.statement,
        "```\n",
        "Provide the proof body (everything after `:= by`).",
    ]

    messages.append({"role": "user", "content": "\n".join(user_parts)})

    return messages


def build_retry_prompt(
    error_message: str,
    previous_attempt: str,
    retry_template: str | None = None,
) -> dict:
    """Build a retry message after a failed compilation.

    Returns a single user message dict to append to conversation.
    """
    if retry_template:
        text = retry_template.format(error=error_message)
    else:
        text = (
            f"The previous proof attempt failed with the following compilation error:\n\n"
            f"```\n{error_message}\n```\n\n"
            f"Please fix the proof. Provide the corrected proof body "
            f"(everything after `:= by`), wrapped in a ```lean code block."
        )

    return {"role": "user", "content": text}
