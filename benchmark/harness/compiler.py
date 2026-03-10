"""Lean 4 compilation verification for benchmark.

Substitutes proof bodies into theorem files and verifies via lake build
or check_snippet.sh.
"""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
from dataclasses import dataclass, field
from pathlib import Path

# Project root (statlean/)
PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
CHECK_SNIPPET = PROJECT_ROOT / "scripts" / "check_snippet.sh"


@dataclass
class CompileResult:
    """Result of compiling a proof attempt."""
    success: bool
    error_message: str
    sorry_count: int  # sorry count in target theorem's substituted proof
    wall_time_s: float
    check_mode: str = "lake"  # "lake" or "snippet" — for traceability
    file_sorry_count: int = 0  # total sorry warnings in the whole module
    target_sorry_free: bool = False  # whether the target theorem is sorry-free


class LeanCompiler:
    """Verifies Lean 4 proof attempts by substitution + compilation."""

    def __init__(self, project_root: Path | str | None = None, timeout: int = 120):
        self.project_root = Path(project_root) if project_root else PROJECT_ROOT
        self.timeout = timeout

    def check_proof(
        self,
        lean_file: str,
        theorem_name: str,
        proof_body: str,
        *,
        use_snippet: bool = False,
    ) -> CompileResult:
        """Substitute proof_body for the theorem's sorry and compile.

        Args:
            lean_file: Path to .lean file relative to project root
            theorem_name: Name of the theorem to replace
            proof_body: The proof text (everything after `:= by`)
            use_snippet: Use check_snippet.sh (opt-in, default False for reliability)

        Returns:
            CompileResult with success status and error details.
        """
        abs_path = self.project_root / lean_file
        if not abs_path.exists():
            return CompileResult(
                success=False,
                error_message=f"File not found: {abs_path}",
                sorry_count=0,
                wall_time_s=0.0,
            )

        original = abs_path.read_text()

        # Find the theorem and its proof body
        substituted, start_line, end_line, decl_line = self._substitute_proof(
            original, theorem_name, proof_body
        )
        if substituted is None:
            return CompileResult(
                success=False,
                error_message=f"Could not find theorem '{theorem_name}' in {lean_file}",
                sorry_count=0,
                wall_time_s=0.0,
            )

        # Count sorry in the substituted proof body itself
        target_sorry = proof_body.lower().count("sorry")

        if use_snippet and CHECK_SNIPPET.exists():
            result = self._check_via_snippet(
                abs_path, substituted, start_line, end_line
            )
            result.check_mode = "snippet"
        else:
            result = self._check_via_lake(
                abs_path, original, substituted, lean_file, theorem_name,
                decl_line=decl_line,
            )
            result.check_mode = "lake"

        result.sorry_count = target_sorry

        # If the proof body itself contains sorry, override success to False
        # regardless of what lake build reported (it compiles with sorry as warning)
        if target_sorry > 0:
            result.success = False
            result.target_sorry_free = False
            if not result.error_message or result.error_message == "":
                result.error_message = f"Proof body contains {target_sorry} sorry"

        return result

    def check_full_file(self, lean_content: str, lean_file: str) -> CompileResult:
        """Check a complete .lean file by writing it and running lake build."""
        abs_path = self.project_root / lean_file
        original = abs_path.read_text() if abs_path.exists() else None

        try:
            abs_path.write_text(lean_content)
            module = lean_file.replace("/", ".").removesuffix(".lean")
            result = self._run_lake_build(module)
            return result
        finally:
            if original is not None:
                abs_path.write_text(original)
            elif abs_path.exists():
                abs_path.unlink()

    def _substitute_proof(
        self, source: str, theorem_name: str, proof_body: str
    ) -> tuple[str | None, int, int, int]:
        """Replace a theorem's proof body, return (new_source, start_line, end_line, decl_line).

        Handles patterns:
          theorem foo ... := by
            <proof>
          theorem foo ... := by sorry
          theorem foo ... where
            <proof>

        decl_line is the 0-indexed line number of the theorem declaration (stable
        across substitution since it precedes the proof body).
        """
        lines = source.split("\n")

        # Find the theorem declaration line
        decl_pattern = re.compile(
            rf"^(theorem|lemma|def|noncomputable def)\s+{re.escape(theorem_name)}\b"
        )
        decl_line = None
        for i, line in enumerate(lines):
            if decl_pattern.match(line.strip()):
                decl_line = i
                break

        if decl_line is None:
            return None, 0, 0, 0

        # Scan forward from declaration until we find proof start.
        # No hardcoded window — scan until next top-level declaration or EOF.
        proof_start = None
        for i in range(decl_line, len(lines)):
            stripped = lines[i].strip()
            if ":= by" in lines[i] or stripped == ":= by":
                proof_start = i
                break
            if ":= sorry" in lines[i]:
                proof_start = i
                break
            if stripped.endswith("where"):
                proof_start = i
                break
            if stripped == "sorry" and i > decl_line:
                proof_start = i
                break
            # Stop if we hit a new declaration (means no proof body found)
            if i > decl_line and stripped and re.match(
                r"^(theorem|lemma|def|noncomputable|section|end\s|namespace|open\s|#|/-!|attribute|instance|@\[)",
                stripped,
            ):
                break

        if proof_start is None:
            return None, 0, 0, 0

        # Find where the proof body ends
        proof_end = self._find_proof_end(lines, proof_start)

        # Build the new source
        header_line = lines[proof_start]
        if ":= by" in header_line:
            if header_line.strip() == ":= by" or header_line.strip().endswith(":= by"):
                new_lines = lines[:proof_start + 1] + [proof_body] + lines[proof_end + 1:]
            else:
                idx = header_line.index(":= by")
                prefix = header_line[:idx] + ":= by"
                new_lines = lines[:proof_start] + [prefix, proof_body] + lines[proof_end + 1:]
        elif ":= sorry" in header_line:
            idx = header_line.index(":= sorry")
            prefix = header_line[:idx] + ":= by"
            new_lines = lines[:proof_start] + [prefix, proof_body] + lines[proof_end + 1:]
        elif lines[proof_start].strip() == "sorry":
            new_lines = lines[:proof_start] + [proof_body] + lines[proof_end + 1:]
        else:
            new_lines = lines[:proof_start + 1] + [proof_body] + lines[proof_end + 1:]

        new_source = "\n".join(new_lines)
        new_start = proof_start + 1
        new_end = proof_start + 1 + proof_body.count("\n") + 1

        return new_source, new_start, new_end, decl_line

    def _find_proof_end(self, lines: list[str], proof_start: int) -> int:
        """Find the last line of the current proof body."""
        if proof_start >= len(lines) - 1:
            return proof_start

        base_indent = len(lines[proof_start]) - len(lines[proof_start].lstrip())

        # Handle single-line sorry
        if "sorry" in lines[proof_start] and (
            ":= by sorry" in lines[proof_start]
            or ":= sorry" in lines[proof_start]
            or lines[proof_start].strip() == "sorry"
        ):
            return proof_start

        end = proof_start
        for i in range(proof_start + 1, len(lines)):
            stripped = lines[i].strip()
            if not stripped:
                end = i
                continue

            current_indent = len(lines[i]) - len(lines[i].lstrip())

            if current_indent <= base_indent and stripped and not stripped.startswith("--"):
                if re.match(
                    r"^(theorem|lemma|def|noncomputable|section|end|namespace|open|#|/-|attribute|instance|@)",
                    stripped,
                ):
                    break
            end = i

        return end

    def _check_via_snippet(
        self, abs_path: Path, substituted: str, start_line: int, end_line: int
    ) -> CompileResult:
        """Use check_snippet.sh for fast incremental checking."""
        import time as _time

        original = abs_path.read_text()
        try:
            abs_path.write_text(substituted)
            start = _time.monotonic()
            result = subprocess.run(
                ["bash", str(CHECK_SNIPPET), str(abs_path), str(start_line), str(end_line)],
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=str(self.project_root),
            )
            wall_time = _time.monotonic() - start

            if result.returncode == 0:
                return CompileResult(
                    success=True,
                    error_message="",
                    sorry_count=0,
                    wall_time_s=wall_time,
                    target_sorry_free=True,
                )
            else:
                error = result.stderr.strip() or result.stdout.strip()
                return CompileResult(
                    success=False,
                    error_message=error[:2000],
                    sorry_count=0,
                    wall_time_s=wall_time,
                )
        except subprocess.TimeoutExpired:
            return CompileResult(
                success=False,
                error_message=f"Compilation timed out after {self.timeout}s",
                sorry_count=0,
                wall_time_s=float(self.timeout),
            )
        finally:
            abs_path.write_text(original)

    def _check_via_lake(
        self,
        abs_path: Path,
        original: str,
        substituted: str,
        lean_file: str,
        theorem_name: str = "",
        decl_line: int | None = None,
    ) -> CompileResult:
        """Write file, run lake build, restore original.

        Distinguishes target-theorem sorry from file-level sorry:
        - success = True if build passes AND the target theorem is sorry-free
        - file_sorry_count records total sorry warnings (may include other theorems)
        - target_sorry_free specifically checks the target
        """
        import time as _time

        module = lean_file.replace("/", ".").removesuffix(".lean")
        try:
            abs_path.write_text(substituted)
            start = _time.monotonic()
            try:
                result = subprocess.run(
                    ["lake", "build", module],
                    capture_output=True,
                    text=True,
                    timeout=self.timeout,
                    cwd=str(self.project_root),
                )
                wall_time = _time.monotonic() - start
            except subprocess.TimeoutExpired:
                return CompileResult(
                    success=False,
                    error_message=f"lake build timed out after {self.timeout}s",
                    sorry_count=0,
                    wall_time_s=float(self.timeout),
                )

            output = (result.stderr + "\n" + result.stdout).strip()

            if result.returncode == 0:
                # Count all sorry warnings in the module
                file_sorry_count = output.count("declaration uses 'sorry'")

                # Check if the TARGET theorem specifically uses sorry.
                # Lean outputs: warning: <file>:<line>:<col>: declaration uses 'sorry'
                # followed by a note line naming the declaration.
                target_has_sorry = self._target_uses_sorry(
                    output, theorem_name, lean_file, decl_line=decl_line
                )

                target_sorry_free = not target_has_sorry
                if file_sorry_count > 0 and not target_has_sorry:
                    warning_msg = (
                        f"INFO: {file_sorry_count} sorry warning(s) in module "
                        f"attributed to other declarations, target '{theorem_name}' clean"
                    )
                elif target_has_sorry:
                    warning_msg = f"target '{theorem_name}' uses sorry"
                else:
                    warning_msg = ""

                return CompileResult(
                    success=target_sorry_free,
                    error_message=warning_msg,
                    sorry_count=1 if target_has_sorry else 0,
                    wall_time_s=wall_time,
                    file_sorry_count=file_sorry_count,
                    target_sorry_free=target_sorry_free,
                )
            else:
                error_lines = []
                for line in output.split("\n"):
                    line_s = line.strip()
                    if line_s.startswith("error:") and ".lean:" in line_s:
                        error_lines.append(line_s)
                    elif line_s.startswith("warning:") and ".lean:" in line_s:
                        error_lines.append(line_s)
                if not error_lines:
                    error_lines = [l for l in output.split("\n")[-5:] if l.strip()]
                error = "\n".join(error_lines)
                return CompileResult(
                    success=False,
                    error_message=error[:2000],
                    sorry_count=0,
                    wall_time_s=wall_time,
                )
        finally:
            abs_path.write_text(original)

    @staticmethod
    def _target_uses_sorry(
        build_output: str,
        theorem_name: str,
        lean_file: str,
        decl_line: int | None = None,
    ) -> bool:
        """Check if a specific theorem is among the sorry warnings.

        Lean 4 outputs sorry warnings like:
            warning: Statlean/Foo.lean:42:0: declaration uses 'sorry'
        Sometimes followed by a note with the declaration name.

        We use two independent signals (either triggers True):
        1. **Line-number match**: Parse the warning line number and compare to
           the target theorem's declaration line (reliable — Lean always emits
           the warning at the declaration site).
        2. **Name match**: Check if the theorem name appears in the warning context
           lines (fallback for when decl_line is unavailable).

        If NEITHER matches, the sorry warnings belong to other declarations.
        """
        if "declaration uses 'sorry'" not in build_output:
            return False

        # Normalize lean_file for path matching (strip leading ./)
        lean_file_norm = lean_file.lstrip("./")

        lines = build_output.split("\n")
        for i, line in enumerate(lines):
            if "declaration uses 'sorry'" not in line:
                continue

            # Signal 1: line-number match
            # Format: "warning: <path>:<line>:<col>: declaration uses 'sorry'"
            if decl_line is not None:
                m = re.search(r"(\S+\.lean):(\d+):\d+:\s*declaration uses", line)
                if m:
                    warn_file = m.group(1).lstrip("./")
                    warn_line_1idx = int(m.group(2))
                    # decl_line is 0-indexed, Lean uses 1-indexed
                    file_match = (
                        lean_file_norm in warn_file
                        or warn_file in lean_file_norm
                    )
                    if warn_line_1idx == decl_line + 1 and file_match:
                        return True

            # Signal 2: name match in surrounding lines
            context = line
            if i + 1 < len(lines):
                context += " " + lines[i + 1]
            if i + 2 < len(lines):
                context += " " + lines[i + 2]
            if theorem_name in context:
                return True

        # No match — sorry warnings belong to other declarations in the file.
        return False
