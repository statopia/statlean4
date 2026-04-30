#!/usr/bin/env python3
"""match_pitfall.py — Python port of pitfallsMatcher.ts.

Match a Lean compiler error against the 23-rule routing table from
`docs/pitfalls/`, returning a one-line suggestion pointing at the most
relevant file:§section the agent should consult.

The hint is appended to the `lake-build-fail` event's `blocker` field by
`process_sorry_result.py` on every `--status lake_build_fail` invocation
(T1 within T2 chain — see docs/E12_PHASE_02_PITFALLS_KB_SPEC.md §7).

Path alias: any `read_file path="docs/pitfalls/<name>.md"` call from
prove-deep.md narrative resolves to `theme/pitfalls/<name>.md` in the
statlean repo. The hint strings below deliberately say `docs/pitfalls/`
(byte-equal to czy) so that agents following prove-deep.md instructions
produce the right `read_file` calls. The CLI read_file resolver must map
`docs/pitfalls/` → `theme/pitfalls/` (D-5 shim; see _path_alias.py).

CLI:
    python3 theme/scripts/match_pitfall.py \\
        --error-text "<raw LSP/lake stderr>"
        [--sandbox <path>]   # if provided, emits pitfall-matched milestone
        [--sorry-id <id>]    # for milestone payload

Exit codes:
  0 — a rule matched; one line printed to stdout
  1 — no rule matched; no output
  2 — argument error
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"

# Maximum chars of error text inspected (matches pitfallsMatcher.ts:199).
_MAX_ERROR_LEN = 4000


@dataclass
class PitfallRule:
    """Mirror of PitfallRule interface from pitfallsMatcher.ts."""
    pattern: re.Pattern
    file: str      # "docs/pitfalls/lean_syntax_errors.md" (verbatim — path alias in CLI)
    section: str   # "§A.1"
    hint: str      # one-sentence hint


def _c(pat: str, flags: int = 0) -> re.Pattern:
    """Compile with re.IGNORECASE always (matches TS default `RegExp.test`
    case-insensitive behaviour — all TS patterns are used without `i` flag
    but matched via case-insensitive .test semantics in pitfallsMatcher).

    Actually: TS patterns are NOT given the `i` flag by default — only rule
    21 explicitly uses `/i`. We reproduce the exact TS behaviour:
    - Most patterns: re.IGNORECASE (TS RegExp literals without /i are still
      case-sensitive, but the hint file targets Lean compiler output which
      uses consistent casing; mirroring TS exactly means NO re.IGNORECASE for
      most rules). We match the TS source flag-by-flag below.
    """
    return re.compile(pat, flags)


# ── PITFALL_RULES — byte-equal logical port of pitfallsMatcher.ts:37-187 ──
#
# Rule ordering: FIRST match wins (matches TS priority table).
# Flags documented per-rule; re.DOTALL used for TS `/s` patterns.
#
# Rules 4, 7, 13, 18, 19 use re.DOTALL (TS `/s` flag for multiline matching).
# Rule 21 uses re.IGNORECASE (TS `/i` flag).
# All other rules: no flags (TS patterns have neither /s nor /i).

PITFALL_RULES: list[PitfallRule] = [
    # ── Parser / lexer (lean_syntax_errors.md §A) ─────────────────────
    # Rule 1
    PitfallRule(
        pattern=_c(r"unexpected token ['\"`]([λΠΣ∀∃])['\"`]"),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.1",
        hint="Reserved-keyword char (λ Π Σ ∀ ∃) embedded in an identifier. "
             "Rename every occurrence to ASCII (λ→lambda, Σ→Sigma).",
    ),
    # Rule 2
    PitfallRule(
        pattern=_c(r"unexpected token ['\"`](in|notin|and|or|not)['\"`]"),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.2",
        hint="English-word operator. If in a ∑/∏ binder: write `∑ i ∈ S, f i` "
             "not `∑ i in S, f i` — `in` was removed from binders. "
             "Otherwise use ∈, ∉, ∧, ∨, ¬.",
    ),
    # Rule 3
    PitfallRule(
        pattern=_c(
            r"unexpected token ['\"`](theorem|def|lemma|noncomputable|instance|variable)['\"`]"
        ),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.3",
        hint="Previous declaration is unclosed. "
             "Read 5–20 lines BEFORE the reported error and balance ( { [.",
    ),
    # Rule 4  (re.DOTALL — TS /s flag)
    PitfallRule(
        pattern=_c(
            r"Unknown identifier.*\bNote: It is not possible to treat .* as an implicitly bound variable",
            re.DOTALL,
        ),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.4",
        hint="You used a name in a binder before declaring it. "
             "Move its declaration earlier in the signature.",
    ),
    # Rule 5
    PitfallRule(
        pattern=_c(r"unexpected identifier; expected command"),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.5",
        hint="`/-! ... -/` section-doc inside a tactic block ends parsing. "
             "Use `-- ...` line comments inside `by`.",
    ),
    # Rule 6  (combining marks U+0300–U+036F)
    PitfallRule(
        pattern=_c(r"(expected token|unexpected token).*[̀-ͯ]"),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§A.6",
        hint="Combining mark (β̂ θ̂ X̄ X̃) rejected by the lexer. "
             "Rename to ASCII (β̂→hat_beta, X̄→bar_X).",
    ),

    # ── Statistics domain: Fin n vs Fin p dimension confusion ─────────
    # Rule 7  (re.DOTALL — TS /s flag)
    PitfallRule(
        pattern=_c(
            r"failed to synthesize.*\bHAdd\b.*Fin\s*[np].*→\s*ℝ.*Fin\s*[np].*→\s*ℝ",
            re.DOTALL,
        ),
        file="docs/pitfalls/statistics_domain.md",
        section="§D.3",
        hint="Dimension mismatch: noise must be `Fin n → ℝ` (observations), "
             "not `Fin p → ℝ` (parameters). "
             "Fix: `(eps : Fin n → ℝ)` so that "
             "`((Xᵀ*X)⁻¹*Xᵀ).mulVec eps : Fin p → ℝ` matches "
             "`beta_0 : Fin p → ℝ`.",
    ),

    # ── Typeclass synthesis (typeclass_errors.md §A) ──────────────────
    # Rule 8
    PitfallRule(
        pattern=_c(r"failed to synthesize.*\bOrderBot\b|failed to synthesize.*\bSupSet\b.*ℝ"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§A.1",
        hint="ℝ has no OrderBot. Use `⨆ j : Fin p, f j` (iSup) instead of "
             "`Finset.univ.sup`, or `Finset.sup'` with a nonempty proof.",
    ),
    # Rule 9
    PitfallRule(
        pattern=_c(
            r"failed to synthesize.*\b(IsProbabilityMeasure|IsFiniteMeasure|SigmaFinite)\b"
        ),
        file="docs/pitfalls/typeclass_errors.md",
        section="§A.2",
        hint="Add `haveI : IsProbabilityMeasure μ := ⟨measure_univ⟩` or "
             "`haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm`.",
    ),
    # Rule 10
    PitfallRule(
        pattern=_c(r"failed to synthesize.*\bMeasurableSpace\b"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§A.3",
        hint="Add `[MeasurableSpace α]` parameter, or "
             "`import Mathlib.MeasureTheory.MeasurableSpace.Basic` "
             "for ℝ/ℕ/ℤ borel auto-derive.",
    ),
    # Rule 11
    PitfallRule(
        pattern=_c(r"failed to synthesize.*\bIntegrable\b"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§A.4",
        hint="Add `(hf : Integrable f μ)` hypothesis or derive via "
             "`Integrable.of_bound h_meas.aestronglyMeasurable C h_bound`.",
    ),
    # Rule 12
    PitfallRule(
        pattern=_c(r"failed to synthesize.*\bFintype\b"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§A.5",
        hint="Ensure `n : ℕ` is concrete or add "
             "`haveI : Fintype (Fin n) := Fin.fintype n`.",
    ),
    # Rule 13  (re.DOTALL — TS /s flag; ✝ is U+2020)
    PitfallRule(
        pattern=_c(
            r"(synthesized type|inferred type).*inst[✝*]?\d|synthesized .* inferred .* inst[✝*]",
            re.DOTALL,
        ),
        file="docs/pitfalls/instance_pollution.md",
        section="§A",
        hint="Multiple MeasurableSpace Ω in scope. "
             "Pin ambient: `let m0 : MeasurableSpace Ω := ‹MeasurableSpace Ω›`, "
             "then use `@MeasurableSet Ω m0 ...` for ambient facts.",
    ),

    # ── Performance (typeclass_errors.md §B) ──────────────────────────
    # Rule 14
    PitfallRule(
        pattern=_c(r"\(deterministic\) timeout at ['\"`]?typeclass['\"`]?"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§B.1",
        hint="Typeclass loop. Try `letI : T := ...` to skip search, "
             "or check for sub-σ-algebra ambiguity (instance_pollution.md).",
    ),
    # Rule 15
    PitfallRule(
        pattern=_c(r"\(deterministic\) timeout|maximum number of heartbeats"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§B.2",
        hint="500k-heartbeat timeout. For sub-σ-algebra cases use the "
             "three-tier strategy (instance_pollution.md §B.3); "
             "else `set_option maxHeartbeats 800000 in`.",
    ),
    # Rule 16
    PitfallRule(
        pattern=_c(r"maximum recursion depth has been reached"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§B.3",
        hint="Replace term-mode chain with tactic-mode + intermediate `have` steps; "
             "or `set_option maxRecDepth 1024 in`.",
    ),
    # Rule 17
    PitfallRule(
        pattern=_c(r"fail to show termination"),
        file="docs/pitfalls/typeclass_errors.md",
        section="§B.4",
        hint="Add `termination_by <decreasing measure>` to the recursive def.",
    ),

    # ── Elaboration (lean_syntax_errors.md §B) ────────────────────────
    # Rule 18  (re.DOTALL — TS /s flag; [^]* → [\s\S]*? in Python)
    PitfallRule(
        pattern=_c(
            r"type mismatch[\s\S]*?\bℕ\b[\s\S]*?\bℝ\b"
            r"|type mismatch[\s\S]*?\bℝ\b[\s\S]*?\bℕ\b",
            re.DOTALL,
        ),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§B.2",
        hint="ℕ↔ℝ coercion: `(x : ℝ)` or `↑x`.",
    ),
    # Rule 19  (re.DOTALL — TS /s flag)
    PitfallRule(
        pattern=_c(
            r"tactic ['\"`]exact['\"`] failed.*type mismatch",
            re.DOTALL,
        ),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§B.3",
        hint="Try `apply` instead of `exact`, or break into intermediate `have` steps. "
             "Use `refine ?_` to inspect expected type.",
    ),
    # Rule 20
    PitfallRule(
        pattern=_c(r"no goals to be solved"),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§B.6",
        hint="Previous tactic already closed the goal. Delete the redundant tactic.",
    ),
    # Rule 21  (re.IGNORECASE — TS /i flag)
    PitfallRule(
        pattern=_c(r"numerals are .* but expected (type )?(is )?Prop", re.IGNORECASE),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§B.5",
        hint="Replace numeric literal with the corresponding lemma term "
             "(e.g. `tendsto_const_nhds` instead of `1`).",
    ),
    # Rule 22
    PitfallRule(
        pattern=_c(
            r"Unknown identifier ['\"`](Tendsto|atTop|𝓝|nhds|IndepFun|iIndepFun"
            r"|Integrable|condExp|gaussianReal|expMeasure)['\"`]"
        ),
        file="docs/pitfalls/lean_syntax_errors.md",
        section="§B.9",
        hint="Missing `open`. Add "
             "`open Filter Topology MeasureTheory ProbabilityTheory ENNReal` at the top.",
    ),

    # ── Statistics-domain "API does not exist" (statistics_domain.md §B) ─
    # Rule 23
    PitfallRule(
        pattern=_c(
            r"Unknown identifier ['\"`](gaussianVolume|expectation|Variance"
            r"|expDistribution|Normal|bernoulliMeasure)['\"`]"
        ),
        file="docs/pitfalls/statistics_domain.md",
        section="§B",
        hint="API does NOT exist — you guessed. "
             "Real names: `gaussianReal` (variance, not σ), `variance` (lowercase), "
             "`expMeasure`. `check_type` first.",
    ),
]

assert len(PITFALL_RULES) == 23, f"Expected 23 rules, got {len(PITFALL_RULES)}"


def match_pitfall(error_text: str) -> Optional[tuple[str, str, str]]:
    """Return (file, section, message) for the first matching rule, or None.

    Mirrors matchPitfallSuggestion from pitfallsMatcher.ts:194-212.
    Truncates error_text to _MAX_ERROR_LEN chars (same as TS :199).
    """
    if not error_text or not isinstance(error_text, str):
        return None
    trimmed = error_text[:_MAX_ERROR_LEN]
    for rule in PITFALL_RULES:
        if rule.pattern.search(trimmed):
            msg = (
                f"📚 Similar error pattern → see `{rule.file}` {rule.section}. "
                f"{rule.hint} "
                f'Read with `read_file path="{rule.file}"` for full context.'
            )
            return (rule.file, rule.section, msg)
    return None


def match_pitfall_suggestion(error_text: str) -> Optional[str]:
    """Public API: return the one-line hint string or None."""
    result = match_pitfall(error_text)
    return result[2] if result is not None else None


def match_pitfall_suggestion_from_list(errors: list[dict]) -> Optional[str]:
    """Variant that takes a list of {'message': str} dicts.

    Mirrors matchPitfallSuggestionFromList from pitfallsMatcher.ts:219-227.
    Returns the first match found across all errors, or None.
    """
    for e in errors:
        msg = e.get("message", "") if isinstance(e, dict) else str(e)
        result = match_pitfall_suggestion(msg)
        if result is not None:
            return result
    return None


def _emit_milestone(sandbox: Path, sorry_id: str, file: str, section: str) -> None:
    """Emit pitfall-matched milestone to events.jsonl (best-effort)."""
    try:
        subprocess.run(
            [
                sys.executable, str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", "pitfall-matched",
                "--details", json.dumps({
                    "file": file,
                    "section": section,
                    "sorry_id": sorry_id,
                }),
            ],
            check=True,
            timeout=10,
        )
    except Exception as e:
        print(f"[match_pitfall] emit pitfall-matched failed: {e}", file=sys.stderr)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--error-text",
        required=True,
        help="Raw LSP/lake stderr to match against pitfall rules.",
    )
    ap.add_argument(
        "--sandbox",
        default=None,
        help="Sandbox path — if provided, emits pitfall-matched milestone.",
    )
    ap.add_argument(
        "--sorry-id",
        default=None,
        help="Sorry ID for milestone payload (used with --sandbox).",
    )
    args = ap.parse_args()

    result = match_pitfall(args.error_text)
    if result is None:
        sys.exit(1)

    file, section, msg = result
    print(msg)

    if args.sandbox:
        sandbox = Path(args.sandbox)
        if not sandbox.exists():
            print(
                f"[match_pitfall] sandbox does not exist: {sandbox}",
                file=sys.stderr,
            )
        else:
            _emit_milestone(sandbox, args.sorry_id or "", file, section)

    sys.exit(0)


if __name__ == "__main__":
    main()
