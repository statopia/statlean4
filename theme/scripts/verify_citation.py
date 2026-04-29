#!/usr/bin/env python3
"""verify_citation.py — bundle the side-effect chain for citation
verification (E11 slice; per docs/E11_CITATION_VERIFY_SPEC.md).

Two modes share yaml + milestone infrastructure but dispatch to
different verifier bodies:

  --mode library   compiler-driven 4-tactic ladder (czy citationVerify.ts:72-123)
                   tries `exact <name>`, then `apply <name> <;> assumption`,
                   then `exact <name>.mp`, then `exact <name>.mpr` —
                   first PASS short-circuits. Each tactic attempt does
                   tempfile-replace + lake build + revert-on-fail.
  --mode reference LLM 3-way check via citation-verify Task subagent.
                   Subagent emits JSON; this script parses + writes yaml.

Per CLAUDE.md Rule 9 §3 (T-tier): T2 single-script bundling. Agent
invokes once per eligible sorry; script atomically:

  - Reads sorry_backlog.yaml under flock + migrates v1 → v2 if needed
  - Validates eligibility (coverage_state + sorry_id present)
  - Dispatches matching path (compiler ladder OR JSON-parse)
  - On PASS:  writes state=DONE + done_reason + citation_verified=true
              + citation_verified_at = unix_ms
              (library path additionally leaves the working tactic in place)
  - On FAIL:  writes citation_verified=false + citation_verified_at
              (state stays INITIALIZED; coverage_state preserved per Q4=(a))
              (library path: source tree byte-identical to pre-call state)
  - Emits one `citation-verified` milestone with verdict + verifier mode

Rule 3 Layer 1 invariant (per record_retreat.py:11-13 precedent):
mutates ONLY the targeted sorry's state / done_reason /
citation_verified / citation_verified_at fields. Locked theorem
signature / file / line / theorem / parent_id / children /
history_log / coverage_state / coverage_citation / references stay
untouched. Library path additionally writes the sub-`.lean` body —
that's body-only mutation, not signature mutation; Layer 1 protects
the statement, not the proof body.

Exit codes:
  0  — verification applied (PASS or FAIL with proper yaml write)
  2  — validation error (sorry not found, ineligible coverage_state, malformed input)
  3  — yaml parse error
  4  — IO / lock failure

CLI:
  Library mode:
    python3 theme/scripts/verify_citation.py --mode library \\
        --sorry-id <id> --cited-lemma <Foo.bar> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--module-path Statlean.X.Y]   # for `lake build` target
        [--backlog-path PATH]

  Reference mode:
    python3 theme/scripts/verify_citation.py --mode reference \\
        --sorry-id <id> --subagent-json-file <path> \\
        --sandbox /home/gavin/statlean/Statlean/Web/$JOB_ID \\
        [--backlog-path PATH]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
EMIT_EVENT = SCRIPTS_DIR / "emit_event.py"
BACKLOG_DEFAULT = SCRIPTS_DIR.parent / "input" / "sorry_backlog.yaml"

sys.path.insert(0, str(SCRIPTS_DIR))
from _yaml_io import atomic_write_yaml, locked_backlog  # noqa: E402

# ── Library path tactic ladder (czy citationVerify.ts:89-94) ──────────


def _build_tactics(cited_lemma: str) -> List[str]:
    """Return czy's 4-tactic ladder in order. First PASS short-circuits.

    Byte-faithful to czy `:89-94`. The trailing `(by assumption)` on
    tactics 3-4 is load-bearing: iff-form lemmas typically carry
    hypothesis side-conditions on their `.mp` / `.mpr` projections,
    and `by assumption` discharges them from the local context.
    Without it, tactics 3-4 only fire when the iff projection has
    zero subgoals — a strictly weaker verifier than czy."""
    return [
        f"exact {cited_lemma}",
        f"apply {cited_lemma} <;> assumption",
        f"exact {cited_lemma}.mp (by assumption)",
        f"exact {cited_lemma}.mpr (by assumption)",
    ]


# ── Tactic attempt helper (split for testability) ─────────────────────


def _try_tactic(
    file_path: Path,
    sorry_line: int,
    tactic: str,
    module_path: Optional[str] = None,
) -> Tuple[bool, str]:
    """Attempt one tactic: replace `:= sorry` (or `sorry`) on `sorry_line`
    with the tactic, run `lake build`, return (passed, output_excerpt).

    On FAIL: ALWAYS reverts the file mutation before returning. The
    source tree is byte-identical to its pre-call state on FAIL —
    matches the contract of czy's `replace_sorry` `[REPLACE-FAIL]`
    branch (`toolRunner.ts:1184`).

    On PASS: file is left with the tactic in place. State=DONE rows
    are not re-attacked, so the post-mutation source IS what
    `lake build` and downstream pipeline want.

    Tests mock this helper directly. Real-mode invokes
    `subprocess.run(['lake', 'build', module_path or ''])`.
    """
    if not file_path.is_file():
        return False, f"file not found: {file_path}"
    original_bytes = file_path.read_bytes()
    try:
        # Apply edit
        lines = original_bytes.decode("utf-8").splitlines(keepends=True)
        if sorry_line < 1 or sorry_line > len(lines):
            return False, f"sorry_line {sorry_line} out of range (1..{len(lines)})"
        # Replace the FIRST occurrence of `sorry` on the target line.
        # Prefer matching `:= by sorry` → `:= by <tactic>` so block-tactic
        # context is preserved; fall back to bare `sorry` → `by <tactic>`.
        target = lines[sorry_line - 1]
        if "sorry" not in target:
            return False, f"no `sorry` on line {sorry_line}"
        # Substitute first occurrence only
        new_target = re.sub(r"\bsorry\b", f"by {tactic}", target, count=1)
        # If the target already had `by`, the agent's tactic context
        # belongs inside the same `by` block; collapse the redundant
        # `by by`.
        new_target = new_target.replace("by by ", "by ")
        lines[sorry_line - 1] = new_target
        file_path.write_text("".join(lines), encoding="utf-8")

        # Run lake build
        cmd = ["lake", "build"]
        if module_path:
            cmd.append(module_path)
        proc = subprocess.run(
            cmd,
            cwd=str(file_path.parent.parent.resolve()
                    if file_path.parent.name == "Statlean"
                    else file_path.parent.resolve()),
            capture_output=True,
            text=True,
            timeout=60,
        )
        if proc.returncode == 0:
            return True, "lake build clean"
        # Revert on fail
        file_path.write_bytes(original_bytes)
        excerpt = (proc.stderr or proc.stdout or "")[-200:]
        return False, excerpt
    except subprocess.TimeoutExpired:
        # Defensive: revert if we can
        try:
            file_path.write_bytes(original_bytes)
        except OSError:
            pass
        return False, "lake build timed out (60s)"
    except Exception as e:
        try:
            file_path.write_bytes(original_bytes)
        except OSError:
            pass
        return False, f"exception: {e}"


# ── Reference path JSON parse (czy citationVerify.ts:218-292) ─────────


_FENCE_RE = re.compile(r"```(?:json)?\s*\n?([\s\S]*?)\n?```")


def _unwrap_fenced_json(s: str) -> str:
    """Strip markdown code fences. Mirrors czy `:347-350` `stripJsonFences`."""
    m = _FENCE_RE.search(s)
    return m.group(1) if m else s


def parse_reference_subagent_output(raw_text: str) -> Tuple[bool, str]:
    """Parse citation-verify Task subagent's JSON output.

    Expected shape (czy `:177-204` REFERENCE_VERIFY_SYSTEM contract):
      { "verified": bool, "reasoning": "<text>" }

    Returns (verified, reasoning_excerpt). On any parse failure,
    returns (False, "parse failed: ...") — czy treats malformed output
    as fail (`:268-272`).
    """
    unwrapped = _unwrap_fenced_json(raw_text.strip())
    if not unwrapped.strip():
        return False, "parse failed: empty subagent output"
    try:
        parsed = json.loads(unwrapped)
    except json.JSONDecodeError as e:
        return False, f"parse failed: {e}"
    if not isinstance(parsed, dict):
        return False, f"parse failed: root not object ({type(parsed).__name__})"
    verified_raw = parsed.get("verified")
    if not isinstance(verified_raw, bool):
        # czy `:265-267`: missing/non-bool → fail
        return False, f"parse failed: missing or non-bool 'verified' field"
    reasoning = str(parsed.get("reasoning") or "")
    return verified_raw, reasoning[:1000]  # bound for milestone payload


# ── Eligibility ───────────────────────────────────────────────────────


_ELIGIBLE_LIBRARY = {"cited_by_library"}
_ELIGIBLE_REFERENCE = {"cited_by_reference"}


def _check_eligible(item: Dict[str, Any], mode: str) -> Optional[str]:
    """Return None if eligible, else error message."""
    cs = item.get("coverage_state")
    if mode == "library":
        if cs not in _ELIGIBLE_LIBRARY:
            return (
                f"sorry has coverage_state={cs!r}; "
                f"library mode requires one of {sorted(_ELIGIBLE_LIBRARY)}"
            )
    elif mode == "reference":
        if cs not in _ELIGIBLE_REFERENCE:
            return (
                f"sorry has coverage_state={cs!r}; "
                f"reference mode requires one of {sorted(_ELIGIBLE_REFERENCE)}"
            )
    if item.get("state") == "DONE":
        return f"sorry already DONE (idempotence guard)"
    return None


# ── Core ──────────────────────────────────────────────────────────────


def apply_library_verification(
    backlog_path: Path,
    sorry_id: str,
    cited_lemma: str,
    statlean_root: Path,
    module_path: Optional[str] = None,
    try_tactic_fn=None,  # injected for testability
) -> Dict[str, Any]:
    """Run the 4-tactic ladder. Returns the milestone payload dict.

    `try_tactic_fn(file_path, sorry_line, tactic, module_path) ->
    (passed, output)` is injected for tests; defaults to `_try_tactic`.

    Raises ValueError on validation failure.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")
    if not cited_lemma or not cited_lemma.strip():
        raise ValueError("cited-lemma is empty")
    fn = try_tactic_fn or _try_tactic

    started_ms = int(time.time() * 1000)
    tactics = _build_tactics(cited_lemma.strip())

    # Note: the tactic ladder (which includes subprocess `lake build`
    # calls inside `_try_tactic`) runs UNDER the backlog flock. With a
    # 60s lake-build timeout × 4 tactics, a single library verification
    # can hold the lock for up to ~240s. Concurrent verifies on
    # DIFFERENT sorries serialize too because they share one backlog
    # file. Per spec §6.1 R7 dispatches sorries serially anyway, so
    # this is acceptable — but document for future debuggers.
    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sorry_id), None)
        if item is None:
            raise ValueError(f"sorry_id not in sorry_items: {sorry_id}")
        err = _check_eligible(item, "library")
        if err is not None:
            raise ValueError(err)

        rel_file = item.get("file") or ""
        line_n = int(item.get("line", 0) or 0)
        if not rel_file or line_n <= 0:
            raise ValueError(
                f"sorry {sorry_id} has invalid file/line: {rel_file!r}, {line_n}"
            )
        # statlean_root is the parent of `Statlean/`; rel_file is like
        # "Statlean/X/Y.lean" so the absolute path is statlean_root / rel_file.
        file_path = (statlean_root / rel_file).resolve()

        verdict = "fail"
        passing_tactic: Optional[str] = None
        last_output = ""
        for tactic in tactics:
            try:
                passed, output = fn(file_path, line_n, tactic, module_path)
            except Exception as e:
                # Tool exception → fall through to next tactic
                # (czy `:143-156` "tool exception treated as fall-through")
                last_output = f"tactic raised: {e}"
                continue
            last_output = output
            if passed:
                verdict = "pass"
                passing_tactic = tactic
                break

        # Mutate yaml — only the four allow-listed fields
        now_ms = int(time.time() * 1000)
        for it in items:
            if it.get("id") == sorry_id:
                it["citation_verified"] = (verdict == "pass")
                it["citation_verified_at"] = now_ms
                if verdict == "pass":
                    it["state"] = "DONE"
                    it["done_reason"] = "library_verified"
                # On fail: state stays INITIALIZED; coverage_state preserved
                break

        atomic_write_yaml(backlog_path, data)

        elapsed = now_ms - started_ms
        return {
            "sorry_id": sorry_id,
            "verdict": verdict,
            "verifier": "library_compiler",
            "cited_lemma": cited_lemma.strip()[:200],
            "tactic_used": passing_tactic if verdict == "pass" else None,
            "reasoning": last_output[:200] if verdict == "fail" else "",
            "time_elapsed_ms": elapsed,
            "done_reason_set": "library_verified" if verdict == "pass" else None,
        }


def apply_reference_verification(
    backlog_path: Path,
    sorry_id: str,
    subagent_text: str,
) -> Dict[str, Any]:
    """Parse citation-verify Task subagent's JSON output and persist.

    Raises ValueError on validation failure.
    """
    if not backlog_path.exists():
        raise ValueError(f"backlog not found: {backlog_path}")

    started_ms = int(time.time() * 1000)
    verified, reasoning = parse_reference_subagent_output(subagent_text)
    verdict = "pass" if verified else "fail"

    with locked_backlog(backlog_path) as data:
        items: List[Dict[str, Any]] = data.get("sorry_items") or []
        item = next((it for it in items if it.get("id") == sorry_id), None)
        if item is None:
            raise ValueError(f"sorry_id not in sorry_items: {sorry_id}")
        err = _check_eligible(item, "reference")
        if err is not None:
            raise ValueError(err)

        # Cited-lemma excerpt for milestone — pull from coverage_citation
        # (E4 wrote it as "-- cited from reference: <text>"). Strip the
        # prefix for cleaner milestone payload.
        coverage_citation = str(item.get("coverage_citation") or "")
        prefix = "-- cited from reference: "
        if coverage_citation.startswith(prefix):
            cited_excerpt = coverage_citation[len(prefix):]
        else:
            cited_excerpt = coverage_citation

        now_ms = int(time.time() * 1000)
        for it in items:
            if it.get("id") == sorry_id:
                it["citation_verified"] = (verdict == "pass")
                it["citation_verified_at"] = now_ms
                if verdict == "pass":
                    it["state"] = "DONE"
                    it["done_reason"] = "reference_axiom"
                # On fail: state stays INITIALIZED; coverage_state preserved
                break

        atomic_write_yaml(backlog_path, data)

        elapsed = now_ms - started_ms
        return {
            "sorry_id": sorry_id,
            "verdict": verdict,
            "verifier": "reference_llm",
            "cited_lemma": cited_excerpt[:200],
            "tactic_used": None,
            "reasoning": reasoning[:200],
            "time_elapsed_ms": elapsed,
            "done_reason_set": "reference_axiom" if verdict == "pass" else None,
        }


# ── CLI ───────────────────────────────────────────────────────────────


def _emit(sandbox: Path, name: str, details: dict) -> None:
    """Best-effort milestone emission; logs but doesn't abort
    (matches record_retreat / extract_references pattern)."""
    try:
        subprocess.run(
            [
                "python3", str(EMIT_EVENT),
                "--sandbox", str(sandbox),
                "milestone",
                "--name", name,
                "--details", json.dumps(details, ensure_ascii=False),
            ],
            check=True,
        )
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        print(
            f"[verify_citation] emit_event {name} failed: {e}",
            file=sys.stderr,
        )


def _validate_payload(payload: Dict[str, Any]) -> None:
    """Spec §4 invariants asserted before emit."""
    verdict = payload["verdict"]
    verifier = payload["verifier"]
    done_set = payload["done_reason_set"]
    tactic = payload["tactic_used"]
    # verdict == "pass" ↔ done_reason_set != null
    assert (verdict == "pass") == (done_set is not None), (
        f"invariant: verdict={verdict} done_reason_set={done_set!r}"
    )
    # library: tactic_used iff pass
    if verifier == "library_compiler":
        assert (tactic is not None) == (verdict == "pass"), (
            f"library: verdict={verdict} but tactic_used={tactic!r}"
        )
    # reference: tactic_used always null
    if verifier.startswith("reference_"):
        assert tactic is None, (
            f"reference: tactic_used must be null, got {tactic!r}"
        )


def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    p.add_argument(
        "--mode",
        required=True,
        choices=["library", "reference"],
    )
    p.add_argument("--sorry-id", required=True)
    p.add_argument("--sandbox", required=True, help="for emit_event milestone")
    p.add_argument("--backlog-path", default=str(BACKLOG_DEFAULT))

    # Library-only flags
    p.add_argument(
        "--cited-lemma",
        help="Mathlib name (e.g. `Real.sqrt_lt_sqrt`); REQUIRED for --mode library",
    )
    p.add_argument(
        "--statlean-root",
        help="path to repo root (parent of Statlean/); defaults to backlog parent's parent",
    )
    p.add_argument(
        "--module-path",
        help="lake build target (e.g. `Statlean.Concentration.MGF`); optional",
    )

    # Reference-only flags
    p.add_argument(
        "--subagent-json-file",
        help="path to citation-verify Task subagent's JSON stdout; REQUIRED for --mode reference",
    )

    return p.parse_args()


def main() -> int:
    args = _parse_args()
    backlog_path = Path(args.backlog_path).resolve()
    sandbox = Path(args.sandbox).resolve()

    try:
        if args.mode == "library":
            if not args.cited_lemma:
                print(
                    "[verify_citation] --cited-lemma is required for --mode library",
                    file=sys.stderr,
                )
                return 2
            statlean_root = (
                Path(args.statlean_root).resolve()
                if args.statlean_root
                else backlog_path.parent.parent
            )
            payload = apply_library_verification(
                backlog_path=backlog_path,
                sorry_id=args.sorry_id,
                cited_lemma=args.cited_lemma,
                statlean_root=statlean_root,
                module_path=args.module_path,
            )
        else:  # reference
            if not args.subagent_json_file:
                print(
                    "[verify_citation] --subagent-json-file is required for --mode reference",
                    file=sys.stderr,
                )
                return 2
            json_path = Path(args.subagent_json_file).resolve()
            if not json_path.is_file():
                print(
                    f"[verify_citation] subagent json file not found: {json_path}",
                    file=sys.stderr,
                )
                return 2
            subagent_text = json_path.read_text(encoding="utf-8")
            payload = apply_reference_verification(
                backlog_path=backlog_path,
                sorry_id=args.sorry_id,
                subagent_text=subagent_text,
            )
    except ValueError as e:
        print(f"[verify_citation] validation: {e}", file=sys.stderr)
        return 2
    except yaml.YAMLError as e:
        print(f"[verify_citation] yaml parse failed: {e}", file=sys.stderr)
        return 3
    except OSError as e:
        print(f"[verify_citation] IO failure: {e}", file=sys.stderr)
        return 4

    _validate_payload(payload)
    _emit(sandbox, "citation-verified", payload)

    print(
        f"citation-verified: sorry={args.sorry_id} verdict={payload['verdict']} "
        f"verifier={payload['verifier']} "
        f"done_reason={payload['done_reason_set']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
