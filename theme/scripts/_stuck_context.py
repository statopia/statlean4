"""_stuck_context.py — assemble StuckContext for H4 dispatch_helper from
SDK-bridge persisted state (events.jsonl + history_log + sandbox files).

Architectural translation per `docs/H4_DISPATCH_HELPER_SPEC.md` D-6:
czy keeps `pending: { lastError, deadEnds, attempts, ... }` in an
in-memory `ProofStateManager` map (`controlAgent.ts:540-555`,
`proofLoop.ts:721-728`). The SDK-bridge has no such in-memory state;
instead, the relevant signals live in:

  - `<sandbox>/events.jsonl`  — `subagent-stuck` milestones with
    `details.blocker` (most recent error)
  - `theme/input/sorry_backlog.yaml` — parent's `history_log[]` with
    `retreat_reason` strings (cross-round restrategize history)
  - sandbox `.lean` file — code snippet around the failing `sorry` line
  - LSP probe (agent-side, not this module) — current Lean goal

This module reconstructs the czy `StuckContext` shape
(`helperSearchSubAgent.ts:67-76`):

    {
      currentGoal?: str,    # ≤ 1500 chars  (R6: agent-side LSP probe)
      lastError?:   str,    # ≤  200 chars  (czy proofLoop.ts:722)
      deadEnds?:    [str],  # last 5 entries, each ≤ 200 chars
                            # (czy proofLoop.ts:723-725 .slice(-5))
      codeAttempted?: str,  # ≤ 800 chars   (czy proofLoop.ts:727)
    }

Pure-functional + small surface; H4-mvp uses this only for its
`decide-helper-markers` SKILL inputs (lastError + deadEnds), but the
full structure is built so H5/H6 placeholders can read currentGoal +
codeAttempted when they land (D-9 forward-compat).

Layer 1 invariant: this module reads but never writes yaml/events.
"""
from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional


# czy length limits (verbatim per spec §3.4)
_LAST_ERROR_MAX = 200       # czy proofLoop.ts:722 entry.lastError.slice(0, 200)
_DEAD_END_ENTRY_MAX = 200   # czy proofLoop.ts:724 deadEnds.slice(-5) (each entry)
_DEAD_END_KEEP = 5          # czy proofLoop.ts:724 .slice(-5)
_CURRENT_GOAL_MAX = 1500    # czy proofLoop.ts:714 joined.slice(0, 1500)
_CODE_ATTEMPTED_MAX = 800   # czy proofLoop.ts:727 traceSummary.slice(0, 800)
_HISTORY_RETREAT_KEEP = 3   # last 3 retreat_reason strings (D-6 augmentation)
_DEDUPE_PREFIX = 80         # spec §3.4 "de-dupe by 80-char prefix"


@dataclass
class StuckContext:
    """Mirror of czy `helperSearchSubAgent.StuckContext`.

    All fields optional; `to_dict()` drops keys whose value is None or
    empty list so the JSON we serialize for downstream helpers (and tests)
    is minimal and matches czy's `undefined`-elision pattern.
    """
    current_goal: Optional[str] = None
    last_error: Optional[str] = None
    dead_ends: Optional[List[str]] = None
    code_attempted: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        out: Dict[str, Any] = {}
        if self.current_goal:
            out["currentGoal"] = self.current_goal
        if self.last_error:
            out["lastError"] = self.last_error
        if self.dead_ends:
            out["deadEnds"] = list(self.dead_ends)
        if self.code_attempted:
            out["codeAttempted"] = self.code_attempted
        return out


def _clamp(s: Optional[str], n: int) -> Optional[str]:
    """Return s clamped to n chars, or None if s is None/empty after strip.

    Mirrors czy's `.slice(0, N)` which is byte-positional in TS strings;
    Python `s[:n]` is char-positional but for our content (LLM output,
    Lean error text) the difference is negligible. Length budget is a
    UI/cost guard, not a security boundary.
    """
    if s is None:
        return None
    s = s.strip()
    if not s:
        return None
    return s[:n] if len(s) > n else s


def _read_events_jsonl(sandbox: Path) -> List[Dict[str, Any]]:
    """Load events.jsonl as a list of dicts; missing file → [].

    Each line is a JSON object per emit_event.py's append-only
    contract. Malformed lines are silently skipped (a bad line should
    never make StuckContext assembly fatal — the alternative is the
    helper dispatch breaking on a single corrupt event).
    """
    events_path = sandbox / "events.jsonl"
    if not events_path.exists():
        return []
    out: List[Dict[str, Any]] = []
    try:
        with events_path.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    out.append(json.loads(line))
                except json.JSONDecodeError:
                    # Corrupt line — skip, do not abort. Logging is
                    # left to the caller; this is a read-only assembly
                    # path, not a validation gate.
                    continue
    except OSError:
        # File vanished mid-read or unreadable — treat as empty.
        return []
    return out


def _stuck_events_for(events: List[Dict[str, Any]], sub_problem_id: str) -> List[Dict[str, Any]]:
    """Filter events.jsonl to subagent-stuck milestones for this sorry.

    `process_sorry_result.py:233-239` emits:
        {"kind":"sandbox_milestone","name":"subagent-stuck",
         "details":{"sorry_id":<id>,"blocker":<str>,...}}

    We match by `details.sorry_id == sub_problem_id` AND `name == "subagent-stuck"`.
    Order preserved (events.jsonl is append-only chronological).
    """
    matched: List[Dict[str, Any]] = []
    for ev in events:
        if ev.get("kind") != "sandbox_milestone":
            continue
        if ev.get("name") != "subagent-stuck":
            continue
        details = ev.get("details") or {}
        if details.get("sorry_id") != sub_problem_id:
            continue
        matched.append(ev)
    return matched


def _last_error_from_events(stuck_events: List[Dict[str, Any]]) -> Optional[str]:
    """Most-recent `subagent-stuck` event's blocker → lastError.

    czy parity: `pendingEntry.lastError` is the most recent compile
    error string. SDK-bridge translation: walk events.jsonl from the
    end (i.e. the last matching subagent-stuck event for this sorry).
    """
    if not stuck_events:
        return None
    last = stuck_events[-1]
    blocker = (last.get("details") or {}).get("blocker")
    if not isinstance(blocker, str):
        return None
    return _clamp(blocker, _LAST_ERROR_MAX)


def _dedupe_by_prefix(items: List[str], prefix_len: int) -> List[str]:
    """Drop later duplicates whose first `prefix_len` chars match an
    earlier survivor. Order-preserving.

    Spec §3.4: "de-dupe by 80-char prefix" so two stucks with the same
    error class don't both occupy a slot in deadEnds.
    """
    seen = set()
    out: List[str] = []
    for s in items:
        key = s[:prefix_len]
        if key in seen:
            continue
        seen.add(key)
        out.append(s)
    return out


def _dead_ends_from_events_and_history(
    stuck_events: List[Dict[str, Any]],
    parent_history_log: List[Dict[str, Any]],
) -> List[str]:
    """Assemble deadEnds list per spec §3.4.

    Sources (chronological order):
      1. parent's history_log[].retreat_reason — most recent
         _HISTORY_RETREAT_KEEP entries (cross-round restrategize/retreat
         history); these are explicit "this approach failed" labels.
      2. subagent-stuck blockers for this sorry — chronological.

    De-dupe by 80-char prefix (spec §3.4); take the LAST
    _DEAD_END_KEEP entries (czy `.slice(-5)` parity at proofLoop.ts:724).
    Each entry clamped to _DEAD_END_ENTRY_MAX chars.
    """
    candidates: List[str] = []

    # 1. Parent history retreat reasons (most recent N) — these are
    # higher-signal than blocker text since they're written by
    # record_retreat / restrategize_node with a structured reason.
    history_reasons: List[str] = []
    for entry in parent_history_log[-_HISTORY_RETREAT_KEEP:]:
        rr = entry.get("retreat_reason")
        if isinstance(rr, str) and rr.strip():
            history_reasons.append(rr.strip())
    candidates.extend(history_reasons)

    # 2. Sorry-level subagent-stuck blockers (chronological)
    for ev in stuck_events:
        blocker = (ev.get("details") or {}).get("blocker")
        if isinstance(blocker, str) and blocker.strip():
            candidates.append(blocker.strip())

    # Clamp each entry first so de-dupe sees the clamped form
    clamped = [c[:_DEAD_END_ENTRY_MAX] for c in candidates]
    deduped = _dedupe_by_prefix(clamped, _DEDUPE_PREFIX)

    # czy proofLoop.ts:724 .slice(-5) — keep the last N (most recent)
    return deduped[-_DEAD_END_KEEP:]


def _code_attempted_from_sandbox(
    sandbox: Path,
    file_rel: Optional[str],
    target_line: Optional[int],
    window: int = 20,
) -> Optional[str]:
    """Read sandbox file at target_line ± `window` lines.

    Returns clamped string, or None if file/line unavailable. czy parity:
    `taskResult?.traceSummary?.slice(0, 800)` — but the SDK-bridge has no
    traceSummary equivalent today, so we approximate by snipping the
    .lean file around the failing line (which is what the agent would
    look at anyway when debugging the stuck).
    """
    if not file_rel or target_line is None or target_line <= 0:
        return None
    abs_path = (sandbox / file_rel).resolve()
    # Defense against path traversal: refuse paths that escape the sandbox.
    try:
        abs_path.relative_to(sandbox.resolve())
    except ValueError:
        return None
    if not abs_path.is_file():
        return None
    try:
        text = abs_path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return None
    lines = text.splitlines()
    if not lines:
        return None
    lo = max(0, target_line - 1 - window)
    hi = min(len(lines), target_line - 1 + window + 1)
    snippet = "\n".join(lines[lo:hi])
    return _clamp(snippet, _CODE_ATTEMPTED_MAX)


def assemble_stuck_context(
    sandbox: Path,
    sub_problem_id: str,
    parent_history_log: Optional[List[Dict[str, Any]]] = None,
    file_rel: Optional[str] = None,
    target_line: Optional[int] = None,
    current_goal: Optional[str] = None,
) -> StuckContext:
    """Build a czy-equivalent StuckContext for the H4 dispatcher.

    Args:
      sandbox: per-job sandbox dir (must exist; events.jsonl optional).
      sub_problem_id: the sorry_item id whose stuck we're assembling.
      parent_history_log: parent's history_log[] from sorry_backlog.yaml
        (caller already loaded it). Pass None or [] if no parent or no
        history yet.
      file_rel: relative path inside sandbox to the .lean file containing
        the stuck sorry. Optional; if None or file missing, codeAttempted
        is None.
      target_line: 1-based line number of the failing sorry. Required for
        codeAttempted snippet.
      current_goal: pre-probed Lean goal text from agent-side LSP (czy
        proofLoop.ts:704-714). The LSP probe is NOT this module's
        responsibility (matches czy's contract — proofLoop owns the
        probe, not the helper-dispatch code).

    Returns:
      StuckContext dataclass; use .to_dict() for JSON serialization.
      Empty events.jsonl + empty history → all-None fields.
    """
    events = _read_events_jsonl(sandbox)
    stuck_events = _stuck_events_for(events, sub_problem_id)
    history = parent_history_log or []

    last_error = _last_error_from_events(stuck_events)
    dead_ends = _dead_ends_from_events_and_history(stuck_events, history)
    code_attempted = _code_attempted_from_sandbox(sandbox, file_rel, target_line)

    return StuckContext(
        current_goal=_clamp(current_goal, _CURRENT_GOAL_MAX),
        last_error=last_error,
        dead_ends=dead_ends if dead_ends else None,
        code_attempted=code_attempted,
    )
