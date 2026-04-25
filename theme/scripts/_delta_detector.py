"""_delta_detector — pure prompt-build + response-parse for the
formalization-delta detector.

Companion to `detect_delta.py` (the CLI wrapper). Splitting the pure
logic out makes the heavy lifting (building a clear LLM prompt;
robustly parsing whatever the model returns) unit-testable without
needing the `claude` CLI on PATH.

Output schema mirrors the `formalization_delta` event from
ui-signals.md §6:

    {
      "change_detected": bool,
      "change_type": str (DELTA_CHANGE_TYPES enum, present iff detected),
      "summary": str (present iff detected),
      "severity": "info" | "notable" | "breaking" (present iff detected),
      "details": dict (optional, present iff detected)
    }

`change_detected: false` is a valid outcome — the script exits cleanly
without emitting. We deliberately model this as a positive "no change"
signal rather than missing fields so prompt-engineering pressure on the
model is symmetric (must always return a JSON object).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Optional

# Re-export the canonical enums from emit_event.py so the detector and
# the emitter agree on what's valid. If emit_event.py grows a new
# change_type, the detector picks it up automatically.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from emit_event import (  # noqa: E402
    DELTA_CHANGE_TYPES,
    DELTA_SEVERITIES,
)


# ── Prompt construction ────────────────────────────────────────────

PROMPT_TEMPLATE = """\
You are a formalization-integrity auditor. Two artifacts are shown
below — a BEFORE state (typically the source spec, e.g. theorems.yaml)
and an AFTER state (typically the formalized Lean file). Your job is
to detect whether the AFTER artifact has *weakened, narrowed, or
materially altered* the mathematical content of the BEFORE artifact.

What counts as a change worth flagging:
  - dim-reduction        — quantifier domain narrowed (ℝ → ℕ, ℝ^n → ℝ^1, …)
  - hypothesis-add       — a regularity / structure hypothesis was added
                           that the BEFORE statement did not have
  - hypothesis-remove    — a hypothesis was dropped
  - type-weaken          — a type was changed to a less general one
  - conclusion-replace   — the conclusion was replaced (e.g. wrapped
                           in `True ∧ original`, or replaced with a
                           trivial form)
  - structure-introduce  — a `structure {{ holds : True }}` shim was
                           introduced that hides assumptions
  - scope-restrict       — the universally-quantified scope was narrowed
  - other                — semantic change that doesn't match above

What does NOT count:
  - Pure cosmetic differences (whitespace, names of bound variables,
    rearranging lemma order, comments).
  - Notation differences (ℝ vs Real, ⟨…⟩ vs ⟨...⟩, etc.) where the
    semantics is identical.
  - The AFTER being a faithful Lean encoding of the BEFORE.

Severity guide:
  - info     — additive / cosmetic, no semantic change (rare)
  - notable  — semantic change worth surfacing; default when unsure
  - breaking — weakens the theorem; integrity gate should ideally
               have caught this

Respond with EXACTLY one JSON object on a single line, no prose, no
code fences:

  {{ "change_detected": false }}

OR

  {{ "change_detected": true, "change_type": "<enum>", \
"summary": "<one-line reason>", "severity": "<info|notable|breaking>" }}

Allowed change_type values: {change_types}
Allowed severity values: {severities}

────────── BEFORE ({before_label}) ──────────
{before_text}
────────── END BEFORE ──────────

────────── AFTER ({after_label}) ──────────
{after_text}
────────── END AFTER ──────────
"""


def build_prompt(
    before_text: str,
    after_text: str,
    before_label: str = "before",
    after_label: str = "after",
) -> str:
    """Compose the LLM prompt. Pure / deterministic.

    Truncates each artifact to a soft cap so a runaway theorems.yaml
    doesn't blow the context. Hard truncation point is large enough
    that any realistic single-theorem comparison fits.
    """
    SOFT_CAP = 20_000  # chars per artifact; ~5K tokens
    if len(before_text) > SOFT_CAP:
        before_text = before_text[:SOFT_CAP] + f"\n[truncated {len(before_text) - SOFT_CAP} chars]"
    if len(after_text) > SOFT_CAP:
        after_text = after_text[:SOFT_CAP] + f"\n[truncated {len(after_text) - SOFT_CAP} chars]"
    return PROMPT_TEMPLATE.format(
        change_types=", ".join(DELTA_CHANGE_TYPES),
        severities=", ".join(DELTA_SEVERITIES),
        before_label=before_label,
        after_label=after_label,
        before_text=before_text,
        after_text=after_text,
    )


# ── Response parsing ───────────────────────────────────────────────

def _extract_first_json_object(raw: str) -> Optional[str]:
    """Best-effort: find the first balanced top-level JSON object in
    a string. Tolerates surrounding prose / code fences and nested
    objects (e.g. the optional `details` field). Returns the string
    or None.

    Walks the input character-by-character tracking brace depth, with
    a tiny string-literal sub-state so a `}` inside a JSON string
    doesn't fool the depth counter. Backslash-escapes inside strings
    are honoured.
    """
    # Strip code fences if present.
    cleaned = raw.replace("```json", "").replace("```", "")
    start = cleaned.find("{")
    if start < 0:
        return None
    depth = 0
    in_string = False
    escape = False
    for i in range(start, len(cleaned)):
        ch = cleaned[i]
        if in_string:
            if escape:
                escape = False
                continue
            if ch == "\\":
                escape = True
                continue
            if ch == '"':
                in_string = False
            continue
        if ch == '"':
            in_string = True
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return cleaned[start:i + 1]
    return None


def parse_response(raw: str) -> Optional[dict]:
    """Parse a model response into the canonical detector dict.

    Returns:
      - {"change_detected": False}                          — explicit no-change
      - {"change_detected": True, "change_type": ...,
         "summary": ..., "severity": ..., ["details": ...]} — detected
      - None                                                 — unparseable / invalid

    Validates enums; rejects responses that violate the schema even if
    they're technically valid JSON. Caller should treat None as a
    detector failure (log + exit non-zero).
    """
    if not raw or not raw.strip():
        return None
    obj_str = _extract_first_json_object(raw)
    if obj_str is None:
        return None
    try:
        parsed = json.loads(obj_str)
    except json.JSONDecodeError:
        return None
    if not isinstance(parsed, dict):
        return None
    detected = parsed.get("change_detected")
    if not isinstance(detected, bool):
        return None
    if detected is False:
        return {"change_detected": False}

    # detected is True → require the full schema.
    change_type = parsed.get("change_type")
    summary = parsed.get("summary")
    severity = parsed.get("severity")

    if not isinstance(change_type, str) or change_type not in DELTA_CHANGE_TYPES:
        return None
    if not isinstance(summary, str) or not summary.strip():
        return None
    if not isinstance(severity, str) or severity not in DELTA_SEVERITIES:
        return None

    out: dict = {
        "change_detected": True,
        "change_type": change_type,
        "summary": summary.strip(),
        "severity": severity,
    }
    details = parsed.get("details")
    if isinstance(details, dict):
        out["details"] = details
    return out


# ── Identity short-circuit ────────────────────────────────────────


def texts_are_trivially_identical(before: str, after: str) -> bool:
    """Cheap pre-check: skip the LLM call when the artifacts are
    byte-identical (after stripping leading/trailing whitespace).

    Doesn't try to be clever about whitespace-only changes inside the
    text — the LLM can recognise those as cosmetic and return
    `change_detected: false` itself. This pre-check is purely about
    saving the LLM round trip on no-op writes.
    """
    return before.strip() == after.strip()
