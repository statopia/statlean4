"""H1 L1 unit tests for elaborate_plan.py.

Coverage matrix per `docs/H1_ELABORATE_PLAN_SPEC.md` §7.1.

Verdict branches (D-9 single milestone, three verdicts):
  L1.1  direct mode happy path — non-decomposed parent, non-empty plan
  L1.2  assembly mode happy path — decomposed parent, non-empty plan
  L1.3  parent.coverage_stable=False AND informal_round=0 → exit 2
        (alignment loop has not converged; §8 S2.3 cap_reached fix
        below tests cap path that DOES allow firing)
  L1.4  parent_id not found → exit 2
  L1.5  detailed_proof_plan already present → skipped_already_present
  L1.6  empty plan text → skipped_empty_plan
  L1.7  whitespace-only plan text → skipped_empty_plan
  L1.8  Layer 1 invariant — every non-target field byte-identical
        (yaml round-trip fingerprint compares pre/post-write)
  L1.9  flock — concurrent elaborate on same parent serializes
  L1.10 atomic write — preserves file mode 0o644
  L1.11 mode arg mismatch — `--mode assembly` on parent with no children
        → exit 2 (R6 mitigation per spec §8)

Plus boundary tests:
  - cap_reached path (informal_round >= 2 AND coverage_stable=False)
    fires successfully (§8 S2.3 fix)
  - subagent text file missing → exit 2
  - --mode direct on parent WITH children → exit 2 (symmetric R6)
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, Dict, List, Optional

import pytest
import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from elaborate_plan import (  # noqa: E402
    INFORMAL_ROUND_CAP,
    MODES,
    _is_loop_exited,
    apply_elaboration,
)


SCRIPTS_DIR = Path(__file__).resolve().parent.parent
ELAB = SCRIPTS_DIR / "elaborate_plan.py"


# ── Fixtures ─────────────────────────────────────────────────────────


def _decomposed_parent_with_children(
    coverage_stable: bool = True,
    informal_round: int = 1,
    detailed_proof_plan: Any = None,
    direct_assembly: Optional[str] = "Brief assembly: combine s1 + s2 via Iff.intro",
    proof_sketch: Any = None,
) -> List[Dict[str, Any]]:
    """v2 backlog with decomposed parent + 2 children (assembly mode
    fixture). coverage_stable=True by default = alignment loop exited."""
    parent = {
        "id": "p", "file": "Statlean/Foo.lean", "line": 10,
        "theorem": "p_thm", "type": "blocked",
        "depth": 0, "priority": 50, "estimated_lines": 100,
        "dependencies": [], "unlocks": [],
        "state": "INACTIVE_WAIT",
        "children": ["p.s1", "p.s2"],
        "parent_id": None,
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": informal_round,
        "coverage_stable": coverage_stable,
        "detailed_proof_plan": detailed_proof_plan,
        "direct_assembly": direct_assembly,
        "proof_sketch": proof_sketch,
    }
    children = []
    for cid in ("p.s1", "p.s2"):
        ch = {
            "id": cid, "file": "Statlean/Foo.lean", "line": 12,
            "theorem": cid + "_thm", "type": "ready", "depth": 1,
            "priority": 50, "estimated_lines": 30,
            "dependencies": [], "unlocks": [],
            "state": "INITIALIZED", "children": [], "parent_id": "p",
            "history_log": [], "stuck_rounds": 0, "attempts": 0,
            "references": [], "coverage_state": "needs_proof",
            "citation_verified": False,
            "informal_round": 0, "coverage_stable": False,
            "detailed_proof_plan": None,
            "direct_assembly": None, "proof_sketch": None,
        }
        children.append(ch)
    return [parent] + children


def _flat_parent_no_children(
    coverage_stable: bool = True,
    informal_round: int = 1,
    detailed_proof_plan: Any = None,
    proof_sketch: Optional[str] = "Brief direct strategy: apply Real.norm_add_le",
    direct_assembly: Any = None,
) -> List[Dict[str, Any]]:
    """v2 backlog with single non-decomposed parent (direct mode fixture)."""
    parent = {
        "id": "p", "file": "Statlean/Foo.lean", "line": 10,
        "theorem": "p_thm", "type": "ready",
        "depth": 0, "priority": 50, "estimated_lines": 100,
        "dependencies": [], "unlocks": [],
        "state": "INITIALIZED",
        "children": [],  # NO children → direct mode
        "parent_id": None,
        "history_log": [], "stuck_rounds": 0, "attempts": 0,
        "references": [], "coverage_state": "needs_proof",
        "citation_verified": False,
        "informal_round": informal_round,
        "coverage_stable": coverage_stable,
        "detailed_proof_plan": detailed_proof_plan,
        "direct_assembly": direct_assembly,
        "proof_sketch": proof_sketch,
    }
    return [parent]


def _write_backlog(path: Path, items: List[Dict[str, Any]]) -> None:
    data = {"schema_version": 2, "version": "v100", "sorry_items": items}
    path.write_text(yaml.safe_dump(data, sort_keys=False, allow_unicode=True))
    os.chmod(path, 0o644)


def _by_id(backlog: Path, item_id: str) -> Dict[str, Any]:
    data = yaml.safe_load(backlog.read_text())
    return next(it for it in data["sorry_items"] if it["id"] == item_id)


def _read_yaml(path: Path) -> Dict[str, Any]:
    return yaml.safe_load(path.read_text())


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    s = tmp_path / "sandbox"
    s.mkdir()
    return s


@pytest.fixture
def backlog_decomposed(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _write_backlog(p, _decomposed_parent_with_children())
    return p


@pytest.fixture
def backlog_flat(tmp_path: Path) -> Path:
    p = tmp_path / "sorry_backlog.yaml"
    _write_backlog(p, _flat_parent_no_children())
    return p


# ── Helper / unit tests ─────────────────────────────────────────────


def test_is_loop_exited_via_coverage_stable() -> None:
    """Either signal alone is sufficient (czy parity per
    proofLoop.ts:929-940 — fires unconditionally post-loop)."""
    assert _is_loop_exited({"coverage_stable": True, "informal_round": 0})


def test_is_loop_exited_via_cap_reached() -> None:
    """§8 S2.3 fix: cap_reached leaves coverage_stable=False but
    informal_round at cap. H1 must fire on this signal too."""
    assert _is_loop_exited({"coverage_stable": False, "informal_round": INFORMAL_ROUND_CAP})


def test_is_loop_exited_above_cap() -> None:
    """Defensive: above cap also counts as loop exited."""
    assert _is_loop_exited({"coverage_stable": False, "informal_round": 99})


def test_is_loop_not_exited_when_neither_signal() -> None:
    """coverage_stable=False AND informal_round < cap → loop still in
    progress; H1 must refuse."""
    assert not _is_loop_exited({"coverage_stable": False, "informal_round": 0})
    assert not _is_loop_exited({"coverage_stable": False, "informal_round": 1})


# ── L1.1 direct mode happy path ─────────────────────────────────────


def test_l1_1_direct_mode_happy_path(backlog_flat: Path) -> None:
    """Non-decomposed parent with proof_sketch + non-empty plan text."""
    plan = "1. Prove the goal by applying Real.norm_add_le to (a+b).\n2. Discharge h1."
    payload = apply_elaboration(backlog_flat, "p", "direct", plan)
    assert payload["verdict"] == "elaborated"
    assert payload["variant"] == "direct"
    assert payload["plan_length"] == len(plan)
    parent = _by_id(backlog_flat, "p")
    assert parent["detailed_proof_plan"] == plan


# ── L1.2 assembly mode happy path ───────────────────────────────────


def test_l1_2_assembly_mode_happy_path(backlog_decomposed: Path) -> None:
    """Decomposed parent with direct_assembly + child_lemmas + non-empty plan."""
    plan = "1. Open with intro h.\n2. Apply p.s1 with h.\n3. Close via p.s2."
    payload = apply_elaboration(backlog_decomposed, "p", "assembly", plan)
    assert payload["verdict"] == "elaborated"
    assert payload["variant"] == "assembly"
    assert payload["plan_length"] == len(plan)
    parent = _by_id(backlog_decomposed, "p")
    assert parent["detailed_proof_plan"] == plan


# ── L1.3 alignment loop has not converged ───────────────────────────


def test_l1_3_loop_not_converged_raises(tmp_path: Path) -> None:
    """coverage_stable=False AND informal_round=0 → loop still active.
    Script must refuse before any LLM read."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _decomposed_parent_with_children(
        coverage_stable=False, informal_round=0,
    ))
    with pytest.raises(ValueError, match="alignment loop has not converged"):
        apply_elaboration(p, "p", "assembly", "any plan text")
    # yaml unchanged: detailed_proof_plan still None
    assert _by_id(p, "p").get("detailed_proof_plan") is None


def test_cap_reached_eligible_to_elaborate(tmp_path: Path) -> None:
    """§8 S2.3 fix: cap_reached leaves coverage_stable=False but the
    alignment loop has terminated. H1 must fire (czy parity)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _decomposed_parent_with_children(
        coverage_stable=False, informal_round=INFORMAL_ROUND_CAP,
    ))
    plan = "Cap-reached path: assemble children in topological order."
    payload = apply_elaboration(p, "p", "assembly", plan)
    assert payload["verdict"] == "elaborated"
    assert _by_id(p, "p")["detailed_proof_plan"] == plan


# ── L1.4 parent_id not found ────────────────────────────────────────


def test_l1_4_parent_not_found_raises(backlog_flat: Path) -> None:
    with pytest.raises(ValueError, match="parent_id not in sorry_items"):
        apply_elaboration(backlog_flat, "ghost", "direct", "plan")


# ── L1.5 idempotence — already present ──────────────────────────────


def test_l1_5_already_present_skipped(tmp_path: Path) -> None:
    """parent.detailed_proof_plan already set + non-empty → skipped."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _flat_parent_no_children(
        detailed_proof_plan="existing plan body",
    ))
    payload = apply_elaboration(p, "p", "direct", "fresh plan body")
    assert payload["verdict"] == "skipped_already_present"
    assert payload["variant"] is None
    assert payload["plan_length"] == 0
    # yaml unchanged — existing plan retained
    assert _by_id(p, "p")["detailed_proof_plan"] == "existing plan body"


def test_already_present_empty_string_does_not_skip(tmp_path: Path) -> None:
    """Idempotence guard: empty-string detailed_proof_plan is treated
    as not-present (defensive — None and "" both indicate absence)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _flat_parent_no_children(
        detailed_proof_plan="",
    ))
    payload = apply_elaboration(p, "p", "direct", "fresh plan body")
    assert payload["verdict"] == "elaborated"
    assert _by_id(p, "p")["detailed_proof_plan"] == "fresh plan body"


# ── L1.6 / L1.7 empty / whitespace plan ─────────────────────────────


def test_l1_6_empty_plan_skipped(backlog_flat: Path) -> None:
    payload = apply_elaboration(backlog_flat, "p", "direct", "")
    assert payload["verdict"] == "skipped_empty_plan"
    assert payload["variant"] is None
    assert payload["plan_length"] == 0
    # yaml unchanged
    assert _by_id(backlog_flat, "p")["detailed_proof_plan"] is None


def test_l1_7_whitespace_only_plan_skipped(backlog_flat: Path) -> None:
    payload = apply_elaboration(backlog_flat, "p", "direct", "   \n\t  \n  ")
    assert payload["verdict"] == "skipped_empty_plan"
    assert _by_id(backlog_flat, "p")["detailed_proof_plan"] is None


# ── L1.8 Layer 1 invariant: only detailed_proof_plan mutates ────────


def test_l1_8_layer_1_invariant_assembly_mode(backlog_decomposed: Path) -> None:
    """Round-trip yaml fingerprint differs ONLY on
    parent.detailed_proof_plan. theorem, file, line, children,
    coverage_state, references, citation_verified, informal_round,
    coverage_stable, parent_id, direct_assembly, proof_sketch all
    byte-identical pre/post."""
    pre = _read_yaml(backlog_decomposed)
    pre_parent = next(it for it in pre["sorry_items"] if it["id"] == "p").copy()

    plan = "the elaborated plan body, citing p.s1 and p.s2."
    apply_elaboration(backlog_decomposed, "p", "assembly", plan)

    post = _read_yaml(backlog_decomposed)
    post_parent = next(it for it in post["sorry_items"] if it["id"] == "p")

    PROTECTED = (
        "id", "file", "line", "theorem", "type", "depth", "priority",
        "estimated_lines", "dependencies", "unlocks", "state", "children",
        "parent_id", "history_log", "stuck_rounds", "attempts",
        "references", "coverage_state", "citation_verified",
        "informal_round", "coverage_stable",
        # Brief seeds — H1 is read-only on these (D-11 contract)
        "direct_assembly", "proof_sketch",
    )
    for k in PROTECTED:
        assert post_parent.get(k) == pre_parent.get(k), (
            f"protected field {k} drifted: {pre_parent.get(k)!r} → "
            f"{post_parent.get(k)!r}"
        )

    # Only detailed_proof_plan should change
    assert pre_parent.get("detailed_proof_plan") is None
    assert post_parent.get("detailed_proof_plan") == plan

    # Children rows untouched at field level. The migration may add
    # additive defaults on read (e.g. H7's assumption_hints=[],
    # assumption_analysis=""); those are harmless idempotent migrations,
    # not perturbations. Compare on the load-bearing field set.
    CHILD_PROTECTED = (
        "id", "file", "line", "theorem", "type", "depth", "priority",
        "estimated_lines", "dependencies", "unlocks", "state", "children",
        "parent_id", "history_log", "stuck_rounds", "attempts",
        "references", "coverage_state", "citation_verified",
        "informal_round", "coverage_stable",
        "detailed_proof_plan", "direct_assembly", "proof_sketch",
    )
    pre_children = {it["id"]: it for it in pre["sorry_items"] if it["id"] != "p"}
    post_children = {it["id"]: it for it in post["sorry_items"] if it["id"] != "p"}
    assert set(pre_children.keys()) == set(post_children.keys())
    for cid, pre_ch in pre_children.items():
        post_ch = post_children[cid]
        for k in CHILD_PROTECTED:
            assert post_ch.get(k) == pre_ch.get(k), (
                f"child {cid} field {k} drifted: {pre_ch.get(k)!r} → "
                f"{post_ch.get(k)!r}"
            )


def test_l1_8_layer_1_invariant_skipped_empty_no_change(
    backlog_decomposed: Path,
) -> None:
    """skipped_empty_plan path: yaml fully byte-identical post-call."""
    pre = _read_yaml(backlog_decomposed)
    payload = apply_elaboration(backlog_decomposed, "p", "assembly", "")
    assert payload["verdict"] == "skipped_empty_plan"
    post = _read_yaml(backlog_decomposed)
    assert pre == post


# ── L1.9 flock concurrent invocations ───────────────────────────────


def test_l1_9_concurrent_serialize_via_flock(tmp_path: Path) -> None:
    """Two concurrent elaborate calls on the same parent: flock
    serializes; the second sees a non-null detailed_proof_plan after
    the first commits and returns skipped_already_present.

    This isn't proof of full concurrency safety, but it does verify
    flock is in effect (no torn writes; second invocation sees a
    consistent post-first-commit view)."""
    p = tmp_path / "b.yaml"
    _write_backlog(p, _flat_parent_no_children())
    verdicts: list = []
    errors: list = []

    def worker(idx: int) -> None:
        try:
            payload = apply_elaboration(
                p, "p", "direct", f"plan body from worker {idx}",
            )
            verdicts.append(payload["verdict"])
        except Exception as e:  # noqa: BLE001
            errors.append(str(e))

    t1 = threading.Thread(target=worker, args=(1,))
    t2 = threading.Thread(target=worker, args=(2,))
    t1.start()
    time.sleep(0.005)
    t2.start()
    t1.join()
    t2.join()

    assert not errors, f"unexpected errors: {errors}"
    assert len(verdicts) == 2
    # Exactly one elaborated, one skipped_already_present
    assert verdicts.count("elaborated") == 1
    assert verdicts.count("skipped_already_present") == 1


# ── L1.10 atomic write preserves file mode ──────────────────────────


def test_l1_10_atomic_write_preserves_file_mode(backlog_flat: Path) -> None:
    os.chmod(backlog_flat, 0o644)
    apply_elaboration(backlog_flat, "p", "direct", "non-empty plan")
    assert (os.stat(backlog_flat).st_mode & 0o777) == 0o644


# ── L1.11 mode arg mismatch ─────────────────────────────────────────


def test_l1_11_assembly_on_parent_with_no_children_raises(
    backlog_flat: Path,
) -> None:
    """--mode assembly + parent.children empty → exit 2 (R6 mitigation)."""
    with pytest.raises(ValueError, match="mode assembly but parent .* has no children"):
        apply_elaboration(backlog_flat, "p", "assembly", "any plan")
    assert _by_id(backlog_flat, "p")["detailed_proof_plan"] is None


def test_direct_on_parent_with_children_raises(backlog_decomposed: Path) -> None:
    """Symmetric R6: --mode direct + parent.children non-empty → exit 2."""
    with pytest.raises(ValueError, match="mode direct but parent .* has 2 children"):
        apply_elaboration(backlog_decomposed, "p", "direct", "any plan")
    assert _by_id(backlog_decomposed, "p")["detailed_proof_plan"] is None


def test_invalid_mode_raises(backlog_flat: Path) -> None:
    """--mode bogus → exit 2."""
    with pytest.raises(ValueError, match="--mode must be one of"):
        apply_elaboration(backlog_flat, "p", "bogus", "any plan")


# ── CLI smoke: subagent text file missing / round-trip ──────────────


def test_cli_subagent_file_missing_returns_2(
    backlog_flat: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """Missing --subagent-text-file → exit 2 with clear stderr."""
    result = subprocess.run(
        [
            "python3", str(ELAB),
            "--parent-id", "p",
            "--subagent-text-file", str(tmp_path / "does-not-exist.txt"),
            "--mode", "direct",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog_flat),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 2
    assert "subagent text file not found" in result.stderr


def test_cli_emits_milestone_on_elaborated(
    backlog_flat: Path, sandbox: Path, tmp_path: Path,
) -> None:
    """End-to-end CLI: writes plan, emits plan-elaborated milestone."""
    txt = tmp_path / "_elaborate_plan_p.txt"
    plan = "Numbered step plan body for test_cli."
    txt.write_text(plan, encoding="utf-8")

    result = subprocess.run(
        [
            "python3", str(ELAB),
            "--parent-id", "p",
            "--subagent-text-file", str(txt),
            "--mode", "direct",
            "--sandbox", str(sandbox),
            "--backlog-path", str(backlog_flat),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode == 0, result.stderr
    events_path = sandbox / "events.jsonl"
    assert events_path.exists()
    content = events_path.read_text()
    assert "plan-elaborated" in content
    assert '"verdict":"elaborated"' in content
    assert '"variant":"direct"' in content
    assert _by_id(backlog_flat, "p")["detailed_proof_plan"] == plan


def test_module_present_marker() -> None:
    from elaborate_plan import apply_elaboration as _ae  # noqa: F401
    assert callable(_ae)
