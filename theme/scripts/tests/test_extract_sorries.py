"""Unit tests for extract_sorries.py.

Must produce output shape-compatible with the TS parseSorriesFromLean
in website/src/lib/sorryParse.ts so the two consumer paths interoperate
during migration.

Run:
  pytest theme/scripts/tests/test_extract_sorries.py -v
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[3]
SCRIPT = REPO_ROOT / "theme" / "scripts" / "extract_sorries.py"


# Import the pure function for direct testing too.
sys.path.insert(0, str(REPO_ROOT / "theme" / "scripts"))
from extract_sorries import extract_sorries_from_content  # noqa: E402


def test_single_decl_with_sorry() -> None:
    src = "theorem foo : True := by sorry\n"
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert len(out) == 1
    assert out[0].theorem == "foo"
    assert out[0].startLine == 1
    assert out[0].endLine == 1
    assert out[0].jobId == "J"
    assert out[0].file == "F.lean"
    assert out[0].id == "J.foo.L1"


def test_multi_line_decl() -> None:
    src = """theorem bar : ∀ n, n + 0 = n := by
  intro n
  sorry
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert len(out) == 1
    assert out[0].theorem == "bar"
    assert out[0].startLine == 1
    assert out[0].endLine == 3


def test_multiple_decls() -> None:
    src = """theorem a : True := trivial

theorem b : True := by sorry

lemma c (x : Nat) : x = x := rfl

def d : Nat := by sorry
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    # a has no sorry, c has no sorry; b and d do.
    names = [t.theorem for t in out]
    assert names == ["b", "d"]


def test_one_entry_per_decl_even_with_multiple_sorries() -> None:
    src = """theorem foo : True ∧ True := by
  refine ⟨?h, ?h2⟩
  · sorry
  · sorry
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert len(out) == 1
    assert out[0].theorem == "foo"


def test_comment_stripping_line_comment() -> None:
    src = "-- sorry in comment\ntheorem foo : True := trivial\n"
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert out == []


def test_comment_stripping_block_comment() -> None:
    src = """/- sorry -/
theorem foo : True := trivial
/- multiple
   line block with sorry inside
-/
theorem bar : True := trivial
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert out == []


def test_private_protected_noncomputable_prefixes() -> None:
    src = """private theorem a := sorry
protected lemma b := by sorry
noncomputable def c := by sorry
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert [t.theorem for t in out] == ["a", "b", "c"]


def test_abbrev_and_def_recognized() -> None:
    src = """abbrev A := by sorry
def B := by sorry
"""
    out = extract_sorries_from_content(src, "J", "F.lean")
    assert [t.theorem for t in out] == ["A", "B"]


# ---- CLI mode ----


@pytest.fixture
def sandbox(tmp_path: Path) -> Path:
    sb = tmp_path / "SandboxJob"
    sb.mkdir()
    (sb / "Main.lean").write_text(
        "theorem mainA : True := by sorry\n"
        "theorem mainB : True := trivial\n"
    )
    sub = sb / "sub"
    sub.mkdir()
    (sub / "Helper.lean").write_text(
        "lemma helper : True := by sorry\n"
    )
    return sb


def _run_cli(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True, text=True, check=False,
    )


def test_cli_sandbox_mode_writes_json(sandbox: Path) -> None:
    out_file = sandbox / "sorry_list.json"
    r = _run_cli(
        "--sandbox", str(sandbox),
        "--output", str(out_file),
    )
    assert r.returncode == 0, r.stderr
    data = json.loads(out_file.read_text())
    # Should see mainA and helper (not mainB).
    names = sorted(t["theorem"] for t in data)
    assert names == ["helper", "mainA"]
    # Sandbox basename is the derived jobId.
    assert all(t["jobId"] == "SandboxJob" for t in data)
    # Paths are relative.
    paths = sorted(t["file"] for t in data)
    assert paths == ["Main.lean", "sub/Helper.lean"]


def test_cli_sandbox_mode_stdout(sandbox: Path) -> None:
    r = _run_cli("--sandbox", str(sandbox), "--output", "-")
    assert r.returncode == 0, r.stderr
    data = json.loads(r.stdout)
    assert len(data) == 2


def test_cli_lean_file_mode_requires_job_id(tmp_path: Path) -> None:
    f = tmp_path / "F.lean"
    f.write_text("theorem foo := sorry\n")
    r = _run_cli("--lean-file", str(f), "--output", "-")
    assert r.returncode != 0
    assert "job-id" in r.stderr.lower() or "requires" in r.stderr.lower()


def test_cli_lean_file_mode_happy(tmp_path: Path) -> None:
    f = tmp_path / "F.lean"
    f.write_text("theorem foo := sorry\n")
    r = _run_cli(
        "--lean-file", str(f),
        "--job-id", "JOBX",
        "--output", "-",
    )
    assert r.returncode == 0, r.stderr
    data = json.loads(r.stdout)
    assert len(data) == 1
    assert data[0]["jobId"] == "JOBX"
    assert data[0]["theorem"] == "foo"


def test_cli_output_shape_matches_parseSorriesFromLean(tmp_path: Path) -> None:
    """Pin the exact keyset produced — web's SorryTarget interface depends on it."""
    sb = tmp_path / "J"
    sb.mkdir()
    (sb / "X.lean").write_text("theorem foo : True := by sorry\n")
    out = sb / "sorry_list.json"
    r = _run_cli("--sandbox", str(sb), "--output", str(out))
    assert r.returncode == 0, r.stderr
    data = json.loads(out.read_text())
    assert len(data) == 1
    required_keys = {"id", "jobId", "theorem", "file", "startLine", "endLine", "context"}
    assert required_keys <= data[0].keys()
