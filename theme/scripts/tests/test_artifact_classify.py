"""Mirror of website/server/services/artifactClassifier.test.ts.

Both implementations must stay byte-identical in semantics. If either
side changes a rule, both test suites must be updated together.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Allow running this file directly via `pytest theme/scripts/tests/...`
# without an installable package (the scripts dir is sibling to tests).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from _artifact_classify import classify_artifact_path  # noqa: E402


# ── 1. primary kinds ────────────────────────────────────────────────────
class TestPrimary:
    def test_sorry_list_top(self):
        assert classify_artifact_path("sorry_list.json") == "sorry-list"

    def test_sorry_list_nested(self):
        assert classify_artifact_path("sub/sorry_list.json") == "sorry-list"

    def test_theorems_top(self):
        assert classify_artifact_path("theorems.yaml") == "yaml"

    def test_theorems_nested(self):
        assert classify_artifact_path("a/b/theorems.yaml") == "yaml"

    def test_main_lean(self):
        assert classify_artifact_path("Main.lean") == "lean-live"

    def test_helper_lean(self):
        assert classify_artifact_path("Helper.lean") == "lean-live"
        assert classify_artifact_path("sub/Helper.lean") == "lean-live"

    def test_paper_top(self):
        assert classify_artifact_path("paper.tex") == "pdf-extract"

    def test_paper_nested(self):
        assert classify_artifact_path("anything/paper.tex") == "pdf-extract"

    def test_raw_content(self):
        assert classify_artifact_path("raw_content.md") == "pdf-extract"

    def test_raw_md(self):
        assert classify_artifact_path("raw/foo.md") == "pdf-extract"

    def test_raw_tex(self):
        assert classify_artifact_path("raw/foo.tex") == "pdf-extract"

    def test_raw_markdown(self):
        assert classify_artifact_path("raw/foo.markdown") == "pdf-extract"

    def test_extracted_tex(self):
        assert classify_artifact_path("extracted/paper.tex") == "pdf-extract"

    def test_extracted_md(self):
        assert classify_artifact_path("extracted/notes.md") == "pdf-extract"


# ── 2. secondary fallbacks ─────────────────────────────────────────────
class TestSecondary:
    def test_notation_yaml_top(self):
        assert classify_artifact_path("notation.yaml") == "yaml"

    def test_scope_yaml_top(self):
        assert classify_artifact_path("scope.yaml") == "yaml"

    def test_nested_other_yaml_null(self):
        # Only theorems.yaml is the canonical name we promote at depth.
        assert classify_artifact_path("sub/something.yaml") is None

    def test_random_md_top(self):
        assert classify_artifact_path("notes.md") == "pdf-extract"

    def test_random_tex_top(self):
        assert classify_artifact_path("draft.tex") == "pdf-extract"


# ── 3. non-classified ──────────────────────────────────────────────────
class TestNonClassified:
    def test_empty(self):
        assert classify_artifact_path("") is None

    def test_just_slash(self):
        assert classify_artifact_path("/") is None

    def test_lock(self):
        assert classify_artifact_path("foo.lock") is None

    def test_tmp(self):
        assert classify_artifact_path("foo.tmp") is None

    def test_random_json(self):
        assert classify_artifact_path("extract_summary.json") is None
        assert classify_artifact_path("input_content_list.json") is None

    def test_pdf_binary(self):
        assert classify_artifact_path("input.pdf") is None

    def test_no_extension(self):
        assert classify_artifact_path("README") is None


# ── 4. normalization ───────────────────────────────────────────────────
class TestNormalization:
    def test_windows_backslash(self):
        assert classify_artifact_path("raw\\input.md") == "pdf-extract"
        assert classify_artifact_path("sub\\Helper.lean") == "lean-live"

    def test_leading_dot_slash(self):
        assert classify_artifact_path("./Main.lean") == "lean-live"
        assert classify_artifact_path("././theorems.yaml") == "yaml"

    def test_trailing_slash(self):
        assert classify_artifact_path("Main.lean/") == "lean-live"

    def test_uppercase_strict(self):
        # Strict lowercase. PDF toolchains all emit lowercase.
        assert classify_artifact_path("Main.LEAN") is None

    def test_path_with_spaces(self):
        assert classify_artifact_path("my paper.tex") == "pdf-extract"


# ── 5. integration: jobmoe1utvq3yq5 ───────────────────────────────────
class TestJobmoe1utvq3yq5:
    """Reproduce the exact path/kind_tag mismatches seen in the bug job."""

    def test_paper_tex_inferred_pdf_extract(self):
        # paper.tex was emitted with kind_tag="yaml" by the agent. The
        # classifier must infer "pdf-extract" so reconcileKindTag flags it.
        assert classify_artifact_path("paper.tex") == "pdf-extract"

    def test_theorems_yaml_inferred_yaml(self):
        assert classify_artifact_path("theorems.yaml") == "yaml"

    def test_main_lean_inferred_lean_live(self):
        # skeleton/live transition is the caller's concern; path can
        # only tell us "lean-live".
        assert classify_artifact_path("Main.lean") == "lean-live"


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
