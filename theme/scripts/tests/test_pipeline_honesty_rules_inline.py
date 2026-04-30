"""
Phase 5 (czy port arch fix): assert lean-skeleton anti-vacuity rules
are inlined verbatim into pipeline.md Step 3.

Background: jobmolovhy6getc (2026-05-01) empirically confirmed that
`Skill {skill: "lean-skeleton"}` is never invoked at runtime — the
65-line czy honestyRules port at SKILL.md sat as dead text, never
reaching agent context. Phase 5 inlines the content into pipeline.md
where the agent unavoidably reads it.

This test pins the runtime dispatch path:
- pipeline.md Step 3 contains the rules byte-equal with SKILL.md (the
  documentation source-of-truth)
- SKILL.md retains the rules with a migration note pointing here
- A future drift between pipeline.md and SKILL.md must be detected
  by this test so the inline doesn't silently fall out of sync with
  the SoT.
"""
from pathlib import Path
import re

REPO = Path("/home/gavin/statlean-merge")
PIPELINE = REPO / ".claude/commands/pipeline.md"
SKILL = REPO / "theme/skills/lean-skeleton/SKILL.md"


def _extract_anti_vacuity_block(text: str) -> str:
    """Extract from 'Escapable existential' to 'rewrite before write_file.'.
    The block is identical in both files (czy honestyRules.ts:25-46 source).
    """
    m = re.search(
        r"(\*\*Escapable existential.*?rewrite before \`write_file\`\.)",
        text,
        re.DOTALL,
    )
    assert m, "anti-vacuity rule block not found"
    return m.group(1)


def _extract_naming_block(text: str) -> str:
    """Extract identifier naming block (czy honestyRules.ts:162-200)."""
    m = re.search(
        r"(HARD BAN.*?Always safe.*?subscripts.*?superscripts \`x² ε⁺ X⁻¹\`\.)",
        text,
        re.DOTALL,
    )
    assert m, "identifier naming block not found"
    return m.group(1)


def test_pipeline_md_contains_anti_vacuity_rules():
    """The 6 anti-vacuity bullets must be in pipeline.md Step 3."""
    pipe = PIPELINE.read_text()
    for needle in [
        "Escapable existential",
        "Stub binder",
        "Vacuous wrapper",
        "Disconnected binder",
        "Collapsed quantifier",
        "Weakening",
    ]:
        assert needle in pipe, f"missing anti-vacuity rule: {needle}"


def test_pipeline_md_contains_naming_rules():
    """The HARD BAN keyword list must be in pipeline.md Step 3."""
    pipe = PIPELINE.read_text()
    for needle in [
        "HARD BAN",
        "λ` `Π` `Σ` `∀` `∃",
        "hλ_pos",
        "Σ_inv",
    ]:
        assert needle in pipe, f"missing naming rule: {needle}"


def test_anti_vacuity_block_byte_equal_with_skill_md():
    """The migration must preserve content byte-equal — no paraphrasing
    or rewording allowed (czy intent constraint per user directive
    2026-05-01: 不能改变 port 来的本意)."""
    skill_block = _extract_anti_vacuity_block(SKILL.read_text())
    pipe_block = _extract_anti_vacuity_block(PIPELINE.read_text())
    assert skill_block == pipe_block, (
        "anti-vacuity block drifted between SKILL.md (SoT) and "
        "pipeline.md (runtime). Mirror any edit to both.\n"
        f"SKILL: {skill_block[:200]}\n"
        f"pipe:  {pipe_block[:200]}"
    )


def _strip_heading_levels(block: str) -> str:
    """Normalize markdown heading depth: when content moves between files
    at different nesting levels (SKILL.md uses ### / pipeline.md uses
    #####), heading prefixes change but body text does not. Compare the
    body without the leading `#` count."""
    lines = []
    for line in block.splitlines():
        stripped = line.lstrip("#").lstrip(" ")
        # Keep the line text minus the heading indicator; preserves all
        # content (paragraph text, bullets, table rows) byte-equal while
        # tolerating heading-level shifts.
        lines.append(stripped if line.startswith("#") else line)
    return "\n".join(lines)


def test_naming_block_byte_equal_with_skill_md():
    """The identifier naming body content must match between SKILL.md
    (SoT) and pipeline.md (runtime). Heading depth normalization is
    applied — the inline lives one nesting level deeper, so `###` becomes
    `#####`, but the heading TEXT and all body content (tables, bullets,
    examples) must be identical."""
    skill_block = _strip_heading_levels(_extract_naming_block(SKILL.read_text()))
    pipe_block = _strip_heading_levels(_extract_naming_block(PIPELINE.read_text()))
    assert skill_block == pipe_block, (
        "identifier naming body drifted between SKILL.md (SoT) and "
        "pipeline.md (runtime). Mirror any edit to both."
    )


def test_skill_md_carries_migration_note():
    """SKILL.md must point readers to the pipeline.md inline as the
    runtime dispatch path. Prevents future maintainers from editing
    SKILL.md alone (which is dead text at runtime)."""
    skill = SKILL.read_text()
    assert "MIGRATION NOTE" in skill
    assert "pipeline.md" in skill
    assert "runtime dispatch path" in skill


def test_pipeline_md_inline_cites_czy_source():
    """The inline must keep czy source attribution (`honestyRules.ts:25-46`)
    so the SoT chain stays visible — czy-parity audit-trail."""
    pipe = PIPELINE.read_text()
    assert "honestyRules.ts:25-46" in pipe, (
        "missing czy SoT attribution for SKELETON_HONESTY_RULES"
    )
    assert "honestyRules.ts:162-200" in pipe, (
        "missing czy SoT attribution for LEAN_NAMING_CONVENTION"
    )
