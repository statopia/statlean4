"""test_match_pitfall.py — L1 unit tests for match_pitfall.py.

Coverage:
- Each of 23 rules: positive match + at least one negative
- Empty / non-string input → None
- Multi-error list → first match wins
- DOTALL semantics for rules 4, 7, 13, 18, 19
- match_pitfall_suggestion_from_list API
- CLI exit codes (subprocess)
- Path alias shim (_path_alias.py)
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

# Allow importing match_pitfall from the scripts directory.
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from match_pitfall import (  # noqa: E402
    PITFALL_RULES,
    match_pitfall,
    match_pitfall_suggestion,
    match_pitfall_suggestion_from_list,
)
from _path_alias import resolve_pitfalls_alias  # noqa: E402

MATCH_PITFALL_PY = Path(__file__).resolve().parent.parent / "match_pitfall.py"


# ── Sanity check on rule count ───────────────────────────────────────────

def test_rule_count():
    assert len(PITFALL_RULES) == 23


# ── Helper ───────────────────────────────────────────────────────────────

def _match(text: str):
    """Return (file, section) or None."""
    r = match_pitfall(text)
    if r is None:
        return None
    return (r[0], r[1])


# ── Rule 1 ───────────────────────────────────────────────────────────────

def test_rule1_positive():
    assert _match("unexpected token 'λ'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.1")

def test_rule1_positive_other_chars():
    for ch in "ΠΣ∀∃":
        assert _match(f"unexpected token '{ch}'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.1")

def test_rule1_negative():
    assert _match("unexpected token 'x'") is None or \
           _match("unexpected token 'x'")[1] != "§A.1"


# ── Rule 2 ───────────────────────────────────────────────────────────────

def test_rule2_positive_in():
    assert _match("unexpected token 'in'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.2")

def test_rule2_positive_and():
    assert _match("unexpected token 'and'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.2")

def test_rule2_negative():
    # 'if' is not in the keyword list
    r = _match("unexpected token 'if'")
    assert r is None or r[1] != "§A.2"


# ── Rule 3 ───────────────────────────────────────────────────────────────

def test_rule3_positive_theorem():
    assert _match("unexpected token 'theorem'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.3")

def test_rule3_positive_lemma():
    assert _match("unexpected token 'lemma'") == ("docs/pitfalls/lean_syntax_errors.md", "§A.3")

def test_rule3_negative():
    r = _match("unexpected token 'fun'")
    assert r is None or r[1] != "§A.3"


# ── Rule 4 (DOTALL) ──────────────────────────────────────────────────────

def test_rule4_positive_multiline():
    err = "Unknown identifier 'X'\nNote: It is not possible to treat 'X' as an implicitly bound variable"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§A.4")

def test_rule4_dotall_newline_between():
    err = "Unknown identifier 'myVar'\nSome intermediate line\nNote: It is not possible to treat 'myVar' as an implicitly bound variable"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§A.4")

def test_rule4_negative():
    r = _match("Unknown identifier 'X'")
    assert r is None or r[1] != "§A.4"


# ── Rule 5 ───────────────────────────────────────────────────────────────

def test_rule5_positive():
    assert _match("unexpected identifier; expected command") == ("docs/pitfalls/lean_syntax_errors.md", "§A.5")

def test_rule5_negative():
    r = _match("unexpected identifier; expected token")
    assert r is None or r[1] != "§A.5"


# ── Rule 6 (combining marks) ─────────────────────────────────────────────

def test_rule6_positive():
    # U+0302 combining circumflex accent after 'e'
    assert _match("expected token ê̂") == ("docs/pitfalls/lean_syntax_errors.md", "§A.6")

def test_rule6_positive_unexpected():
    assert _match("unexpected token β̂ here") == ("docs/pitfalls/lean_syntax_errors.md", "§A.6")

def test_rule6_negative():
    r = _match("expected token x")
    assert r is None or r[1] != "§A.6"


# ── Rule 7 (DOTALL) ──────────────────────────────────────────────────────

def test_rule7_positive_single_line():
    err = "failed to synthesize HAdd (Fin n → ℝ) (Fin n → ℝ)"
    assert _match(err) == ("docs/pitfalls/statistics_domain.md", "§D.3")

def test_rule7_positive_multiline():
    err = "failed to synthesize\n  HAdd\n  Fin n → ℝ\n  Fin p → ℝ"
    assert _match(err) == ("docs/pitfalls/statistics_domain.md", "§D.3")

def test_rule7_negative():
    r = _match("failed to synthesize HAdd (Fin n → ℤ) (Fin n → ℤ)")
    assert r is None or r[1] != "§D.3"


# ── Rule 8 ───────────────────────────────────────────────────────────────

def test_rule8_positive_orderbot():
    assert _match("failed to synthesize OrderBot ℝ") == ("docs/pitfalls/typeclass_errors.md", "§A.1")

def test_rule8_positive_supset():
    assert _match("failed to synthesize SupSet ℝ for real numbers") == ("docs/pitfalls/typeclass_errors.md", "§A.1")

def test_rule8_negative():
    r = _match("failed to synthesize Add ℝ")
    assert r is None or r[1] != "§A.1"


# ── Rule 9 ───────────────────────────────────────────────────────────────

def test_rule9_positive_prob():
    assert _match("failed to synthesize IsProbabilityMeasure μ") == ("docs/pitfalls/typeclass_errors.md", "§A.2")

def test_rule9_positive_sigma():
    assert _match("failed to synthesize SigmaFinite μ") == ("docs/pitfalls/typeclass_errors.md", "§A.2")

def test_rule9_negative():
    r = _match("failed to synthesize IsRingHom f")
    assert r is None or r[1] != "§A.2"


# ── Rule 10 ──────────────────────────────────────────────────────────────

def test_rule10_positive():
    assert _match("failed to synthesize MeasurableSpace α") == ("docs/pitfalls/typeclass_errors.md", "§A.3")

def test_rule10_negative():
    r = _match("failed to synthesize Measurable f")
    assert r is None or r[1] != "§A.3"


# ── Rule 11 ──────────────────────────────────────────────────────────────

def test_rule11_positive():
    assert _match("failed to synthesize Integrable f μ") == ("docs/pitfalls/typeclass_errors.md", "§A.4")

def test_rule11_negative():
    r = _match("failed to synthesize StronglyMeasurable f")
    assert r is None or r[1] != "§A.4"


# ── Rule 12 ──────────────────────────────────────────────────────────────

def test_rule12_positive():
    assert _match("failed to synthesize Fintype (Fin n)") == ("docs/pitfalls/typeclass_errors.md", "§A.5")

def test_rule12_negative():
    r = _match("failed to synthesize Finite α")
    assert r is None or r[1] != "§A.5"


# ── Rule 13 (DOTALL, U+2020 ✝) ───────────────────────────────────────────

def test_rule13_positive_inst_digit():
    assert _match("synthesized type inst✝1") == ("docs/pitfalls/instance_pollution.md", "§A")

def test_rule13_positive_multiline():
    err = "synthesized type\n  inst✝3\ninferred type\n  inst2"
    assert _match(err) == ("docs/pitfalls/instance_pollution.md", "§A")

def test_rule13_positive_inferred():
    assert _match("inferred type inst*2 here") == ("docs/pitfalls/instance_pollution.md", "§A")

def test_rule13_negative():
    r = _match("synthesized type SomeType")
    assert r is None or r[1] != "§A"


# ── Rule 14 ──────────────────────────────────────────────────────────────

def test_rule14_positive():
    assert _match("(deterministic) timeout at 'typeclass'") == ("docs/pitfalls/typeclass_errors.md", "§B.1")

def test_rule14_positive_no_quotes():
    assert _match("(deterministic) timeout at typeclass") == ("docs/pitfalls/typeclass_errors.md", "§B.1")

def test_rule14_negative():
    # "timeout at elaboration" should fall to rule 15, not rule 14
    r = _match("(deterministic) timeout at elaboration")
    assert r is None or r[1] == "§B.2"


# ── Rule 15 ──────────────────────────────────────────────────────────────

def test_rule15_positive_timeout():
    assert _match("(deterministic) timeout in tactic") == ("docs/pitfalls/typeclass_errors.md", "§B.2")

def test_rule15_positive_heartbeats():
    assert _match("maximum number of heartbeats (400000) reached") == ("docs/pitfalls/typeclass_errors.md", "§B.2")

def test_rule15_negative():
    r = _match("(soft) timeout in simp")
    assert r is None or r[1] != "§B.2"


# ── Rule 16 ──────────────────────────────────────────────────────────────

def test_rule16_positive():
    assert _match("maximum recursion depth has been reached") == ("docs/pitfalls/typeclass_errors.md", "§B.3")

def test_rule16_negative():
    r = _match("maximum depth reached")
    assert r is None or r[1] != "§B.3"


# ── Rule 17 ──────────────────────────────────────────────────────────────

def test_rule17_positive():
    assert _match("fail to show termination for myDef") == ("docs/pitfalls/typeclass_errors.md", "§B.4")

def test_rule17_negative():
    r = _match("cannot show termination easily")
    assert r is None or r[1] != "§B.4"


# ── Rule 18 (DOTALL) ─────────────────────────────────────────────────────

def test_rule18_positive_nat_real():
    err = "type mismatch\n  expected: ℝ\n  got: ℕ"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§B.2")

def test_rule18_positive_real_nat():
    err = "type mismatch\n  expected: ℕ\n  got: ℝ"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§B.2")

def test_rule18_dotall():
    err = "type mismatch\nsome long elaboration\nmany lines\nhere\nℕ and then later\nℝ coercion needed"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§B.2")

def test_rule18_negative():
    r = _match("type mismatch\n  expected: ℤ\n  got: ℚ")
    assert r is None or r[1] != "§B.2"


# ── Rule 19 (DOTALL) ─────────────────────────────────────────────────────

def test_rule19_positive_multiline():
    err = "tactic 'exact' failed\ntype mismatch in goal"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§B.3")

def test_rule19_dotall():
    err = "tactic 'exact' failed\nmany lines between\nmore lines\ntype mismatch here"
    assert _match(err) == ("docs/pitfalls/lean_syntax_errors.md", "§B.3")

def test_rule19_negative():
    r = _match("tactic 'apply' failed\ntype mismatch")
    assert r is None or r[1] != "§B.3"


# ── Rule 20 ──────────────────────────────────────────────────────────────

def test_rule20_positive():
    assert _match("no goals to be solved") == ("docs/pitfalls/lean_syntax_errors.md", "§B.6")

def test_rule20_negative():
    r = _match("no goals remaining")
    assert r is None or r[1] != "§B.6"


# ── Rule 21 (IGNORECASE) ─────────────────────────────────────────────────

def test_rule21_positive_lower():
    assert _match("numerals are natural but expected type is Prop") == ("docs/pitfalls/lean_syntax_errors.md", "§B.5")

def test_rule21_positive_mixed_case():
    assert _match("Numerals Are Natural But Expected Type Is Prop") == ("docs/pitfalls/lean_syntax_errors.md", "§B.5")

def test_rule21_negative():
    r = _match("numerals are natural but expected type is Nat")
    assert r is None or r[1] != "§B.5"


# ── Rule 22 ──────────────────────────────────────────────────────────────

def test_rule22_positive_condexp():
    assert _match("Unknown identifier 'condExp'") == ("docs/pitfalls/lean_syntax_errors.md", "§B.9")

def test_rule22_positive_tendsto():
    assert _match("Unknown identifier 'Tendsto'") == ("docs/pitfalls/lean_syntax_errors.md", "§B.9")

def test_rule22_positive_nhds():
    assert _match("Unknown identifier 'nhds'") == ("docs/pitfalls/lean_syntax_errors.md", "§B.9")

def test_rule22_negative():
    r = _match("Unknown identifier 'myLocalDef'")
    assert r is None or r[1] != "§B.9"


# ── Rule 23 ──────────────────────────────────────────────────────────────

def test_rule23_positive_gaussian():
    assert _match("Unknown identifier 'gaussianVolume'") == ("docs/pitfalls/statistics_domain.md", "§B")

def test_rule23_positive_normal():
    assert _match("Unknown identifier 'Normal'") == ("docs/pitfalls/statistics_domain.md", "§B")

def test_rule23_negative():
    r = _match("Unknown identifier 'gaussianReal'")
    # gaussianReal is in rule 22 (§B.9), not rule 23
    assert r is None or r[1] != "§B"


# ── No match ─────────────────────────────────────────────────────────────

def test_no_match():
    assert match_pitfall("completely unrelated error: foo bar baz") is None

def test_empty_string():
    assert match_pitfall("") is None

def test_none_input():
    assert match_pitfall(None) is None  # type: ignore[arg-type]


# ── match_pitfall_suggestion API ─────────────────────────────────────────

def test_suggestion_returns_string():
    r = match_pitfall_suggestion("no goals to be solved")
    assert isinstance(r, str)
    assert "📚" in r
    assert "docs/pitfalls/lean_syntax_errors.md" in r
    assert "§B.6" in r

def test_suggestion_none_on_miss():
    assert match_pitfall_suggestion("completely unrelated error") is None


# ── match_pitfall_suggestion_from_list API ────────────────────────────────

def test_from_list_first_match():
    errors = [
        {"message": "unrelated error one"},
        {"message": "no goals to be solved"},
        {"message": "maximum recursion depth has been reached"},
    ]
    r = match_pitfall_suggestion_from_list(errors)
    assert r is not None
    assert "§B.6" in r  # first match is rule 20 (no goals)

def test_from_list_empty():
    assert match_pitfall_suggestion_from_list([]) is None

def test_from_list_all_miss():
    errors = [{"message": "foo"}, {"message": "bar"}]
    assert match_pitfall_suggestion_from_list(errors) is None

def test_from_list_single_hit():
    errors = [{"message": "failed to synthesize MeasurableSpace α"}]
    r = match_pitfall_suggestion_from_list(errors)
    assert r is not None
    assert "§A.3" in r


# ── hint message format ───────────────────────────────────────────────────

def test_hint_message_format():
    r = match_pitfall("unexpected token 'λ'")
    assert r is not None
    file, section, msg = r
    assert msg.startswith("📚 Similar error pattern →")
    assert f"`{file}`" in msg
    assert section in msg
    assert f'read_file path="{file}"' in msg


# ── priority ordering (first-match-wins) ─────────────────────────────────

def test_priority_rule7_before_rule10():
    # Error mentioning HAdd + Fin n + ℝ should hit rule 7 (stats domain)
    # not rule 8 (typeclass OrderBot) or rule 10 (MeasurableSpace)
    err = "failed to synthesize HAdd (Fin n → ℝ) (Fin n → ℝ)"
    r = _match(err)
    assert r is not None
    assert r[1] == "§D.3"

def test_priority_rule14_before_rule15():
    # Typeclass-specific timeout should hit rule 14 before generic rule 15
    r = _match("(deterministic) timeout at 'typeclass'")
    assert r is not None
    assert r[1] == "§B.1"


# ── DOTALL explicit semantics ─────────────────────────────────────────────

def test_dotall_rule4_no_match_without_note():
    # Without the "Note: It is not possible..." line, rule 4 should not fire
    r = _match("Unknown identifier 'foo'\nSome other context here")
    # May match rule 22 or 23 for known identifiers, but for 'foo' → None
    assert r is None or r[1] != "§A.4"

def test_dotall_rule18_spans_many_lines():
    # Many lines between "type mismatch" and the ℕ/ℝ occurrences
    lines = ["type mismatch"] + ["some elaboration context"] * 10 + ["expected: ℕ"] + ["got: ℝ"]
    err = "\n".join(lines)
    r = _match(err)
    assert r is not None
    assert r[1] == "§B.2"


# ── CLI exit codes ────────────────────────────────────────────────────────

def test_cli_exit0_on_match():
    result = subprocess.run(
        [sys.executable, str(MATCH_PITFALL_PY), "--error-text", "no goals to be solved"],
        capture_output=True, text=True,
    )
    assert result.returncode == 0
    assert "📚" in result.stdout

def test_cli_exit1_on_no_match():
    result = subprocess.run(
        [sys.executable, str(MATCH_PITFALL_PY), "--error-text", "completely unrelated error"],
        capture_output=True, text=True,
    )
    assert result.returncode == 1
    assert result.stdout.strip() == ""

def test_cli_exit2_on_missing_arg():
    result = subprocess.run(
        [sys.executable, str(MATCH_PITFALL_PY)],
        capture_output=True, text=True,
    )
    assert result.returncode == 2


# ── Path alias shim ───────────────────────────────────────────────────────

def test_path_alias_translates_docs_pitfalls():
    assert resolve_pitfalls_alias("docs/pitfalls/lean_syntax_errors.md") == \
        "theme/pitfalls/lean_syntax_errors.md"

def test_path_alias_translates_all_files():
    names = [
        "README.md", "lean_syntax_errors.md", "typeclass_errors.md",
        "instance_pollution.md", "measure_theory_patterns.md",
        "statistics_domain.md", "mathlib_style.md",
    ]
    for name in names:
        src = f"docs/pitfalls/{name}"
        assert resolve_pitfalls_alias(src) == f"theme/pitfalls/{name}"

def test_path_alias_passthrough_non_pitfalls():
    assert resolve_pitfalls_alias("theme/proof_knowledge.yaml") == \
        "theme/proof_knowledge.yaml"
    assert resolve_pitfalls_alias("Statlean/Web/job1/Main.lean") == \
        "Statlean/Web/job1/Main.lean"

def test_path_alias_empty_string():
    assert resolve_pitfalls_alias("") == ""
