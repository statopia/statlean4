#!/usr/bin/env python3
"""Ingest new proof knowledge entries into theme/proof_knowledge.yaml.

Usage:
  # From a YAML file
  python3 scripts/ingest_knowledge.py --input /tmp/new_knowledge.yaml

  # From stdin (pipe from agent output)
  echo '...' | python3 scripts/ingest_knowledge.py --stdin

  # Run tests
  python3 scripts/ingest_knowledge.py --test
"""

import argparse
import re
import sys
from pathlib import Path

# Use ruamel if available for round-trip, else pyyaml
try:
    import yaml
except ImportError:
    print("ERROR: pyyaml not installed. Run: pip install pyyaml", file=sys.stderr)
    sys.exit(1)

KNOWLEDGE_PATH = Path(__file__).parent.parent / "theme" / "proof_knowledge.yaml"

# ── Helpers ──────────────────────────────────────────────────────────────────

STOP_WORDS = {
    "a", "an", "the", "is", "are", "was", "were", "be", "been", "being",
    "have", "has", "had", "do", "does", "did", "will", "would", "shall",
    "should", "may", "might", "must", "can", "could", "of", "in", "to",
    "for", "with", "on", "at", "from", "by", "about", "as", "into",
    "through", "during", "before", "after", "above", "below", "between",
    "or", "and", "but", "not", "no", "nor", "so", "yet", "both", "either",
    "neither", "each", "every", "all", "any", "few", "more", "most",
    "other", "some", "such", "than", "too", "very", "just", "because",
    "if", "when", "where", "how", "what", "which", "who", "whom", "this",
    "that", "these", "those", "it", "its",
}


def extract_keywords(text: str) -> set[str]:
    """Extract meaningful keywords from trigger text."""
    words = set(re.findall(r"[a-zA-Z_][a-zA-Z0-9_]*", text.lower()))
    return words - STOP_WORDS


def jaccard_similarity(a: set, b: set) -> float:
    """Jaccard similarity between two keyword sets."""
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    return len(a & b) / len(a | b)


def find_similar(trigger: str, entries: list[dict], threshold: float = 0.5) -> list[tuple[float, dict]]:
    """Find entries with similar triggers, sorted by similarity desc."""
    kw = extract_keywords(trigger)
    results = []
    for entry in entries:
        existing_kw = extract_keywords(entry.get("trigger", ""))
        sim = jaccard_similarity(kw, existing_kw)
        if sim >= threshold:
            results.append((sim, entry))
    results.sort(key=lambda x: -x[0])
    return results


# ── Core logic ───────────────────────────────────────────────────────────────

LEVEL_MAP = {
    "L1": "L1_tactic_tips",
    "L2": "L2_api_chains",
    "L3": "L3_strategies",
}

# Required fields per level
REQUIRED_FIELDS = {
    "L1": {"trigger", "tip"},
    "L2": {"trigger", "chain"},
    "L3": {"trigger", "strategy"},
}

# Optional fields (accepted but not required)
OPTIONAL_FIELDS = {"workflow", "key_api", "source", "confidence", "frequency", "anti"}


def validate_entry(entry: dict) -> tuple[bool, str]:
    """Validate a new_knowledge entry. Returns (ok, error_msg)."""
    level = entry.get("level", "")
    if level not in LEVEL_MAP:
        return False, f"Invalid level: {level}. Must be L1, L2, or L3."

    required = REQUIRED_FIELDS[level]
    missing = required - set(entry.keys())
    if missing:
        return False, f"Missing required fields for {level}: {missing}"

    confidence = entry.get("confidence", 3)
    if level == "L1":
        freq = entry.get("frequency", 1)
        # L1 needs frequency >= 2 to auto-ingest (but we track freq=1 for later)
        pass  # Frequency check is soft — script accumulates
    elif level == "L2":
        chain = entry.get("chain", "")
        if "→" not in chain and len(chain.split()) < 2:
            return False, f"L2 chain too short (need ≥2 API): {chain}"
    elif level == "L3":
        if confidence < 3:
            return False, f"L3 confidence {confidence} < 3 — not ingested."

    return True, ""


def load_knowledge() -> dict:
    """Load the proof_knowledge.yaml file."""
    if not KNOWLEDGE_PATH.exists():
        return {"version": "v1", "entry_count": 0,
                "L3_strategies": [], "L2_api_chains": [], "L1_tactic_tips": []}
    with open(KNOWLEDGE_PATH) as f:
        data = yaml.safe_load(f)
    # Ensure all sections exist
    for section in ["L3_strategies", "L2_api_chains", "L1_tactic_tips"]:
        if data.get(section) is None:
            data[section] = []
    return data


def save_knowledge(data: dict):
    """Save the proof_knowledge.yaml file with section comments preserved."""
    # Update entry count
    total = (len(data.get("L3_strategies", []))
             + len(data.get("L2_api_chains", []))
             + len(data.get("L1_tactic_tips", [])))
    data["entry_count"] = total

    # Write with manual formatting for readability
    lines = []
    lines.append("# theme/proof_knowledge.yaml — 四层证明知识库")
    lines.append("# 使用方法：按 trigger 字段匹配当前 goal，读对应 strategy/chain/tip")
    lines.append("# 可选 workflow 字段：描述证明组织方式（\"做 X 之前先做 Y\"），避免 agent 重复试错")
    lines.append("# 维护：成功证明后由 scripts/ingest_knowledge.py 自动入库")
    lines.append(f"version: {data.get('version', 'v1')}")
    lines.append(f"entry_count: {total}")
    lines.append("")

    # L3
    lines.append("# ═══════════════════════════════════════════")
    lines.append("# L3 — 证明策略（按 goal 形状索引）")
    lines.append("# ═══════════════════════════════════════════")
    lines.append("L3_strategies:")
    for entry in data.get("L3_strategies", []):
        lines.append("")
        lines.append(f'  - trigger: "{entry["trigger"]}"')
        lines.append(f'    strategy: "{entry["strategy"]}"')
        if "workflow" in entry:
            lines.append(f'    workflow: "{entry["workflow"]}"')
        if "key_api" in entry:
            lines.append(f'    key_api: {entry["key_api"]}')
        if "source" in entry:
            lines.append(f'    source: {entry["source"]}')
        lines.append(f'    confidence: {entry.get("confidence", 3)}')
    lines.append("")

    # L2
    lines.append("# ═══════════════════════════════════════════")
    lines.append("# L2 — API 链路（Mathlib 引理串联方案）")
    lines.append("# ═══════════════════════════════════════════")
    lines.append("L2_api_chains:")
    for entry in data.get("L2_api_chains", []):
        lines.append("")
        lines.append(f'  - trigger: "{entry["trigger"]}"')
        lines.append(f'    chain: "{entry["chain"]}"')
        if "workflow" in entry:
            lines.append(f'    workflow: "{entry["workflow"]}"')
        if "source" in entry:
            lines.append(f'    source: {entry["source"]}')
        if "confidence" in entry:
            lines.append(f'    confidence: {entry["confidence"]}')
    lines.append("")

    # L1
    lines.append("# ═══════════════════════════════════════════")
    lines.append("# L1 — Tactic 技巧（常见坑和惯用法）")
    lines.append("# ═══════════════════════════════════════════")
    lines.append("L1_tactic_tips:")
    for entry in data.get("L1_tactic_tips", []):
        lines.append("")
        lines.append(f'  - trigger: "{entry["trigger"]}"')
        lines.append(f'    tip: "{entry["tip"]}"')
        if "frequency" in entry:
            lines.append(f'    frequency: {entry["frequency"]}')
    lines.append("")

    with open(KNOWLEDGE_PATH, "w") as f:
        f.write("\n".join(lines))


def ingest_entries(new_entries: list[dict], dry_run: bool = False) -> dict:
    """Ingest a list of new_knowledge entries. Returns summary."""
    data = load_knowledge()
    summary = {"added": 0, "updated": 0, "skipped": 0, "errors": []}

    for entry in new_entries:
        # Validate
        ok, err = validate_entry(entry)
        if not ok:
            summary["errors"].append(err)
            summary["skipped"] += 1
            continue

        level = entry["level"]
        section_key = LEVEL_MAP[level]
        existing = data[section_key]
        trigger = entry["trigger"]

        # Dedup check
        similar = find_similar(trigger, existing, threshold=0.5)
        if similar and similar[0][0] > 0.8:
            # High similarity — update existing entry
            best_sim, best_entry = similar[0]
            if level == "L1":
                old_freq = best_entry.get("frequency", 1)
                best_entry["frequency"] = old_freq + entry.get("frequency", 1)
            if "source" in entry and "source" in best_entry:
                # Merge sources
                existing_sources = set(best_entry["source"]) if isinstance(best_entry["source"], list) else {best_entry["source"]}
                new_sources = set(entry["source"]) if isinstance(entry["source"], list) else {entry["source"]}
                best_entry["source"] = sorted(existing_sources | new_sources)
            summary["updated"] += 1
            continue

        # Build the entry for insertion
        new_entry = {"trigger": trigger}
        if level == "L3":
            new_entry["strategy"] = entry["strategy"]
            if "workflow" in entry:
                new_entry["workflow"] = entry["workflow"]
            if "key_api" in entry:
                new_entry["key_api"] = entry["key_api"]
            if "source" in entry:
                new_entry["source"] = entry["source"]
            new_entry["confidence"] = entry.get("confidence", 3)
            if similar and similar[0][0] > 0.5:
                # Medium similarity — add review marker
                new_entry["strategy"] = f"# REVIEW: similar to existing. " + new_entry["strategy"]
        elif level == "L2":
            new_entry["chain"] = entry["chain"]
            if "workflow" in entry:
                new_entry["workflow"] = entry["workflow"]
            if "source" in entry:
                new_entry["source"] = entry["source"]
            if "confidence" in entry:
                new_entry["confidence"] = entry["confidence"]
        elif level == "L1":
            new_entry["tip"] = entry["tip"]
            new_entry["frequency"] = entry.get("frequency", 1)

        existing.append(new_entry)
        summary["added"] += 1

    if not dry_run:
        save_knowledge(data)

    return summary


# ── Input parsing ────────────────────────────────────────────────────────────

def parse_new_knowledge_yaml(text: str) -> list[dict]:
    """Parse a new_knowledge YAML block (possibly embedded in agent output)."""
    # Try to extract just the new_knowledge section
    match = re.search(r"new_knowledge:\s*\n((?:\s+-.*\n?|\s+\w+:.*\n?)*)", text)
    if match:
        yaml_text = "items:\n" + match.group(1)
    else:
        yaml_text = text

    try:
        parsed = yaml.safe_load(yaml_text)
    except yaml.YAMLError as e:
        print(f"YAML parse error: {e}", file=sys.stderr)
        return []

    if isinstance(parsed, dict) and "items" in parsed:
        return parsed["items"]
    if isinstance(parsed, dict) and "new_knowledge" in parsed:
        return parsed["new_knowledge"]
    if isinstance(parsed, list):
        return parsed
    return []


# ── Tests ────────────────────────────────────────────────────────────────────

def run_tests():
    """Run unit tests."""
    passed = 0
    failed = 0

    # Test 1: keyword extraction
    kw = extract_keywords("∫ f dμ ≤ ∫ g dμ with integrability")
    assert "integrability" in kw, f"Test 1 failed: {kw}"
    passed += 1

    # Test 2: Jaccard similarity
    a = {"integral", "mono", "ae", "integrability"}
    b = {"integral", "mono", "bound", "integrability"}
    sim = jaccard_similarity(a, b)
    assert 0.5 < sim < 0.8, f"Test 2 failed: sim={sim}"
    passed += 1

    # Test 3: validate L3 entry
    ok, _ = validate_entry({"level": "L3", "trigger": "test", "strategy": "test", "confidence": 3})
    assert ok, "Test 3 failed"
    passed += 1

    # Test 4: validate L3 low confidence rejected
    ok, err = validate_entry({"level": "L3", "trigger": "test", "strategy": "test", "confidence": 2})
    assert not ok, f"Test 4 failed: {err}"
    passed += 1

    # Test 5: validate L2 entry
    ok, _ = validate_entry({"level": "L2", "trigger": "test", "chain": "A → B → C"})
    assert ok, "Test 5 failed"
    passed += 1

    # Test 6: validate missing fields
    ok, err = validate_entry({"level": "L1", "trigger": "test"})
    assert not ok, f"Test 6 failed"
    passed += 1

    # Test 7: parse new_knowledge YAML
    text = """new_knowledge:
  - level: L3
    trigger: "test goal"
    strategy: "test strategy"
    confidence: 4
  - level: L1
    trigger: "test tip"
    tip: "use simp"
    frequency: 3
"""
    entries = parse_new_knowledge_yaml(text)
    assert len(entries) == 2, f"Test 7 failed: got {len(entries)} entries"
    assert entries[0]["level"] == "L3", f"Test 7 failed: {entries[0]}"
    passed += 1

    # Test 8: dedup detection
    existing = [{"trigger": "integral mono ae with integrability bound"}]
    similar = find_similar("integral mono ae integrability", existing)
    assert len(similar) > 0 and similar[0][0] > 0.7, f"Test 8 failed: {similar}"
    passed += 1

    # Test 9: load existing knowledge file
    data = load_knowledge()
    assert "L3_strategies" in data, "Test 9 failed"
    assert len(data["L3_strategies"]) > 0, "Test 9 failed: no L3 entries"
    passed += 1

    # Test 10: dry-run ingest
    test_entries = [
        {"level": "L1", "trigger": "unique test trigger xyz123", "tip": "test tip", "frequency": 1},
    ]
    summary = ingest_entries(test_entries, dry_run=True)
    assert summary["added"] == 1, f"Test 10 failed: {summary}"
    passed += 1

    print(f"\n✓ All {passed} tests passed ({failed} failed)")
    return failed == 0


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="Ingest proof knowledge entries")
    parser.add_argument("--input", type=str, help="Path to YAML file with new_knowledge entries")
    parser.add_argument("--stdin", action="store_true", help="Read from stdin")
    parser.add_argument("--test", action="store_true", help="Run unit tests")
    parser.add_argument("--dry-run", action="store_true", help="Validate without writing")
    args = parser.parse_args()

    if args.test:
        success = run_tests()
        sys.exit(0 if success else 1)

    if args.stdin:
        text = sys.stdin.read()
    elif args.input:
        text = Path(args.input).read_text()
    else:
        parser.print_help()
        sys.exit(1)

    entries = parse_new_knowledge_yaml(text)
    if not entries:
        print("No valid entries found in input.", file=sys.stderr)
        sys.exit(1)

    summary = ingest_entries(entries, dry_run=args.dry_run)

    print(f"Knowledge ingestion {'(dry-run) ' if args.dry_run else ''}summary:")
    print(f"  Added:   {summary['added']}")
    print(f"  Updated: {summary['updated']}")
    print(f"  Skipped: {summary['skipped']}")
    if summary["errors"]:
        print(f"  Errors:")
        for err in summary["errors"]:
            print(f"    - {err}")


if __name__ == "__main__":
    main()
