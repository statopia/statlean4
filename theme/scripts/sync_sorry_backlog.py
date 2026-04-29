#!/usr/bin/env python3
"""Synchronize sorry_backlog.yaml with actual sorry occurrences in Statlean/.

Scans all .lean files under Statlean/, matches sorry sites against backlog entries,
and reconciles:
  - Existing entries: update `line` numbers, preserve human annotations
  - New sorry sites: add with type=unknown, priority=99
  - Eliminated sorry: remove from backlog
  - DAG: rebuild unlocks/dependencies from `dependencies` field

Usage:
    python3 theme/scripts/sync_sorry_backlog.py [--backlog PATH] [--statlean-dir PATH] [--dry-run]
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

import yaml

# czy newloop merge: schema_version=2 fields (state/children/parent_id/
# history_log) — migration is idempotent, runs on every load so the live
# yaml gets the v2 fields on first sync after slice 1 ships.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402


# ── Slice 4 C — sync tree-awareness ───────────────────────────────────
#
# czy newloop port introduces yaml entries that exist for state-machine
# reasons rather than direct source backing (decomposed-but-unproved
# parents, INACTIVE_WAIT internal nodes, retreated-with-history-log
# nodes). The original sync_sorry_backlog dropped any yaml entry not
# matching a source sorry — that broke the prefab-tree fixture approach
# for L3 multi-level-cascade evidence (see SLICE_3C_LLM_SMOKE.md run-3).
#
# Slice 4 C adds:
#   - `_is_tree_structural(item)` — predicate identifying tree state
#   - `_validate_tree_integrity(items)` — orphan / cycle warnings
#   - Sync now PRESERVES tree-structural items even when source has
#     no matching sorry. Flat orphans (no parent_id, no children, plain
#     INITIALIZED state) are STILL removed — backwards-compat preserved.

_TREE_PRESERVING_STATES = {"INACTIVE_WAIT", "DONE"}


def _is_tree_structural(item: Dict[str, Any]) -> bool:
    """Return True iff this item should survive sync regardless of source
    backing. A tree-structural item carries state-machine state that
    sync_sorry_backlog wasn't designed to scrub.

    Cases that qualify (any one is sufficient):
      - parent_id is set (non-empty / non-null) — child of a decomposed
        parent; not directly source-backed
      - children list is non-empty — internal tree node above a leaf
      - state is INACTIVE_WAIT (parent waiting on children) or DONE
        (already proved or done-by-dependency; preserves audit trail)

    Cases that do NOT qualify (preserve original sync semantics):
      - top-level INITIALIZED entry — flat sorry tracker, sync decides
        by source match
      - top-level ACTIVE_PROVING entry — sub-agent is in-flight on a
        source-backed sorry; sync still source-keys it
    """
    parent_id = item.get("parent_id")
    if parent_id is not None and parent_id != "" and parent_id != "None":
        return True
    if item.get("children"):
        return True
    if item.get("state") in _TREE_PRESERVING_STATES:
        return True
    return False


def _validate_tree_integrity(items: List[Dict[str, Any]]) -> List[str]:
    """Sanity-check the parent_id chain over a list of items.

    Returns a list of human-readable warnings (empty if clean):
      - "orphan parent_id: <id> → <missing-parent>" — child references
        a parent that's not in the backlog
      - "cyclic parent chain at <id>: re-visited <id>" — A→B→A loop
        detected during walk-up

    Cycle detection is bounded by visited-set; never hangs. Warnings
    are non-fatal — sync still completes; the caller decides whether to
    print / log them. A future slice may upgrade these to errors with a
    --strict flag.
    """
    warnings: List[str] = []
    by_id: Dict[str, Dict[str, Any]] = {
        it["id"]: it for it in items if "id" in it
    }
    for it in items:
        pid = it.get("parent_id")
        if pid in (None, "", "None"):
            continue
        if pid not in by_id:
            warnings.append(
                f"orphan parent_id: {it.get('id', '?')} → {pid} (not in backlog)"
            )
    # Cycle detection — separate pass so each item gets its own visited set
    for it in items:
        cursor: Optional[str] = it.get("parent_id") if it.get("parent_id") not in (None, "", "None") else None
        visited: set = {it.get("id")} if it.get("id") else set()
        while cursor is not None:
            if cursor in visited:
                warnings.append(
                    f"cyclic parent chain at {it.get('id', '?')}: re-visited {cursor}"
                )
                break
            visited.add(cursor)
            parent = by_id.get(cursor)
            if parent is None:
                break  # orphan, already warned above
            next_pid = parent.get("parent_id")
            cursor = next_pid if next_pid not in (None, "", "None") else None
    return warnings


def find_sorry_sites(statlean_dir: Path) -> List[Dict[str, Any]]:
    """Scan .lean files for sorry occurrences with surrounding context."""
    sites: List[Dict[str, Any]] = []

    for lean_file in sorted(statlean_dir.rglob("*.lean")):
        rel_path = str(lean_file.relative_to(statlean_dir.parent))
        lines = lean_file.read_text(encoding="utf-8").splitlines()

        # Track current theorem/def context
        current_decl: Optional[str] = None
        current_decl_line: int = 0
        current_decl_kind: str = "unknown"  # "theorem", "lemma", "def", etc.

        in_block_comment = False
        for i, line in enumerate(lines, 1):
            # Track block comments /- ... -/ and /-! ... -/
            # Simple heuristic: track nesting depth
            if not in_block_comment:
                if re.search(r"/[-!]", line) and not re.search(r"-/", line):
                    in_block_comment = True
                    continue
                # Single-line block comment: /- ... -/ on same line
                if re.search(r"/[-!]", line) and re.search(r"-/", line):
                    # Remove block comment content before checking for sorry
                    line = re.sub(r"/[-!].*?-/", "", line)
            else:
                if re.search(r"-/", line):
                    in_block_comment = False
                continue

            # Track declarations
            decl_match = re.match(
                r"^\s*(?:noncomputable\s+)?(?:private\s+|protected\s+)?(theorem|lemma|def|abbrev|structure|class)\s+(\w+)", line
            )
            if decl_match:
                current_decl_kind = decl_match.group(1)
                current_decl = decl_match.group(2)
                current_decl_line = i

            # Detect sorry (not in comments)
            stripped = line.split("--")[0]  # Remove line comments
            if re.search(r"\bsorry\b", stripped):
                # Skip placeholder definitions (def X := sorry)
                # These are pipeline-generated stubs, not real proof targets
                if current_decl_kind in ("def", "abbrev", "structure", "class"):
                    continue

                # Extract blocker from nearby structured comments
                blocker = ""
                for j in range(max(0, i - 5), min(len(lines), i + 3)):
                    m = re.search(r"blocker:\s*(.+)", lines[j], re.IGNORECASE)
                    if m:
                        blocker = m.group(1).strip().strip('"').strip("'")
                        break

                sites.append({
                    "file": rel_path,
                    "line": i,
                    "theorem": current_decl or f"anonymous_L{i}",
                    "decl_line": current_decl_line,
                    "blocker": blocker,
                })

    return sites


def make_site_key(file: str, theorem: str) -> str:
    """Canonical key for matching backlog entries to code sites."""
    return f"{file}::{theorem}"


def sync_backlog(
    backlog_path: Path,
    statlean_dir: Path,
    dry_run: bool = False,
) -> Dict[str, Any]:
    """Synchronize backlog YAML with actual sorry sites. Returns stats."""
    # Load existing backlog
    if backlog_path.exists():
        data = yaml.safe_load(backlog_path.read_text(encoding="utf-8")) or {}
    else:
        data = {}

    # czy newloop merge: ensure v2 schema fields are present on every
    # load. Idempotent — v2 input passes through unchanged.
    migrate_yaml_v1_to_v2(data)

    existing_items: List[Dict[str, Any]] = list(data.get("sorry_items", []) or [])

    # Index existing items by file::theorem AND by id.
    # Slice 4 C: tree-structural items (parent_id set, INACTIVE_WAIT,
    # children non-empty, etc.) DON'T participate in file::theorem
    # source-match dedup — multiple tree levels can share the same
    # source key (root + mid + leaf all referencing one file/theorem).
    existing_by_key: Dict[str, Dict[str, Any]] = {}
    existing_by_id: Dict[str, Dict[str, Any]] = {}
    for item in existing_items:
        if "id" in item:
            existing_by_id[item["id"]] = item
        if _is_tree_structural(item):
            continue  # tree items don't claim a source-match key
        key = make_site_key(item.get("file", ""), item.get("theorem", ""))
        existing_by_key[key] = item

    # Scan code
    sites = find_sorry_sites(statlean_dir)

    # Group sites by theorem (multiple sorry lines in same theorem → one entry)
    theorem_sites: Dict[str, List[Dict[str, Any]]] = defaultdict(list)
    for site in sites:
        key = make_site_key(site["file"], site["theorem"])
        theorem_sites[key].append(site)

    # Reconcile
    new_items: List[Dict[str, Any]] = []
    stats = {"updated": 0, "added": 0, "removed": 0, "unchanged": 0}

    # Process each code sorry group
    seen_keys: set = set()
    for key, group in sorted(theorem_sites.items()):
        seen_keys.add(key)
        first = group[0]
        sorry_lines = [s["line"] for s in group]

        if key in existing_by_key:
            # Update existing entry
            item = dict(existing_by_key[key])
            old_line = item.get("line")
            item["line"] = sorry_lines[0]
            if len(sorry_lines) > 1:
                item["sorry_lines"] = sorry_lines
            elif "sorry_lines" in item:
                del item["sorry_lines"]

            if old_line != sorry_lines[0]:
                stats["updated"] += 1
            else:
                stats["unchanged"] += 1
            new_items.append(item)
        else:
            # New sorry site
            # Generate ID from file path
            parts = first["file"].replace("Statlean/", "").replace(".lean", "").split("/")
            id_prefix = ".".join(p.lower() for p in parts)
            new_id = f"{id_prefix}.{first['theorem']}"

            item = {
                "id": new_id,
                "file": first["file"],
                "line": sorry_lines[0],
                "theorem": first["theorem"],
                "type": "unknown",
                "depth": 1,
                "priority": 99,
                "blocker": first.get("blocker", ""),
                "estimated_lines": 50,
                "dependencies": [],
                "unlocks": [],
            }
            if len(sorry_lines) > 1:
                item["sorry_lines"] = sorry_lines
            new_items.append(item)
            stats["added"] += 1

    # Slice 4 C: preserve tree-structural entries that don't match a
    # source sorry. Iterate by ID (unique) — tree levels sharing the
    # same source key would have collapsed under existing_by_key dedup.
    # Flat orphans (non-tree, no source backing) are still removed
    # (backwards-compat).
    stats["preserved_tree"] = 0
    new_ids = {ni.get("id") for ni in new_items if "id" in ni}
    for item in existing_items:
        item_id = item.get("id")
        if item_id in new_ids:
            continue  # already in new_items via source-match
        if _is_tree_structural(item):
            new_items.append(item)
            new_ids.add(item_id)
            stats["preserved_tree"] += 1
        else:
            # Was a flat entry without source backing → drop
            stats["removed"] += 1

    # Slice 4 C: tree integrity — warnings on orphan refs / cycles.
    # Non-fatal; printed to stderr so the caller (prove-deep narrative
    # or human) sees them but sync still completes.
    integrity_warnings = _validate_tree_integrity(new_items)
    if integrity_warnings:
        for w in integrity_warnings:
            print(f"[sync] tree-integrity warning: {w}", file=sys.stderr)
        stats["tree_warnings"] = len(integrity_warnings)

    # Rebuild unlocks from dependencies
    id_set = {item["id"] for item in new_items if "id" in item}
    for item in new_items:
        item["unlocks"] = []  # Clear and rebuild
    dep_map: Dict[str, List[str]] = defaultdict(list)
    for item in new_items:
        for dep_id in item.get("dependencies", []):
            if dep_id in id_set:
                dep_map[dep_id].append(item["id"])
    for item in new_items:
        item["unlocks"] = sorted(dep_map.get(item.get("id", ""), []))

    # Update type=blocked for items with unresolved dependencies
    proved_ids: set = set()  # IDs not in the sorry list anymore
    for item in new_items:
        deps = item.get("dependencies", [])
        unresolved = [d for d in deps if d in id_set]
        if unresolved and item.get("type") not in ("blocked",):
            item["type"] = "blocked"

    # Sort by priority
    new_items.sort(key=lambda x: (x.get("priority", 99), x.get("id", "")))

    # Rebuild YAML
    version = data.get("version", "v1")
    # Bump version
    vmatch = re.match(r"v(\d+)", str(version))
    if vmatch:
        new_version = f"v{int(vmatch.group(1)) + 1}"
    else:
        new_version = "v1"

    output = {
        "version": new_version,
        "generated": __import__("datetime").date.today().isoformat(),
        "total_sorry": sum(len(item.get("sorry_lines", [item.get("line", 0)])) for item in new_items),
        "sorry_items": new_items,
    }

    if not dry_run:
        # Preserve comments at top by writing fresh YAML
        with open(backlog_path, "w", encoding="utf-8") as f:
            f.write(f"version: {output['version']}\n")
            f.write(f"generated: {output['generated']}\n")
            f.write(f"total_sorry: {output['total_sorry']}\n")
            f.write("\nsorry_items:\n")
            if not new_items:
                f.write("  []\n")
            else:
                for item in new_items:
                    f.write(f"\n- id: {item['id']}\n")
                    f.write(f"  file: {item['file']}\n")
                    f.write(f"  line: {item['line']}\n")
                    if "sorry_lines" in item:
                        f.write(f"  sorry_lines: {item['sorry_lines']}\n")
                    f.write(f"  theorem: {item['theorem']}\n")
                    f.write(f"  type: {item.get('type', 'unknown')}\n")
                    f.write(f"  depth: {item.get('depth', 1)}\n")
                    f.write(f"  priority: {item.get('priority', 99)}\n")
                    blocker = item.get("blocker", "")
                    if blocker:
                        f.write(f'  blocker: "{blocker}"\n')
                    f.write(f"  estimated_lines: {item.get('estimated_lines', 50)}\n")
                    deps = item.get("dependencies", [])
                    f.write(f"  dependencies: [{', '.join(deps)}]\n")
                    unlocks = item.get("unlocks", [])
                    f.write(f"  unlocks: [{', '.join(unlocks)}]\n")
                    # Preserve custom fields (proof_sketch, notes, etc.)
                    _known = {"id", "file", "line", "sorry_lines", "theorem",
                              "type", "depth", "priority", "blocker",
                              "estimated_lines", "dependencies", "unlocks"}
                    for k, v in item.items():
                        if k in _known:
                            continue
                        if isinstance(v, str) and "\n" in v:
                            f.write(f"  {k}: |\n")
                            for ln in v.splitlines():
                                f.write(f"    {ln}\n")
                        elif isinstance(v, str):
                            f.write(f'  {k}: "{v}"\n')
                        elif v is None:
                            # Slice 4 C: explicit null vs the prior bug
                            # where Python None was str()-formatted as
                            # "None" and re-parsed as the string "None"
                            # by yaml.safe_load. Now round-trips clean.
                            f.write(f"  {k}: null\n")
                        elif isinstance(v, (list, dict)):
                            # Slice 4 C: lists / dicts (children,
                            # history_log entries, etc.) need real yaml
                            # serialization — Python repr produced flow
                            # style with single-quoted strings that
                            # yaml accepted but looked wrong.
                            dumped = yaml.safe_dump(
                                v, default_flow_style=None,
                                allow_unicode=True, sort_keys=False,
                            ).rstrip("\n")
                            if "\n" in dumped:
                                f.write(f"  {k}:\n")
                                for ln in dumped.splitlines():
                                    f.write(f"    {ln}\n")
                            else:
                                f.write(f"  {k}: {dumped}\n")
                        else:
                            f.write(f"  {k}: {v}\n")

    return stats


def main() -> None:
    ap = argparse.ArgumentParser(description="Sync sorry_backlog.yaml with code")
    ap.add_argument(
        "--backlog",
        default="theme/input/sorry_backlog.yaml",
        help="Path to sorry_backlog.yaml",
    )
    ap.add_argument(
        "--statlean-dir",
        default="Statlean",
        help="Path to Statlean/ directory",
    )
    ap.add_argument("--dry-run", action="store_true", help="Don't write changes")
    args = ap.parse_args()

    backlog_path = Path(args.backlog).resolve()
    statlean_dir = Path(args.statlean_dir).resolve()

    if not statlean_dir.is_dir():
        print(f"[sync] error: {statlean_dir} is not a directory", file=sys.stderr)
        sys.exit(1)

    stats = sync_backlog(backlog_path, statlean_dir, dry_run=args.dry_run)

    mode = "DRY RUN" if args.dry_run else "UPDATED"
    print(f"[sync] {mode}: +{stats['added']} added, ~{stats['updated']} updated, "
          f"-{stats['removed']} removed, ={stats['unchanged']} unchanged")
    if stats["added"] > 0:
        print(f"[sync] new sorry sites found — review priorities in {backlog_path.name}")
    if stats["removed"] > 0:
        print(f"[sync] {stats['removed']} sorry eliminated — removed from backlog")


if __name__ == "__main__":
    main()
