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

        for i, line in enumerate(lines, 1):
            # Track declarations
            decl_match = re.match(
                r"^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure|class)\s+(\w+)", line
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

    existing_items: List[Dict[str, Any]] = list(data.get("sorry_items", []) or [])

    # Index existing items by file::theorem
    existing_by_key: Dict[str, Dict[str, Any]] = {}
    existing_by_id: Dict[str, Dict[str, Any]] = {}
    for item in existing_items:
        key = make_site_key(item.get("file", ""), item.get("theorem", ""))
        existing_by_key[key] = item
        if "id" in item:
            existing_by_id[item["id"]] = item

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

    # Count removed (in backlog but not in code)
    for key, item in existing_by_key.items():
        if key not in seen_keys:
            stats["removed"] += 1

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
