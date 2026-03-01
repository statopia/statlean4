#!/usr/bin/env python3
"""Select prove targets from sorry_backlog.yaml, optionally filtered by manifest.

Outputs prove_targets.json with prompts ready for Claude Code subagents.
Does NOT call any external API — target selection + prompt generation only.

Usage:
    python3 prove_select_targets.py --repo-root /path/to/repo [--manifest path] [--max-targets 3]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

import yaml


def select_targets(
    backlog_path: Path,
    manifest_path: Path | None,
    max_targets: int,
    failed: set[str] | None = None,
) -> list[dict[str, Any]]:
    """Select sorry targets from backlog, optionally filtered by manifest."""
    if not backlog_path.exists():
        print("[prove-select] no sorry_backlog.yaml found", file=sys.stderr)
        return []

    data = yaml.safe_load(backlog_path.read_text()) or {}
    items: list[dict] = list(data.get("sorry_items") or [])

    # Filter by manifest if provided
    manifest_files: set[str] | None = None
    manifest_targets: set[tuple[str, str]] | None = None
    if manifest_path and manifest_path.is_file():
        try:
            manifest = json.loads(manifest_path.read_text())
            entries = list((manifest.get("entries") or {}).values())
            manifest_files = {
                e["file"]
                for e in entries
                if "file" in e
            }
            manifest_targets = {
                (e.get("file", ""), e.get("lean_name", ""))
                for e in entries
                if e.get("file") and e.get("lean_name")
            }
            if manifest_targets:
                print(
                    f"[prove-select] pipeline mode: {len(manifest_targets)} theorem sites from manifest",
                    file=sys.stderr,
                )
            else:
                print(
                    f"[prove-select] pipeline mode: {len(manifest_files)} files from manifest",
                    file=sys.stderr,
                )
        except (json.JSONDecodeError, KeyError) as exc:
            print(
                f"[prove-select] manifest parse error ({exc}), using full backlog",
                file=sys.stderr,
            )

    # Filter
    failed = failed or set()
    filtered = [
        it
        for it in items
        if it.get("type") not in ("blocked",)
        and it.get("theorem", "") not in failed
        and (
            (manifest_targets is not None and (it.get("file", ""), it.get("theorem", "")) in manifest_targets)
            or (manifest_targets is None and (manifest_files is None or it.get("file", "") in manifest_files))
        )
    ]

    # Sort by priority
    filtered.sort(key=lambda x: x.get("priority", 99))
    return filtered[:max_targets]


def build_prompt(target: dict, repo_root: Path, playbook_path: Path) -> str:
    """Build a prove prompt for a single target."""
    file = target["file"]
    theorem = target["theorem"]
    module_name = file.replace("Statlean/", "").replace("/", ".").replace(".lean", "")

    # Backlog context
    backlog_context = json.dumps(target, indent=2, ensure_ascii=False)

    # Playbook
    playbook = ""
    if playbook_path.is_file():
        playbook = playbook_path.read_text()
    else:
        playbook = "(prove_playbook.md not found — use standard approach)"

    return f"""{playbook}

================================================================
TARGET
================================================================

File: {file}
Theorem: {theorem}
Module: Statlean.{module_name}
Workspace: {repo_root}

Backlog context:
{backlog_context}

================================================================
EXECUTION
================================================================

1. Read the target file, locate theorem {theorem}
2. Follow the playbook above: strategy selection → API search → write proof → compile → fix
3. Verify: cd {repo_root} && lake build Statlean.{module_name}
4. Focus ONLY on theorem {theorem} — do NOT modify other declarations
5. Each sub-lemma proved → immediately write to file and lake build verify

Acceptance:
- sorry is eliminated from theorem {theorem}
- Incremental build passes (lake build Statlean.{module_name})
"""


def main() -> None:
    ap = argparse.ArgumentParser(description="Select prove targets for Claude Code subagents")
    ap.add_argument("--repo-root", required=True, help="Repository root path")
    ap.add_argument("--manifest", default=None, help="Path to manifest.json (pipeline mode)")
    ap.add_argument("--max-targets", type=int, default=3, help="Max targets to select")
    ap.add_argument("--output", default=None, help="Output JSON path (default: theme/out/prove_targets.json)")
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()
    backlog_path = repo_root / "theme" / "input" / "sorry_backlog.yaml"
    playbook_path = repo_root / "theme" / "prove_playbook.md"
    manifest_path = Path(args.manifest) if args.manifest else None
    output_path = Path(args.output) if args.output else repo_root / "theme" / "out" / "prove_targets.json"

    targets = select_targets(backlog_path, manifest_path, args.max_targets)

    if not targets:
        print("[prove-select] no actionable targets found", file=sys.stderr)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(json.dumps({"targets": []}, indent=2))
        print(f"[prove-select] wrote {output_path} (0 targets)")
        return

    # Build prompts
    results = []
    for t in targets:
        prompt = build_prompt(t, repo_root, playbook_path)
        results.append({
            "id": t.get("id", ""),
            "file": t["file"],
            "theorem": t["theorem"],
            "line": t.get("line", 0),
            "priority": t.get("priority", 99),
            "prompt": prompt,
        })

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps({"targets": results}, indent=2, ensure_ascii=False))
    print(f"[prove-select] wrote {output_path} ({len(results)} targets)")
    for r in results:
        print(f"  - {r['file']}:{r['theorem']} (priority={r['priority']})")


if __name__ == "__main__":
    main()
