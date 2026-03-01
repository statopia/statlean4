#!/usr/bin/env python3
"""Auto-shelve: detect zero-sorry modules and update Verified.lean / Statlean.lean imports.

After a prove pass, this script:
1. Scans Statlean/**/*.lean for zero-sorry modules
2. Adds missing zero-sorry modules to Verified.lean
3. Adds missing modules (any sorry status) to Statlean.lean
4. Calls sync_sorry_backlog.py to reconcile the backlog

Usage:
    python3 theme/scripts/auto_shelve.py --repo-root . [--dry-run] [--fix]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime
from pathlib import Path


def has_sorry(lean_file: Path) -> bool:
    """Check if a .lean file contains any sorry (outside comments)."""
    for line in lean_file.read_text(encoding="utf-8").splitlines():
        stripped = line.split("--")[0]  # remove line comments
        if re.search(r"\bsorry\b", stripped):
            return True
    return False


def file_to_module(lean_file: Path, repo_root: Path) -> str:
    """Convert a .lean file path to a Lean module name.

    e.g. Statlean/Gaussian/Basic.lean -> Statlean.Gaussian.Basic
    """
    rel = lean_file.relative_to(repo_root)
    return str(rel).replace("/", ".").removesuffix(".lean")


def parse_imports(filepath: Path) -> list[str]:
    """Extract 'import Statlean.X' module names from a file."""
    modules = []
    for line in filepath.read_text(encoding="utf-8").splitlines():
        m = re.match(r"^import\s+(Statlean\.\S+)", line)
        if m:
            modules.append(m.group(1))
    return modules


def find_import_insert_pos(lines: list[str]) -> int:
    """Find the line index after the last import statement (before docstring/content)."""
    last_import = -1
    for i, line in enumerate(lines):
        if re.match(r"^import\s+", line):
            last_import = i
    return last_import + 1 if last_import >= 0 else 0


def scan_all_modules(repo_root: Path) -> list[Path]:
    """Find all .lean files under Statlean/, excluding Verified.lean itself."""
    statlean_dir = repo_root / "Statlean"
    return sorted(
        f for f in statlean_dir.rglob("*.lean")
        if f.name != "Verified.lean"
    )


def run(repo_root: Path, fix: bool) -> dict:
    """Main logic. Returns a report dict."""
    verified_path = repo_root / "Statlean" / "Verified.lean"
    statlean_path = repo_root / "Statlean.lean"

    all_files = scan_all_modules(repo_root)
    zero_sorry_files = [f for f in all_files if not has_sorry(f)]
    all_modules = [file_to_module(f, repo_root) for f in all_files]
    zero_sorry_modules = set(file_to_module(f, repo_root) for f in zero_sorry_files)

    # Current imports
    verified_imports = set(parse_imports(verified_path))
    statlean_imports = set(parse_imports(statlean_path))

    # Diffs
    verified_to_add = sorted(zero_sorry_modules - verified_imports)
    statlean_to_add = sorted(set(all_modules) - statlean_imports)

    report = {
        "phase": "auto-shelve",
        "timestamp": datetime.now().isoformat(),
        "zero_sorry_modules": len(zero_sorry_modules),
        "total_modules": len(all_modules),
        "verified_added": verified_to_add,
        "statlean_added": statlean_to_add,
        "fix": fix,
    }

    if not fix:
        # Dry-run: just print
        print(f"[auto-shelve] DRY RUN")
        print(f"  zero-sorry modules: {len(zero_sorry_modules)}/{len(all_modules)}")
        if verified_to_add:
            print(f"  Verified.lean needs: {', '.join(verified_to_add)}")
        else:
            print(f"  Verified.lean: up to date")
        if statlean_to_add:
            print(f"  Statlean.lean needs: {', '.join(statlean_to_add)}")
        else:
            print(f"  Statlean.lean: up to date")
        return report

    # --- Fix mode: write files ---

    # Update Verified.lean
    if verified_to_add:
        lines = verified_path.read_text(encoding="utf-8").splitlines()
        insert_pos = find_import_insert_pos(lines)
        new_lines = [f"import {m}" for m in verified_to_add]
        lines = lines[:insert_pos] + new_lines + lines[insert_pos:]
        verified_path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        print(f"[auto-shelve] Verified.lean: added {len(verified_to_add)} imports")
        for m in verified_to_add:
            print(f"  + import {m}")
    else:
        print(f"[auto-shelve] Verified.lean: up to date")

    # Update Statlean.lean
    if statlean_to_add:
        content = statlean_path.read_text(encoding="utf-8")
        if not content.endswith("\n"):
            content += "\n"
        new_imports = "\n".join(f"import {m}" for m in statlean_to_add)
        content += new_imports + "\n"
        statlean_path.write_text(content, encoding="utf-8")
        print(f"[auto-shelve] Statlean.lean: added {len(statlean_to_add)} imports")
        for m in statlean_to_add:
            print(f"  + import {m}")
    else:
        print(f"[auto-shelve] Statlean.lean: up to date")

    # Sync sorry backlog
    sync_script = repo_root / "theme" / "scripts" / "sync_sorry_backlog.py"
    if sync_script.exists():
        print(f"[auto-shelve] running sync_sorry_backlog.py...")
        subprocess.run(
            [sys.executable, str(sync_script)],
            cwd=str(repo_root),
            check=False,
        )
    else:
        print(f"[auto-shelve] WARNING: sync_sorry_backlog.py not found, skipping")

    # Log to pipeline.jsonl
    log_dir = repo_root / "theme" / "out" / "logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    log_file = log_dir / "pipeline.jsonl"
    with open(log_file, "a", encoding="utf-8") as f:
        f.write(json.dumps(report) + "\n")

    return report


def main() -> None:
    ap = argparse.ArgumentParser(description="Auto-shelve: update Verified.lean / Statlean.lean")
    ap.add_argument("--repo-root", default=".", help="Repository root directory")
    ap.add_argument("--dry-run", action="store_true", help="Only report, don't write (default)")
    ap.add_argument("--fix", action="store_true", help="Actually write changes")
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()

    if not (repo_root / "Statlean").is_dir():
        print(f"[auto-shelve] error: {repo_root / 'Statlean'} not found", file=sys.stderr)
        sys.exit(1)

    fix = args.fix and not args.dry_run
    report = run(repo_root, fix=fix)

    total_changes = len(report.get("verified_added", [])) + len(report.get("statlean_added", []))
    if total_changes == 0:
        print(f"[auto-shelve] nothing to do")


if __name__ == "__main__":
    main()
