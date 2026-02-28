#!/usr/bin/env python3
"""Infrastructure audit: check that definitions live in Basic.lean and imports flow downward.

Checks:
1. Definitions (def/structure/class/abbrev) in non-Basic.lean files → warning
2. Basic.lean files importing non-Basic.lean files in same topic → warning (import direction)
3. Duplicate definitions across files → warning
4. Ontology consistency: requires-dependencies vs actual imports, lean_topic vs file location

Exit code 0 (warnings only, does not block pipeline).
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

import yaml

STATLEAN_DIR = "Statlean"
LEAN_DEF_PATTERN = re.compile(
    r"^(def|structure|class|abbrev)\s+(\S+)", re.MULTILINE
)
LEAN_IMPORT_PATTERN = re.compile(
    r"^import\s+(Statlean\.\S+)", re.MULTILINE
)


def audit(repo_root: Path) -> list[str]:
    warnings: list[str] = []
    statlean = repo_root / STATLEAN_DIR

    if not statlean.is_dir():
        warnings.append(f"[infra-audit] {STATLEAN_DIR}/ not found")
        return warnings

    # Collect all definitions and their locations
    defs_by_file: dict[str, list[tuple[str, str]]] = {}  # file → [(kind, name)]
    all_defs: dict[str, list[str]] = {}  # name → [files]

    for lean_file in sorted(statlean.rglob("*.lean")):
        rel = lean_file.relative_to(repo_root)
        content = lean_file.read_text(encoding="utf-8")
        is_basic = lean_file.stem == "Basic"

        # Check 1: definitions in non-Basic files
        matches = LEAN_DEF_PATTERN.findall(content)
        if matches:
            defs_by_file[str(rel)] = matches
            for kind, name in matches:
                all_defs.setdefault(name, []).append(str(rel))
                if not is_basic and kind in ("def", "structure", "class", "abbrev"):
                    # Check if this looks like a standalone definition (not a local let-binding)
                    # Only warn for top-level defs in theorem files
                    parent_dir = lean_file.parent.name
                    if parent_dir not in ("Basic",):
                        warnings.append(
                            f"[infra-audit] WARN: {kind} `{name}` in {rel} "
                            f"(consider moving to {parent_dir}/Basic.lean)"
                        )

        # Check 2: import direction — Basic.lean should not import sibling theorem files
        if is_basic:
            imports = LEAN_IMPORT_PATTERN.findall(content)
            topic = lean_file.parent.name
            for imp in imports:
                parts = imp.split(".")
                # Statlean.Topic.Something where Something != Basic
                if len(parts) >= 3 and parts[1] == topic and parts[2] != "Basic":
                    warnings.append(
                        f"[infra-audit] WARN: {rel} imports {imp} "
                        f"(Basic.lean should not import sibling theorem files)"
                    )

    # Check 3: duplicate definitions
    for name, files in all_defs.items():
        if len(files) > 1:
            warnings.append(
                f"[infra-audit] WARN: `{name}` defined in multiple files: {', '.join(files)}"
            )

    return warnings


def audit_ontology(repo_root: Path) -> list[str]:
    """Check ontology consistency with actual file structure."""
    warnings: list[str] = []
    ontology_path = repo_root / "theme" / "input" / "stat_ontology.yaml"

    if not ontology_path.is_file():
        return warnings  # No ontology file, skip

    with open(ontology_path, encoding="utf-8") as f:
        data = yaml.safe_load(f)

    concepts = data.get("concepts", []) if data else []
    if not concepts:
        return warnings

    concept_ids = {c["id"] for c in concepts}

    for concept in concepts:
        cid = concept["id"]

        # Check: requires references valid concept IDs
        for req in concept.get("requires", []):
            if req not in concept_ids:
                warnings.append(
                    f"[ontology-audit] WARN: concept `{cid}` requires "
                    f"unknown concept `{req}`"
                )

        # Check: parent references valid concept ID
        parent = concept.get("parent")
        if parent and parent not in concept_ids:
            warnings.append(
                f"[ontology-audit] WARN: concept `{cid}` has "
                f"unknown parent `{parent}`"
            )

        # Check: statlean file path exists if specified
        statlean_path = concept.get("statlean", "")
        if statlean_path:
            full_path = repo_root / statlean_path
            if not full_path.is_file():
                warnings.append(
                    f"[ontology-audit] WARN: concept `{cid}` references "
                    f"non-existent file `{statlean_path}`"
                )

        # Check: lean_topic/lean_module consistency with statlean path
        topic = concept.get("lean_topic")
        module = concept.get("lean_module")
        if topic and module and statlean_path:
            expected = f"Statlean/{topic}/{module}.lean"
            if statlean_path != expected:
                warnings.append(
                    f"[ontology-audit] WARN: concept `{cid}` has "
                    f"lean_topic={topic}, lean_module={module} but "
                    f"statlean={statlean_path} (expected {expected})"
                )

    return warnings


def main() -> None:
    repo_root = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(".")
    resolved = repo_root.resolve()
    warnings = audit(resolved)
    warnings.extend(audit_ontology(resolved))

    if warnings:
        for w in warnings:
            print(w)
        print(f"\n[infra-audit] {len(warnings)} warnings (non-blocking)")
    else:
        print("[infra-audit] PASS — no issues found")


if __name__ == "__main__":
    main()
