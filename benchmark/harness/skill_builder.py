"""Build Skill context for benchmark problems.

Filters tactic_patterns.yaml and mathlib_api_index.md by problem category,
then combines with system_prompt.md into a uniform skill package.
"""

from __future__ import annotations

import os
import re
from pathlib import Path

import yaml

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SKILL_PACKAGE_DIR = Path(__file__).resolve().parent.parent / "config" / "skill_package"


def load_tactic_patterns(path: Path | None = None) -> list[dict]:
    """Load tactic patterns from YAML."""
    if path is None:
        path = PROJECT_ROOT / "theme" / "tactic_patterns.yaml"
    with open(path) as f:
        data = yaml.safe_load(f)
    return data.get("patterns", [])


def load_api_index(path: Path | None = None) -> dict[str, list[str]]:
    """Load mathlib API index, returning {section_name: [api_names]}.

    Parses markdown with ## sections and ``` code blocks.
    """
    if path is None:
        path = PROJECT_ROOT / "theme" / "mathlib_api_index.md"
    content = path.read_text()

    sections = {}
    current_section = None
    in_code_block = False
    apis = []

    for line in content.split("\n"):
        if line.startswith("## "):
            if current_section and apis:
                sections[current_section] = apis
            current_section = line[3:].strip()
            apis = []
            in_code_block = False
        elif line.strip() == "```":
            if in_code_block:
                in_code_block = False
            else:
                in_code_block = True
        elif in_code_block and line.strip():
            apis.append(line.strip())

    if current_section and apis:
        sections[current_section] = apis

    return sections


def filter_patterns_for_problem(
    patterns: list[dict], categories: list[str], keywords: list[str] | None = None
) -> list[dict]:
    """Filter tactic patterns relevant to a problem.

    Args:
        patterns: All loaded patterns
        categories: Category tags to match (e.g., ["integral", "condExp"])
        keywords: Optional keywords to search in goal/notes fields
    """
    matched = []
    cat_set = set(c.lower() for c in categories)

    for p in patterns:
        p_cat = p.get("category", "").lower()
        if p_cat in cat_set:
            matched.append(p)
            continue
        if keywords:
            text = (p.get("goal", "") + " " + p.get("notes", "")).lower()
            if any(kw.lower() in text for kw in keywords):
                matched.append(p)

    # Sort by frequency (most useful first)
    def _freq(p):
        v = p.get("frequency", 0)
        if isinstance(v, int):
            return v
        try:
            return int(str(v).rstrip("+"))
        except (ValueError, TypeError):
            return 0
    matched.sort(key=_freq, reverse=True)
    return matched


def filter_api_sections(
    api_index: dict[str, list[str]], section_names: list[str]
) -> dict[str, list[str]]:
    """Filter API index to only include relevant sections.

    Uses fuzzy matching on section names.
    """
    result = {}
    for target in section_names:
        target_lower = target.lower()
        for section, apis in api_index.items():
            if target_lower in section.lower() or section.lower() in target_lower:
                result[section] = apis
    return result


def format_patterns_for_prompt(patterns: list[dict], max_patterns: int = 15) -> str:
    """Format filtered patterns into a prompt-friendly string."""
    if not patterns:
        return "No relevant tactic patterns found."

    lines = ["## Relevant Tactic Patterns\n"]
    for p in patterns[:max_patterns]:
        lines.append(f"### {p.get('id', 'unknown')}")
        lines.append(f"- **Goal**: {p.get('goal', 'N/A')}")
        tactics = p.get("tactics", "")
        if isinstance(tactics, list):
            tactics = " | ".join(tactics)
        lines.append(f"- **Tactics**: `{tactics}`")
        if p.get("notes"):
            lines.append(f"- **Notes**: {p['notes']}")
        lines.append("")
    return "\n".join(lines)


def format_apis_for_prompt(filtered_apis: dict[str, list[str]]) -> str:
    """Format filtered API sections into a prompt-friendly string."""
    if not filtered_apis:
        return "No relevant Mathlib APIs found."

    lines = ["## Relevant Mathlib APIs\n"]
    for section, apis in filtered_apis.items():
        lines.append(f"### {section}")
        lines.append("```")
        for api in apis:
            lines.append(api)
        lines.append("```")
        lines.append("")
    return "\n".join(lines)


def build_skill_context(
    problem_config: dict,
    system_prompt_path: Path | None = None,
) -> str:
    """Build the complete Skill context for a problem.

    Args:
        problem_config: Problem dict from problems.yaml with fields:
            - categories: list[str] (e.g., ["condExp", "integral"])
            - api_sections: list[str] (e.g., ["Conditional Expectation", "Variance"])
            - keywords: list[str] (optional)
        system_prompt_path: Path to system_prompt.md

    Returns:
        Complete skill context string (identical for all models).
    """
    if system_prompt_path is None:
        system_prompt_path = SKILL_PACKAGE_DIR / "system_prompt.md"

    # Load system prompt
    system_prompt = ""
    if system_prompt_path.exists():
        system_prompt = system_prompt_path.read_text()

    # Load and filter patterns
    patterns = load_tactic_patterns()
    categories = problem_config.get("categories", [])
    keywords = problem_config.get("keywords", [])
    filtered_patterns = filter_patterns_for_problem(patterns, categories, keywords)
    patterns_text = format_patterns_for_prompt(filtered_patterns)

    # Load and filter API index
    api_index = load_api_index()
    api_sections = problem_config.get("api_sections", [])
    filtered_apis = filter_api_sections(api_index, api_sections)
    apis_text = format_apis_for_prompt(filtered_apis)

    # Combine
    parts = [system_prompt, "", patterns_text, "", apis_text]
    return "\n".join(parts).strip()


def load_retry_template(path: Path | None = None) -> str:
    """Load the retry template for multi-round experiments."""
    if path is None:
        path = SKILL_PACKAGE_DIR / "retry_template.md"
    if path.exists():
        return path.read_text()
    return (
        "The previous proof attempt failed with the following error:\n\n"
        "```\n{error}\n```\n\n"
        "Please fix the proof. Common issues:\n"
        "- Unknown identifier: check Mathlib API name spelling\n"
        "- Type mismatch: check expected vs actual types\n"
        "- Sorry remaining: complete all proof branches\n\n"
        "Provide the corrected proof body (everything after `:= by`)."
    )
