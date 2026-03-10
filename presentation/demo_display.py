#!/usr/bin/env python3
"""
Audience display for /prove-out demo.

Usage:
  Terminal 2 (projector): python3 presentation/demo_display.py
  Terminal 1 (operator):  claude  →  /prove-out <target>

Reads /tmp/prove_stages.log in real time and renders each line
with colors. Supports two content types:
  - Real-time log lines ([tag] prefixed)
  - Stage summary blocks (━━━ STAGE N/5: NAME ━━━ ... ━━━━━)
"""

import os
import sys
import time
import re

LOG_PATH = "/tmp/prove_stages.log"

# ANSI color codes
RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"
BLUE = "\033[34m"
GREEN = "\033[32m"
RED = "\033[31m"
YELLOW = "\033[33m"
WHITE = "\033[37m"
CYAN = "\033[36m"
MAGENTA = "\033[35m"

BOLD_BLUE = f"{BOLD}{BLUE}"
BOLD_GREEN = f"{BOLD}{GREEN}"
BOLD_RED = f"{BOLD}{RED}"
BOLD_CYAN = f"{BOLD}{CYAN}"
BOLD_WHITE = f"{BOLD}{WHITE}"
BOLD_YELLOW = f"{BOLD}{YELLOW}"
BOLD_MAGENTA = f"{BOLD}{MAGENTA}"

SEP_CHAR = "\u2501"  # ━

# [tag] → color mapping
TAG_COLORS = {
    "[target]": BOLD_WHITE,
    "[file]": DIM,
    "[grade]": BOLD_YELLOW,
    "[search]": CYAN,
    "[hit]": BOLD_GREEN,
    "[miss]": DIM,
    "[idea]": BOLD_MAGENTA,
    "[write]": WHITE,
    "[build]": YELLOW,
    "[pass]": BOLD_GREEN,
    "[fail]": BOLD_RED,
    "[fix]": YELLOW,
}


def colorize_line(line: str) -> str:
    """Apply color to a single line based on content."""
    stripped = line.strip()
    if not stripped:
        return line

    # Stage header/footer: lines containing ━━━
    if SEP_CHAR * 3 in stripped:
        if "STAGE" in stripped:
            return f"{BOLD_CYAN}{line}{RESET}"
        return f"{BOLD_BLUE}{line}{RESET}"

    # [tag] prefixed log lines
    for tag, color in TAG_COLORS.items():
        if stripped.startswith(tag):
            # Color the tag, rest in default or same color
            tag_end = len(tag)
            # Find tag position in original line (preserving indentation)
            idx = line.find(tag)
            if idx >= 0:
                before = line[:idx]
                after = line[idx + tag_end:]
                return f"{before}{BOLD}{color}{tag}{RESET}{color}{after}{RESET}"
            return f"{color}{line}{RESET}"

    # PASS / FORMALIZED lines
    if "PASS" in stripped or "PROVED" in stripped or "FORMALIZED" in stripped:
        return f"{BOLD_GREEN}{line}{RESET}"

    # FAIL lines
    if "FAIL" in stripped:
        return f"{BOLD_RED}{line}{RESET}"

    # Labels (Theorem:, File:, Grade:, etc.)
    label_match = re.match(
        r"(\s*(?:Theorem|File|Grade|Goal|Strategy|Command|Result|Time|"
        r"Sorry count|APIs used|New (?:theorems|patterns)|Search tier|"
        r"Matched|Tactic pattern|Key tactics|Lines):)(.*)", line
    )
    if label_match:
        return f"{BOLD_WHITE}{label_match.group(1)}{RESET}{label_match.group(2)}"

    # Numbered list items (1. hasDerivAt_id etc.)
    if re.match(r"\s+\d+\.", stripped):
        return f"{WHITE}{line}{RESET}"

    # Lean tactic keywords
    lean_kw = ("theorem ", "lemma ", "by", "exact ", "intro ", "apply ",
               "simp", "rw ", "have ", "calc", "congr", "unfold ")
    if any(stripped.startswith(kw) for kw in lean_kw):
        return f"{WHITE}{line}{RESET}"

    return line


def clear_screen():
    os.system("clear" if os.name != "nt" else "cls")


def main():
    # Clear log file on startup
    with open(LOG_PATH, "w") as f:
        pass

    clear_screen()
    print()
    print(f"  {DIM}Waiting for /prove-out output ...{RESET}")
    print(f"  {DIM}(watching {LOG_PATH}){RESET}")
    print()
    sys.stdout.flush()

    pos = 0
    first_line_seen = False

    try:
        while True:
            try:
                with open(LOG_PATH, "r") as f:
                    f.seek(pos)
                    new_content = f.read()
                    if new_content:
                        if not first_line_seen:
                            clear_screen()
                            print()
                            first_line_seen = True
                        for line in new_content.splitlines():
                            print(colorize_line(line))
                        sys.stdout.flush()
                        pos = f.tell()
            except FileNotFoundError:
                pass
            time.sleep(0.3)

    except KeyboardInterrupt:
        print()
        print(f"  {DIM}Demo display stopped.{RESET}")
        print()
        sys.exit(0)


if __name__ == "__main__":
    main()
