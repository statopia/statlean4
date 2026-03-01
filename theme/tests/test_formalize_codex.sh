#!/bin/bash
# Test: verify Codex follows formalize_playbook.md
#
# Usage:
#   bash theme/tests/test_formalize_codex.sh
#
# What it does:
#   1. Cleans previous checkpoint log
#   2. Runs Codex with a formalization task
#   3. Checks the checkpoint log for compliance
#   4. Checks that the Lean file was actually created/modified
#   5. Checks that `lake build` passes

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"

LOG="theme/out/formalize_checkpoint.jsonl"

echo "============================================"
echo "Test: Codex formalize playbook compliance"
echo "============================================"

# --- Pre-clean ---
rm -f "$LOG"
mkdir -p theme/out

# --- Choose test target ---
# Use a concept that does NOT exist yet, so the agent has to create something.
# If you want to test with an existing PDF, change the prompt.
TEST_PROMPT="Read AGENTS.md and theme/formalize_playbook.md first. Then: 形式化 lecture-5-handout.pdf 里的 Sufficiency（充分统计量）的定义。Follow formalize_playbook.md Steps 0-7 exactly, writing checkpoint log to theme/out/formalize_checkpoint.jsonl after each step."

echo ""
echo "Prompt: $TEST_PROMPT"
echo ""

# --- Run Codex ---
echo "[1/4] Running Codex..."
codex exec --full-auto "$TEST_PROMPT" 2>&1 | tee theme/out/codex_test_output.log

# --- Check log ---
echo ""
echo "[2/4] Checking checkpoint log..."
if [ ! -f "$LOG" ]; then
    echo "FAIL: No checkpoint log written at $LOG"
    echo "  → Codex did NOT follow the playbook."
    exit 1
fi

python3 theme/scripts/check_formalize_log.py "$LOG"
CHECK_EXIT=$?

# --- Check Lean files ---
echo ""
echo "[3/4] Checking for new/modified Lean files..."
CHANGED=$(git diff --name-only --diff-filter=AM -- 'Statlean/*.lean' 'Statlean/**/*.lean' 2>/dev/null || true)
if [ -z "$CHANGED" ]; then
    echo "WARN: No Lean files were created or modified."
else
    echo "Modified/Added Lean files:"
    echo "$CHANGED" | sed 's/^/  /'
fi

# --- Build check ---
echo ""
echo "[4/4] Running lake build..."
if lake build 2>&1 | tail -5; then
    echo "Build: PASS"
else
    echo "Build: FAIL"
fi

# --- Summary ---
echo ""
echo "============================================"
if [ "$CHECK_EXIT" -eq 0 ] && [ -n "$CHANGED" ]; then
    echo "OVERALL: PASS ✓"
    echo "  Codex followed the playbook and produced compilable Lean code."
else
    echo "OVERALL: NEEDS REVIEW"
    [ "$CHECK_EXIT" -ne 0 ] && echo "  - Checkpoint log incomplete or failed"
    [ -z "$CHANGED" ] && echo "  - No Lean files modified"
fi
echo "============================================"
echo ""
echo "Full Codex output: theme/out/codex_test_output.log"
echo "Checkpoint log:    $LOG"
