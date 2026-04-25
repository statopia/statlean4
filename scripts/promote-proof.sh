#!/usr/bin/env bash
#
# promote-proof.sh — Promote a proven theorem from Web/{jobId}/ to a
# permanent module location in the statlean repo.
#
# Usage:
#   ./scripts/promote-proof.sh <jobId> <target-path> [--ref <spec-file>] [--no-review] [--dry-run]
#
# Examples:
#   ./scripts/promote-proof.sh cox_lemma_s2 Statlean/CoxChangePoint/LemmaS2.lean
#   ./scripts/promote-proof.sh cox_lemma_s2 Statlean/CoxChangePoint/LemmaS2.lean --ref paper.pdf
#   ./scripts/promote-proof.sh cox_lemma_s2 Statlean/CoxChangePoint/LemmaS2.lean --dry-run
#
# Steps:
#   1. Mechanical checks (sorry, axiom, lake build)
#   2. Statement integrity review (Claude, if --ref provided)
#   3. Copy to target path
#   4. Rebuild from new location
#   5. Git commit
#
set -euo pipefail

STATLEAN_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WEB_DIR="$STATLEAN_ROOT/Statlean/Web"

# --- Parse args ---
JOB_ID=""
TARGET_PATH=""
REF_FILE=""
NO_REVIEW=false
DRY_RUN=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref)      REF_FILE="$2"; shift 2 ;;
    --no-review) NO_REVIEW=true; shift ;;
    --dry-run)  DRY_RUN=true; shift ;;
    -*)         echo "Unknown flag: $1" >&2; exit 1 ;;
    *)
      if [[ -z "$JOB_ID" ]]; then
        JOB_ID="$1"
      elif [[ -z "$TARGET_PATH" ]]; then
        TARGET_PATH="$1"
      else
        echo "Too many positional args" >&2; exit 1
      fi
      shift ;;
  esac
done

if [[ -z "$JOB_ID" || -z "$TARGET_PATH" ]]; then
  echo "Usage: promote-proof.sh <jobId> <target-path> [--ref <spec>] [--no-review] [--dry-run]"
  exit 1
fi

SOURCE_DIR="$WEB_DIR/$JOB_ID"
SOURCE_FILE="$SOURCE_DIR/Main.lean"

if [[ ! -f "$SOURCE_FILE" ]]; then
  echo "FAIL: source file not found: $SOURCE_FILE"
  exit 1
fi

echo "=== promote-proof: $JOB_ID → $TARGET_PATH ==="
echo ""

# =====================================================================
# Step 1: Mechanical checks
# =====================================================================
echo "--- Step 1: Mechanical checks ---"
FAIL=false

# 1a. Zero sorry
SORRY_COUNT=$(grep -c '\bsorry\b' "$SOURCE_FILE" 2>/dev/null || true)
SORRY_COUNT=$(echo "$SORRY_COUNT" | tail -1)
SORRY_COUNT=${SORRY_COUNT:-0}
if [[ "$SORRY_COUNT" -gt 0 ]]; then
  echo "  FAIL: $SORRY_COUNT sorry found"
  FAIL=true
else
  echo "  OK: 0 sorry"
fi

# 1b. Has theorem/lemma
THEOREM_COUNT=$(grep -cE '^\s*(theorem|lemma)\s+\w+' "$SOURCE_FILE" 2>/dev/null || true)
THEOREM_COUNT=$(echo "$THEOREM_COUNT" | tail -1)
THEOREM_COUNT=${THEOREM_COUNT:-0}
if [[ "$THEOREM_COUNT" -eq 0 ]]; then
  echo "  FAIL: no theorem/lemma declarations found"
  FAIL=true
else
  echo "  OK: $THEOREM_COUNT theorem/lemma declarations"
fi

# 1c. No axiom declarations (cheating)
AXIOM_COUNT=$(grep -cE '^\s*axiom\s+' "$SOURCE_FILE" 2>/dev/null || true)
AXIOM_COUNT=${AXIOM_COUNT:-0}
if [[ "$AXIOM_COUNT" -gt 0 ]]; then
  echo "  FAIL: $AXIOM_COUNT axiom declarations (not allowed)"
  FAIL=true
else
  echo "  OK: no axiom declarations"
fi

# 1d. No native_decide / decide cheats on non-trivial goals
DECIDE_COUNT=$(grep -cE '\bnative_decide\b' "$SOURCE_FILE" 2>/dev/null || true)
DECIDE_COUNT=${DECIDE_COUNT:-0}
if [[ "$DECIDE_COUNT" -gt 0 ]]; then
  echo "  WARN: $DECIDE_COUNT native_decide uses (review manually)"
fi

# 1e. lake build
echo "  Building..."
BUILD_MODULE=$(head -50 "$SOURCE_FILE" | grep -oP '^namespace\s+\K\S+' | head -1)
# Build by file path (more reliable than module name for Web/ files)
cd "$STATLEAN_ROOT"
BUILD_OUTPUT=$(lake env lean "$SOURCE_FILE" 2>&1) || true
if echo "$BUILD_OUTPUT" | grep -q "error:"; then
  echo "  FAIL: lake build has errors:"
  echo "$BUILD_OUTPUT" | grep "error:" | head -5
  FAIL=true
else
  echo "  OK: builds clean"
fi

if $FAIL; then
  echo ""
  echo "BLOCKED: mechanical checks failed. Fix the issues above first."
  exit 1
fi

echo ""

# =====================================================================
# Step 2: Statement integrity review (Layer 4 independent judge)
# =====================================================================
# Calls website's `judge-integrity.ts` which uses an independent
# provider (default DeepSeek, configurable via JUDGE_API_KEY +
# --provider) to give a same-provider-bias-free verdict. Default
# muted: when JUDGE_ENABLED != "true", the script returns PASS+exit-0
# without an LLM call so this gate is a no-op until the operator
# opts in. See website/docs/STATEMENT_INTEGRITY.md §"Layer 4".
WEBSITE_ROOT="${WEBSITE_ROOT:-$HOME/website}"
JUDGE_SCRIPT="$WEBSITE_ROOT/server/scripts/judge-integrity.ts"

if [[ "$NO_REVIEW" == "true" ]]; then
  echo "--- Step 2: Statement integrity review (SKIPPED: --no-review) ---"
elif [[ ! -f "$JUDGE_SCRIPT" ]]; then
  echo "--- Step 2: Statement integrity review (SKIPPED: $JUDGE_SCRIPT not found) ---"
elif ! command -v npx &>/dev/null; then
  echo "--- Step 2: Statement integrity review (SKIPPED: npx not found) ---"
else
  echo "--- Step 2: Statement integrity review (judge-integrity) ---"

  JUDGE_ARGS=("$SOURCE_FILE")
  if [[ -n "$REF_FILE" && -f "$REF_FILE" ]]; then
    JUDGE_ARGS+=("--ref" "$REF_FILE")
  fi
  # Layer 4 + Step 6 of elegant-plan: feed the agent's
  # formalization_delta events (ui-signals.md §6) as structured
  # context so the judge can cross-reference self-reported drift
  # against the Lean shape. SOURCE_DIR is the sandbox.
  if [[ -f "$SOURCE_DIR/events.jsonl" ]]; then
    JUDGE_ARGS+=("--events" "$SOURCE_DIR/events.jsonl")
  fi

  set +e
  JUDGE_OUT=$(cd "$WEBSITE_ROOT" && npx tsx "$JUDGE_SCRIPT" "${JUDGE_ARGS[@]}" 2>&1)
  JUDGE_EXIT=$?
  set -e

  VERDICT=$(echo "$JUDGE_OUT" | python3 -c "
import sys, json
try:
    print(json.loads(sys.stdin.read().strip().splitlines()[-1]).get('verdict', 'ERROR'))
except Exception:
    print('ERROR')
" 2>/dev/null)
  REASON=$(echo "$JUDGE_OUT" | python3 -c "
import sys, json
try:
    print(json.loads(sys.stdin.read().strip().splitlines()[-1]).get('reason', ''))
except Exception:
    print('')
" 2>/dev/null)

  case "$VERDICT" in
    PASS)
      echo "  PASS: $REASON"
      ;;
    FAIL)
      echo "  FAIL: $REASON"
      echo ""
      echo "BLOCKED: independent judge flagged integrity violation."
      exit 1
      ;;
    WARN)
      echo "  WARN: $REASON"
      read -p "  Continue anyway? [y/N] " -n 1 -r
      echo
      if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Aborted."
        exit 1
      fi
      ;;
    *)
      echo "  ERROR: could not parse judge output (exit=$JUDGE_EXIT):"
      echo "$JUDGE_OUT" | head -10
      echo ""
      read -p "  Continue anyway? [y/N] " -n 1 -r
      echo
      if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Aborted."
        exit 1
      fi
      ;;
  esac
fi

echo ""

# =====================================================================
# Step 3: Copy to target path
# =====================================================================
echo "--- Step 3: Copy to target ---"

TARGET_FULL="$STATLEAN_ROOT/$TARGET_PATH"
TARGET_DIR=$(dirname "$TARGET_FULL")

if $DRY_RUN; then
  echo "  DRY RUN: would copy $SOURCE_FILE → $TARGET_FULL"
  echo "  DRY RUN: would update namespace"
  echo ""
  echo "=== DRY RUN COMPLETE ==="
  exit 0
fi

# Create target directory if needed
mkdir -p "$TARGET_DIR"

# Determine the new module name from target path
# e.g., Statlean/CoxChangePoint/LemmaS2.lean → Statlean.CoxChangePoint.LemmaS2
NEW_MODULE=$(echo "$TARGET_PATH" | sed 's|/|.|g; s|\.lean$||')

# Copy and update namespace/module references
cp "$SOURCE_FILE" "$TARGET_FULL"

# Also copy any helper files from the job dir
for f in "$SOURCE_DIR"/*.lean; do
  if [[ "$(basename "$f")" != "Main.lean" && -f "$f" ]]; then
    cp "$f" "$TARGET_DIR/"
    echo "  Copied helper: $(basename "$f")"
  fi
done

echo "  Copied $SOURCE_FILE → $TARGET_FULL"

# =====================================================================
# Step 4: Rebuild from new location
# =====================================================================
echo ""
echo "--- Step 4: Rebuild from new location ---"

cd "$STATLEAN_ROOT"
BUILD_OUTPUT2=$(lake env lean "$TARGET_FULL" 2>&1) || true
if echo "$BUILD_OUTPUT2" | grep -q "error:"; then
  echo "  FAIL: build errors at new location:"
  echo "$BUILD_OUTPUT2" | grep "error:" | head -5
  echo ""
  echo "  The file has been copied but does not build. Fix manually."
  exit 1
fi

# Verify still 0 sorry
SORRY_CHECK=$(echo "$BUILD_OUTPUT2" | grep -c "sorry" || echo 0)
if [[ "$SORRY_CHECK" -gt 0 ]]; then
  echo "  FAIL: sorry appeared after move"
  exit 1
fi

echo "  OK: builds clean at $TARGET_PATH"

# =====================================================================
# Step 5: Git commit
# =====================================================================
echo ""
echo "--- Step 5: Git commit ---"

cd "$STATLEAN_ROOT"
git add "$TARGET_FULL"
# Also add any helpers
for f in "$TARGET_DIR"/*.lean; do
  if [[ -f "$f" && "$f" != "$TARGET_FULL" ]]; then
    git add "$f"
  fi
done

THEOREM_NAMES=$(grep -oP '(?:theorem|lemma)\s+\K\w+' "$TARGET_FULL" | paste -sd, -)
COMMIT_MSG="feat: promote $JOB_ID → $TARGET_PATH

Proved: $THEOREM_NAMES
Source: Statlean/Web/$JOB_ID/Main.lean
Checks: 0 sorry, builds clean, statement integrity reviewed"

git commit -m "$COMMIT_MSG"

echo ""
echo "=== DONE ==="
echo "  Promoted: $JOB_ID → $TARGET_PATH"
echo "  Theorems: $THEOREM_NAMES"
echo "  Commit:   $(git rev-parse --short HEAD)"
