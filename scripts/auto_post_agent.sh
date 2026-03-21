#!/bin/bash
# PostToolUse hook for Agent tool.
# Automatically checks sorry count change and increments stuck if unchanged.
# No manual intervention needed.

STUCK_FILE="/tmp/statlean_stuck_counts.txt"

# Extract tool_use_id to find the matching per-agent before-state file
INPUT=$(cat)
TOOL_USE_ID=$(echo "$INPUT" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    print(d.get('tool_use_id', 'unknown'))
except: print('unknown')
" 2>/dev/null)
BEFORE_FILE="/tmp/statlean_sorry_before_${TOOL_USE_ID}.txt"

# Read saved "before" state (per-agent, no race condition)
if [ ! -f "$BEFORE_FILE" ]; then
    exit 0  # No before state, skip
fi

FILE=$(head -1 "$BEFORE_FILE" 2>/dev/null)
BEFORE=$(tail -1 "$BEFORE_FILE" 2>/dev/null)
SORRY_ID=$(basename "$FILE" .lean 2>/dev/null)

if [ -z "$FILE" ] || [ -z "$BEFORE" ]; then
    exit 0
fi

# Count current sorry
AFTER=$(grep -c ' sorry$' "$FILE" 2>/dev/null || echo "?")

if [ "$AFTER" -lt "$BEFORE" ] 2>/dev/null; then
    # Sorry reduced — reset stuck count
    touch "$STUCK_FILE"
    if grep -q "^${SORRY_ID}:" "$STUCK_FILE" 2>/dev/null; then
        sed -i "s/^${SORRY_ID}:.*/${SORRY_ID}: 0/" "$STUCK_FILE"
    fi
    MSG="✅ Agent reduced sorry: $BEFORE → $AFTER. Stuck count reset."
else
    # Sorry NOT reduced — increment stuck
    touch "$STUCK_FILE"
    STUCK=$(grep "^${SORRY_ID}:" "$STUCK_FILE" 2>/dev/null | cut -d: -f2 | tr -d ' ')
    STUCK=${STUCK:-0}
    NEW=$((STUCK + 1))
    if grep -q "^${SORRY_ID}:" "$STUCK_FILE" 2>/dev/null; then
        sed -i "s/^${SORRY_ID}:.*/${SORRY_ID}: ${NEW}/" "$STUCK_FILE"
    else
        echo "${SORRY_ID}: ${NEW}" >> "$STUCK_FILE"
    fi
    MSG="❌ Agent did NOT reduce sorry ($BEFORE → $AFTER). stuck_rounds: $STUCK → $NEW."
    if [ "$NEW" -ge 3 ]; then
        MSG="$MSG R6 REQUIRED: WebSearch before next agent."
    fi
fi

# Clean up before file
rm -f "$BEFORE_FILE"

# Output message to Claude
cat << ENDJSON
{
  "hookSpecificOutput": {
    "hookEventName": "PostToolUse",
    "additionalContext": "$MSG"
  }
}
ENDJSON
