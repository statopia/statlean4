#!/bin/bash
# PostToolUse hook for Agent tool.
# Automatically checks sorry count change and increments stuck if unchanged.
# No manual intervention needed.
#
# Background-agent skip: PostToolUse fires when the Agent tool *returns*,
# which for `run_in_background: true` is immediately at dispatch — long
# before the agent has done any work. Counting sorry at that moment always
# reports "no change" and falsely increments stuck_rounds. We detect the
# background flag from the tool input and exit 0 silently. The actual
# completion arrives later as a `task-notification` event (which is not a
# tool call and therefore not handled by PostToolUse hooks at all).

STUCK_FILE="/tmp/statlean_stuck_counts.txt"

# Extract tool_use_id and check if the agent was launched in background.
INPUT=$(cat)
read TOOL_USE_ID IS_BACKGROUND <<< $(echo "$INPUT" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    print(d.get('tool_use_id', 'unknown'),
          'true' if d.get('tool_input', {}).get('run_in_background') else 'false')
except:
    print('unknown false')
" 2>/dev/null)
BEFORE_FILE="/tmp/statlean_sorry_before_${TOOL_USE_ID}.txt"

# Background agents: clean up the before-state file (it'd dangle otherwise)
# and skip the sorry-count check. Caller is responsible for inspecting
# results when the task-notification arrives.
if [ "$IS_BACKGROUND" = "true" ]; then
    rm -f "$BEFORE_FILE"
    exit 0
fi

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
