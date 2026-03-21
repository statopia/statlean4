#!/bin/bash
# PreToolUse hook for Agent tool.
# Checks if the current sorry has stuck_rounds >= 3.
# If so, blocks the Agent call and outputs a reminder to WebSearch first.

STUCK_FILE="/tmp/statlean_stuck_counts.txt"

# Read the agent prompt from stdin to extract the target file
INPUT=$(cat)

# Find the highest stuck count across all sorries
MAX_STUCK=0
if [ -f "$STUCK_FILE" ]; then
    while IFS=': ' read -r id count; do
        count=$(echo "$count" | tr -d ' ')
        if [ "$count" -gt "$MAX_STUCK" ] 2>/dev/null; then
            MAX_STUCK=$count
        fi
    done < "$STUCK_FILE"
fi

if [ "$MAX_STUCK" -ge 3 ]; then
    # Output JSON to block the Agent call
    cat << ENDJSON
{
  "hookSpecificOutput": {
    "hookEventName": "PreToolUse",
    "permissionDecision": "deny",
    "permissionDecisionReason": "R6 REQUIRED: stuck_rounds=$MAX_STUCK (≥3). You MUST run WebSearch before launching another agent. Run: bash scripts/agent_workflow.sh post <file> <before_sorry> to get the WebSearch commands."
  }
}
ENDJSON
else
    # Allow the Agent call
    echo '{"continue": true}'
fi
