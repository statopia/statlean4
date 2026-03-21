#!/bin/bash
# PreToolUse hook for Agent tool.
# Checks if the current sorry has stuck_rounds >= 3.
# If so, blocks the Agent call and outputs a reminder to WebSearch first.

STUCK_FILE="/tmp/statlean_stuck_counts.txt"

# Read the agent prompt from stdin to extract the target file and tool_use_id
INPUT=$(cat)

# Extract tool_use_id for per-agent state isolation (fixes parallel race condition)
TOOL_USE_ID=$(echo "$INPUT" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    print(d.get('tool_use_id', 'unknown'))
except: print('unknown')
" 2>/dev/null)
BEFORE_FILE="/tmp/statlean_sorry_before_${TOOL_USE_ID}.txt"

# Try to extract the .lean file from the agent prompt
LEAN_FILE=$(echo "$INPUT" | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    prompt = d.get('tool_input', {}).get('prompt', '')
    import re
    m = re.search(r'(Statlean/[A-Za-z/]+\.lean)', prompt)
    if m: print(m.group(1))
except: pass
" 2>/dev/null)

# Save before-state for PostToolUse hook (per-agent file, no race condition)
if [ -n "$LEAN_FILE" ] && [ -f "$LEAN_FILE" ]; then
    SORRY_BEFORE=$(grep -c ' sorry$' "$LEAN_FILE" 2>/dev/null || echo 0)
    echo "$LEAN_FILE" > "$BEFORE_FILE"
    echo "$SORRY_BEFORE" >> "$BEFORE_FILE"
fi

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
