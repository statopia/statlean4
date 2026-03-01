#!/usr/bin/env bash
# Incremental single-declaration type-checking via lean --stdin.
#
# Usage:
#   scripts/check_snippet.sh Statlean/Gaussian/Poincare.lean 120 180
#   scripts/check_snippet.sh Statlean/Gaussian/Poincare.lean  # whole file
#   echo 'theorem foo : 1 + 1 = 2 := by norm_num' | scripts/check_snippet.sh --stdin Statlean/Gaussian/Poincare.lean
#
# Arguments:
#   $1 - Source .lean file (for extracting imports)
#   $2 - Start line (optional, default: extract imports + all content)
#   $3 - End line (optional, default: EOF from start)
#   --stdin: read snippet from stdin instead of file lines
#
# The script:
#   1. Extracts all `import` lines from the source file
#   2. Extracts the declaration at the given line range (or from stdin)
#   3. Pipes the combined snippet to `lake env lean --stdin`
#   4. Returns only error output (exit code propagated)

set -euo pipefail

PROJ_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJ_ROOT"

USE_STDIN=false
if [[ "${1:-}" == "--stdin" ]]; then
    USE_STDIN=true
    shift
fi

FILE="${1:?Usage: check_snippet.sh [--stdin] FILE [START_LINE] [END_LINE]}"
START="${2:-}"
END="${3:-}"

if [[ ! -f "$FILE" ]]; then
    echo "ERROR: File not found: $FILE" >&2
    exit 1
fi

# Extract imports from the file
IMPORTS=$(grep -n '^import ' "$FILE" | sed 's/^[0-9]*://')

# Extract open statements (needed for namespace resolution)
OPENS=$(grep -n '^open ' "$FILE" | sed 's/^[0-9]*://')

# Build the snippet
SNIPPET="$IMPORTS"$'\n'"$OPENS"$'\n'

if $USE_STDIN; then
    SNIPPET+=$(cat)
elif [[ -n "$START" ]]; then
    if [[ -z "$END" ]]; then
        # Auto-detect end: find next declaration or end of file
        TOTAL=$(wc -l < "$FILE")
        END=$TOTAL
    fi
    SNIPPET+=$(sed -n "${START},${END}p" "$FILE")
else
    # No line range: just compile the whole file (but faster via stdin)
    SNIPPET=$(cat "$FILE")
fi

# Run through lean
echo "$SNIPPET" | lake env lean --stdin --threads=4 2>&1
