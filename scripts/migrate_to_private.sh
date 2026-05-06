#!/usr/bin/env bash
# migrate_to_private.sh — switch a STATLEAN_ROOT clone from the public repo
# (statopia/statlean4) to the private companion (statopia/statlean4-private).
#
# Run this ONCE on every machine that has a local statlean clone used by
# prover (developer laptops + production server). Idempotent: safe to re-run.
#
# Usage:
#   STATLEAN_ROOT=/srv/statlean bash migrate_to_private.sh
#   # or, if STATLEAN_ROOT is already in your env / .env:
#   bash migrate_to_private.sh
#   # or pass the path:
#   bash migrate_to_private.sh /path/to/local/statlean
#
# What it does:
#   1. Sanity checks (path exists, is a git repo, working tree clean)
#   2. Switches origin URL to statopia/statlean4-private (SSH by default)
#   3. Fetches private main; resets local main to private/main if histories
#      diverged because of the public-side slim commit
#   4. Verifies the critical files prover expects are present
#
# Exit codes: 0 = success / already-migrated, 1+ = failure (each step prints
# a hint about what to fix)
#
# Prereq: the GitHub account associated with this machine's SSH key (or
# git credential helper for HTTPS) must have accepted the collaborator
# invitation to statopia/statlean4-private.

set -euo pipefail

OLD_URLS=(
  "git@github.com:statopia/statlean4.git"
  "https://github.com/statopia/statlean4.git"
  "git@github.com:mockingbird-gan/statlean4.git"
  "https://github.com/mockingbird-gan/statlean4.git"
)
NEW_SSH_URL="git@github.com:statopia/statlean4-private.git"
NEW_HTTPS_URL="https://github.com/statopia/statlean4-private.git"

CRITICAL_FILES=(
  "theme/proof_knowledge.yaml"
  "theme/prove_playbook.md"
  "theme/formalize_playbook.md"
  "theme/sorry_grading.md"
  "theme/shao_reference_guide.md"
  "theme/api_gotchas.tsv"
  "theme/statlean_api_index.tsv"
  "theme/scripts/sync_sorry_backlog.py"
  ".claude/commands/prove-deep.md"
)

ROOT="${1:-${STATLEAN_ROOT:-}}"
if [ -z "$ROOT" ]; then
  echo "ERROR: pass STATLEAN_ROOT as first arg or export it"
  echo "  example: STATLEAN_ROOT=/srv/statlean bash $0"
  exit 1
fi
ROOT="$(cd "$ROOT" 2>/dev/null && pwd || echo "$ROOT")"
if [ ! -d "$ROOT/.git" ]; then
  echo "ERROR: $ROOT is not a git repo"
  exit 1
fi

cd "$ROOT"
echo "=== migrating statlean clone at $ROOT ==="

# --- 0. dirty tree check -----------------------------------------------------
if [ -n "$(git status --porcelain)" ]; then
  echo "ERROR: working tree has uncommitted changes:"
  git status --short
  echo ""
  echo "Commit or stash them first, then re-run this script."
  exit 2
fi

# --- 1. inspect current remote ----------------------------------------------
CURRENT_URL="$(git remote get-url origin 2>/dev/null || echo '')"
echo "current origin: $CURRENT_URL"

# --- 2. switch URL if needed ------------------------------------------------
if [ "$CURRENT_URL" = "$NEW_SSH_URL" ] || [ "$CURRENT_URL" = "$NEW_HTTPS_URL" ]; then
  echo "  -> already pointing at private repo, skipping URL switch"
else
  KNOWN=0
  for u in "${OLD_URLS[@]}"; do
    if [ "$CURRENT_URL" = "$u" ]; then KNOWN=1; break; fi
  done
  if [ $KNOWN -eq 0 ]; then
    echo "WARN: origin is not a known statlean URL. Continuing anyway."
  fi

  # Pick SSH or HTTPS based on the existing URL's protocol
  if echo "$CURRENT_URL" | grep -q '^https://'; then
    TARGET="$NEW_HTTPS_URL"
  else
    TARGET="$NEW_SSH_URL"
  fi
  echo "  -> setting origin to $TARGET"
  git remote set-url origin "$TARGET"
fi

# --- 3. fetch + reconcile ---------------------------------------------------
echo "fetching private main..."
git fetch origin main

LOCAL_HEAD="$(git rev-parse HEAD)"
REMOTE_HEAD="$(git rev-parse origin/main)"
MERGE_BASE="$(git merge-base HEAD origin/main || echo '')"

if [ "$LOCAL_HEAD" = "$REMOTE_HEAD" ]; then
  echo "  -> already at origin/main"
elif [ "$MERGE_BASE" = "$LOCAL_HEAD" ]; then
  echo "  -> fast-forward to origin/main"
  git pull --ff-only origin main
elif [ "$MERGE_BASE" = "$REMOTE_HEAD" ]; then
  echo "WARN: local has commits not in origin/main; refusing to discard."
  echo "      run \`git log origin/main..HEAD\` to inspect; resolve manually."
  exit 3
else
  echo "  -> divergent history (likely picked up the public slim commit)."
  echo "     resetting local main to origin/main (private)."
  git reset --hard origin/main
fi

# --- 4. verify critical files ------------------------------------------------
echo "verifying prover-critical files..."
MISSING=()
for f in "${CRITICAL_FILES[@]}"; do
  [ -e "$f" ] || MISSING+=("$f")
done
if [ ${#MISSING[@]} -gt 0 ]; then
  echo "ERROR: still missing files after pull:"
  printf '  %s\n' "${MISSING[@]}"
  echo ""
  echo "Possible causes:"
  echo "  - You haven't accepted the invitation at"
  echo "    https://github.com/statopia/statlean4-private/invitations"
  echo "  - The GitHub account associated with your SSH key / credential is"
  echo "    not a collaborator on statopia/statlean4-private."
  echo "  - HTTPS PAT lacks 'repo' scope for private repos."
  exit 4
fi

# --- 5. summary --------------------------------------------------------------
echo ""
echo "=== migration complete ==="
echo "origin    : $(git remote get-url origin)"
echo "HEAD      : $(git rev-parse --short HEAD)  $(git log -1 --pretty=%s)"
echo ""
echo "next step: if a prover server runs against \$STATLEAN_ROOT and writes"
echo "back (promoteToStatlib / statleanCommit), make sure that machine's"
echo "credentials have PUSH access to statopia/statlean4-private (deploy"
echo "key with 'Allow write access', or PAT with 'repo' scope)."
