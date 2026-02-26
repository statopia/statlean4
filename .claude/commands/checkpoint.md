---
description: Save progress to memory and optionally commit
allowed-tools: Read, Write, Edit, Bash(git:*), Bash(grep:*), Bash(wc:*), Grep, Glob
argument-hint: [commit-message]
---

# Checkpoint Progress

Save current session progress so it survives conversation interruptions.

## Step 1: Capture state
- Count current sorrys: `grep -rn "sorry" Statlean/ --include="*.lean" | grep -v "^.*:.*--.*sorry" | grep -v AutoPromoted`
- Check build status: does `lake build` pass?
- Identify what changed this session via `git diff --stat`

## Step 2: Update memory
Read and update `/home/gavin/.claude/projects/-home-gavin-statlean/memory/MEMORY.md`:
- Update sorry count and which ones were resolved
- Record any new Mathlib API discoveries (patterns, lemma names, gotchas)
- Update "Completed" section if any sorry was fully proved
- Update "Key Lean/Mathlib Patterns Learned" if new patterns found
- Keep MEMORY.md under 200 lines

## Step 3: Commit (if message provided)
If `$ARGUMENTS` is non-empty:
- Stage changed `.lean` files (not docs or scripts unless relevant)
- Commit with the provided message
- Do NOT push unless explicitly asked

## Step 4: Report
Summarize what was saved and what the next session should focus on.
