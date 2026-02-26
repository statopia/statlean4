---
description: Resume research from memory, rebuild context fast
allowed-tools: Read, Grep, Glob, Bash(lake:*), Bash(git:*), Bash(grep:*), Bash(wc:*)
model: sonnet
---

# Resume Session

Quickly rebuild working context for this formalization project. Run these in parallel:

## 1. Read project memory
- Read `/home/gavin/.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Read any other files in that memory directory

## 2. Check current state
- `git log --oneline -10` — recent work
- `git diff --stat` — uncommitted changes
- `git status` — working tree state

## 3. Sorry scan
- `grep -rn "sorry" Statlean/ --include="*.lean" | grep -v "^.*:.*--.*sorry" | grep -v AutoPromoted | wc -l` — sorry count
- Quick categorization of sorry locations

## 4. Build health
- `lake build 2>&1 | tail -20` — does it compile?

## 5. Synthesize
Based on all the above, report:
- What was last worked on
- Current sorry count and distribution
- Build status (clean or broken)
- Suggested next action based on project roadmap

If there are arguments, focus on that specific area:
$ARGUMENTS
