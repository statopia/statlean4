---
description: Deep prove mode — attack a sorry with full infrastructure building, sub-lemma extraction, and parallel agents
allowed-tools: Read, Edit, Write, Grep, Glob, Bash(lake:*), Bash(grep:*), Task, WebSearch, WebFetch
model: opus
argument-hint: [sorry-id from backlog, or "next" for highest priority, or "all-leaves"]
---

# Deep Prove Mode

Target: $ARGUMENTS

## Phase 0: Load Backlog & Select Target

1. Read `theme/input/sorry_backlog.yaml` to get the full sorry dependency graph.
2. Select target(s) based on argument:
   - **Specific ID** (e.g., `uslln.uniform_slln`): Attack that sorry directly.
   - **`next`**: Pick the unblocked sorry with highest priority (lowest number).
   - **`all-leaves`**: Attack ALL leaf/unblocked sorries in parallel using sub-agents.
3. Verify the target is not `blocked` (all dependencies resolved). If blocked, report which dependency must be resolved first and suggest attacking that instead.

## Phase 1: Deep Research (parallel agents)

Launch parallel research agents for:
- **Agent A**: Read the sorry file + all upstream dependencies. Extract exact goal state.
- **Agent B**: Deep Mathlib search for ALL potentially relevant API (search 5+ patterns).
- **Agent C**: Read project MEMORY.md + similar proved lemmas for reusable patterns.

Wait for all agents. Synthesize findings into a strategy.

## Phase 2: Sub-Lemma Extraction

If the sorry has `sub_lemmas_needed` in the backlog:
1. Create ALL sub-lemma declarations with `sorry` in the target file.
2. Rewrite the main theorem to use the sub-lemmas.
3. Build to verify the extraction compiles.
4. Now each sub-lemma is independently attackable.

## Phase 3: Prove (depth-first, leaf-first)

For each sub-lemma (sorted by difficulty: leaf → intermediate → hard):
1. Attempt proof using Mathlib API found in Phase 1.
2. Build after each proof (max 5 cycles per sub-lemma).
3. If stuck after 3 cycles:
   - If infrastructure can be built in ≤50 lines → build it.
   - Otherwise → leave honest sorry with structured comment.
4. Report progress after each sub-lemma.

## Phase 4: Assembly

Once all leaf sub-lemmas are proved:
1. Attempt the intermediate/hard sub-lemmas that are now unblocked.
2. If the main theorem is now fully proved → verify full project build.
3. If sorry remains → update `sorry_backlog.yaml` with new state.

## Phase 5: Checkpoint

1. Commit with descriptive message.
2. Update `sorry_backlog.yaml` — remove closed items, add newly discovered gaps.
3. Update MEMORY.md with new Mathlib patterns learned.
4. Report:
   ```
   DEEP PROVE REPORT: <target>
     Duration: X min
     Sorries before: N
     Sorries after:  M
     Proved:         [list]
     New gaps:       [list]
     Backlog update: [added/removed items]
   ```

## Parallel Mode (`all-leaves`)

When target is `all-leaves`:
1. Read backlog, filter to `type: leaf` or `type: honest` with no unresolved `dependencies`.
2. For each eligible sorry, spawn an independent sub-agent (Task tool) with:
   - The file path and theorem name
   - Relevant Mathlib API hints from MEMORY.md
   - Instructions to prove and build-verify independently
3. Collect results from all agents.
4. Commit all successful proofs in one commit.
5. Update backlog.

## Key Context

- Project: `/home/gavin/statlean`
- Build: `lake build <module>` or `lake build` (full)
- Backlog: `theme/input/sorry_backlog.yaml`
- Memory: `.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Mathlib index: `theme/mathlib_stats_index.md`
- Proved patterns: See MEMORY.md "Key Lean/Mathlib Patterns Learned"
