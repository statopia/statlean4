---
description: Deep prove mode — attack a sorry with full infrastructure building, sub-lemma extraction, and parallel agents
allowed-tools: Read, Edit, Write, Grep, Glob, Bash(lake:*), Bash(grep:*), Bash(echo:*), Task, WebSearch, WebFetch
model: opus
argument-hint: [sorry-id from backlog, or "next" for highest priority, or "all-leaves"]
---

# Deep Prove Mode

Target: $ARGUMENTS

**Time budget: UNLIMITED.** This mode may run for hours. Do not give up after 3 rounds.
The shallow `/prove` has a 3-round budget. `/prove-deep` does NOT — keep going until
the proof is complete or you've exhausted all viable strategies.

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
- **Agent B**: Deep Mathlib search — first check `theme/mathlib_api_index.md` (level 1),
  then `#check`/`exact?` (level 2), then grep Mathlib source (level 3).
  Search ACROSS namespaces — not just Probability, but also Topology, Metric, Filter,
  Order, Analysis as needed by the proof strategy.
- **Agent C**: Read project MEMORY.md + similar proved lemmas for reusable patterns.

Wait for all agents. Synthesize findings into a strategy.

## Phase 2: Sub-Lemma Extraction

Analyze the sorry and decompose it into independently provable sub-lemmas:
1. Create ALL sub-lemma declarations with `sorry` in the target file.
2. Each sub-lemma gets a structured docstring with proof sketch and API hints.
3. Rewrite the main theorem to use the sub-lemmas (the main theorem body should
   have NO sorry — only the sub-lemmas have sorry).
4. Build to verify the extraction compiles.
5. Now each sub-lemma is independently attackable.

## Phase 3: Prove (depth-first, leaf-first)

For each sub-lemma (sorted by difficulty: leaf → intermediate → hard):
1. Attempt proof using Mathlib API found in Phase 1.
2. Build after each proof (incremental: `lake build Statlean.<Module>`).
3. If stuck after 5 cycles on one sub-lemma:
   - Try a DIFFERENT proof strategy (not just retry the same approach).
   - Search for alternative Mathlib API in adjacent namespaces.
   - If infrastructure can be built in ≤100 lines → build it.
   - Only after exhausting alternatives → leave honest sorry with structured comment.
4. Report progress after each sub-lemma.

## Phase 3.5: Infrastructure Extraction (MANDATORY)

After Phase 3, BEFORE attempting assembly:
1. Identify all proved sub-lemmas and new definitions that are **independent of
   remaining sorry**.
2. Move these into a `<Module>Proved.lean` companion file (zero sorry).
3. Register the Proved file in `Statlean/Verified.lean`.
4. Build `lake build Statlean.Verified` to confirm zero sorry pollution.
5. The sorry-bearing main theorem imports from the Proved file.

This ensures that even partial progress is captured in the project.

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
     Infrastructure: [new definitions/lemmas added to Statlean]
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

## Acceleration Rules

1. **Index first**: ALWAYS read `theme/mathlib_api_index.md` before any grep/`#check`.
   If the API is in the index, use it directly (0 cost).
2. **Incremental build**: `lake build Statlean.<Module>` not `lake build` (saves minutes).
3. **Parallel search**: When searching for 3+ APIs, spawn parallel haiku agents.
4. **No redundant search**: If a subagent already searched, trust its results.
5. **Cache proof patterns**: When a proof technique works, record it in MEMORY.md
   for future sessions.

## Key Context

- Project: `/home/gavin/statlean`
- Build: `lake build <module>` or `lake build` (full)
- Backlog: `theme/input/sorry_backlog.yaml`
- Memory: `.claude/projects/-home-gavin-statlean/memory/MEMORY.md`
- Mathlib index: `theme/mathlib_api_index.md`
- Proved patterns: See MEMORY.md "Key Lean/Mathlib Patterns Learned"
