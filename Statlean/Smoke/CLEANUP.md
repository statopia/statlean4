# Slice 3.C smoke-test artifacts — DELETE WHEN SMOKE DONE

This directory + a sorry_backlog.yaml entry exist **purely** for the
slice 3.C end-to-end real-LLM smoke. None of this is production
content — delete after the smoke evidence is captured.

## What got committed during the smoke runs

The smoke fixture run completed cleanly and the agent auto-committed
the proof + finalize to `merge/newloop-import`. So the fixture is
NOT just untracked working-tree state — it's in git history. Revert
strategy is one `git revert` over a small commit range.

### Commits that introduced or extended fixture content

  | SHA | Subject | What it touches |
  |---|---|---|
  | `b78be75` | test(smoke.fixture.trivial_3way): close 3-way decomposition smoke | Statlean/Smoke/SliceFixture.lean (proof), MEMORY.md (knowledge entry) |
  | `6de18fe` | docs(prove-deep): cycle finalize for smoke.fixture.trivial_3way | sorry_backlog.yaml (synced; sub-rows removed since proved), MEMORY.md |

The earlier (pre-fixture) cov_hSub_eq_uZeta L3 run also auto-committed:

  | SHA | Subject | What it touches |
  |---|---|---|
  | `48f7017` | docs(variance.ustatistic): roadmap for cov_hSub_eq_uZeta R6 infra gap | Statlean/Variance/UStatistic.lean (R6 inline roadmap — keep if useful) |
  | `8d36bdb` | docs(prove-deep): cycle finalize for cov_hSub_eq_uZeta — memory + backlog | MEMORY.md, sorry_backlog.yaml (R6 stuck record) |

The cov_hSub_eq_uZeta commits are the agent's reflection on a real
hard sorry — separate from the fixture smoke; **decide-keep
independently**.

### Untracked working-tree artifacts

  - `Statlean/Smoke/CLEANUP.md` (this file)
  - `events.jsonl` (drop from working tree if present)
  - `Statlean/Web/smoke-3c-*/` sandbox dirs (gitignored — safe to leave)
  - `reports/prove_deep_smoke.fixture.trivial_3way.md` (gitignored
    per `prove_deep_end.py`'s convention — auto-generated final report)

## One-line cleanup

To revert ALL the smoke fixture artifacts (assuming you don't want
the fixture or the trivial_3way knowledge entry in MEMORY.md):

```bash
cd /home/gavin/statlean-merge

# 1. Revert the two fixture commits (creates new revert commits;
#    NOT --hard so you can inspect before pushing).
git revert --no-edit 6de18fe b78be75

# 2. Remove the Statlean/Smoke directory (still has CLEANUP.md +
#    SliceFixture.lean — both went into the revert above? actually
#    the revert undoes their content but the files come back IF the
#    revert decided to "delete" them, since they were CREATED by
#    these commits. Verify with `ls Statlean/Smoke/` post-revert).
ls Statlean/Smoke 2>/dev/null && rm -rf Statlean/Smoke

# 3. Sandbox dirs (gitignored, optional)
rm -rf Statlean/Web/smoke-3c-*

# 4. Verify
git status -uno
git diff --stat
```

To cherry-pick KEEP just the L3 evidence (the agent's MEMORY entry +
proof of 3-way trivial Nat facts) but drop the fixture file
specifically: that's a manual edit, not one-line. Suggest to do this
only if the trivial_3way proof is somehow useful as documentation;
otherwise full revert is cleanest.

## Why these artifacts exist

The first L3 smoke ran on `cov_hSub_eq_uZeta` (50 lines, top-level
node `parent_id: None`). Slice 3.B narrative correctly skipped retreat
for top-level nodes, and the 50-line target didn't trigger Phase 1
mandatory decomposition. So three slice 3.A/3.B paths remained
unexercised at L3:
  - `decompose_node.py` (Phase 1 path)
  - `record_retreat.py` (sub-tree retreat after stuck × 3)
  - `propagate_done.py` cascade (leaf-proved → ancestor DONE)

The fixture (`smoke.fixture.trivial_3way`) was structured to force
Phase 1 (`estimated_lines: 200 > 150`) and provide an actually-
provable 3-conjunction (each subgoal one tactic). Run 2 successfully
exercised:
  - `decompose_node.py` (3 children inserted, parent → INACTIVE_WAIT)
    — confirmed via `subtasks-split` event with `sub_problem_ids:
    [smoke.fixture.trivial_3way.{sub1,sub2,sub3}]`
  - `process_sorry_result --status proved` for each sub-leaf
    (confirmed: 3× `sorry-proved` events with sorry_id matching subs)
  - `propagate_done.py` cascade — confirmed `dag-cycle-done` event with
    `root_id: smoke.fixture.trivial_3way, ancestors_promoted:
    [smoke.fixture.trivial_3way]`

It does NOT cover `record_retreat.py` (the sub-leaves were too
trivial to fail 3 times). Retreat coverage is exhaustive at L1 + L2
(`theme/scripts/tests/test_record_retreat.py`,
`test_slice_3_integration.py`) and at L3 indirectly via
`subagent-stuck` + `stuck_rounds` bump on the cov_hSub_eq_uZeta run.
