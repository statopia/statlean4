# Demo Preparation Notes

## Before the Talk

1. **Warm build**: Run `lake build` once so incremental builds are fast
2. **Open files**: VS Code with `Statlean/LimitTheorems/CLT.lean` ready
3. **Terminal**: Have a terminal in project root ready

## Demo 1: Compilation (~1 min, with Slide 3)

```bash
lake build Statlean.Verified
```

- Should produce zero sorry warnings
- If slow, use pre-recorded backup

## Demo 2: CLT Proof Walkthrough (~2 min, with Slide 9)

- Open `Statlean/LimitTheorems/CLT.lean` in VS Code
- Walk through `central_limit_theorem` (line 46-98)
- Highlight 3 steps:
  1. `charfun_normalized_sum_bound` (Taylor bound)
  2. `squeeze_zero` + `tendsto_sub_nhds_zero_iff` (pointwise convergence)
  3. `levy_continuity` (final step)
- Hover to show Lean InfoView goal state

## Demo 3: Claude Code Workflow (~2 min, with Slide 8)

- Show sorry_backlog.yaml structure
- Show `/prove` command attacking a sorry
- Highlight: API search → tactic generation → lake build verify

## Risk Mitigation

- Pre-record all demos as backup (asciinema)
- Keep demos short: 1-2 min each, total ~5 min
- Test everything 30 min before talk
