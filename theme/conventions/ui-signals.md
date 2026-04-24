# UI-Signals: Output Conventions for Agents in `statlean` Skills

**Audience**: Authors of `.claude/commands/*.md` skill specs AND the
Claude agent executing them. This file is the single source of truth
for every piece of structured output that downstream consumers
(primarily the `statlean-web` UI, secondarily the CLI user) depend on.

**Why this file exists**: `statlean-web` observes the agent's narrative
+ tool calls + sandbox artifacts and projects them into UI elements
(step-breakdown cards, the report stream, progress indicators,
sorry counts, error banners). For the projection to be stable, the
agent MUST emit certain things in exact shapes — not as suggestions,
but as contracts. A deviation makes the UI silently mis-render, not
loud-fail. That's why every convention below is MUST, not SHOULD.

If you are an agent reading this mid-session: treat every "MUST" below
as binding, the same way you treat "do not modify the locked theorem
signature" in Rule 3. A tool-result may remind you of the formats by
example; those examples are canonical.

The contract registry in `website/docs/CLI_WEB_CONFORMANCE.md` lists
every consumer of each convention (file:line). If you add or change a
convention here, also update that registry or the web UI will drift.

---

## §1. Step Header Format (for the report narrative)

Each major step in a skill's flow MUST be announced with a Markdown
header line of exactly this shape:

```
## Step N: <short title>
```

- Zero leading whitespace.
- Exactly `## ` (two hashes + one space) at the start.
- The literal word `Step`, one space, an integer N, a colon, one space.
- `<short title>` is free text on the same line (no newline before it).

A subsequent step announcement with the same N is allowed only for
retries/sub-phases, and MUST disambiguate by title (e.g.
`## Step 4: Build & Fix (attempt 2)`). Using the same N + same title
twice is a contract violation — the web UI deduplicates by N and will
drop the second occurrence.

**Accepted fallback shapes** (the web parser tolerates these so that a
skill mid-migration or a legacy fixture still renders — do NOT rely on
them for new work):

- `### Step N: <title>`  (three hashes)
- `**Step N: <title>**`  (bold instead of header)
- `# Step N: <title>`    (one hash)

**Narrative content follows the header** with a blank line separator.
Anything until the next Step header is the body of that step.

**Examples (canonical)**:

```
## Step 1: PDF Extract

Running `pdf_extract.py --backend mineru --pages 8-10`.
Found Assumption (A1) on page 8.

## Step 2: LaTeX Ingest

Parsing theorems.yaml...
```

**Forbidden (contract violation)**:

- `Step 1: PDF Extract` (no header prefix — UI will treat as body text)
- `## Step1: PDF Extract` (no space after `Step`)
- `## STEP 1: PDF EXTRACT` (lowercase `Step` required)
- `## Step 1 - PDF Extract` (dash instead of colon)
- Inlining `Step N:` inside a paragraph (the shape MUST be a standalone line)

**Test fixture**: `website/src/lib/reportStepParser.test.ts` pins this
convention against live-job prose samples. Changes to the grammar above
MUST also update that fixture; otherwise `npm run test` goes red.

---

## §2. Events JSONL Stream

**Status**: ✅ infrastructure landed (roadmap A1 in progress). Skills are
being migrated to emit. Until every skill has emit calls, §1's Step
header parser continues to serve as fallback.

### Location

Each job sandbox (`<STATLEAN_ROOT>/Statlean/Web/<jobId>/`) contains one
`events.jsonl` file. Append-only, one JSON object per line, UTF-8.
Skills emit by calling `theme/scripts/emit_event.py` (see below).

### Schema

All events share `ts` (int, milliseconds since epoch) and `kind`
(enum). Remaining fields depend on kind.

#### `kind: "step"`

Announces a phase boundary. Pairs 1:1 with the Markdown Step header
in §1 (same `id` integer).

```jsonl
{"ts": 1777000000, "kind": "step", "id": 1, "title": "PDF Extract", "status": "start"}
{"ts": 1777000030, "kind": "step", "id": 1, "status": "done"}
```

- `id` (int, required): step number, matches the `N` in `## Step N:` marker.
- `title` (string, optional on `done`/`error`, REQUIRED on `start`):
  short human-readable step name.
- `status` (enum, required): `"start"` | `"done"` | `"error"`.
  `"error"` is used when the step itself failed and the web UI should
  render the card in an error state; for general agent-level errors
  use a separate `error` event (below) instead.

#### `kind: "artifact"`

Announces that a file is ready for the UI to surface.

```jsonl
{"ts": 1777000030, "kind": "artifact", "kind_tag": "pdf-extract", "path": "extracted/paper.tex", "size": 1191}
```

- `kind_tag` (enum, required): UI classifier. One of:
  `"pdf-extract"` · `"yaml"` · `"lean-skeleton"` · `"lean-live"` ·
  `"sorry-list"` · `"sub-agent-result"`.
- `path` (string, required): path **relative to the sandbox**, not
  absolute. The web UI displays this; absolute server paths would
  leak `/home/gavin/...` to the client.
- `size` (int, optional): bytes. If omitted, the emit script stats
  the path on disk.

#### `kind: "error"`

Structured error report. See §3 for the `code` enum.

```jsonl
{"ts": 1777000045, "kind": "error", "code": "OCR_FAIL", "msg": "MinerU failed on both backends"}
```

- `code` (enum, required): from the enum in §3 below.
- `msg` (string, required): human-readable detail.

### How skills emit

Use the `emit_event.py` helper. From a Bash cell:

```bash
SANDBOX=/home/gavin/statlean/Statlean/Web/$JOB_ID

# Step start
python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" step \
    --id 1 --title "PDF Extract" --status start

# Step done (same id, no --title needed)
python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" step \
    --id 1 --status done

# Artifact ready (size auto-stats from disk)
python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" artifact \
    --kind-tag pdf-extract --path extracted/paper.tex

# Structured error
python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" error \
    --code OCR_FAIL --msg "MinerU failed on both backends"
```

Behavior and guarantees:

- **Append-only atomicity**: `O_APPEND` write(2) calls with payloads
  under 4 KB (PIPE_BUF) are atomic under POSIX, so parallel sub-agents
  can emit concurrently without explicit locking.
- **Loud on misuse**: unwritable sandbox / missing sandbox / bad
  arguments → non-zero exit, stderr message. A silent malformed emit
  would show stale UI, which is worse than a visible failure.
- **Fire-and-forget cost**: each call ~20 ms (Python interpreter
  startup dominates). Don't emit in tight inner loops — once per
  step / artifact / error is the right granularity.
- **CLI-standalone safe**: if a skill emits but no web UI is
  listening, `events.jsonl` just sits in the sandbox. No harm.

### Consumer side

The web server (`server/routes/proveCli.ts`) tails `events.jsonl`
during a live job and re-emits each parsed event as an SSE `ui_event`
frame. The web UI stores them in `job.events[]` and `StepBreakdown`
renders from that when non-empty, falling back to §1's Markdown
parser when empty (legacy sessions or skills that haven't migrated).

### Migration status

Skills that have emit calls wired in:

- [ ] `pipeline.md`
- [ ] `prove.md`
- [ ] `prove-deep.md`
- [ ] `tex2lean.md`
- [ ] `build-fix.md`
- [ ] `theme/skills/pdf-extract/SKILL.md`

When all are checked, the §1 Markdown parser can be retired (current
plan is to keep it as fallback indefinitely for CLI-standalone users
who may not have emit installed).

---

## §3. Error Code Enum

**Status**: ✅ infrastructure landed (roadmap A4). Skills are being
migrated to emit structured codes; until then the web falls back to
prose-regex matching for legacy system errors.

### When to use

Two preferred paths, both accepted by the web UI's `friendlyErrorMessage`:

1. **Emit via `events.jsonl`** (preferred, machine-readable):
   ```bash
   python3 theme/scripts/emit_event.py --sandbox "$SANDBOX" \
       error --code INTEGRITY_VIOLATION --msg "theorem signature was altered at line 42"
   ```
   The web server forwards this as a `ui_event` SSE frame; JobRunner
   promotes it to `job.errorMessage` in the shape
   ```
   ERROR_CODE: INTEGRITY_VIOLATION
   theorem signature was altered at line 42
   ```

2. **Print inline in skill prose** (fallback, human-readable):
   ```
   [agent narrative explaining what failed]
   ERROR_CODE: OCR_FAIL
   MinerU failed on both hybrid and pipeline backends for this PDF.
   ```
   The same `ERROR_CODE:` prefix is picked up by `extractErrorCode` in
   `website/src/lib/errorMessages.ts`.

Either path triggers the UI's friendly-message lookup. Use path 1 when
you have a concrete sandbox; path 2 when you're aborting hard and don't
want to depend on the emit script being reachable.

### Enum

| Code | Meaning | Typical emitter |
|------|---------|-----------------|
| `INTEGRITY_VIOLATION` | Rule 3 statement-integrity gate rejected the proof (signature altered, trivialized, or wrapped) | `/prove` / `writeFile` tool / pre-promote audit |
| `LOCK_FAIL_TRIVIAL` | Skeleton is vacuous (conclusion `True`, `False` hypothesis, etc.) — pipeline bug upstream | `lock_signatures` tool / `/tex2lean` honesty check |
| `OCR_FAIL` | MinerU exhausted all backends; no usable markdown produced | `pdf_extract.py` (`run_mineru` raising SystemExit) |
| `BUILD_TIMEOUT` | `lake build` exceeded its wall budget | `/build-fix` |
| `BUILD_ERROR` | `lake build` produced errors the agent could not repair within retry budget | `/build-fix` (final give-up) |
| `SNIPPET_TIMEOUT` | `check_snippet.sh` incremental compile timed out — divergent tactic | `/prove` Phase 2 |
| `SCOPE_DECLINE` | Theorem is outside what this skill can attempt (missing Mathlib dep, statement needs redesign) | `/prove` / `/pipeline` after triage |
| `USER_ABORT` | User aborted via `request_user_decision` | whichever skill hosted the decision prompt |

Add new codes by editing this table AND
`website/src/lib/errorMessages.ts::ERROR_CODE_MESSAGES` in the same
commit. The `§13` contract registry row in
`website/docs/CLI_WEB_CONFORMANCE.md` tracks the sync.

### What NOT to use error codes for

System-level errors that originate outside skill code (provider API key
invalid, HTTP 429 rate limit, filesystem ENOENT, network outage) are
handled by the prose-regex fallback in `errorMessages.ts`. Don't force
these into the code enum — they're not skill-level and the code taxonomy
should stay compact.

---

## §4. (Reserved) Tool Call Conventions

**Status**: Not yet fleshed out.

Place to document:
- Which MCP tools exist and their exact input/output shapes
  (`request_user_decision`, `ask_user`, ...).
- Naming conventions for slash-command arguments.
- Slash-command invocation shape (currently `/pipeline <pdf> --theorem
  "..." --pages "..." --prove-depth deep`).

---

## §5. (Reserved) Sorry-List Artifact

**Status**: Not yet implemented. Roadmap item A3.

**Target**: A single `sorry_list.json` per job sandbox, written by
`/build-fix` or the lake wrapper, listing all remaining `sorry`
positions with theorem name, file, line range, and local context.
Replaces the browser-side regex scan (`parseSorriesFromLean`).

Schema TBD.

---

## Versioning

If you need to evolve a contract in a way that is not purely additive,
bump a version marker at the top of the affected section and leave the
old grammar documented for one release. The web parser can then sniff
the version and dispatch. Avoid silent breaking changes — those are
exactly what this file exists to prevent.
