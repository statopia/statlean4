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

## §2. (Reserved) Events JSONL Stream

**Status**: Not yet implemented. Roadmap items A1 + A2.

**Target**: Each sandbox (`Statlean/Web/<jobId>/`) will contain an
`events.jsonl` file that skill tools append structured events to.
Schema TBD, but will include at minimum:

```jsonl
{"ts": 1777000000, "kind": "step",     "id": 1, "title": "PDF Extract", "status": "start"}
{"ts": 1777000030, "kind": "step",     "id": 1, "status": "done"}
{"ts": 1777000030, "kind": "artifact", "kind_tag": "pdf-extract", "path": "extracted/paper.tex", "size": 1191}
{"ts": 1777000045, "kind": "error",    "code": "OCR_FAIL", "msg": "..."}
```

Once live this will supersede §1's header-parsing path for step-breakdown
rendering. §1 will remain as a human-readable narrative signal.

---

## §3. (Reserved) Error Code Enum

**Status**: Not yet implemented. Roadmap item A4.

**Target**: When a skill fails in a structured way the agent MUST emit

```
ERROR_CODE: <CODE>
<human-readable explanation>
```

on a line of its own (typically inside the failing step's narrative).
`<CODE>` is from a fixed enum maintained below. The web UI maps code →
friendly message via a lookup table.

Enum (initial sketch, to be finalized with A4):

- `INTEGRITY_VIOLATION` — Rule 3 statement-integrity gate rejected the proof
- `OCR_FAIL` — PDF extraction exhausted all MinerU backends
- `BUILD_TIMEOUT` — `lake build` did not finish within its budget
- `SCOPE_DECLINE` — theorem is outside what this skill can attempt
- `USER_ABORT` — user aborted via `request_user_decision`

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
