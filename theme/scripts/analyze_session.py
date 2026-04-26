#!/usr/bin/env python3
"""analyze_session.py — post-hoc analyzer for Claude Code CLI sessions
in the statlean repo.

Reads a session transcript from
`~/.claude/projects/-home-gavin-statlean/<uuid>.jsonl` (Claude Code's
per-working-directory log of every tool_use / tool_result / message)
and prints a readable breakdown:

- Session span + duration
- Slash-command invocation (/pipeline / /prove-deep / ...)
- Tool usage histogram + Lake/check-snippet/emit/extract counters
- Files modified (Edit/Write, paths relativised to STATLEAN_ROOT)
- KB file access report (proof_knowledge.yaml, mathlib indices,
  playbook MDs, etc.) — ⚠ when a file was NOT consulted, so pipeline.md's
  "R3: 读 proof_knowledge.yaml" MUSTs are easy to audit after the fact
- Tail: top Reads, Bash commands by leading token

Usage:
    # Analyze the most recently modified transcript (default)
    python3 theme/scripts/analyze_session.py

    # A specific session by uuid
    python3 theme/scripts/analyze_session.py --uuid 591a2575-b388-4736-895e-c95faac35917

    # The session whose time window contains a git commit (handy after
    # commit + "how did that run actually behave?" postmortem)
    python3 theme/scripts/analyze_session.py --around 6534406

    # JSON form (for later automation)
    python3 theme/scripts/analyze_session.py --json

Design notes:
- stdlib only; no deps.
- STATLEAN_ROOT env (default /home/gavin/statlean) resolves both the
  repo root AND the transcript directory (Claude Code encodes cwd by
  replacing `/` with `-` under ~/.claude/projects/).
- Prove-deep in CLI-standalone mode emits no events.jsonl (per the
  prove-deep.md clause we committed in 2fd1e41), so this tool is the
  primary observability surface for CLI runs. On web-driven jobs it
  complements /api/debug/session rather than replacing it.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


KB_FILES = [
    "proof_knowledge.yaml",
    "api_gotchas.tsv",
    "mathlib_api_index.md",
    "mathlib_full_type_index.tsv",
    "statlean_api_index.tsv",
    "l0_snippets.yaml",
    "prove_playbook.md",
    "formalize_playbook.md",
    "shao_reference_guide.md",
    "sorry_grading.md",
]


def statlean_root() -> Path:
    return Path(os.environ.get("STATLEAN_ROOT") or "/home/gavin/statlean").resolve()


def transcript_dir(repo_root: Path) -> Path:
    """Claude Code encodes the working-directory path by replacing `/` with
    `-`, then stores transcripts under `~/.claude/projects/<encoded>/`."""
    encoded = str(repo_root).replace("/", "-")
    return Path.home() / ".claude" / "projects" / encoded


@dataclass
class SessionStats:
    uuid: str = ""
    path: Path = Path("")
    first_ts: Optional[datetime] = None
    last_ts: Optional[datetime] = None
    event_types: Counter = field(default_factory=Counter)
    tool_names: Counter = field(default_factory=Counter)
    bash_buckets: Counter = field(default_factory=Counter)
    reads: Counter = field(default_factory=Counter)
    edits: Counter = field(default_factory=Counter)
    writes: Counter = field(default_factory=Counter)
    kb_hits: dict = field(default_factory=lambda: defaultdict(Counter))
    tool_result_errors: int = 0
    assistant_chars: int = 0
    user_chars: int = 0
    slash_text: str = ""
    emit_event_calls: int = 0
    extract_sorries_calls: int = 0
    lake_build_calls: int = 0
    check_snippet_calls: int = 0


def parse_ts(s: Optional[str]) -> Optional[datetime]:
    if not s:
        return None
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00"))
    except (TypeError, ValueError):
        return None


def relativise(file_path: str, root: Path) -> str:
    """Strip the STATLEAN_ROOT prefix so paths in the report are short.
    Out-of-repo paths (e.g. ~/.claude/projects/...) stay absolute."""
    if not file_path:
        return "(empty)"
    try:
        p = Path(file_path).resolve()
        if str(p).startswith(str(root) + os.sep) or str(p) == str(root):
            return str(p.relative_to(root))
    except (OSError, ValueError):
        pass
    return file_path


def analyze(transcript_path: Path, repo_root: Path) -> SessionStats:
    s = SessionStats(uuid=transcript_path.stem, path=transcript_path)
    with transcript_path.open() as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
            except json.JSONDecodeError:
                continue
            s.event_types[ev.get("type", "?")] += 1
            ts = parse_ts(ev.get("timestamp"))
            if ts:
                if s.first_ts is None or ts < s.first_ts:
                    s.first_ts = ts
                if s.last_ts is None or ts > s.last_ts:
                    s.last_ts = ts

            msg = ev.get("message", {}) if isinstance(ev.get("message"), dict) else {}
            content = msg.get("content")
            if not isinstance(content, list):
                continue

            for block in content:
                if not isinstance(block, dict):
                    continue
                btype = block.get("type")
                if btype == "tool_use":
                    _absorb_tool_use(block, s, repo_root)
                elif btype == "tool_result":
                    if block.get("is_error"):
                        s.tool_result_errors += 1
                elif btype == "text":
                    text = block.get("text", "") or ""
                    if ev.get("type") == "assistant":
                        s.assistant_chars += len(text)
                    elif ev.get("type") == "user":
                        s.user_chars += len(text)
                        if not s.slash_text and text.lstrip().startswith("/"):
                            first_line = text.lstrip().split("\n", 1)[0]
                            s.slash_text = first_line[:160]
    return s


def _absorb_tool_use(block: dict, s: SessionStats, repo_root: Path) -> None:
    name = block.get("name", "?")
    s.tool_names[name] += 1
    inp = block.get("input", {}) if isinstance(block.get("input"), (dict, list)) else {}
    inp_str = json.dumps(inp) if isinstance(inp, (dict, list)) else str(inp)

    for kb in KB_FILES:
        if kb in inp_str:
            s.kb_hits[kb][name] += 1

    if name == "Bash":
        cmd = inp.get("command", "") if isinstance(inp, dict) else ""
        if "emit_event.py" in cmd:
            s.emit_event_calls += 1
        if "extract_sorries.py" in cmd:
            s.extract_sorries_calls += 1
        if re.search(r"\blake\s+build\b", cmd):
            s.lake_build_calls += 1
        if "check_snippet" in cmd:
            s.check_snippet_calls += 1
        stripped = cmd.lstrip()
        if stripped:
            first_word = stripped.split(None, 1)[0]
            # Strip trailing paths / args so `python3` stays a useful bucket.
            first_word = first_word.split("/")[-1]
            s.bash_buckets[first_word] += 1
        else:
            s.bash_buckets["(empty)"] += 1
    elif name == "Read":
        fp = inp.get("file_path", "") if isinstance(inp, dict) else ""
        s.reads[relativise(fp, repo_root)] += 1
    elif name in ("Edit", "MultiEdit"):
        fp = inp.get("file_path", "") if isinstance(inp, dict) else ""
        s.edits[relativise(fp, repo_root)] += 1
    elif name == "Write":
        fp = inp.get("file_path", "") if isinstance(inp, dict) else ""
        s.writes[relativise(fp, repo_root)] += 1


def resolve_target(args: argparse.Namespace, t_dir: Path, repo_root: Path) -> Path:
    if args.uuid:
        p = t_dir / f"{args.uuid}.jsonl"
        if not p.exists():
            sys.exit(f"[analyze-session] uuid not found: {p}")
        return p
    if args.around:
        try:
            ct = int(subprocess.check_output(
                ["git", "log", "-1", "--format=%ct", args.around],
                cwd=repo_root, text=True,
                stderr=subprocess.PIPE,
            ).strip())
        except subprocess.CalledProcessError as e:
            sys.exit(f"[analyze-session] git log failed: {e.stderr.decode(errors='ignore').strip()}")
        commit_dt = datetime.fromtimestamp(ct, tz=timezone.utc)
        all_sessions = sorted(t_dir.glob("*.jsonl"), key=lambda p: p.stat().st_mtime)
        for p in all_sessions:
            stats = analyze(p, repo_root)
            if stats.first_ts and stats.last_ts and stats.first_ts <= commit_dt <= stats.last_ts:
                return p
        # Fallback: closest by mtime.
        if all_sessions:
            best = min(all_sessions, key=lambda p: abs(p.stat().st_mtime - ct))
            print(
                f"[analyze-session] no session brackets commit {args.around}; "
                f"nearest by mtime: {best.name}",
                file=sys.stderr,
            )
            return best
        sys.exit(f"[analyze-session] no sessions under {t_dir}")
    # --latest (default)
    all_sessions = sorted(t_dir.glob("*.jsonl"), key=lambda p: p.stat().st_mtime, reverse=True)
    if not all_sessions:
        sys.exit(f"[analyze-session] no sessions under {t_dir}")
    return all_sessions[0]


def render(s: SessionStats) -> str:
    lines = []
    if s.first_ts and s.last_ts:
        dur_min = (s.last_ts - s.first_ts).total_seconds() / 60
        span = (
            f"{s.first_ts.strftime('%Y-%m-%d %H:%M')}–"
            f"{s.last_ts.strftime('%H:%M')} UTC ({dur_min:.1f} min)"
        )
    else:
        span = "(no timestamps)"
    lines.append(f"Session: {s.uuid}")
    lines.append(f"Span:    {span}")
    lines.append(f"File:    {s.path}")
    if s.slash_text:
        lines.append(f"Invoke:  {s.slash_text}")
    lines.append("")

    total = sum(s.tool_names.values())
    tool_str = "  ·  ".join(f"{k} {v}" for k, v in s.tool_names.most_common())
    lines.append(f"Tool uses: {total}    [{tool_str}]")
    lines.append(
        f"  lake build ×{s.lake_build_calls}   check_snippet ×{s.check_snippet_calls}   "
        f"tool errors {s.tool_result_errors}"
    )
    lines.append(
        f"  emit_event.py ×{s.emit_event_calls}   extract_sorries.py ×{s.extract_sorries_calls}"
    )
    lines.append("")

    if s.edits or s.writes:
        lines.append("Files modified:")
        for p, n in s.edits.most_common():
            lines.append(f"  Edit  ×{n}  {p}")
        for p, n in s.writes.most_common():
            lines.append(f"  Write ×{n}  {p}")
        lines.append("")

    lines.append("KB access:")
    any_hit = False
    for kb in KB_FILES:
        hits = s.kb_hits.get(kb, Counter())
        total_kb = sum(hits.values())
        mark = " " if total_kb > 0 else "⚠"
        via = ", ".join(f"{k}×{v}" for k, v in hits.most_common()) if total_kb else "not consulted"
        lines.append(f"  {mark} {kb:40s} {total_kb}  ({via})")
        if total_kb:
            any_hit = True
    if not any_hit:
        lines.append("  (no KB file was touched by this session)")
    lines.append("")

    lines.append(f"Prose output: assistant {s.assistant_chars} chars  ·  user-echo {s.user_chars} chars")

    if s.reads:
        lines.append("")
        lines.append("Top Reads:")
        for p, n in s.reads.most_common(5):
            lines.append(f"  ×{n}  {p}")
    if s.bash_buckets:
        lines.append("")
        lines.append("Bash commands (by leading token):")
        for k, n in s.bash_buckets.most_common(8):
            lines.append(f"  ×{n}  {k}")

    return "\n".join(lines) + "\n"


def as_json(s: SessionStats) -> str:
    def _default(v):
        if isinstance(v, datetime):
            return v.isoformat()
        if isinstance(v, Path):
            return str(v)
        if isinstance(v, Counter):
            return dict(v)
        raise TypeError(f"unsupported: {type(v)}")
    payload = {
        "uuid": s.uuid,
        "file": str(s.path),
        "first_ts": s.first_ts,
        "last_ts": s.last_ts,
        "event_types": dict(s.event_types),
        "tool_names": dict(s.tool_names),
        "bash_buckets": dict(s.bash_buckets),
        "reads": dict(s.reads),
        "edits": dict(s.edits),
        "writes": dict(s.writes),
        "kb_hits": {k: dict(v) for k, v in s.kb_hits.items()},
        "tool_result_errors": s.tool_result_errors,
        "assistant_chars": s.assistant_chars,
        "user_chars": s.user_chars,
        "slash_text": s.slash_text,
        "emit_event_calls": s.emit_event_calls,
        "extract_sorries_calls": s.extract_sorries_calls,
        "lake_build_calls": s.lake_build_calls,
        "check_snippet_calls": s.check_snippet_calls,
    }
    return json.dumps(payload, default=_default, indent=2, ensure_ascii=False)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    group = ap.add_mutually_exclusive_group()
    group.add_argument("--uuid", help="Session uuid (file stem, no .jsonl).")
    group.add_argument(
        "--around",
        help="Find the session whose time window contains the given git commit "
             "(ref / SHA). Useful for postmortem after `git commit`.",
    )
    group.add_argument(
        "--latest", action="store_true",
        help="Most recently modified session (default when no flag given).",
    )
    ap.add_argument("--json", action="store_true", help="Emit JSON instead of formatted text.")
    ap.add_argument(
        "--transcript-dir",
        help="Override the transcript directory (default: derived from STATLEAN_ROOT).",
    )
    args = ap.parse_args()

    repo_root = statlean_root()
    t_dir = Path(args.transcript_dir).expanduser() if args.transcript_dir else transcript_dir(repo_root)
    if not t_dir.is_dir():
        sys.exit(f"[analyze-session] transcript dir not found: {t_dir}")

    target = resolve_target(args, t_dir, repo_root)
    stats = analyze(target, repo_root)
    if args.json:
        print(as_json(stats))
    else:
        print(render(stats), end="")


if __name__ == "__main__":
    main()
