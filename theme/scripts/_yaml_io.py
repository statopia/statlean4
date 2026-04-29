"""Shared yaml-io helpers for the czy newloop port (slice 3+).

Centralizes the atomic-write + file-mode preservation pattern that
`record_retreat.py` (slice 2) introduced privately. New scripts
(`decompose_node.py`, `propagate_done.py`, …) import from here so we
don't duplicate the pattern.

The functions here are thin and mechanical — they don't know about
sorry_backlog schema. Schema-aware logic stays in the calling script.

Why a separate module:
  - `record_retreat.py` keeps its own private copies for now
    (refactoring a passing §8-reviewed slice would re-open closure
    verification); slice 4 can DRY them up if/when convenient.
  - Slice 3.A's two new scripts can use this module from day 1.
"""
from __future__ import annotations

import fcntl
import os
import sys
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Dict, Iterator, List

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _history_log_types import migrate_yaml_v1_to_v2  # noqa: E402


def atomic_write_yaml(path: Path, data: Dict[str, Any]) -> None:
    """Write yaml atomically: stat existing mode → tempfile in same dir
    → fchmod tempfile → write → os.replace.

    Same-directory tempfile is required for `os.replace` to be POSIX-
    atomic. File mode preservation matters because `tempfile.mkstemp`
    defaults to 0o600 which would silently downgrade repo's 0o644 yaml.
    """
    if path.exists():
        original_mode = os.stat(path).st_mode & 0o777
    else:
        original_mode = 0o644

    fd, tmp_path = tempfile.mkstemp(
        prefix=path.name + ".",
        suffix=".tmp",
        dir=str(path.parent),
    )
    try:
        os.fchmod(fd, original_mode)
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            yaml.safe_dump(data, f, sort_keys=False, allow_unicode=True)
        os.replace(tmp_path, path)
    except Exception:
        try:
            os.unlink(tmp_path)
        except FileNotFoundError:
            pass
        raise


@contextmanager
def locked_backlog(path: Path) -> Iterator[Dict[str, Any]]:
    """Read sorry_backlog.yaml under fcntl.LOCK_EX, yielding the
    migrated v2-shape data dict. Caller mutates and re-writes on exit
    via `atomic_write_yaml(path, data)` BEFORE the lock is released.

    Usage:
        with locked_backlog(BACKLOG_PATH) as data:
            # inspect / mutate `data` …
            atomic_write_yaml(BACKLOG_PATH, data)

    flock is fd-bound; once we leave this with-block the fd closes and
    the lock releases. Atomic-write (os.replace) replaces the inode
    while we still hold the lock on the OLD inode — the new inode is
    unlocked from our perspective, but any other process trying to
    re-acquire flock must re-open and will see the new content.

    Raises ValueError if `path` doesn't exist (caller is expected to
    handle this case before locking).
    """
    if not path.exists():
        raise ValueError(f"backlog not found: {path}")
    with open(path, "rb") as lock_f:
        fcntl.flock(lock_f, fcntl.LOCK_EX)
        try:
            data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
            migrate_yaml_v1_to_v2(data)
            yield data
        finally:
            fcntl.flock(lock_f, fcntl.LOCK_UN)


def find_item(items: List[dict], item_id: str) -> dict | None:
    """Linear lookup by id — same pattern used across the slice 1+2
    scripts. Returns None if not found."""
    return next((it for it in items if it.get("id") == item_id), None)
