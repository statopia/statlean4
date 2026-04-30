"""_path_alias.py — CLI read_file path alias shim (D-5, E12 phase 02).

The agent prompt (prove-deep.md narrative + LEAN_KB_REFERENCES in phase 03)
references pitfalls files as `docs/pitfalls/<name>.md` (byte-equal to czy,
which stores them at `website-czy/docs/pitfalls/`). In the SDK-bridge
architecture the files live at `statlean-merge/theme/pitfalls/` (KB home
convention, D-1).

This module provides a single function `resolve_pitfalls_alias` that
translates `docs/pitfalls/<name>.md` → `theme/pitfalls/<name>.md` before
the path is resolved against STATLEAN_ROOT. Import it in any script that
handles `read_file` path arguments coming from the agent.

Web path is unaffected: `createToolRouter` uses `path.endsWith(filename)`
which is path-insensitive (basename match).

Usage::

    from _path_alias import resolve_pitfalls_alias
    file_path = resolve_pitfalls_alias(file_path)
    # file_path now points at theme/pitfalls/ if it was docs/pitfalls/
"""

_ALIAS_PREFIX = "docs/pitfalls/"
_CANONICAL_PREFIX = "theme/pitfalls/"


def resolve_pitfalls_alias(file_path: str) -> str:
    """Translate ``docs/pitfalls/<name>`` → ``theme/pitfalls/<name>``."""
    if file_path.startswith(_ALIAS_PREFIX):
        return _CANONICAL_PREFIX + file_path[len(_ALIAS_PREFIX):]
    return file_path
