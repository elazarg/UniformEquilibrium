"""Static file resolution for the portal's mounts, per Games/DESIGN.md.

Mounts (checked longest-prefix-first): "/" -> portal/, "/standoff/" ->
games/standoff/, "/sequencer/" -> games/sequencer/, "/breeder/" ->
games/breeder/, "/atlas/" -> games/atlas/. A request for a mount root or any
other directory path serves that directory's index.html. Resolution is
traversal-safe: the resolved file must stay inside its mount directory.
"""
from __future__ import annotations

import mimetypes
from pathlib import Path
from typing import Optional, Tuple
from urllib.parse import unquote

# Order matters: more specific prefixes must be tried before "/", which
# would otherwise swallow every request.
MOUNTS = (
    ("/standoff/", "games/standoff"),
    ("/sequencer/", "games/sequencer"),
    ("/breeder/", "games/breeder"),
    ("/atlas/", "games/atlas"),
    ("/", "portal"),
)

mimetypes.add_type("application/wasm", ".wasm")


def _match_mount(path: str) -> Optional[Tuple[str, str]]:
    for prefix, rel_dir in MOUNTS:
        if path.startswith(prefix):
            return prefix, rel_dir
    return None


def resolve_static(games_root: Path, path: str) -> Optional[Tuple[Path, str]]:
    """Resolve a request path to (file_path, content_type), or None if not found."""
    matched = _match_mount(path)
    if matched is None:
        return None
    prefix, rel_dir = matched
    remainder = unquote(path[len(prefix):])
    root = (games_root / rel_dir).resolve()

    if remainder == "":
        candidate = root / "index.html"
    else:
        candidate = (root / remainder).resolve()
        try:
            candidate.relative_to(root)
        except ValueError:
            return None  # escaped the mount directory: path-traversal attempt
        if candidate.is_dir():
            candidate = candidate / "index.html"

    if not candidate.is_file():
        return None
    content_type, _ = mimetypes.guess_type(str(candidate))
    return candidate, content_type or "application/octet-stream"
