"""Canonical discovery of project-owned Lean source files."""

from __future__ import annotations

import os
import pathlib


LIBRARY_ROOTS = frozenset(
    {
        "AxiomAudit",
        "Experiments",
        "Literature",
        "MathUE",
        "Research",
        "Theorems",
        "UniformEquilibrium",
    }
)

PRUNED_DIRECTORIES = frozenset(
    {".git", ".lake", "__pycache__", ".pytest_cache"}
)


def project_lean_files(root: pathlib.Path) -> list[pathlib.Path]:
    """Return Lean files under the explicit project library roots.

    Both a root's matching top-level module and every Lean source below its
    directory are included.  Directory traversal does not consult Git, so a
    newly created, nonignored source in an allowed lane is checked before it
    is staged.
    """

    root = root.resolve()
    files: list[pathlib.Path] = []
    for library in sorted(LIBRARY_ROOTS):
        umbrella = root / f"{library}.lean"
        if umbrella.is_file():
            files.append(umbrella)
        directory = root / library
        if not directory.is_dir():
            continue
        for current, names, filenames in os.walk(directory):
            names[:] = sorted(
                name for name in names if name not in PRUNED_DIRECTORIES
            )
            base = pathlib.Path(current)
            files.extend(
                base / name for name in filenames if name.endswith(".lean")
            )
    return sorted(files)
