#!/usr/bin/env python3
"""Select focused Lean targets, falling back to full builds when unsafe."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import PurePosixPath

try:
    from scripts.lean_source_roots import LIBRARY_ROOTS
except ModuleNotFoundError:  # Direct execution.
    from lean_source_roots import LIBRARY_ROOTS


STRUCTURAL = {
    ".gitmodules",
    "GameTheory",
    "lake-manifest.json",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
}
def changed(base: str, head: str) -> list[tuple[str, tuple[str, ...]]]:
    output = subprocess.run(
        ["git", "diff", "--name-status", "--find-renames", base, head],
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout
    entries = []
    for line in output.splitlines():
        fields = line.split("\t")
        entries.append((fields[0], tuple(path.replace("\\", "/") for path in fields[1:])))
    return entries


def target(path: str) -> str | None:
    source = PurePosixPath(path)
    if source.suffix != ".lean":
        return None
    parts = source.with_suffix("").parts
    if not parts or parts[0] not in LIBRARY_ROOTS:
        return None
    return "+" + ".".join(parts)


def plan(base: str, head: str) -> tuple[str, tuple[str, ...]]:
    targets: set[str] = set()
    for status, paths in changed(base, head):
        if any(path in STRUCTURAL or path.startswith("GameTheory/") for path in paths):
            return "full", ()
        if status.startswith(("D", "R")) and any(path.endswith(".lean") for path in paths):
            return "full", ()
        for path in paths:
            if not path.endswith(".lean"):
                continue
            module = target(path)
            if module is None:
                return "full", ()
            targets.add(module)
    return ("focused", tuple(sorted(targets))) if targets else ("none", ())


def main() -> None:
    parser = argparse.ArgumentParser()
    output = parser.add_mutually_exclusive_group(required=True)
    output.add_argument("--mode", action="store_true")
    output.add_argument("--targets", action="store_true")
    parser.add_argument("base")
    parser.add_argument("head")
    args = parser.parse_args()
    mode, targets = plan(args.base, args.head)
    print(mode if args.mode else "\n".join(targets))


if __name__ == "__main__":
    main()
