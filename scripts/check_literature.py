#!/usr/bin/env python3
"""Check literature catalog completeness and source-distribution policy."""

from __future__ import annotations

import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]


def main() -> int:
    errors: list[str] = []
    generated = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "generate_literature.py"), "--check"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if generated.returncode:
        errors.append(generated.stdout.strip())
    tracked = subprocess.run(
        ["git", "ls-files", "--", "*.pdf", "*.PDF"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if tracked.returncode:
        errors.append(tracked.stderr.strip())
    elif tracked.stdout.strip():
        errors.append("tracked PDF files are forbidden:\n" + tracked.stdout.strip())
    if errors:
        print("Literature check failed:", file=sys.stderr)
        print(*errors, sep="\n", file=sys.stderr)
        return 1
    print("Literature check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
