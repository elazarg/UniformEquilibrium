#!/usr/bin/env python3
"""Normalize project-owned Markdown filenames to UPPER_SNAKE_CASE.md."""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PRUNED_DIRECTORIES = {
    ".git",
    ".lake",
    "GameTheory",
    "__pycache__",
    ".pytest_cache",
    "ephemeral",
}
TEXT_SUFFIXES = {
    ".json",
    ".md",
    ".py",
    ".toml",
    ".txt",
    ".yaml",
    ".yml",
}


def project_files() -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for directory, names, filenames in os.walk(ROOT):
        names[:] = [name for name in names if name not in PRUNED_DIRECTORIES]
        base = pathlib.Path(directory)
        files.extend(base / filename for filename in filenames)
    return files


def normalized_name(name: str) -> str:
    path = pathlib.Path(name)
    if path.suffix.lower() != ".md":
        return name
    stem = path.stem
    stem = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", stem)
    stem = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", stem)
    stem = re.sub(r"[^A-Za-z0-9]+", "_", stem).strip("_").upper()
    return f"{stem}.md"


def rename_plan() -> dict[pathlib.Path, pathlib.Path]:
    plan: dict[pathlib.Path, pathlib.Path] = {}
    for source in project_files():
        if source.suffix.lower() != ".md" or source.is_symlink():
            continue
        target = source.with_name(normalized_name(source.name))
        if source != target:
            plan[source] = target
    targets = list(plan.values())
    if len(targets) != len(set(targets)):
        raise RuntimeError("Markdown normalization has target collisions")
    for source, target in plan.items():
        if target.exists() and not source.samefile(target):
            raise RuntimeError(f"Markdown normalization target exists: {target}")
    return plan


def replacement_pairs(
    document: pathlib.Path, plan: dict[pathlib.Path, pathlib.Path]
) -> list[tuple[str, str]]:
    pairs: set[tuple[str, str]] = set()
    for source, target in plan.items():
        old_root = source.relative_to(ROOT).as_posix()
        new_root = target.relative_to(ROOT).as_posix()
        pairs.add((old_root, new_root))
        old_relative = os.path.relpath(source, document.parent).replace(os.sep, "/")
        new_relative = os.path.relpath(target, document.parent).replace(os.sep, "/")
        pairs.add((old_relative, new_relative))
        if source.parent == document.parent:
            pairs.add((source.name, target.name))
    return sorted(pairs, key=lambda pair: len(pair[0]), reverse=True)


def apply_plan(plan: dict[pathlib.Path, pathlib.Path]) -> None:
    text_files = [
        path
        for path in project_files()
        if path.suffix.lower() in TEXT_SUFFIXES and path.suffix.lower() != ".lean"
    ]
    for document in text_files:
        text = document.read_text(encoding="utf-8")
        updated = text
        for old, new in replacement_pairs(document, plan):
            updated = updated.replace(old, new)
        if updated != text:
            document.write_text(updated, encoding="utf-8")
    for index, (source, target) in enumerate(sorted(
        plan.items(), key=lambda item: len(item[0].parts), reverse=True
    )):
        if target.exists() and source.samefile(target):
            temporary = source.with_name(f".markdown-rename-{index}.tmp")
            if temporary.exists():
                raise RuntimeError(f"temporary rename target exists: {temporary}")
            source.rename(temporary)
            temporary.rename(target)
        else:
            source.rename(target)
        print(f"renamed {source.relative_to(ROOT)} -> {target.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    plan = rename_plan()
    if not plan:
        return 0
    if args.apply:
        apply_plan(plan)
        return 0
    print("Markdown filenames are not normalized:", file=sys.stderr)
    for source, target in sorted(plan.items()):
        print(
            f"{source.relative_to(ROOT)} -> {target.relative_to(ROOT)}",
            file=sys.stderr,
        )
    print("Run: python scripts/normalize_markdown_names.py --apply", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
