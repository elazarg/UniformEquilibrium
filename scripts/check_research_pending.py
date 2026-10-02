#!/usr/bin/env python3
"""Check integrity and portability of frozen, uncompiled Research implementation."""

from __future__ import annotations

import hashlib
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Research/Pending/MANIFEST.json"


def checked_path(root: pathlib.Path, name: str) -> pathlib.Path:
    relative = pathlib.PurePosixPath(name)
    if relative.is_absolute() or ".." in relative.parts or "\\" in name:
        raise ValueError(f"nonportable path: {name}")
    path = root.joinpath(*relative.parts)
    if path.is_symlink() or root.resolve() not in path.resolve().parents:
        raise ValueError(f"path escapes checkout: {name}")
    return path


def check(root: pathlib.Path, manifest: dict) -> list[str]:
    errors: list[str] = []
    artifacts = manifest["artifacts"]
    if manifest["status"] != "uncompiled":
        errors.append("frozen drafts must retain their uncompiled status")
    for name, item in artifacts.items():
        try:
            path = checked_path(root, name)
        except ValueError as error:
            errors.append(str(error))
            continue
        if not path.is_file():
            errors.append(f"missing artifact: {name}")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            errors.append(f"hash mismatch: {name}")
        if name.endswith(".lean"):
            errors.append(f"unchecked artifact in compiled source inventory: {name}")
        for change in item.get("changes", []):
            if change not in artifacts:
                errors.append(f"{name}: unrecorded source change: {change}")
        if "intended_owner" in item:
            try:
                checked_path(root, item["intended_owner"])
            except ValueError as error:
                errors.append(str(error))
    for plan in manifest["plans"]:
        for field in ("changes", "records"):
            for name in plan.get(field, []):
                if name not in artifacts:
                    errors.append(f"{plan['name']}: unrecorded {field} entry: {name}")
        for dependency in plan.get("depends_on", []):
            if dependency not in {item["name"] for item in manifest["plans"]}:
                errors.append(f"{plan['name']}: unknown plan dependency: {dependency}")
    for name in manifest["legacy_paths"].values():
        if name not in artifacts:
            errors.append(f"legacy path maps to missing artifact: {name}")
    directory = root / "Research/Pending"
    actual = {
        path.relative_to(root).as_posix()
        for path in directory.rglob("*")
        if path.is_file() and path.name not in {"README.md", "MANIFEST.json"}
    }
    errors.extend(f"unrecorded artifact: {name}" for name in sorted(actual - artifacts.keys()))
    return errors


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    errors = check(ROOT, manifest)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Pending Research integrity passed: {len(manifest['artifacts'])} artifacts; "
          "no Lean verification claimed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
