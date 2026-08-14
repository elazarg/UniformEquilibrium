#!/usr/bin/env python3
"""Synchronize production UE code from an exact Git revision.

Source-owned files are read with ``git show`` and the GameTheory dependency is
inspected from its working tree. Conjecture declarations remain target-owned
because open claims are proposition definitions, never placeholder proofs.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path
from typing import BinaryIO


IMPORT_LINE_RE = re.compile(r"^(\s*import\s+)(.+?)(\s*(?:--.*)?)$", re.MULTILINE)

TARGET_OWNED_UE = {
    "UniformEquilibrium/Conjecture/UniformExistenceConjecture.lean",
    "UniformEquilibrium/Quitting/Conjecture/Basic.lean",
}

SPECIAL_SOURCE_FILES = {
    "GameTheory/Concepts/Correlation/PrivateRecommendationTargetSeparator.lean":
        "UniformEquilibrium/Diagnostics/PrivateRecommendationTargetSeparator.lean",
}

SPECIAL_IMPORT_REWRITES = {
    "GameTheory.Concepts.Correlation.PrivateRecommendationTargetSeparator":
        "UniformEquilibrium.Diagnostics.PrivateRecommendationTargetSeparator",
}

# Research modules may need project-owned mathematics that is not currently in
# the production dependency closure. Keep these roots in MathUE and include
# their transitive source-only `Math.*` dependencies.
EXTRA_MATH_MODULES = {
    "Math.AnalyticConeLift",
    "Math.AnalyticFiniteRayMaximum",
    "Math.CyclicMaxAffineBound",
    "Math.GradedConvolution",
    "Math.InfinitesimalRatFunc",
    "Math.Interval.PolynomialKrawczyk",
    "Math.Interval.ScalarDyadicPolynomial",
    "Math.KrawczykBridge",
    "Math.LinearAlgebra.CyclicSchur",
    "Math.LinearAlgebra.OwnerObstructionCokernel",
    "Math.Probability.AnalyticChargedCirculationFixedCoordinate",
    "Math.RamifiedBinomialBranch",
}

# These exact-computation certificate modules use ``native_decide``.  The
# mathematical setup around them is copied; only the prohibited certificates
# are omitted from the standalone trust boundary.
PROHIBITED_UE = {
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseGroupZeroTwo.lean",
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseGroupThreeFive.lean",
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseGroupSixEight.lean",
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseNine.lean",
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseTenRootZero.lean",
    "UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicPhaseTenRootOne.lean",
}

BLOCK_PAIR_UMBRELLA = "UniformEquilibrium/Quitting/Examples/BlockPair/All.lean"


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={repo.as_posix()}", "-C", str(repo), *args]
    )


def git_tree(repo: Path, revision: str) -> list[str]:
    return git(repo, "ls-tree", "-r", "--name-only", revision).decode().splitlines()


class GitSnapshot:
    """Fast repeated reads from one revision through ``git cat-file``."""

    def __init__(self, repo: Path, revision: str) -> None:
        self.revision = revision
        self.process = subprocess.Popen(
            [
                "git",
                "-c",
                f"safe.directory={repo.as_posix()}",
                "-C",
                str(repo),
                "cat-file",
                "--batch",
            ],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
        )
        if self.process.stdin is None or self.process.stdout is None:
            raise RuntimeError("failed to open git cat-file pipes")
        self.input: BinaryIO = self.process.stdin
        self.output: BinaryIO = self.process.stdout

    def read(self, path: str) -> bytes:
        self.input.write(f"{self.revision}:{path}\n".encode("utf-8"))
        self.input.flush()
        header = self.output.readline().decode("utf-8").rstrip("\n")
        if header.endswith(" missing"):
            raise RuntimeError(f"missing source object: {path}")
        fields = header.split()
        if len(fields) != 3 or fields[1] != "blob":
            raise RuntimeError(f"unexpected git cat-file response for {path}: {header}")
        size = int(fields[2])
        contents = self.output.read(size)
        if len(contents) != size or self.output.read(1) != b"\n":
            raise RuntimeError(f"truncated git cat-file response for {path}")
        return contents

    def close(self) -> None:
        self.input.close()
        self.output.close()
        return_code = self.process.wait()
        if return_code:
            raise RuntimeError(f"git cat-file exited with status {return_code}")


def module_name(path: str) -> str | None:
    return path[:-5].replace("/", ".") if path.endswith(".lean") else None


def module_index(paths: list[str]) -> dict[str, str]:
    return {
        name.casefold(): path
        for path in paths
        if (name := module_name(path)) is not None
    }


def dependency_worktree_index(root: Path) -> dict[str, str]:
    paths: list[str] = []
    for prefix in ("GameTheory", "Math"):
        directory = root / prefix
        if directory.is_dir():
            paths.extend(path.relative_to(root).as_posix() for path in directory.rglob("*.lean"))
    for filename in ("GameTheory.lean", "Math.lean"):
        if (root / filename).is_file():
            paths.append(filename)
    return module_index(paths)


def imports(contents: bytes) -> list[str]:
    result: list[str] = []
    for match in IMPORT_LINE_RE.finditer(contents.decode("utf-8")):
        result.extend(match.group(2).split())
    return result


def rewrite_imports(contents: bytes, copied_math: set[str]) -> bytes:
    text = contents.decode("utf-8")

    def replace(match: re.Match[str]) -> str:
        modules = []
        for name in match.group(2).split():
            replacement = SPECIAL_IMPORT_REWRITES.get(name, name)
            if replacement.casefold() in copied_math:
                replacement = "MathUE." + replacement[len("Math.") :]
            modules.append(replacement)
        return match.group(1) + " ".join(modules) + match.group(3)

    return IMPORT_LINE_RE.sub(replace, text).encode("utf-8")


def sanitize_block_pair_umbrella(contents: bytes) -> bytes:
    prohibited_modules = {
        module_name(path) for path in PROHIBITED_UE if module_name(path) is not None
    }
    lines = contents.decode("utf-8").splitlines(keepends=True)
    return "".join(
        line
        for line in lines
        if not any(
            re.match(rf"^\s*import\s+{re.escape(module)}(?:\s|$)", line)
            for module in prohibited_modules
        )
    ).encode("utf-8")


def safe_unlink(root: Path, path: Path) -> None:
    resolved = path.resolve()
    if not resolved.is_relative_to(root) or path.is_symlink():
        raise RuntimeError(f"refusing to remove unsafe path: {path}")
    if path.is_file():
        path.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--dependency", type=Path, required=True)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument(
        "--overlay-root",
        type=Path,
        help="Read target-owned files here when synchronizing into staging.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    source = args.source.resolve()
    dependency = args.dependency.resolve()
    target = args.target.resolve()
    overlay = (args.overlay_root or target).resolve()

    source_paths = git_tree(source, args.source_revision)
    source_modules = module_index(source_paths)
    dependency_modules = dependency_worktree_index(dependency)
    snapshot = GitSnapshot(source, args.source_revision)

    source_ue = {
        path
        for path in source_paths
        if (path == "UniformEquilibrium.lean" or path.startswith("UniformEquilibrium/"))
        and path.endswith(".lean")
        and path not in PROHIBITED_UE
    }
    source_contents = {path: snapshot.read(path) for path in source_ue}
    for source_path, target_path in SPECIAL_SOURCE_FILES.items():
        source_contents[target_path] = snapshot.read(source_path)

    pending = list(EXTRA_MATH_MODULES) + [
        name
        for contents in source_contents.values()
        for name in imports(contents)
        if name.casefold().startswith("math.")
    ]
    copied_modules: dict[str, str] = {}
    scanned: set[str] = set()
    while pending:
        imported = pending.pop()
        key = imported.casefold()
        if key in scanned:
            continue
        scanned.add(key)
        source_path = source_modules.get(key)
        if source_path is None or key in dependency_modules:
            continue
        copied_modules[key] = source_path
        pending.extend(
            name
            for name in imports(snapshot.read(source_path))
            if name.casefold().startswith("math.")
        )

    target.mkdir(parents=True, exist_ok=True)
    desired_ue = set(source_ue) | set(SPECIAL_SOURCE_FILES.values())
    for protected in TARGET_OWNED_UE:
        desired_ue.add(protected)
        source_file = overlay / protected
        if not source_file.is_file():
            raise RuntimeError(f"missing target-owned overlay: {source_file}")
        destination = target / protected
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source_file.read_bytes())

    ue_root = target / "UniformEquilibrium"
    if ue_root.is_dir():
        for existing in ue_root.rglob("*.lean"):
            relative = existing.relative_to(target).as_posix()
            if relative not in desired_ue:
                safe_unlink(target, existing)

    copied_keys = set(copied_modules)
    for path, contents in sorted(source_contents.items()):
        if path in TARGET_OWNED_UE:
            continue
        if path == BLOCK_PAIR_UMBRELLA:
            contents = sanitize_block_pair_umbrella(contents)
        destination = target / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(rewrite_imports(contents, copied_keys))

    math_root = target / "MathUE"
    desired_math_paths: set[str] = set()
    for key, source_path in sorted(copied_modules.items()):
        module = module_name(source_path)
        assert module is not None
        output_path = "MathUE/" + module[len("Math.") :].replace(".", "/") + ".lean"
        desired_math_paths.add(output_path)
        destination = target / output_path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(
            rewrite_imports(snapshot.read(source_path), copied_keys)
        )
    if math_root.is_dir():
        for existing in math_root.rglob("*.lean"):
            relative = existing.relative_to(target).as_posix()
            if relative not in desired_math_paths:
                safe_unlink(target, existing)

    math_umbrella = "".join(
        f"import MathUE.{module_name(path)[len('Math.') :]}\n"
        for _, path in sorted(copied_modules.items())
    )
    (target / "MathUE.lean").write_text(math_umbrella, encoding="utf-8")

    ue_umbrella = target / "UniformEquilibrium.lean"
    umbrella_text = ue_umbrella.read_text(encoding="utf-8")
    if not umbrella_text.startswith("import MathUE\n"):
        ue_umbrella.write_text("import MathUE\n" + umbrella_text, encoding="utf-8")

    unresolved: set[tuple[str, str]] = set()
    checked = [target / "UniformEquilibrium.lean", target / "MathUE.lean"]
    checked.extend((target / "UniformEquilibrium").rglob("*.lean"))
    checked.extend((target / "MathUE").rglob("*.lean"))
    for path in checked:
        for imported in imports(path.read_bytes()):
            if imported.startswith(("MathUE.", "UniformEquilibrium.")):
                expected = (target / imported.replace(".", "/")).with_suffix(".lean")
                if not expected.is_file():
                    unresolved.add((path.relative_to(target).as_posix(), imported))
            elif imported.startswith(("Math.", "GameTheory.")):
                if imported.casefold() not in dependency_modules:
                    unresolved.add((path.relative_to(target).as_posix(), imported))

    print(f"source UE files: {len(source_ue)}")
    print(f"copied MathUE files: {len(copied_modules)}")
    print(f"unresolved imports: {len(unresolved)}")
    for path, imported in sorted(unresolved):
        print(f"  {path}: {imported}")
    if unresolved:
        snapshot.close()
        raise SystemExit(1)
    snapshot.close()


if __name__ == "__main__":
    main()
