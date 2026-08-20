#!/usr/bin/env python3
"""Reconstruct historical UE code into an external staging tree.

Source-owned files are read with ``git show`` and the GameTheory dependency is
inspected from its working tree. Conjecture declarations remain target-owned
because open claims are proposition definitions, never placeholder proofs.
This is historical staging-only tooling, not a synchronizer for the live tree.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
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


@dataclass(frozen=True)
class Operation:
    """One filesystem operation in a fully preflighted synchronization."""

    action: str
    path: str
    source: str | None = None
    size: int | None = None


@dataclass(frozen=True)
class SyncPlan:
    source: Path
    source_revision: str
    dependency: Path
    target: Path
    operations: tuple[Operation, ...]
    contents: dict[str, bytes]
    unresolved: tuple[tuple[str, str], ...]

    def manifest(self) -> dict[str, object]:
        return {
            "source": str(self.source),
            "source_revision": self.source_revision,
            "dependency": str(self.dependency),
            "target": str(self.target),
            "operations": [
                {
                    key: value
                    for key, value in {
                        "action": operation.action,
                        "path": operation.path,
                        "source": operation.source,
                        "size": operation.size,
                    }.items()
                    if value is not None
                }
                for operation in self.operations
            ],
            "unresolved_imports": [
                {"path": path, "import": imported}
                for path, imported in self.unresolved
            ],
        }


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
            self.process.kill()
            self.process.wait()
            raise RuntimeError("failed to open git cat-file pipes")
        self.input: BinaryIO = self.process.stdin
        self.output: BinaryIO = self.process.stdout
        self._closed = False

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
        if self._closed:
            return
        self._closed = True
        try:
            self.input.close()
        finally:
            try:
                self.output.close()
            finally:
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


def _has_symlink_component(path: Path) -> bool:
    """Return whether an existing component of ``path`` is a symlink."""
    current = Path(path.anchor)
    for component in path.parts[1:]:
        current /= component
        if current.is_symlink():
            return True
    return False


def _paths_overlap(first: Path, second: Path) -> bool:
    return first == second or first.is_relative_to(second) or second.is_relative_to(first)


def validate_paths(
    source: Path,
    dependency: Path,
    target: Path,
    *,
    live_root: Path,
) -> tuple[Path, Path, Path]:
    """Validate the resolved roots before reading or mutating any target path.

    The synchronizer is historical staging tooling.  Its target must be a
    separate, non-repository tree: this prevents an old source snapshot from
    deleting current project files or from treating a dependency checkout as
    disposable staging output.
    """
    raw_target = target
    if raw_target.is_symlink() or _has_symlink_component(raw_target.absolute()):
        raise RuntimeError(f"refusing symlink target: {raw_target}")

    source = source.resolve()
    dependency = dependency.resolve()
    target = target.resolve()
    live_root = live_root.resolve()

    if not source.is_dir():
        raise RuntimeError(f"source is not a directory: {source}")
    if not dependency.is_dir():
        raise RuntimeError(f"dependency is not a directory: {dependency}")
    if target == Path(target.anchor):
        raise RuntimeError(f"refusing filesystem root as target: {target}")
    if target in {Path.cwd().resolve(), Path.home().resolve()}:
        raise RuntimeError(f"refusing broad target directory: {target}")
    if target == live_root or target.is_relative_to(live_root):
        raise RuntimeError(
            f"refusing live repository target; use an external staging directory: {target}"
        )
    if _paths_overlap(target, source) or _paths_overlap(target, dependency):
        raise RuntimeError(
            "refusing overlapping source, dependency, and target directories"
        )
    if target.exists() and not target.is_dir():
        raise RuntimeError(f"target is not a directory: {target}")
    if (target / ".git").exists():
        raise RuntimeError(
            f"refusing repository root as target; use a staging directory: {target}"
        )

    # A target below another checkout is just as dangerous as the live tree:
    # stale-file cleanup could modify that checkout's working tree.
    for parent in target.parents:
        if (parent / ".git").exists():
            raise RuntimeError(
                f"refusing target inside a repository; use a staging directory: {target}"
            )
    return source, dependency, target


def safe_unlink(root: Path, path: Path) -> None:
    root = root.resolve()
    if _has_symlink_component(path.absolute()):
        raise RuntimeError(f"refusing to remove symlink path: {path}")
    resolved = path.resolve()
    if not resolved.is_relative_to(root) or path.is_symlink():
        raise RuntimeError(f"refusing to remove unsafe path: {path}")
    if path.is_file():
        path.unlink()


def _safe_destination(target: Path, relative: str) -> Path:
    destination = target / relative
    if _has_symlink_component(destination.absolute()):
        raise RuntimeError(f"refusing symlink destination: {destination}")
    if not destination.resolve().is_relative_to(target.resolve()):
        raise RuntimeError(f"refusing destination outside target: {destination}")
    return destination


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Reconstruct a historical UniformEquilibrium snapshot into an "
            "external staging tree. This is not a current-tree synchronizer."
        )
    )
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--dependency", type=Path, required=True)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument(
        "--overlay-root",
        type=Path,
        help="Read target-owned files here when synchronizing into staging.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print a JSON operation manifest without deleting or copying files.",
    )
    return parser.parse_args()


def _operation_for_write(
    target: Path, relative: str, contents: bytes, source: str
) -> Operation:
    _safe_destination(target, relative)
    return Operation("copy", relative, source, len(contents))


def _operation_for_delete(target: Path, relative: str) -> Operation:
    path = _safe_destination(target, relative)
    if path.is_symlink():
        raise RuntimeError(f"refusing to remove symlink path: {path}")
    return Operation("delete", relative)


def _planned_unresolved(
    planned_contents: dict[str, bytes],
    dependency_modules: dict[str, str],
) -> tuple[tuple[str, str], ...]:
    unresolved: set[tuple[str, str]] = set()
    for relative, contents in planned_contents.items():
        for imported in imports(contents):
            if imported.startswith(("MathUE.", "UniformEquilibrium.")):
                expected = imported.replace(".", "/") + ".lean"
                if expected not in planned_contents:
                    unresolved.add((relative, imported))
            elif imported.startswith(("Math.", "GameTheory.")):
                if imported.casefold() not in dependency_modules:
                    unresolved.add((relative, imported))
    return tuple(sorted(unresolved))


def build_plan(
    source: Path,
    source_revision: str,
    dependency: Path,
    target: Path,
    overlay: Path,
    *,
    live_root: Path,
) -> SyncPlan:
    source, dependency, target = validate_paths(
        source, dependency, target, live_root=live_root
    )
    overlay = overlay.resolve()
    if not overlay.is_dir():
        raise RuntimeError(f"overlay is not a directory: {overlay}")

    source_paths = git_tree(source, source_revision)
    source_modules = module_index(source_paths)
    dependency_modules = dependency_worktree_index(dependency)
    snapshot = GitSnapshot(source, source_revision)

    source_ue = {
        path
        for path in source_paths
        if (path == "UniformEquilibrium.lean" or path.startswith("UniformEquilibrium/"))
        and path.endswith(".lean")
        and path not in PROHIBITED_UE
    }
    try:
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

        operations: list[Operation] = []
        planned_contents: dict[str, bytes] = {}
        desired_ue = set(source_ue) | set(SPECIAL_SOURCE_FILES.values())
        for protected in TARGET_OWNED_UE:
            desired_ue.add(protected)
            source_file = overlay / protected
            if not source_file.is_file():
                raise RuntimeError(f"missing target-owned overlay: {source_file}")
            contents = source_file.read_bytes()
            planned_contents[protected] = contents
            operations.append(
                _operation_for_write(target, protected, contents, str(source_file))
            )

        ue_root = target / "UniformEquilibrium"
        if ue_root.is_dir():
            for existing in sorted(ue_root.rglob("*.lean")):
                relative = existing.relative_to(target).as_posix()
                if relative not in desired_ue:
                    operations.append(_operation_for_delete(target, relative))

        copied_keys = set(copied_modules)
        for path, contents in sorted(source_contents.items()):
            if path in TARGET_OWNED_UE or path == "UniformEquilibrium.lean":
                continue
            if path == BLOCK_PAIR_UMBRELLA:
                contents = sanitize_block_pair_umbrella(contents)
            contents = rewrite_imports(contents, copied_keys)
            planned_contents[path] = contents
            operations.append(
                _operation_for_write(
                    target, path, contents, f"{source_revision}:{path}"
                )
            )

        desired_math_paths: set[str] = set()
        for key, source_path in sorted(copied_modules.items()):
            module = module_name(source_path)
            assert module is not None
            output_path = (
                "MathUE/" + module[len("Math.") :].replace(".", "/") + ".lean"
            )
            desired_math_paths.add(output_path)
            contents = rewrite_imports(snapshot.read(source_path), copied_keys)
            planned_contents[output_path] = contents
            operations.append(
                _operation_for_write(
                    target, output_path, contents, f"{source_revision}:{source_path}"
                )
            )

        math_root = target / "MathUE"
        if math_root.is_dir():
            for existing in sorted(math_root.rglob("*.lean")):
                relative = existing.relative_to(target).as_posix()
                if relative not in desired_math_paths:
                    operations.append(_operation_for_delete(target, relative))

        math_umbrella = "".join(
            f"import MathUE.{module_name(path)[len('Math.') :]}\n"
            for _, path in sorted(copied_modules.items())
        ).encode("utf-8")
        planned_contents["MathUE.lean"] = math_umbrella
        operations.append(
            _operation_for_write(target, "MathUE.lean", math_umbrella, "generated")
        )

        ue_umbrella = source_contents.get("UniformEquilibrium.lean")
        if ue_umbrella is None:
            raise RuntimeError("source snapshot has no UniformEquilibrium.lean umbrella")
        ue_umbrella = rewrite_imports(ue_umbrella, copied_keys)
        if not ue_umbrella.startswith(b"import MathUE\n"):
            ue_umbrella = b"import MathUE\n" + ue_umbrella
        planned_contents["UniformEquilibrium.lean"] = ue_umbrella
        operations.append(
            _operation_for_write(
                target, "UniformEquilibrium.lean", ue_umbrella, "generated"
            )
        )

        unresolved = _planned_unresolved(planned_contents, dependency_modules)
        return SyncPlan(
            source,
            source_revision,
            dependency,
            target,
            tuple(operations),
            planned_contents,
            unresolved,
        )
    finally:
        snapshot.close()


def apply_plan(plan: SyncPlan) -> None:
    plan.target.mkdir(parents=True, exist_ok=True)
    for operation in plan.operations:
        path = _safe_destination(plan.target, operation.path)
        if operation.action == "delete":
            safe_unlink(plan.target, path)
        else:
            contents = plan.contents[operation.path]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(contents)


def main() -> None:
    args = parse_args()
    live_root = Path(__file__).resolve().parents[1]
    plan = build_plan(
        args.source,
        args.source_revision,
        args.dependency,
        args.target,
        args.overlay_root or args.target,
        live_root=live_root,
    )
    print(json.dumps(plan.manifest(), indent=2, sort_keys=True))
    if plan.unresolved:
        raise SystemExit(1)
    if args.dry_run:
        return
    apply_plan(plan)
    print(f"source UE files: {len(plan.contents)}")
    print(f"planned operations: {len(plan.operations)}")


if __name__ == "__main__":
    main()
