#!/usr/bin/env python3
"""Check project Lean import reachability and architecture boundaries.

This is deliberately a static check.  It reads Lean source files and import
commands, without invoking Lean or changing source files.  Imports belonging to
external packages (for example ``Mathlib`` and the pinned ``GameTheory``
dependency) are leaves of the graph unless they name a local project module.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Iterable, Sequence

try:
    from scripts.check_trust import strip_comments_and_strings
except ModuleNotFoundError:  # Direct execution: ``python scripts/check_import_graph.py``.
    from check_trust import strip_comments_and_strings


ROOT = pathlib.Path(__file__).resolve().parents[1]
DEFAULT_UMBRELLAS = (
    "MathUE",
    "UniformEquilibrium",
    "Literature",
    "Research",
    "Theorems",
    "Experiments",
)
PRUNED_DIRECTORIES = {".git", ".lake", "__pycache__", "GameTheory"}
LEAN_LIBRARY_RE = re.compile(
    r"^\s*lean_lib\s+([A-Za-z_][A-Za-z0-9_']*)\s+where\b", re.MULTILINE
)
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
SCRATCH_NAMESPACE_RE = re.compile(
    r"^\s*namespace\s+"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*Scratch)\s*$",
    re.MULTILINE,
)
# These modules exist to make an umbrella inventory reachable.  Ordinary
# consumers must import the declarations they use, otherwise one experimental
# file can accidentally acquire hundreds of unrelated dependencies.
INVENTORY_ONLY_FACADES = {
    "UniformEquilibrium.Diagnostics.Quitting.All": {
        "UniformEquilibrium",
        "AxiomAudit",
    },
    "UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.All": {
        "UniformEquilibrium.Diagnostics.Quitting.All",
        "AxiomAudit",
    },
}


@dataclass(frozen=True)
class ParsedImport:
    """A statically parsed Lean import and its source line."""

    module: str
    line: int


@dataclass(frozen=True)
class Umbrella:
    """A library root and the module-prefix it owns."""

    name: str
    path: pathlib.Path


@dataclass(frozen=True)
class ImportBoundaryRule:
    """A directed import edge forbidden by the project architecture."""

    source_prefix: str
    target_prefix: str
    explanation: str


# Keep these rules explicit and directional.  The layers on the right may
# depend on the layers on the left while the reverse dependency is being
# removed; a bidirectional-looking check would hide which refactoring is
# required and would reject legitimate lower-level consumers.
IMPORT_BOUNDARY_RULES = (
    ImportBoundaryRule(
        "Literature",
        "Research",
        "the final literature audit must not depend on research-only modules",
    ),
    ImportBoundaryRule(
        "Literature",
        "Experiments",
        "the final literature audit must not depend on experimental evidence",
    ),
    ImportBoundaryRule(
        "MathUE",
        "Literature",
        "generic mathematics must not depend on literature audits",
    ),
    ImportBoundaryRule(
        "UniformEquilibrium",
        "Literature",
        "integrated game semantics must not depend on literature audits",
    ),
    ImportBoundaryRule(
        "Theorems",
        "Literature",
        "reader-facing integrated theorems must not depend on literature audits",
    ),
    ImportBoundaryRule(
        "UniformEquilibrium.Certificates",
        "UniformEquilibrium.Architectures",
        "certificates must depend on semantic interfaces, not architectures",
    ),
    ImportBoundaryRule(
        "UniformEquilibrium.Quitting",
        "UniformEquilibrium.Diagnostics",
        "quitting mathematics must depend on semantic interfaces, not diagnostics",
    ),
    ImportBoundaryRule(
        "UniformEquilibrium.Certificates",
        "UniformEquilibrium.Diagnostics",
        "certificates must depend on semantic interfaces, not diagnostics",
    ),
    ImportBoundaryRule(
        "Research",
        "Experiments",
        "Research must not depend on experimental evidence",
    ),
)


def parse_imports(text: str) -> list[ParsedImport]:
    """Parse ordinary Lean ``import`` commands without elaborating Lean.

    Lean accepts the module name on the line after ``import``.  Supporting
    that form matters because several project files use it for long names.
    """

    clean = strip_comments_and_strings(text)
    lines = clean.splitlines()
    imports: list[ParsedImport] = []
    index = 0
    while index < len(lines):
        stripped = lines[index].lstrip()
        if stripped == "import" or stripped.startswith("import ") or stripped.startswith(
            "import\t"
        ):
            rest = stripped[len("import") :].strip()
            import_line = index + 1
            if not rest:
                next_index = index + 1
                while next_index < len(lines) and not lines[next_index].strip():
                    next_index += 1
                if next_index < len(lines):
                    rest = lines[next_index].strip()
                    index = next_index
            for token in rest.split():
                if not MODULE_RE.fullmatch(token):
                    break
                imports.append(ParsedImport(token, import_line))
        index += 1
    return imports


def module_name(path: pathlib.Path, root: pathlib.Path) -> str:
    """Return the Lean module name represented by a source path."""

    relative = path.resolve().relative_to(root.resolve())
    return ".".join(relative.with_suffix("").parts)


def project_lean_files(root: pathlib.Path) -> list[pathlib.Path]:
    """Find project-owned Lean files, excluding the pinned dependency/cache."""

    files: list[pathlib.Path] = []
    for directory, names, filenames in os.walk(root):
        names[:] = [name for name in names if name not in PRUNED_DIRECTORIES]
        base = pathlib.Path(directory)
        files.extend(base / name for name in filenames if name.endswith(".lean"))
    return sorted(files)


def discover_umbrellas(root: pathlib.Path) -> list[Umbrella]:
    """Discover library roots declared by the repository's ``lakefile.lean``."""

    lakefile = root / "lakefile.lean"
    names: Iterable[str]
    if lakefile.is_file():
        names = LEAN_LIBRARY_RE.findall(lakefile.read_text(encoding="utf-8"))
    else:
        names = DEFAULT_UMBRELLAS
    umbrellas = []
    for name in dict.fromkeys(names):
        path = root / f"{name}.lean"
        if path.is_file():
            umbrellas.append(Umbrella(name, path))
    return umbrellas


def import_graph(
    root: pathlib.Path,
) -> tuple[dict[str, pathlib.Path], dict[str, list[ParsedImport]]]:
    """Build the local module graph and retain import source locations."""

    modules = {
        module_name(path, root): path for path in project_lean_files(root)
    }
    imports = {
        name: parse_imports(path.read_text(encoding="utf-8"))
        for name, path in modules.items()
    }
    return modules, imports


def reachable_from(
    root_module: str,
    imports: dict[str, list[ParsedImport]],
    local_modules: set[str],
) -> set[str]:
    """Return local modules reachable from one umbrella root."""

    reachable: set[str] = set()
    stack = [root_module]
    while stack:
        module = stack.pop()
        if module in reachable:
            continue
        reachable.add(module)
        stack.extend(
            item.module
            for item in imports.get(module, [])
            if item.module in local_modules
        )
    return reachable


def _is_prefixed(module: str, prefix: str) -> bool:
    return module == prefix or module.startswith(f"{prefix}.")


def check_import_graph(
    root: pathlib.Path = ROOT,
    umbrella_names: Sequence[str] | None = None,
) -> list[str]:
    """Return diagnostics for reachability, ownership, and API-shape violations."""

    root = root.resolve()
    modules, imports = import_graph(root)
    local_names = set(modules)
    all_umbrellas = discover_umbrellas(root)
    by_name = {umbrella.name: umbrella for umbrella in all_umbrellas}
    names = tuple(umbrella_names) if umbrella_names is not None else tuple(by_name)
    failures: list[str] = []

    for name in names:
        umbrella = by_name.get(name)
        if umbrella is None:
            failures.append(
                f"umbrella {name}: no {name}.lean root found; "
                "add the library root or select an existing umbrella"
            )
            continue
        if name not in modules:
            failures.append(
                f"{umbrella.path}: umbrella module {name} is not in the local graph"
            )
            continue
        reachable = reachable_from(name, imports, local_names)
        orphaned = sorted(
            module
            for module in local_names
            if _is_prefixed(module, name) and module not in reachable
        )
        for module in orphaned:
            failures.append(
                f"{modules[module]}: module {module} is not reachable from "
                f"{name}.lean; add an import path from that umbrella or move it "
                "out of the library lane"
            )

    local_prefixes = tuple(by_name)
    for module, items in imports.items():
        if module == "UniformEquilibrium" and any(
            item.module == "MathUE" for item in items
        ):
            for item in items:
                if item.module != "MathUE" and _is_prefixed(item.module, "MathUE"):
                    failures.append(
                        f"{modules[module]}:{item.line}: redundant direct import "
                        f"{item.module} after import MathUE; keep generic inventory "
                        "ownership in MathUE.lean"
                    )

        for item in items:
            if item.module not in local_names and any(
                _is_prefixed(item.module, prefix) for prefix in local_prefixes
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: imports missing local module "
                    f"{item.module}; check the module path or import spelling"
                )

            if _is_prefixed(module, "UniformEquilibrium") and _is_prefixed(
                item.module, "Research"
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: production module {module} "
                    f"imports research-only module {item.module}; move the "
                    "dependency behind a production interface or move this file "
                    "to Research"
                )
            if _is_prefixed(module, "UniformEquilibrium") and _is_prefixed(
                item.module, "Experiments"
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: production module {module} "
                    f"imports experiment-only module {item.module}; move the "
                    "dependency behind a production interface or move this file "
                    "to Experiments"
                )
            if (
                _is_prefixed(module, "MathUE")
                and _is_prefixed(item.module, "GameTheory")
                and not _is_prefixed(item.module, "GameTheory.Math")
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: MathUE module {module} imports "
                    f"game-semantic module {item.module}; use project-owned "
                    "MathUE mathematics or GameTheory.Math generic interfaces"
                )

            for rule in IMPORT_BOUNDARY_RULES:
                if _is_prefixed(module, rule.source_prefix) and _is_prefixed(
                    item.module, rule.target_prefix
                ):
                    failures.append(
                        f"{modules[module]}:{item.line}: forbidden architectural "
                        f"edge {module} -> {item.module}; {rule.explanation}"
                    )

            # The literature lane is terminal: nothing imports it.  Active
            # claim work lives inside the paper file itself, so no other
            # lane ever needs a literature module.
            if (
                _is_prefixed(item.module, "Literature")
                and not _is_prefixed(module, "Literature")
                and module != "AxiomAudit"
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: module {module} imports "
                    f"{item.module}; nothing imports the literature lane"
                )

            # Research is tentative work: nothing outside Research imports
            # it.  Anything important enough to be imported is important
            # enough to reside under UniformEquilibrium or MathUE.
            if (
                _is_prefixed(item.module, "Research")
                and not _is_prefixed(module, "Research")
                and module != "AxiomAudit"
            ):
                failures.append(
                    f"{modules[module]}:{item.line}: module {module} imports "
                    f"research module {item.module}; promote the imported "
                    "module to UniformEquilibrium or MathUE instead"
                )

            allowed_consumers = INVENTORY_ONLY_FACADES.get(item.module)
            if allowed_consumers is not None and module not in allowed_consumers:
                failures.append(
                    f"{modules[module]}:{item.line}: module {module} imports "
                    f"inventory-only facade {item.module}; import the narrow "
                    "modules containing the declarations actually used"
                )

    for module, path in modules.items():
        if not _is_prefixed(module, "MathUE"):
            continue
        clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        for match in SCRATCH_NAMESPACE_RE.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            failures.append(
                f"{path}:{line}: MathUE namespace {match.group(1)} ends in "
                "Scratch; put implementation details under an Internal namespace"
            )

    return failures


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=ROOT,
        help="repository root (default: this repository)",
    )
    parser.add_argument(
        "--umbrella",
        action="append",
        dest="umbrellas",
        help="check only this library root; may be repeated",
    )
    args = parser.parse_args(argv)
    failures = check_import_graph(args.root, args.umbrellas)
    if failures:
        print("Lean import-graph check failed:", file=sys.stderr)
        print(*failures, sep="\n", file=sys.stderr)
        return 1

    modules, _ = import_graph(args.root.resolve())
    selected = args.umbrellas or [umbrella.name for umbrella in discover_umbrellas(args.root)]
    print(
        f"Lean import-graph check passed ({len(modules)} local modules; "
        f"umbrellas: {', '.join(selected)})."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
