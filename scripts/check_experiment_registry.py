#!/usr/bin/env python3
"""Check that the registered Base experiment suite is closed and runnable."""

from __future__ import annotations

import argparse
import ast
import json
import pathlib
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
BASE = ROOT / "Experiments" / "Base"
RUNNER = BASE / "run_all.py"
NON_EXPERIMENT_MODULES = {"__init__", "run_all"}


def declared_modules(runner: pathlib.Path = RUNNER) -> list[str]:
    tree = ast.parse(runner.read_text(encoding="utf-8"), filename=str(runner))
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(isinstance(target, ast.Name) and target.id == "EXPERIMENT_MODULES"
                   for target in targets):
            continue
        value = ast.literal_eval(statement.value)
        if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
            raise ValueError("EXPERIMENT_MODULES must be a literal list of strings")
        return value
    raise ValueError("run_all.py does not define EXPERIMENT_MODULES")


def has_top_level_run(path: pathlib.Path) -> bool:
    tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    return any(
        isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef))
        and statement.name == "run"
        for statement in tree.body
    )


def registry_issues(base: pathlib.Path = BASE, runner: pathlib.Path = RUNNER) -> list[str]:
    try:
        modules = declared_modules(runner)
    except (OSError, SyntaxError, ValueError) as error:
        return [str(error)]

    issues: list[str] = []
    duplicates = sorted({module for module in modules if modules.count(module) > 1})
    if duplicates:
        issues.append("duplicate registered modules: " + ", ".join(duplicates))

    registered = set(modules)
    programs = {
        path.stem
        for path in base.glob("*.py")
        if path.stem not in NON_EXPERIMENT_MODULES
    }
    missing = sorted(registered - programs)
    unregistered = sorted(programs - registered)
    if missing:
        issues.append("registered modules without source: " + ", ".join(missing))
    if unregistered:
        issues.append("unregistered Base programs: " + ", ".join(unregistered))

    for module in sorted(registered & programs):
        path = base / f"{module}.py"
        try:
            has_run = has_top_level_run(path)
        except (OSError, SyntaxError) as error:
            issues.append(f"{module}: {error}")
            continue
        if not has_run:
            issues.append(f"{module}: missing top-level run()")
    return issues


def execution_issues(root: pathlib.Path = ROOT) -> list[str]:
    result = subprocess.run(
        [sys.executable, str(root / "Experiments" / "Base" / "run_all.py")],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        return ["Base suite failed:\n" + result.stdout.strip()]
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        return [f"Base suite did not emit JSON: {error}"]

    issues: list[str] = []
    modules = declared_modules(root / "Experiments" / "Base" / "run_all.py")
    results = report.get("results")
    if report.get("status") != "passed":
        issues.append("Base suite status is not passed")
    if report.get("experiment_count") != len(modules):
        issues.append("Base suite experiment_count does not match the registry")
    if not isinstance(results, list):
        issues.append("Base suite results must be a list")
        return issues
    identifiers = [entry.get("experiment") for entry in results if isinstance(entry, dict)]
    if len(identifiers) != len(modules):
        issues.append("Base suite result count does not match the registry")
    if len(set(identifiers)) != len(identifiers):
        issues.append("Base suite experiment identifiers are not unique")
    invalid = sorted(
        str(identifier)
        for identifier in identifiers
        if not isinstance(identifier, str)
        or len(identifier) < 2
        or identifier[0] != "E"
        or not identifier[1:].isdigit()
    )
    if invalid:
        issues.append("invalid experiment identifiers: " + ", ".join(invalid))
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--execute",
        action="store_true",
        help="also execute every registered experiment through run_all.py",
    )
    args = parser.parse_args()

    issues = registry_issues()
    if args.execute and not issues:
        issues.extend(execution_issues())
    if issues:
        print("Experiment registry check failed:", file=sys.stderr)
        print(*issues, sep="\n", file=sys.stderr)
        return 1
    mode = "source and execution" if args.execute else "source"
    print(f"Experiment registry {mode} check passed ({len(declared_modules())} programs).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
