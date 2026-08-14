#!/usr/bin/env python3
"""Reject proof escape hatches and global diagnostic weakening project-wide."""

from __future__ import annotations

import os
import pathlib
import re
import subprocess
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PRUNED_DIRECTORIES = {
    ".git",
    ".lake",
    ".pytest_cache",
    "GameTheory",
    "__pycache__",
}
TOKEN_PATTERNS = (
    (re.compile(r"\b(?:sorry|admit)\b"), "proof placeholder"),
    (
        re.compile(r"^\s*axioms?\s+", re.MULTILINE),
        "axiom declaration",
    ),
    (re.compile(r"^\s*set_option\b", re.MULTILINE), "set_option command"),
    (re.compile(r"\bnative_decide\b"), "axiom-backed native decision proof"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by escape hatch"),
    (re.compile(r"\bunsafe\b"), "unsafe declaration or command"),
    (re.compile(r"\bpartial\s+def\b"), "partial definition"),
)
CONFIG_PATTERNS = (
    (re.compile(r"`weak\.linter(?:\.|\b)"), "weak global linter option"),
    (re.compile(r"\bweakLeanArgs\b"), "weak global Lean arguments"),
    (
        re.compile(r"`linter(?:\.[A-Za-z0-9_]+)+\s*,\s*false\b"),
        "disabled global linter",
    ),
    (
        re.compile(r"`warningAsError\s*,\s*false\b"),
        "warnings-as-errors disabled",
    ),
    (
        re.compile(r"-D(?:weak\.)?linter(?:\.[A-Za-z0-9_]+)+=false\b"),
        "command-line linter disablement",
    ),
    (
        re.compile(r"-DwarningAsError=false\b"),
        "command-line warnings-as-errors disablement",
    ),
)
WARNING_AS_ERROR = re.compile(r"⟨\s*`warningAsError\s*,\s*true\s*⟩")
LEAN_LIBRARY_RE = re.compile(
    r"^lean_lib\s+([A-Za-z0-9_'.]+)\s+where\s*$", re.MULTILINE
)


def is_identifier_continuation(char: str) -> bool:
    """Return whether ``char`` can continue a Lean identifier.

    Lean permits one or more primes at the end of identifiers.  In
    particular, a prime following an identifier is not the opening quote of a
    character literal, so the scanner must distinguish those two uses.
    """
    return bool(char) and (
        char.isalnum()
        or char in {"_", "'", "?", "!"}
        or not char.isascii()
    )


def strip_comments_and_strings(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False

    while index < len(text):
        char = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""

        if in_line_comment:
            if char == "\n":
                in_line_comment = False
                output.append(char)
            else:
                output.append(" ")
            index += 1
            continue

        if block_depth:
            if char == "/" and following == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif char == "-" and following == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            if char == "\\" and following:
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                if char == '"':
                    in_string = False
                index += 1
            continue

        if in_char:
            if char == "\\" and following:
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                if char == "'":
                    in_char = False
                index += 1
            continue

        if char == "-" and following == "-":
            in_line_comment = True
            output.extend("  ")
            index += 2
        elif char == "/" and following == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif char == '"':
            in_string = True
            output.append(" ")
            index += 1
        elif char == "'" and not (
            index > 0 and is_identifier_continuation(text[index - 1])
        ):
            in_char = True
            output.append(" ")
            index += 1
        else:
            output.append(char)
            index += 1

    return "".join(output)


def project_files(suffix: str) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for directory, names, filenames in os.walk(ROOT):
        names[:] = [name for name in names if name not in PRUNED_DIRECTORIES]
        base = pathlib.Path(directory)
        files.extend(base / name for name in filenames if name.endswith(suffix))
    return sorted(files)


def lean_files() -> list[pathlib.Path]:
    return project_files(".lean")


def library_roots(lakefile: str) -> set[str]:
    return set(LEAN_LIBRARY_RE.findall(lakefile))


def token_failures(path: pathlib.Path, text: str) -> list[str]:
    clean = strip_comments_and_strings(text)
    failures: list[str] = []
    for pattern, label in TOKEN_PATTERNS:
        for match in pattern.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            failures.append(f"{path}:{line}: forbidden {label}")
    return failures


def check_global_configuration(failures: list[str]) -> None:
    paths = [ROOT / "lakefile.lean"]
    workflows = ROOT / ".github" / "workflows"
    if workflows.is_dir():
        paths.extend(workflows.glob("*.yml"))
        paths.extend(workflows.glob("*.yaml"))
    for path in sorted(paths):
        text = path.read_text(encoding="utf-8")
        for pattern, label in CONFIG_PATTERNS:
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: forbidden {label}"
                )
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    if not WARNING_AS_ERROR.search(strip_comments_and_strings(lakefile)):
        failures.append(
            "lakefile.lean: project libraries must set warningAsError to true"
        )
    libraries = list(LEAN_LIBRARY_RE.finditer(lakefile))
    for index, library in enumerate(libraries):
        end = libraries[index + 1].start() if index + 1 < len(libraries) else len(lakefile)
        body = lakefile[library.end():end]
        if "leanOptions := uniformEquilibriumLeanOptions" not in body:
            failures.append(
                f"lakefile.lean: lean_lib {library.group(1)} does not use the "
                "warnings-as-errors project options"
            )


def check_lean_ownership(files: list[pathlib.Path], failures: list[str]) -> None:
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    roots = library_roots(lakefile)
    exceptions = {pathlib.Path("lakefile.lean")}
    for path in files:
        relative = path.relative_to(ROOT)
        if relative in exceptions:
            continue
        root = relative.parts[0].removesuffix(".lean")
        if root not in roots:
            failures.append(
                f"{relative}: project Lean source is not owned by a lean_lib and "
                "cannot enter the compiled axiom audit"
            )


def check_generated_audit(failures: list[str]) -> None:
    result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "generate_axiom_audit.py"),
            "--check",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    if result.returncode:
        failures.append(result.stdout.strip())


def main() -> int:
    failures: list[str] = []
    files = lean_files()
    for path in files:
        failures.extend(
            token_failures(path.relative_to(ROOT), path.read_text(encoding="utf-8"))
        )
    check_lean_ownership(files, failures)
    check_global_configuration(failures)
    check_generated_audit(failures)

    if failures:
        print("Lean trust check failed:", file=sys.stderr)
        print(*failures, sep="\n", file=sys.stderr)
        return 1

    print(
        f"Lean trust check passed ({len(files)} project-owned Lean files; "
        "warnings-as-errors and exhaustive axiom audit configured)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
