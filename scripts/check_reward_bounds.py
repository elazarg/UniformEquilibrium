#!/usr/bin/env python3
"""Inventory quitting declarations carrying a coordinate reward bound.

This is a reporting census, not a failing lint.  It recognizes the narrow
quitting schema consisting of a real bound variable (``M``, ``B``, or ``C``),
a nonnegative hypothesis for that variable, and a coordinatewise hypothesis
bounding ``reward`` by it.  The corrected classification checks every later
binder type as well as the final result.  This matters because a theorem can
omit the bound from its result while still using it in a later hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import sys
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

try:
    from scripts.check_proof_duplicates import (
        DECLARATION_RE,
        TOP_LEVEL_COMMAND_RE,
        _body_assignment_offset,
        _body_equation_offset,
    )
    from scripts.check_trust import strip_comments_and_strings
except ModuleNotFoundError:  # Direct execution.
    from check_proof_duplicates import (
        DECLARATION_RE,
        TOP_LEVEL_COMMAND_RE,
        _body_assignment_offset,
        _body_equation_offset,
    )
    from check_trust import strip_comments_and_strings


ROOT = pathlib.Path(__file__).resolve().parents[1]
PRUNED_DIRECTORIES = {".git", ".lake", "GameTheory", "__pycache__", ".pytest_cache"}
BOUND_VARIABLES = ("M", "B", "C")
# Python's ``\b`` treats ``M'`` as ending at ``M``.  Account for Lean's
# apostrophe/non-ASCII identifier continuations (and qualified names).
_IDENTIFIER_CONTINUATION = r"\w?!'\u0080-\U0010ffff"
_IDENTIFIER_TOKEN_BOUNDARY = _IDENTIFIER_CONTINUATION + "."


@dataclass(frozen=True)
class RewardBoundDeclaration:
    """One declaration carrying a strict reward-bound hypothesis triple."""

    path: str
    line: int
    kind: str
    name: str
    bound_variable: str
    result_uses_bound: bool
    later_telescope_uses_bound: bool

    @property
    def report_style_classification(self) -> str:
        return "later-use" if self.result_uses_bound else "removable"

    @property
    def corrected_classification(self) -> str:
        return "later-use" if self.later_telescope_uses_bound else "removable"


@dataclass(frozen=True)
class _Signature:
    path: pathlib.Path
    line: int
    kind: str
    name: str
    text: str


def _balanced_end(text: str, start: int, opener: str = "(") -> int:
    """Return the matching delimiter, or the end of text if malformed."""

    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closer = pairs[opener]
    depth = 0
    for index in range(start, len(text)):
        if text[index] == opener:
            depth += 1
        elif text[index] == closer:
            depth -= 1
            if depth == 0:
                return index
    return len(text) - 1


def _binders(signature: str) -> Iterable[tuple[int, int, str]]:
    """Yield top-level telescope binders before the result separator."""

    index = 0
    while index < len(signature):
        character = signature[index]
        if character == ":":
            return
        if character in "([{⦃":
            end = _balanced_end(signature, index, character)
            if character != "[":
                yield index, end, signature[index : end + 1]
            index = end + 1
        else:
            index += 1


def _parenthesized_binders(signature: str) -> Iterable[tuple[int, int, str]]:
    """Yield balanced ``(...)`` chunks from a cleaned declaration signature."""

    return (
        (start, end, chunk)
        for start, end, chunk in _binders(signature)
        if chunk.startswith("(")
    )


def _hypothesis_binders(signature: str) -> Iterable[tuple[int, int, str]]:
    """Yield explicit, implicit, and strict-implicit binder chunks."""

    return _binders(signature)


def _identifier_boundary(identifier: str) -> str:
    """Match one exact local identifier, including apostrophe edge cases."""

    return (
        rf"(?<![{_IDENTIFIER_TOKEN_BOUNDARY}]){re.escape(identifier)}"
        rf"(?![{_IDENTIFIER_TOKEN_BOUNDARY}])"
    )


def _bound_binder(signature: str, variable: str) -> bool:
    return bool(_bound_binders(signature, variable))


def _bound_binders(signature: str, variable: str) -> list[tuple[int, int]]:
    matches: list[tuple[int, int]] = []
    for start, end, chunk in _binders(signature):
        names, separator, binder_type = chunk[1:-1].partition(":")
        if not separator or binder_type.strip() not in {"ℝ", "Real"}:
            continue
        if variable in names.split():
            matches.append((start, end))
    return matches


def _nonnegative_binders(
    signature: str, variable: str
) -> list[tuple[int, int]]:
    pattern = re.compile(
        rf"(?<![{_IDENTIFIER_CONTINUATION}])h"
        rf"[{_IDENTIFIER_CONTINUATION}]*\s*:\s*0\s*≤\s*"
        rf"{_identifier_boundary(variable)}"
    )
    return [
        (start, end)
        for start, end, chunk in _hypothesis_binders(signature)
        if pattern.search(chunk[1:-1])
    ]


def _reward_binders(signature: str, variable: str) -> list[tuple[int, int]]:
    """Find binders of the form ``(hreward : ∀ ..., |reward ...| ≤ M)``."""

    bound = re.compile(
        rf"\|[^|\n]*{_identifier_boundary('reward')}[^|\n]*"
        rf"\|\s*≤\s*{_identifier_boundary(variable)}"
    )
    return [
        (start, end)
        for start, end, chunk in _hypothesis_binders(signature)
        if re.search(
            rf"(?<![{_IDENTIFIER_CONTINUATION}])h"
            rf"[{_IDENTIFIER_CONTINUATION}]*\s*:\s*",
            chunk[1:-1],
        )
        and "∀" in chunk
        and bound.search(chunk[1:-1])
    ]


def _top_level_colons(signature: str) -> list[int]:
    depth = {"(": 0, "[": 0, "{": 0, "⦃": 0}
    closing = {")": "(", "]": "[", "}": "{", "⦄": "⦃"
    }
    colons: list[int] = []
    for index, character in enumerate(signature):
        if character in depth:
            depth[character] += 1
        elif character in closing:
            depth[closing[character]] = max(0, depth[closing[character]] - 1)
        elif character == ":" and not any(depth.values()):
            colons.append(index)
    return colons


def _declaration_signatures(path: pathlib.Path) -> list[_Signature]:
    """Extract declaration signatures, including term/equation declarations."""

    source = path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(source)
    starts = list(DECLARATION_RE.finditer(clean))
    commands = list(TOP_LEVEL_COMMAND_RE.finditer(clean))
    signatures: list[_Signature] = []
    for match in starts:
        end = len(clean)
        for command in commands:
            if command.start() >= match.end():
                end = command.start()
                break
        declaration = clean[match.start() : end]
        body_offset = _body_assignment_offset(declaration)
        if body_offset is None:
            body_offset = _body_equation_offset(declaration)
        if body_offset is None:
            continue
        # ``_body_assignment_offset`` points just after ``:=``; keep the
        # assignment token out of the telescope so its colon is not mistaken
        # for the result-type colon below.
        signature_end = (
            body_offset - 2
            if declaration[body_offset - 2 : body_offset] == ":="
            else body_offset
        )
        signatures.append(
            _Signature(
                path=path,
                line=clean.count("\n", 0, match.start("kind")) + 1,
                kind=match.group("kind"),
                name=match.group("name"),
                text=declaration[:signature_end],
            )
        )
    return signatures


def _project_lean_files(root: pathlib.Path) -> list[pathlib.Path]:
    files: list[pathlib.Path] = []
    for directory, names, filenames in os.walk(root):
        names[:] = [name for name in names if name not in PRUNED_DIRECTORIES]
        base = pathlib.Path(directory)
        files.extend(base / name for name in filenames if name.endswith(".lean"))
    return sorted(files)


def inventory(root: pathlib.Path = ROOT) -> list[RewardBoundDeclaration]:
    """Return a deterministic inventory of strict reward-bound declarations."""

    root = root.resolve()
    declarations: list[RewardBoundDeclaration] = []
    for path in _project_lean_files(root):
        try:
            signatures = _declaration_signatures(path)
        except (FileNotFoundError, UnicodeDecodeError):
            continue
        for signature in signatures:
            for variable in BOUND_VARIABLES:
                if not _bound_binder(signature.text, variable):
                    continue
                nonnegative = _nonnegative_binders(signature.text, variable)
                rewards = _reward_binders(signature.text, variable)
                if not nonnegative or not rewards:
                    continue
                bound_binders = _bound_binders(signature.text, variable)
                if not bound_binders:
                    continue
                bound_end = max(end for _, end in bound_binders)
                consumed_spans = [
                    (start, end)
                    for start, end in (*bound_binders, *nonnegative, *rewards)
                    if start > bound_end
                ]
                retained = signature.text[bound_end + 1 :]
                for start, end in sorted(consumed_spans, reverse=True):
                    if start < bound_end:
                        continue
                    relative_start = start - bound_end - 1
                    relative_end = end - bound_end
                    retained = (
                        retained[:relative_start]
                        + retained[relative_end:]
                    )
                colons = _top_level_colons(signature.text)
                result = signature.text[colons[0] + 1 :] if colons else ""
                declarations.append(
                    RewardBoundDeclaration(
                        path=str(path.relative_to(root)),
                        line=signature.line,
                        kind=signature.kind,
                        name=signature.name,
                        bound_variable=variable,
                        result_uses_bound=bool(
                            re.search(_identifier_boundary(variable), result)
                        ),
                        later_telescope_uses_bound=bool(
                            re.search(_identifier_boundary(variable), retained)
                        ),
                    )
                )
    return sorted(
        declarations,
        key=lambda declaration: (
            declaration.path,
            declaration.line,
            declaration.name,
            declaration.bound_variable,
        ),
    )


def report(root: pathlib.Path = ROOT) -> dict[str, object]:
    declarations = inventory(root)
    corrected_removable = sum(
        declaration.corrected_classification == "removable"
        for declaration in declarations
    )
    report_style_removable = sum(
        declaration.report_style_classification == "removable"
        for declaration in declarations
    )
    return {
        "schema_version": 1,
        "summary": {
            "candidate_count": len(declarations),
            "files": len({declaration.path for declaration in declarations}),
            "report_style_removable": report_style_removable,
            "report_style_later_use": len(declarations) - report_style_removable,
            "corrected_removable": corrected_removable,
            "corrected_later_use": len(declarations) - corrected_removable,
            "report_style_false_positive": sum(
                declaration.report_style_classification == "removable"
                and declaration.corrected_classification == "later-use"
                for declaration in declarations
            ),
        },
        "declarations": [
            {
                **asdict(declaration),
                "report_style_classification": declaration.report_style_classification,
                "corrected_classification": declaration.corrected_classification,
            }
            for declaration in declarations
        ],
    }


def _corrected_removable(result: dict[str, object]) -> list[dict[str, object]]:
    declarations = result["declarations"]
    assert isinstance(declarations, list)
    return [
        declaration
        for declaration in declarations
        if declaration["corrected_classification"] == "removable"
    ]


def _check_diagnostics(
    result: dict[str, object], max_removable: int
) -> list[str]:
    removable = _corrected_removable(result)
    if len(removable) <= max_removable:
        return []
    diagnostics = [
        "Reward-bound ratchet failed: "
        f"{len(removable)} corrected-removable declarations exceed "
        f"--max-removable={max_removable}."
    ]
    diagnostics.extend(
        f"{declaration['path']}:{declaration['line']}: "
        f"{declaration['kind']} {declaration['name']} "
        f"[{declaration['bound_variable']}]"
        for declaration in removable
    )
    return diagnostics


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if corrected-removable declarations exceed the limit",
    )
    parser.add_argument(
        "--max-removable",
        type=int,
        default=None,
        help="corrected-removable limit in --check mode (default: 0)",
    )
    args = parser.parse_args(argv)
    if args.max_removable is not None and args.max_removable < 0:
        parser.error("--max-removable must be nonnegative")
    result = report(args.root)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(json.dumps(result["summary"], sort_keys=True))
        for declaration in result["declarations"]:
            print(
                f"{declaration['path']}:{declaration['line']}: "
                f"{declaration['kind']} {declaration['name']} "
                f"[{declaration['bound_variable']}] "
                f"report={declaration['report_style_classification']} "
                f"corrected={declaration['corrected_classification']}"
            )
    if args.check:
        limit = 0 if args.max_removable is None else args.max_removable
        diagnostics = _check_diagnostics(result, limit)
        if diagnostics:
            print(*diagnostics, sep="\n", file=sys.stderr)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
