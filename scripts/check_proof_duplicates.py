#!/usr/bin/env python3
"""Reject long, exact proof-body copies from canonical Lean into Research.

This is a deliberately narrow maintenance ratchet.  It does not try to decide
whether two theorems are mathematically equivalent, alpha-equivalent, or good
abstractions.  It finds long assignment- or equation-style declaration bodies
that are textually identical after comments are removed and whitespace is
normalized.  String and character literals remain significant.  Cross-lane
matches are then ownership defects: Research should import the maintained
MathUE or UniformEquilibrium declaration and retain only its genuine residual
delta.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Sequence

try:
    from scripts.check_trust import is_identifier_continuation, strip_comments_and_strings
except ModuleNotFoundError:  # Direct execution.
    from check_trust import is_identifier_continuation, strip_comments_and_strings


ROOT = pathlib.Path(__file__).resolve().parents[1]
RESEARCH_LANE = "Research"
CANONICAL_LANES = ("MathUE", "UniformEquilibrium")
MIN_BODY_CHARS = 250

DECLARATION_RE = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable)\s+)*"
    r"(?P<kind>def|theorem|lemma|abbrev|opaque)\s+"
    r"(?P<name>(?:[^\W\d][\w'.!?]*|«[^»\n]+»))",
    re.MULTILINE,
)
TOP_LEVEL_COMMAND_RE = re.compile(
    r"^(?:@\[|"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(?:def|theorem|lemma|abbrev|opaque|structure|class|instance|inductive|"
    r"namespace|section|end|variable|include|omit|open|attribute|local|scoped|"
    r"macro|syntax|elab|example|axiom|import|universe|export|notation|infix|"
    r"infixl|infixr|prefix|postfix|mutual|initialize|builtin_initialize|"
    r"register_option|declare_syntax_cat|set_option)\b|#)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class DeclarationBody:
    """One normalized top-level Lean declaration body."""

    path: pathlib.Path
    line: int
    kind: str
    name: str
    normalized_body: str


def _body_assignment_offset(declaration: str) -> int | None:
    """Locate the depth-zero ``:=`` introducing a declaration body.

    A declaration result may itself start with a chain of ``let`` bindings.
    Their assignment tokens are also at delimiter depth zero, but they belong
    to the result rather than the declaration body.  Track those bindings so
    the scanner reaches the assignment after the complete result expression.
    """

    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    closers = set(pairs.values())
    stack: list[str] = []
    in_result = False
    pending_result_lets = 0
    index = 0
    while index + 1 < len(declaration):
        character = declaration[index]
        if character in pairs:
            stack.append(pairs[character])
        elif character in closers:
            if stack and stack[-1] == character:
                stack.pop()
        elif not stack:
            if declaration[index : index + 2] == ":=":
                if not in_result:
                    return index + 2
                if pending_result_lets:
                    pending_result_lets -= 1
                    index += 2
                    continue
                return index + 2
            if character == ":":
                in_result = True
            elif (
                in_result
                and declaration.startswith("let", index)
                and not is_identifier_continuation(
                    declaration[index - 1] if index else ""
                )
                and not is_identifier_continuation(
                    declaration[index + 3]
                    if index + 3 < len(declaration)
                    else ""
                )
            ):
                pending_result_lets += 1
                index += 3
                continue
        index += 1
    return None


def _body_equation_offset(declaration: str) -> int | None:
    """Locate the first equation clause of a declaration without ``:=``."""

    match = re.search(r"^[ \t]*\|", declaration, re.MULTILINE)
    return match.start() if match is not None else None


def _strip_comments_preserving_literals(text: str) -> str:
    """Blank nested Lean comments without erasing string or character data."""

    output: list[str] = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    in_char = False

    while index < len(text):
        character = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""

        if in_line_comment:
            if character == "\n":
                in_line_comment = False
                output.append(character)
            else:
                output.append(" ")
            index += 1
            continue

        if block_depth:
            if character == "/" and following == "-":
                block_depth += 1
                output.extend("  ")
                index += 2
            elif character == "-" and following == "/":
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if character == "\n" else " ")
                index += 1
            continue

        if in_string:
            output.append(character)
            if character == "\\" and following:
                output.append(following)
                index += 2
            else:
                if character == '"':
                    in_string = False
                index += 1
            continue

        if in_char:
            output.append(character)
            if character == "\\" and following:
                output.append(following)
                index += 2
            else:
                if character == "'":
                    in_char = False
                index += 1
            continue

        if character == "-" and following == "-":
            in_line_comment = True
            output.extend("  ")
            index += 2
        elif character == "/" and following == "-":
            block_depth = 1
            output.extend("  ")
            index += 2
        elif character == '"':
            in_string = True
            output.append(character)
            index += 1
        elif character == "'" and not (
            index > 0 and is_identifier_continuation(text[index - 1])
        ):
            in_char = True
            output.append(character)
            index += 1
        else:
            # Lean accepts both arrows for lambda syntax.  Normalize the token
            # here, while the scanner knows that it is outside a literal.
            output.append("=>" if character == "↦" else character)
            index += 1

    return "".join(output)


def _normalize_body(body: str) -> str:
    """Normalize layout without merging distinct Lean token streams."""

    commentless = _strip_comments_preserving_literals(body)
    output: list[str] = []
    index = 0
    pending_space = False
    in_string = False
    in_char = False
    while index < len(commentless):
        character = commentless[index]
        following = commentless[index + 1] if index + 1 < len(commentless) else ""

        if in_string or in_char:
            output.append(character)
            if character == "\\" and following:
                output.append(following)
                index += 2
            else:
                if (in_string and character == '"') or (
                    in_char and character == "'"
                ):
                    in_string = False
                    in_char = False
                index += 1
            continue

        if character.isspace():
            pending_space = True
            index += 1
            continue
        if pending_space and output:
            output.append(" ")
        pending_space = False
        if character == '"':
            in_string = True
        elif character == "'" and not (
            index > 0 and is_identifier_continuation(commentless[index - 1])
        ):
            in_char = True
        output.append(character)
        index += 1

    return "".join(output)


def declaration_bodies(path: pathlib.Path) -> list[DeclarationBody]:
    """Extract normalized assignment bodies from one Lean source file."""

    source = path.read_text(encoding="utf-8")
    clean = strip_comments_and_strings(source)
    starts = list(DECLARATION_RE.finditer(clean))
    commands = list(TOP_LEVEL_COMMAND_RE.finditer(clean))
    declarations: list[DeclarationBody] = []
    for match in starts:
        end = len(clean)
        for command in commands:
            # A declaration match may begin at a preceding one-line attribute.
            # Do not mistake the declaration command inside that same match for
            # the beginning of the next command.
            if command.start() >= match.end():
                end = command.start()
                break
        declaration = clean[match.start() : end]
        body_offset = _body_assignment_offset(declaration)
        if body_offset is None:
            body_offset = _body_equation_offset(declaration)
        if body_offset is None:
            continue
        body_start = match.start() + body_offset
        normalized = _normalize_body(source[body_start:end])
        if not normalized:
            continue
        declarations.append(
            DeclarationBody(
                path=path,
                line=clean.count("\n", 0, match.start("kind")) + 1,
                kind=match.group("kind"),
                name=match.group("name"),
                normalized_body=normalized,
            )
        )
    return declarations


def _lane_files(root: pathlib.Path, lane: str) -> list[pathlib.Path]:
    directory = root / lane
    if not directory.is_dir():
        return []
    return sorted(directory.rglob("*.lean"))


def duplicate_failures(
    root: pathlib.Path = ROOT, min_body_chars: int = MIN_BODY_CHARS
) -> list[str]:
    """Return diagnostics for long exact Research/canonical body matches."""

    root = root.resolve()
    canonical_by_body: dict[str, list[DeclarationBody]] = {}
    for lane in CANONICAL_LANES:
        for path in _lane_files(root, lane):
            try:
                declarations = declaration_bodies(path)
            except FileNotFoundError:
                # A concurrent, validated module move may race a local check.
                continue
            for declaration in declarations:
                if len(declaration.normalized_body) < min_body_chars:
                    continue
                canonical_by_body.setdefault(declaration.normalized_body, []).append(
                    declaration
                )

    failures: list[str] = []
    for path in _lane_files(root, RESEARCH_LANE):
        try:
            declarations = declaration_bodies(path)
        except FileNotFoundError:
            continue
        for research in declarations:
            if len(research.normalized_body) < min_body_chars:
                continue
            for canonical in canonical_by_body.get(research.normalized_body, []):
                failures.append(
                    f"{research.path}:{research.line}: Research {research.kind} "
                    f"{research.name} copies the {len(research.normalized_body)}-"
                    f"character body of {canonical.path}:{canonical.line} "
                    f"({canonical.kind} {canonical.name}); import and delegate to "
                    "the canonical owner or retain only a genuine Research delta"
                )
    return sorted(failures)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=ROOT,
        help="repository root (default: this repository)",
    )
    parser.add_argument(
        "--min-body-chars",
        type=int,
        default=MIN_BODY_CHARS,
        help=f"minimum normalized body length (default: {MIN_BODY_CHARS})",
    )
    args = parser.parse_args(argv)
    failures = duplicate_failures(args.root, args.min_body_chars)
    if failures:
        print("Lean cross-lane proof-duplicate check failed:", file=sys.stderr)
        print(*failures, sep="\n", file=sys.stderr)
        return 1
    print(
        "Lean cross-lane proof-duplicate check passed "
        f"(Research against {', '.join(CANONICAL_LANES)}; "
        f"minimum {args.min_body_chars} normalized characters)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
