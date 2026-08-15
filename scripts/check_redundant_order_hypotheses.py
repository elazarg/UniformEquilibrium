#!/usr/bin/env python3
"""Inventory duplicate strict and weak order hypotheses in Lean declarations.

The check recognizes simple endpoint comparisons in a declaration telescope.
If the same declaration assumes both ``a < b`` and ``a ≤ b`` (including the
equivalent ``>``/``≥`` spellings), the weak proof is redundant: the strict
proof supplies it via ``.le``.  Terms are deliberately restricted to local
identifiers and numeric literals, keeping this a deterministic narrow census
rather than a heuristic Lean parser.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from dataclasses import asdict, dataclass
from typing import Sequence

try:
    from scripts.check_reward_bounds import (
        ROOT,
        _binders,
        _declaration_signatures,
        _project_lean_files,
    )
except ModuleNotFoundError:  # Direct execution.
    from check_reward_bounds import (
        ROOT,
        _binders,
        _declaration_signatures,
        _project_lean_files,
    )


_IDENTIFIER = r"[A-Za-z_\u0080-\U0010ffff][\w?!'\u0080-\U0010ffff]*"
_NUMBER = r"(?:0|[1-9][0-9]*)"
_TERM = rf"(?:{_IDENTIFIER}|{_NUMBER})"
_COMPARISON_RE = re.compile(rf"^({_TERM})\s*(<|≤|>|≥)\s*({_TERM})$")


@dataclass(frozen=True)
class RedundantOrderHypothesis:
    path: str
    line: int
    kind: str
    name: str
    left: str
    right: str
    strict_hypothesis: str
    weak_hypothesis: str


def _normalize_comparison(text: str) -> tuple[str, str, bool] | None:
    """Return ``(left, right, strict)`` with ``>`` relations reoriented."""

    match = _COMPARISON_RE.fullmatch(" ".join(text.split()))
    if match is None:
        return None
    left, relation, right = match.groups()
    if relation in {">", "≥"}:
        left, right = right, left
    return left, right, relation in {"<", ">"}


def _hypothesis_names(chunk: str) -> tuple[list[str], str] | None:
    names, separator, binder_type = chunk[1:-1].partition(":")
    if not separator:
        return None
    parsed_names = names.split()
    if not parsed_names:
        return None
    return parsed_names, binder_type.strip()


def inventory(root: pathlib.Path = ROOT) -> list[RedundantOrderHypothesis]:
    root = root.resolve()
    redundant: list[RedundantOrderHypothesis] = []
    for path in _project_lean_files(root):
        for signature in _declaration_signatures(path):
            strict: dict[tuple[str, str], list[str]] = {}
            weak: dict[tuple[str, str], list[str]] = {}
            for _start, _end, chunk in _binders(signature.text):
                parsed = _hypothesis_names(chunk)
                if parsed is None:
                    continue
                names, binder_type = parsed
                comparison = _normalize_comparison(binder_type)
                if comparison is None:
                    continue
                left, right, is_strict = comparison
                destination = strict if is_strict else weak
                destination.setdefault((left, right), []).extend(names)
            for relation in sorted(strict.keys() & weak.keys()):
                left, right = relation
                strict_name = strict[relation][0]
                redundant.extend(
                    RedundantOrderHypothesis(
                        path=str(path.relative_to(root)),
                        line=signature.line,
                        kind=signature.kind,
                        name=signature.name,
                        left=left,
                        right=right,
                        strict_hypothesis=strict_name,
                        weak_hypothesis=weak_name,
                    )
                    for weak_name in weak[relation]
                )
    return sorted(
        redundant,
        key=lambda item: (
            item.path,
            item.line,
            item.name,
            item.left,
            item.right,
            item.weak_hypothesis,
        ),
    )


def report(root: pathlib.Path = ROOT) -> dict[str, object]:
    hypotheses = inventory(root)
    return {
        "schema_version": 1,
        "summary": {
            "hypothesis_count": len(hypotheses),
            "declaration_count": len(
                {(item.path, item.line, item.name) for item in hypotheses}
            ),
            "files": len({item.path for item in hypotheses}),
        },
        "hypotheses": [asdict(item) for item in hypotheses],
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=pathlib.Path, default=ROOT)
    parser.add_argument("--format", choices=("json", "text"), default="json")
    parser.add_argument("--check", action="store_true")
    parser.add_argument(
        "--max-hypotheses",
        type=int,
        default=0,
        help="maximum redundant weak hypotheses accepted in --check mode",
    )
    args = parser.parse_args(argv)
    if args.max_hypotheses < 0:
        parser.error("--max-hypotheses must be nonnegative")
    result = report(args.root)
    if args.format == "json":
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(json.dumps(result["summary"], sort_keys=True))
        for item in result["hypotheses"]:
            print(
                f"{item['path']}:{item['line']}: {item['kind']} {item['name']} "
                f"[{item['strict_hypothesis']} ⇒ {item['weak_hypothesis']}]"
            )
    count = result["summary"]["hypothesis_count"]
    if args.check and count > args.max_hypotheses:
        print(
            "Redundant order-hypothesis ratchet failed: "
            f"{count} hypotheses exceed --max-hypotheses={args.max_hypotheses}.",
            file=sys.stderr,
        )
        for item in result["hypotheses"]:
            print(
                f"{item['path']}:{item['line']}: {item['kind']} {item['name']} "
                f"[{item['strict_hypothesis']} ⇒ {item['weak_hypothesis']}]",
                file=sys.stderr,
            )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
