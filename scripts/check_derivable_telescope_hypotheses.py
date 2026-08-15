#!/usr/bin/env python3
"""Reject narrow explicit telescope hypotheses supplied by retained data.

The check recognizes three deterministic schemas:

* ``[Fintype α]`` supplies ``[Finite α]`` for the same syntactic type;
* ``x ∈ collection`` supplies ``collection.Nonempty``; and
* an equality supplies a duplicate simple endpoint comparison, either by
  transporting an existing comparison or by reducing it to numeral
  arithmetic.

Only binders written on the declaration are inspected; section variables and
``include`` commands require elaborator-backed review.  This is deliberately
not a claim that every declaration telescope is logically minimal.  It is a
zero-baseline ratchet for explicit schemas whose derivation does not depend on
the proof body.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from dataclasses import asdict, dataclass
from typing import Iterable, Sequence

try:
    from scripts.check_reward_bounds import (
        ROOT,
        _balanced_end,
        _binders,
        _declaration_signatures,
        _project_lean_files,
    )
except ModuleNotFoundError:  # Direct execution.
    from check_reward_bounds import (
        ROOT,
        _balanced_end,
        _binders,
        _declaration_signatures,
        _project_lean_files,
    )


_IDENTIFIER = r"[A-Za-z_\u0080-\U0010ffff][\w?!'\u0080-\U0010ffff]*"
_QUALIFIED_IDENTIFIER = rf"{_IDENTIFIER}(?:\.{_IDENTIFIER})*"
_NUMBER = r"(?:0|[1-9][0-9]*)"
_TERM = rf"(?:{_IDENTIFIER}|{_NUMBER})"
_COMPARISON_RE = re.compile(rf"^({_TERM})\s*(<|≤|>|≥)\s*({_TERM})$")
_EQUALITY_RE = re.compile(rf"^({_TERM})\s*=\s*({_TERM})$")
_MEMBERSHIP_RE = re.compile(
    rf"^({_IDENTIFIER})\s*∈\s*({_QUALIFIED_IDENTIFIER})$"
)
_NONEMPTY_RE = re.compile(rf"^({_QUALIFIED_IDENTIFIER})\.Nonempty$")


@dataclass(frozen=True)
class DerivableTelescopeHypothesis:
    path: str
    line: int
    kind: str
    name: str
    category: str
    source: str
    redundant: str


def _all_telescope_chunks(signature: str) -> Iterable[str]:
    """Yield every balanced top-level telescope chunk, including instances."""

    index = 0
    while index < len(signature):
        character = signature[index]
        if character == ":":
            return
        if character in "([{⦃":
            end = _balanced_end(signature, index, character)
            yield signature[index : end + 1]
            index = end + 1
        else:
            index += 1


def _instance_class(chunk: str) -> tuple[str, str] | None:
    if not chunk.startswith("["):
        return None
    inner = chunk[1:-1].strip()
    if ":" in inner:
        _name, inner = inner.split(":", 1)
        inner = inner.strip()
    class_name, separator, argument = inner.partition(" ")
    if not separator or class_name not in {"Finite", "Fintype"}:
        return None
    return class_name, " ".join(argument.split())


def _named_hypotheses(signature: str) -> list[tuple[str, str]]:
    hypotheses: list[tuple[str, str]] = []
    for _start, _end, chunk in _binders(signature):
        names, separator, proposition = chunk[1:-1].partition(":")
        if not separator:
            continue
        normalized = " ".join(proposition.split())
        hypotheses.extend((name, normalized) for name in names.split())
    return hypotheses


def _binder_types(hypotheses: list[tuple[str, str]]) -> dict[str, str]:
    return {name: binder_type for name, binder_type in hypotheses}


def _is_real_term(term: str, binder_types: dict[str, str]) -> bool:
    return term.isdecimal() or binder_types.get(term) in {"Real", "ℝ"}


def _is_explicit_finset(
    collection: str, binder_types: dict[str, str]
) -> bool:
    binder_type = binder_types.get(collection, "")
    return bool(re.fullmatch(r"Finset\s+.+", binder_type))


def _normalize_comparison(
    left: str, relation: str, right: str
) -> tuple[str, str, str]:
    if relation in {">", "≥"}:
        left, right = right, left
        relation = "<" if relation == ">" else "≤"
    return left, relation, right


def _numeric_comparison_is_true(
    left: str, relation: str, right: str
) -> bool:
    if not left.isdecimal() or not right.isdecimal():
        return False
    first = int(left)
    second = int(right)
    return first < second if relation == "<" else first <= second


def _equality_redundancies(
    hypotheses: list[tuple[str, str]],
    binder_types: dict[str, str],
) -> Iterable[tuple[str, str, str]]:
    comparisons: list[tuple[str, str, str, str]] = []
    equalities: list[tuple[str, str, str]] = []
    for name, proposition in hypotheses:
        comparison = _COMPARISON_RE.fullmatch(proposition)
        if comparison is not None and all(
            _is_real_term(term, binder_types)
            for term in (comparison.group(1), comparison.group(3))
        ):
            comparisons.append(
                (name, *_normalize_comparison(*comparison.groups()))
            )
        equality = _EQUALITY_RE.fullmatch(proposition)
        if equality is not None and all(
            _is_real_term(term, binder_types) for term in equality.groups()
        ):
            equalities.append((name, *equality.groups()))

    comparison_facts = {
        (left, relation, right): name
        for name, left, relation, right in comparisons
    }
    for equality_name, left, right in equalities:
        if re.fullmatch(_IDENTIFIER, left) and re.fullmatch(_NUMBER, right):
            source, target = left, right
        elif re.fullmatch(_NUMBER, left) and re.fullmatch(_IDENTIFIER, right):
            source, target = right, left
        elif re.fullmatch(_IDENTIFIER, left) and re.fullmatch(
            _IDENTIFIER, right
        ):
            source, target = right, left
        else:
            continue
        for comparison_name, first, relation, second in comparisons:
            if source not in {first, second}:
                continue
            rewritten = (
                target if first == source else first,
                relation,
                target if second == source else second,
            )
            if _numeric_comparison_is_true(*rewritten):
                yield equality_name, comparison_name, "numeral endpoint"
            elif rewritten in comparison_facts:
                source_name = comparison_facts[rewritten]
                if source_name != comparison_name:
                    yield (
                        f"{equality_name}, {source_name}",
                        comparison_name,
                        "equality transport",
                    )


def inventory(
    root: pathlib.Path = ROOT,
) -> list[DerivableTelescopeHypothesis]:
    root = root.resolve()
    findings: list[DerivableTelescopeHypothesis] = []
    for path in _project_lean_files(root):
        for signature in _declaration_signatures(path):
            relative = str(path.relative_to(root))
            instances: dict[str, set[str]] = {"Finite": set(), "Fintype": set()}
            for chunk in _all_telescope_chunks(signature.text):
                parsed = _instance_class(chunk)
                if parsed is not None:
                    class_name, argument = parsed
                    instances[class_name].add(argument)
            for argument in sorted(instances["Finite"] & instances["Fintype"]):
                findings.append(
                    DerivableTelescopeHypothesis(
                        path=relative,
                        line=signature.line,
                        kind=signature.kind,
                        name=signature.name,
                        category="fintype_supplies_finite",
                        source=f"[Fintype {argument}]",
                        redundant=f"[Finite {argument}]",
                    )
                )

            hypotheses = _named_hypotheses(signature.text)
            binder_types = _binder_types(hypotheses)
            memberships: dict[str, list[str]] = {}
            nonempty: dict[str, list[str]] = {}
            for hypothesis_name, proposition in hypotheses:
                membership = _MEMBERSHIP_RE.fullmatch(proposition)
                if membership is not None:
                    _element, collection = membership.groups()
                    if _is_explicit_finset(collection, binder_types):
                        memberships.setdefault(collection, []).append(
                            hypothesis_name
                        )
                nonempty_match = _NONEMPTY_RE.fullmatch(proposition)
                if nonempty_match is not None:
                    nonempty.setdefault(nonempty_match.group(1), []).append(
                        hypothesis_name
                    )
            for collection in sorted(memberships.keys() & nonempty.keys()):
                source = memberships[collection][0]
                for redundant in nonempty[collection]:
                    findings.append(
                        DerivableTelescopeHypothesis(
                            path=relative,
                            line=signature.line,
                            kind=signature.kind,
                            name=signature.name,
                            category="membership_supplies_nonempty",
                            source=source,
                            redundant=redundant,
                        )
                    )

            for source, redundant, detail in _equality_redundancies(
                hypotheses, binder_types
            ):
                findings.append(
                    DerivableTelescopeHypothesis(
                        path=relative,
                        line=signature.line,
                        kind=signature.kind,
                        name=signature.name,
                        category=f"equality_supplies_bound:{detail}",
                        source=source,
                        redundant=redundant,
                    )
                )
    return sorted(
        findings,
        key=lambda item: (
            item.path,
            item.line,
            item.name,
            item.category,
            item.redundant,
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
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--max-hypotheses", type=int, default=0)
    args = parser.parse_args(argv)
    if args.max_hypotheses < 0:
        parser.error("--max-hypotheses must be nonnegative")
    result = report(args.root)
    print(json.dumps(result, indent=2, sort_keys=True))
    count = result["summary"]["hypothesis_count"]
    if args.check and count > args.max_hypotheses:
        print(
            "Derivable telescope-hypothesis ratchet failed: "
            f"{count} hypotheses exceed --max-hypotheses="
            f"{args.max_hypotheses}.",
            file=sys.stderr,
        )
        for item in result["hypotheses"]:
            print(
                f"{item['path']}:{item['line']}: {item['kind']} "
                f"{item['name']} [{item['source']} ⇒ "
                f"{item['redundant']}]",
                file=sys.stderr,
            )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
