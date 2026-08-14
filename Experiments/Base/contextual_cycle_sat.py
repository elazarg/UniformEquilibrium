"""E30: contextual cycle-safe selector synthesis contains 3-SAT.

A selector assigns one Boolean action to every context/variable.  Each clause
is represented by a length-three accounting cycle.  A true literal contributes
-3 and a false literal +1, so the cycle is nonpositive iff the clause is
satisfied.  Checking a selector is linear; finding one is exactly SAT.
"""

from __future__ import annotations

from itertools import combinations, product
import json


Literal = int
Clause = tuple[Literal, Literal, Literal]


def literal_true(literal: Literal, assignment: tuple[bool, ...]) -> bool:
    value = assignment[abs(literal) - 1]
    return value if literal > 0 else not value


def clause_cycle_weight(clause: Clause, assignment: tuple[bool, ...]) -> int:
    return sum(-3 if literal_true(literal, assignment) else 1 for literal in clause)


def satisfies(formula: tuple[Clause, ...], assignment: tuple[bool, ...]) -> bool:
    return all(any(literal_true(literal, assignment) for literal in clause) for clause in formula)


def cycle_safe(formula: tuple[Clause, ...], assignment: tuple[bool, ...]) -> bool:
    return all(clause_cycle_weight(clause, assignment) <= 0 for clause in formula)


def run() -> dict[str, object]:
    variables = 3
    clauses: list[Clause] = []
    for signs in product((-1, 1), repeat=variables):
        clauses.append(tuple(signs[index] * (index + 1) for index in range(variables)))

    assignments = list(product((False, True), repeat=variables))
    formulas_checked = 0
    for clause_count in range(len(clauses) + 1):
        for chosen in combinations(clauses, clause_count):
            formulas_checked += 1
            satisfying = [assignment for assignment in assignments if satisfies(chosen, assignment)]
            safe = [assignment for assignment in assignments if cycle_safe(chosen, assignment)]
            assert satisfying == safe

    all_clauses = tuple(clauses)
    assert not any(satisfies(all_clauses, assignment) for assignment in assignments)

    return {
        "experiment": "E30",
        "status": "passed",
        "variables": variables,
        "possible_clauses": len(clauses),
        "formulas_exhaustively_checked": formulas_checked,
        "selectors_per_formula": len(assignments),
        "unsatisfiable_full_formula_safe_selectors": 0,
        "conclusion": (
            "Selecting one action per public context so that every accounting cycle is nonpositive already expresses 3-SAT.  A proposed selector is checked in linear time, while unrestricted selector synthesis contains an NP-hard core."
        ),
        "limitation": (
            "This is a reduction to an abstract contextual cycle system, not a claim that the full uniform-equilibrium problem is NP-hard under a particular encoding."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
