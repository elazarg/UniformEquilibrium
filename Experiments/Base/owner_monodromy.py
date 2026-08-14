"""E06: owner custody as a cocycle and finite-cover monodromy.

An aggregate scalar edge charge may be a coboundary even when its decomposition
by strategic owner is not.  The typed charge is a vector-valued 1-cocycle.  Its
cycle sums are the custody holonomies.  Reducing them modulo m gives the deck
translation (monodromy) on a finite cover.
"""

from __future__ import annotations

import json
from fractions import Fraction
from typing import NamedTuple


class OwnedEdge(NamedTuple):
    source: str
    target: str
    owner: str
    charge: Fraction


def scalar_cycle_sum(cycle: list[OwnedEdge]) -> Fraction:
    return sum((edge.charge for edge in cycle), Fraction(0))


def typed_cycle_sum(cycle: list[OwnedEdge], owners: list[str]) -> tuple[Fraction, ...]:
    return tuple(
        sum((edge.charge for edge in cycle if edge.owner == owner), Fraction(0))
        for owner in owners
    )


def translate_sheet(
    sheet: tuple[int, ...], holonomy: tuple[Fraction, ...], modulus: int
) -> tuple[int, ...]:
    integral = []
    for value in holonomy:
        assert value.denominator == 1
        integral.append(value.numerator)
    return tuple((coordinate + increment) % modulus for coordinate, increment in zip(sheet, integral))


def monodromy_order(holonomy: tuple[Fraction, ...], modulus: int) -> int:
    sheet = tuple(0 for _ in holonomy)
    current = sheet
    for order in range(1, modulus ** len(holonomy) + 1):
        current = translate_sheet(current, holonomy, modulus)
        if current == sheet:
            return order
    raise AssertionError("finite translation failed to return")


def run() -> dict:
    owners = ["Alice", "Bob"]

    # The aggregate cycle charge is zero, so an untyped scalar potential sees
    # no obstruction.  Custody remembers who generated each leg.
    mixed_cycle = [
        OwnedEdge("x", "y", "Alice", Fraction(1)),
        OwnedEdge("y", "x", "Bob", Fraction(-1)),
    ]
    aggregate = scalar_cycle_sum(mixed_cycle)
    typed = typed_cycle_sum(mixed_cycle, owners)
    assert aggregate == 0
    assert typed == (Fraction(1), Fraction(-1))

    modulus = 5
    start = (0, 0)
    finish = translate_sheet(start, typed, modulus)
    order = monodromy_order(typed, modulus)
    assert finish == (1, 4)
    assert order == modulus

    # A custody-pure cancelling cycle has trivial typed holonomy and lifts to a
    # closed cycle on every sheet.
    pure_canceling_cycle = [
        OwnedEdge("x", "y", "Alice", Fraction(3)),
        OwnedEdge("y", "x", "Alice", Fraction(-3)),
    ]
    pure_typed = typed_cycle_sum(pure_canceling_cycle, owners)
    assert pure_typed == (Fraction(0), Fraction(0))
    assert translate_sheet(start, pure_typed, modulus) == start
    assert monodromy_order(pure_typed, modulus) == 1

    return {
        "experiment": "E06",
        "status": "passed",
        "mixed_cycle": {
            "aggregate_holonomy": str(aggregate),
            "owner_typed_holonomy": [str(x) for x in typed],
            "cover_modulus": modulus,
            "lifted_endpoint": finish,
            "monodromy_order": order,
        },
        "pure_canceling_cycle": {
            "owner_typed_holonomy": [str(x) for x in pure_typed],
            "monodromy_order": monodromy_order(pure_typed, modulus),
        },
        "conclusion": (
            "Owner purification is strictly finer than aggregate potentiality: "
            "a scalar coboundary may retain nontrivial typed monodromy on every "
            "cover whose modulus does not annihilate the custody class."
        ),
        "limitation": (
            "Nontrivial custody monodromy is an algebraic obstruction to typed "
            "potentials, not by itself a strategically harmful game obstruction."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
