"""Exact packet audit for the lock-clean T x P x selected-C model.

The reward table, exact phantom tail, augmented-cap ray, and coalition-lock
audit live in ``triple_t_w_c_lock_clean_probe.py``.  This file adds the full
normalized singleton-packet calculation on exactly that table.

The support enumeration below is a proof regression for the finite linear
part of the packet argument.  The accompanying report turns it into a
continuum statement: a complementary feasible mass would occur on one of
the 15 supports enumerated here, and none does.  Compactness then gives one
uniform positive refusal margin on the entire feasible packet polytope.

Nothing here claims the universal exact-chain charge bound or optimized
projective provenance.  In particular, a finite grid or the absence of pure
coalition locks cannot establish global capacity.
"""

from __future__ import annotations

from fractions import Fraction

from triple_t_w_c_lock_clean_probe import (
    PLAYERS,
    SINGLETONS,
    check_exact_tail_and_caps,
    check_table_and_coalition_locks,
)


Q = Fraction
GRID_DENOMINATOR = 36


def singleton_mixture(mass: tuple[Q, ...], who: int) -> Q:
    return sum(
        (
            mass[owner] * SINGLETONS[frozenset((owner,))][who]
            for owner in PLAYERS
        ),
        Q(0),
    )


def packet_mass_feasible(mass: tuple[Q, ...]) -> bool:
    """The mass projection of (15) for this table.

    Every diagonal singleton reward is one and chi_i <= 1/8.  Hence a target
    exists exactly when every singleton mixture is at least one.  On active
    coordinates complementarity forces the target to equal one.
    """

    return (
        all(component >= 0 for component in mass)
        and sum(mass, Q(0)) == 1
        and all(singleton_mixture(mass, who) >= 1 for who in PLAYERS)
    )


def refusal_gain(mass: tuple[Q, ...], who: int) -> Q:
    assert 0 < mass[who] < 1
    mixture = singleton_mixture(mass, who)
    numerator = sum(
        (
            mass[owner] * SINGLETONS[frozenset((owner,))][who]
            for owner in PLAYERS
            if owner != who
        ),
        Q(0),
    )
    refusal = numerator / (1 - mass[who])
    assert refusal - mixture == mass[who] * (mixture - 1) / (1 - mass[who])
    return refusal - mixture


def solve_unique(matrix: list[list[Q]], target: list[Q]) -> list[Q] | None:
    """Exact square Gaussian elimination, returning None when singular."""

    size = len(matrix)
    augmented = [matrix[index][:] + [target[index]] for index in range(size)]
    for column in range(size):
        pivot = next(
            (
                row
                for row in range(column, size)
                if augmented[row][column] != 0
            ),
            None,
        )
        if pivot is None:
            return None
        augmented[column], augmented[pivot] = (
            augmented[pivot],
            augmented[column],
        )
        divisor = augmented[column][column]
        augmented[column] = [entry / divisor for entry in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            multiplier = augmented[row][column]
            if multiplier == 0:
                continue
            augmented[row] = [
                augmented[row][index]
                - multiplier * augmented[column][index]
                for index in range(size + 1)
            ]
    return [augmented[row][-1] for row in range(size)]


def complementary_candidate(support: tuple[int, ...]) -> tuple[Q, ...]:
    """Solve sum lambda=1 and m_i=1 on a proposed positive support.

    The first ``|support|-1`` active equations plus normalization form a
    nonsingular square system for every nonempty support of this table.  The
    omitted active equation is checked by the caller.
    """

    matrix = [[Q(1) for _ in support]]
    for who in support[:-1]:
        matrix.append(
            [SINGLETONS[frozenset((owner,))][who] for owner in support]
        )
    solution = solve_unique(matrix, [Q(1)] * len(support))
    assert solution is not None
    mass = [Q(0)] * len(PLAYERS)
    for owner, component in zip(support, solution):
        mass[owner] = component
    return tuple(mass)


def check_no_complementary_packet() -> None:
    support_count = 0
    for mask in range(1, 1 << len(PLAYERS)):
        support = tuple(who for who in PLAYERS if mask & (1 << who))
        mass = complementary_candidate(support)
        support_count += 1

        has_exact_support = all(mass[who] > 0 for who in support)
        active_is_complementary = all(
            singleton_mixture(mass, who) == 1 for who in support
        )
        globally_funded = all(
            singleton_mixture(mass, who) >= 1 for who in PLAYERS
        )

        # A complementary feasible packet would have all three properties.
        assert not (
            has_exact_support and active_is_complementary and globally_funded
        )
    assert support_count == 15


def check_packet_witness_and_grid() -> int:
    uniform = (Q(1, 4),) * 4
    assert packet_mass_feasible(uniform)
    assert tuple(singleton_mixture(uniform, who) for who in PLAYERS) == (
        Q(5, 4),
        Q(7, 6),
        Q(4, 3),
        Q(5, 4),
    )
    assert all(refusal_gain(uniform, who) > 0 for who in PLAYERS)

    feasible_count = 0
    smallest_grid_maximum: Q | None = None
    for denominator in range(1, GRID_DENOMINATOR + 1):
        for n0 in range(denominator + 1):
            for n1 in range(denominator - n0 + 1):
                for n2 in range(denominator - n0 - n1 + 1):
                    mass = (
                        Q(n0, denominator),
                        Q(n1, denominator),
                        Q(n2, denominator),
                        Q(denominator - n0 - n1 - n2, denominator),
                    )
                    if not packet_mass_feasible(mass):
                        continue
                    feasible_count += 1
                    gains = [
                        refusal_gain(mass, who)
                        for who in PLAYERS
                        if 0 < mass[who] < 1
                        and singleton_mixture(mass, who) > 1
                    ]
                    assert gains
                    maximum = max(gains)
                    assert maximum > 0
                    if (
                        smallest_grid_maximum is None
                        or maximum < smallest_grid_maximum
                    ):
                        smallest_grid_maximum = maximum
    assert feasible_count > 0
    assert smallest_grid_maximum is not None
    return feasible_count


def check_tail_occupation_is_not_a_packet() -> None:
    # Only player 1 carries hazard on the selected tail.  Its normalized
    # owner occupation is therefore e_1, whose player-0 mixture is 2/3 < 1.
    tail_occupation = (Q(0), Q(1), Q(0), Q(0))
    assert singleton_mixture(tail_occupation, 0) == Q(2, 3)
    assert not packet_mass_feasible(tail_occupation)


def main() -> None:
    check_table_and_coalition_locks()
    check_exact_tail_and_caps()
    check_no_complementary_packet()
    feasible_count = check_packet_witness_and_grid()
    check_tail_occupation_is_not_a_packet()
    print("T x P x selected-C lock-clean packet probe: PASS")
    print("common table: exact-D tail, exact cap ray, 15/15 pure locks excluded")
    print("packet supports eliminated exactly: 15/15 complementary supports")
    print(f"feasible packet grid points checked: {feasible_count}")
    print(f"grid denominators: 1..{GRID_DENOMINATOR}")
    print("tail occupation e_1: underfunded for player 0")
    print("global capacity and optimized/projective provenance: UNPROVED")


if __name__ == "__main__":
    main()
