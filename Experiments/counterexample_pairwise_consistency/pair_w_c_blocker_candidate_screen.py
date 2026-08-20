"""Exact preliminary C screens for the four-player singleton-blocker completion.

The candidate was proposed in an earlier research note.  This probe does
not reproduce or endorse its reported bounded search.  It checks only facts
that have short exact certificates:

* the four rate-covering singleton blockers have positive affine gain at both
  endpoints, hence at every owner rate;
* every nonempty pure quitting-coalition fixed point has a strict deviation;
* ``0 <= chi_i <= 1/8`` follows from Never and the all-three-opponents-Quit
  punishment profile; and
* the table lies in the rational reward box with ``M=2``.

Mixed exact roots, exact charged cycles, arbitrary finite charge capacity, the
exact punishment values, and a canonical W family remain unchecked.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


PLAYERS = tuple(range(4))


def coalitions() -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(group)
        for size in range(1, 5)
        for group in combinations(PLAYERS, size)
    )


COALITIONS = coalitions()

SINGLETONS = {
    frozenset((0,)): (Fraction(1), Fraction(5, 3), Fraction(2, 3), Fraction(2)),
    frozenset((1,)): (Fraction(2, 3), Fraction(1), Fraction(5, 3), Fraction(5, 3)),
    frozenset((2,)): (Fraction(5, 3), Fraction(2), Fraction(1), Fraction(1, 3)),
    frozenset((3,)): (Fraction(5, 3), Fraction(0), Fraction(2), Fraction(1)),
}

PAIRS = {
    frozenset((0, 1)): (
        Fraction(11, 12),
        Fraction(1, 2),
        Fraction(1, 8),
        Fraction(1, 8),
    ),
    frozenset((0, 2)): (
        Fraction(1, 2),
        Fraction(1, 8),
        Fraction(11, 12),
        Fraction(1, 8),
    ),
    frozenset((2, 3)): (
        Fraction(1, 8),
        Fraction(1, 8),
        Fraction(1, 2),
        Fraction(7, 12),
    ),
    frozenset((1, 3)): (Fraction(1, 8), Fraction(1, 4), Fraction(1, 8), Fraction(1, 2)),
    frozenset((1, 2)): (Fraction(1, 8), Fraction(1, 2), Fraction(1, 2), Fraction(1, 8)),
    frozenset((0, 3)): (Fraction(1, 2), Fraction(1, 8), Fraction(1, 8), Fraction(1, 2)),
}


def payoff(quitters: frozenset[int]) -> tuple[Fraction, ...]:
    assert quitters
    if len(quitters) == 1:
        return SINGLETONS[quitters]
    if len(quitters) == 2:
        return PAIRS[quitters]
    if len(quitters) == 3:
        return tuple(
            Fraction(0) if who in quitters else Fraction(1, 8) for who in PLAYERS
        )
    assert len(quitters) == 4
    return (Fraction(0),) * 4


def action_probability(
    hazards: tuple[Fraction, ...], quitters: frozenset[int]
) -> Fraction:
    probability = Fraction(1)
    for who, hazard in enumerate(hazards):
        probability *= hazard if who in quitters else 1 - hazard
    return probability


def endpoint(
    hazards: tuple[Fraction, ...],
    continuation: tuple[Fraction, ...],
    who: int,
    quit_now: bool,
) -> Fraction:
    fixed = list(hazards)
    fixed[who] = Fraction(int(quit_now))
    fixed_hazards = tuple(fixed)
    terminal = sum(
        (
            action_probability(fixed_hazards, quitters) * payoff(quitters)[who]
            for quitters in COALITIONS
        ),
        Fraction(0),
    )
    return terminal + action_probability(fixed_hazards, frozenset()) * continuation[who]


def successor(
    hazards: tuple[Fraction, ...], continuation: tuple[Fraction, ...]
) -> tuple[Fraction, ...]:
    return tuple(
        hazards[who] * endpoint(hazards, continuation, who, True)
        + (1 - hazards[who]) * endpoint(hazards, continuation, who, False)
        for who in PLAYERS
    )


def is_exact_nash(
    hazards: tuple[Fraction, ...], continuation: tuple[Fraction, ...]
) -> bool:
    for who, hazard in enumerate(hazards):
        quit_value = endpoint(hazards, continuation, who, True)
        continue_value = endpoint(hazards, continuation, who, False)
        if hazard > 0 and quit_value < continue_value:
            return False
        if hazard < 1 and continue_value < quit_value:
            return False
    return True


def check_rate_covering_singletons() -> None:
    # owner -> its rate-covering outsider
    blockers = {0: 2, 1: 0, 2: 3, 3: 1}
    for owner, blocker in blockers.items():
        spectator = payoff(frozenset((owner,)))[blocker]
        solo = payoff(frozenset((blocker,)))[blocker]
        join = payoff(frozenset((owner, blocker)))[blocker]
        solo_gain = solo - spectator
        join_gain = join - spectator
        assert solo_gain > 0
        assert join_gain == Fraction(1, 4) > 0

        # Exact affine rate criterion.  Positivity at p=0 and p=1 proves it
        # for every real p in [0,1]; the rational sweep is a regression only.
        for numerator in range(65):
            owner_rate = Fraction(numerator, 64)
            gain = owner_rate * join_gain + (1 - owner_rate) * solo_gain
            assert gain > 0


def check_no_pure_charged_fixed_root() -> None:
    for quitters in COALITIONS:
        action = tuple(Fraction(int(who in quitters)) for who in PLAYERS)
        state = payoff(quitters)
        assert successor(action, state) == state
        assert not is_exact_nash(action, state)


def check_safe_punishment_bounds() -> None:
    # All payoffs are nonnegative, so Never guarantees at least zero.
    assert all(
        coordinate >= 0 for quitters in COALITIONS for coordinate in payoff(quitters)
    )

    # If all three opponents quit surely at date zero, Continue yields 1/8
    # as the unique spectator of a triple and Quit yields zero in the grand
    # coalition.  Hence the behavioral punishment value is at most 1/8.
    for who in PLAYERS:
        opponents_quit = tuple(Fraction(int(other != who)) for other in PLAYERS)
        continuation = (Fraction(0),) * 4
        assert endpoint(opponents_quit, continuation, who, False) == Fraction(1, 8)
        assert endpoint(opponents_quit, continuation, who, True) == 0


def main() -> None:
    assert len(COALITIONS) == 15
    assert set(SINGLETONS) | set(PAIRS) == {
        group for group in COALITIONS if len(group) <= 2
    }
    assert (
        max(
            abs(coordinate)
            for quitters in COALITIONS
            for coordinate in payoff(quitters)
        )
        == 2
    )
    check_rate_covering_singletons()
    check_no_pure_charged_fixed_root()
    check_safe_punishment_bounds()
    print("singleton-blocker candidate exact preliminary screens: PASS")
    print("four affine rate covers and all 15 pure fixed roots checked")
    print("certified behavioral floor enclosure: 0 <= chi_i <= 1/8")
    print("mixed charged cycles and universal C: UNCHECKED")
    print("canonical W family and common cap provenance: UNCHECKED")


if __name__ == "__main__":
    main()
