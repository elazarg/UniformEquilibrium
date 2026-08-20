"""Exact probes for the central T x W x C attachment interface.

The main table is the strict-joiner completion retained from Answer C.  The
new data in this file put an exact positive-debt tail, its canonical windows,
and exact augmented-cap transport on that same table.  All arithmetic is over
``fractions.Fraction``.

This is deliberately an *interface* probe.  It proves neither cutoff-wise
optimized/projective provenance nor the universal charge-capacity statement.
It does check every promoted pure-coalition-lock restriction, so failure of a
singleton-lock screen cannot explain the attachment mismatch in this model.

A second, small negative control checks the charge-one singleton lock from the
older local cap witness.  It records exactly why selected bounded cap paths do
not establish universal C.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


PLAYERS = tuple(range(4))
OWNER = 0
HAZARD_OWNER = 1
SHIFT = 4
VALUE_BUBBLE = Fraction(3, 4)
DEBT_BUBBLE = Fraction(1, 2)
WINDOW_MARGIN = Fraction(1, 4)


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
    frozenset((1, 3)): (
        Fraction(1, 8),
        Fraction(1, 4),
        Fraction(1, 8),
        Fraction(1, 2),
    ),
    frozenset((1, 2)): (
        Fraction(1, 8),
        Fraction(1, 2),
        Fraction(1, 2),
        Fraction(1, 8),
    ),
    frozenset((0, 3)): (
        Fraction(1, 2),
        Fraction(1, 8),
        Fraction(1, 8),
        Fraction(1, 2),
    ),
}


def payoff(quitters: frozenset[int]) -> tuple[Fraction, ...]:
    assert quitters
    if len(quitters) == 1:
        return SINGLETONS[quitters]
    if len(quitters) == 2:
        return PAIRS[quitters]
    if len(quitters) == 3:
        return tuple(
            Fraction(0) if who in quitters else Fraction(1, 8)
            for who in PLAYERS
        )
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
    reward=payoff,
) -> Fraction:
    fixed = list(hazards)
    fixed[who] = Fraction(int(quit_now))
    fixed_hazards = tuple(fixed)
    absorbing = sum(
        (
            action_probability(fixed_hazards, quitters) * reward(quitters)[who]
            for quitters in COALITIONS
        ),
        Fraction(0),
    )
    return (
        absorbing
        + action_probability(fixed_hazards, frozenset()) * continuation[who]
    )


def successor(
    hazards: tuple[Fraction, ...],
    continuation: tuple[Fraction, ...],
    reward=payoff,
) -> tuple[Fraction, ...]:
    return tuple(
        hazards[who] * endpoint(hazards, continuation, who, True, reward)
        + (1 - hazards[who])
        * endpoint(hazards, continuation, who, False, reward)
        for who in PLAYERS
    )


def is_exact_nash(
    hazards: tuple[Fraction, ...],
    continuation: tuple[Fraction, ...],
    reward=payoff,
) -> bool:
    for who, hazard in enumerate(hazards):
        quit_value = endpoint(hazards, continuation, who, True, reward)
        continue_value = endpoint(hazards, continuation, who, False, reward)
        if hazard > 0 and quit_value < continue_value:
            return False
        if hazard < 1 and continue_value < quit_value:
            return False
    return True


def scale(time: int) -> Fraction:
    k = time + SHIFT
    return Fraction(k - 1, k)


def hazard(time: int) -> Fraction:
    return Fraction(1, (time + SHIFT) ** 2)


def root(time: int) -> tuple[Fraction, ...]:
    return (Fraction(0), hazard(time), Fraction(0), Fraction(0))


def value(time: int) -> tuple[Fraction, ...]:
    singleton_one = payoff(frozenset((HAZARD_OWNER,)))
    result = list(singleton_one)
    result[OWNER] += VALUE_BUBBLE * scale(time)
    return tuple(result)


def debt(time: int) -> tuple[Fraction, ...]:
    result = [Fraction(0)] * 4
    result[OWNER] = DEBT_BUBBLE * scale(time)
    return tuple(result)


def cap(time: int) -> tuple[Fraction, ...]:
    return tuple(value(time)[who] + debt(time)[who] for who in PLAYERS)


def dynamic_debt_update(time: int, who: int) -> Fraction:
    hazards = root(time)
    next_value = value(time + 1)
    next_debt = debt(time + 1)
    quit_value = endpoint(hazards, next_value, who, True)
    continue_value = endpoint(hazards, next_value, who, False)
    opponent_continue_mass = Fraction(1)
    for other in PLAYERS:
        if other != who:
            opponent_continue_mass *= 1 - hazards[other]
    return (
        max(
            quit_value,
            continue_value + opponent_continue_mass * next_debt[who],
        )
        - value(time)[who]
    )


def product(values: list[Fraction]) -> Fraction:
    answer = Fraction(1)
    for entry in values:
        answer *= entry
    return answer


def check_table_and_coalition_locks() -> None:
    assert len(COALITIONS) == 15
    assert max(
        abs(coordinate)
        for quitters in COALITIONS
        for coordinate in payoff(quitters)
    ) == 2

    # Never gives the lower floor certificate.  All three opponents quitting
    # at date zero give the upper certificate chi_i <= 1/8.
    assert all(
        coordinate >= 0
        for quitters in COALITIONS
        for coordinate in payoff(quitters)
    )
    for who in PLAYERS:
        punishment_root = tuple(
            Fraction(int(other != who)) for other in PLAYERS
        )
        assert endpoint(punishment_root, (Fraction(0),) * 4, who, False) == Fraction(1, 8)
        assert endpoint(punishment_root, (Fraction(0),) * 4, who, True) == 0

    # Every pure nonempty set reward is a Bellman fixed point, but none of
    # its pure roots is exact Nash.  Hence every promoted pure coalition-lock
    # restriction is passed, not merely the four singleton consequences.
    for quitters in COALITIONS:
        hazards = tuple(Fraction(int(who in quitters)) for who in PLAYERS)
        state = payoff(quitters)
        assert successor(hazards, state) == state
        assert not is_exact_nash(hazards, state)

    blockers = {0: 2, 1: 0, 2: 3, 3: 1}
    for owner, blocker in blockers.items():
        watch = payoff(frozenset((owner,)))[blocker]
        quit_alone = payoff(frozenset((blocker,)))[blocker]
        join = payoff(frozenset((owner, blocker)))[blocker]
        assert quit_alone > watch
        assert join - watch == Fraction(1, 4)


def check_exact_tail_and_caps() -> None:
    base = payoff(frozenset((HAZARD_OWNER,)))
    for time in range(256):
        k = time + SHIFT
        p = hazard(time)
        s = 1 - p

        assert scale(time) == s * scale(time + 1)
        assert p <= Fraction(1, (k - 1) * k)
        assert successor(root(time), value(time + 1)) == value(time)
        assert is_exact_nash(root(time), value(time + 1))
        assert tuple(dynamic_debt_update(time, who) for who in PLAYERS) == debt(time)

        # The cap bridge defect is exactly p_i d_i, and it vanishes because
        # the sole positive-debt player never quits while the mixer has zero debt.
        cap_successor = successor(root(time), cap(time + 1))
        seam = tuple(
            cap(time)[who] - cap_successor[who] for who in PLAYERS
        )
        expected_seam = tuple(
            root(time)[who] * debt(time)[who] for who in PLAYERS
        )
        assert seam == expected_seam == (Fraction(0),) * 4
        assert cap_successor == cap(time)
        assert is_exact_nash(root(time), cap(time + 1))

        # The certified floor enclosure is chi_i <= 1/8.
        assert all(Fraction(1, 8) <= coordinate <= 2 for coordinate in cap(time))

        # Selected cap edges spend no more than the increase of owner cap.
        assert hazard(time) <= cap(time + 1)[OWNER] - cap(time)[OWNER]

        # Exact deleted-survival/debt-ratio clock on every finite one-step edge.
        assert s == debt(time)[OWNER] / debt(time + 1)[OWNER]

        # Exact honest infinite-tail payoff: absorption occurs only through
        # singleton 1, with total probability 1-scale(time).
        honest = tuple((1 - scale(time)) * coordinate for coordinate in base)
        assert honest[OWNER] == Fraction(2, 3 * k)

    limit_value = (
        Fraction(2, 3) + VALUE_BUBBLE,
        Fraction(1),
        Fraction(5, 3),
        Fraction(5, 3),
    )
    limit_debt = (DEBT_BUBBLE, Fraction(0), Fraction(0), Fraction(0))
    limit_cap = tuple(
        limit_value[who] + limit_debt[who] for who in PLAYERS
    )
    assert limit_value[OWNER] == Fraction(17, 12)
    assert limit_cap[OWNER] == Fraction(23, 12) < 2
    assert is_exact_nash((Fraction(0),) * 4, limit_cap)
    assert successor((Fraction(0),) * 4, limit_cap) == limit_cap


def check_canonical_windows() -> None:
    delivery = payoff(frozenset((HAZARD_OWNER,)))
    for window in range(128):
        times = list(range(window, 2 * window + 1))
        survival = product([1 - hazard(time) for time in times])
        expected_survival = Fraction(window + 3, window + 4) * Fraction(
            2 * window + 5, 2 * window + 4
        )
        assert survival == expected_survival
        absorption = 1 - survival
        assert absorption > 0

        # A periodically repeated pass absorbs a.s. only at singleton 1.
        # Player 0's phase-zero stop strictly beats that delivery uniformly.
        phase_zero_stop = endpoint(root(window), delivery, OWNER, True)
        assert phase_zero_stop == 1 - hazard(window) * Fraction(1, 12)
        assert phase_zero_stop - delivery[OWNER] >= Fraction(21, 64)
        assert phase_zero_stop - delivery[OWNER] > WINDOW_MARGIN

        # Exact restart identities for both the value and augmented-cap paths.
        end = 2 * window + 1
        for path in (value, cap):
            assert path(window)[OWNER] == (
                absorption * delivery[OWNER]
                + survival * path(end)[OWNER]
            )
        normalized_value_drift = (
            survival
            * (value(end)[OWNER] - value(window)[OWNER])
            / absorption
        )
        normalized_cap_drift = (
            survival
            * (cap(end)[OWNER] - cap(window)[OWNER])
            / absorption
        )
        assert normalized_value_drift == value(window)[OWNER] - delivery[OWNER]
        assert normalized_cap_drift == cap(window)[OWNER] - delivery[OWNER]

        # The very same word is an exact floor-cap path of positive charge.
        charge = sum((hazard(time) for time in times), Fraction(0))
        assert charge > 0
        assert charge <= cap(end)[OWNER] - cap(window)[OWNER]


def simple_lock_payoff(quitters: frozenset[int]) -> tuple[Fraction, ...]:
    return (
        Fraction(int(0 in quitters)),
        Fraction(0),
        Fraction(0),
        Fraction(-3 if quitters == frozenset((3,)) else 0),
    )


def check_selected_path_is_not_global_capacity() -> None:
    # Negative control from the local T x C witness: singleton {0} is a
    # punishment-rational charge-one exact self-loop.
    state = simple_lock_payoff(frozenset((0,)))
    hazards = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    assert successor(hazards, state, simple_lock_payoff) == state
    assert is_exact_nash(hazards, state, simple_lock_payoff)
    assert 1 - product([1 - entry for entry in hazards]) == 1


def main() -> None:
    check_table_and_coalition_locks()
    check_exact_tail_and_caps()
    check_canonical_windows()
    check_selected_path_is_not_global_capacity()
    print("T x W x C attachment interface exact rational probe: PASS")
    print("lock-clean table: 15/15 pure coalition locks excluded")
    print("256 exact-D/cap edges and 128 canonical windows checked")
    print("fixed W witness: player 0, phase zero, gain >= 21/64")
    print("selected cap words: exact, floor-admissible, positive, bounded")
    print("universal C and optimized/projective provenance: UNPROVED")
    print("simple negative control: universal C fails by charge-one lock")


if __name__ == "__main__":
    main()
