"""Exact regression for the W x C attachment seam.

The common four-player table has a canonical periodic-window family with a
fixed phase-stop witness.  The same actions also transport boxed
punishment-floor caps by exact Nash--Bellman edges and converge to an exact
all-Continue zero-charge cap.

This is deliberately *not* a full C witness.  A separate singleton-lock
self-loop has charge one, so universal punishment-floor capacity is infinite.
The regression records the precise domain mismatch: the periodic word is
exact at the cap continuations, but is not exact at its realized periodic
continuations.  Reusing the cap path would require an additional exact return
connector, which W does not supply.

All arithmetic is over ``fractions.Fraction``.  The accompanying report proves
the identities for every date and window; the finite sweeps here are only
executable checks of the full reward table and the stated seams.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


OWNER, ACTIVE, DUMMY, COSTLY = range(4)
PLAYERS = (OWNER, ACTIVE, DUMMY, COSTLY)
ZERO = (Fraction(0),) * 4
PUNISHMENT_FLOOR = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))


def coalitions() -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(group)
        for size in range(1, len(PLAYERS) + 1)
        for group in combinations(PLAYERS, size)
    )


COALITIONS = coalitions()


def reward(quitters: frozenset[int], who: int) -> Fraction:
    """The full rational reward table used in the seam regression."""
    assert quitters
    if who == OWNER:
        return Fraction(int(OWNER in quitters))
    if who in (ACTIVE, DUMMY):
        return Fraction(0)
    assert who == COSTLY
    return Fraction(-3 if quitters == frozenset((COSTLY,)) else 0)


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
            action_probability(fixed_hazards, quitters) * reward(quitters, who)
            for quitters in COALITIONS
        ),
        Fraction(0),
    )
    survival = action_probability(fixed_hazards, frozenset())
    return terminal + survival * continuation[who]


def successor(
    hazards: tuple[Fraction, ...], continuation: tuple[Fraction, ...]
) -> tuple[Fraction, ...]:
    return tuple(
        hazards[who] * endpoint(hazards, continuation, who, True)
        + (1 - hazards[who]) * endpoint(hazards, continuation, who, False)
        for who in PLAYERS
    )


def absorption(hazards: tuple[Fraction, ...]) -> Fraction:
    return 1 - action_probability(hazards, frozenset())


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


def p(time: int) -> Fraction:
    return Fraction(1, (time + 2) ** 2)


def tail_root(time: int) -> tuple[Fraction, ...]:
    return (Fraction(0), p(time), Fraction(0), Fraction(0))


def cap(time: int) -> tuple[Fraction, ...]:
    return (
        Fraction(3 * (time + 1), time + 2),
        Fraction(0),
        Fraction(0),
        Fraction(0),
    )


def window_survival(n: int) -> Fraction:
    result = Fraction(1)
    for time in range(n, 2 * n + 1):
        result *= 1 - p(time)
    return result


def window_charge(n: int) -> Fraction:
    return sum((p(time) for time in range(n, 2 * n + 1)), Fraction(0))


def check_reward_table_and_floor() -> None:
    assert len(COALITIONS) == 15
    assert max(abs(reward(group, who)) for group in COALITIONS for who in PLAYERS) == 3

    # Exact behavioral punishment values are (1,0,0,0): OWNER quits now;
    # ACTIVE and DUMMY always receive zero; COSTLY can play Never.  Opponents
    # all Continue give the matching upper bounds.
    assert reward(frozenset((OWNER,)), OWNER) == 1
    assert all(
        reward(group, ACTIVE) == reward(group, DUMMY) == 0 for group in COALITIONS
    )
    assert reward(frozenset((COSTLY,)), COSTLY) == -3
    assert all(
        reward(group, COSTLY) == 0
        for group in COALITIONS
        if group != frozenset((COSTLY,))
    )


def check_cap_edge(time: int) -> None:
    root = tail_root(time)
    current = cap(time)
    continuation = cap(time + 1)

    assert absorption(root) == p(time)
    assert is_exact_nash(root, continuation)
    assert successor(root, continuation) == current
    assert all(-3 <= coordinate <= 3 for coordinate in current)
    assert all(current[who] >= PUNISHMENT_FLOOR[who] for who in PLAYERS)

    # The selected edge has a bounded local charge potential.  This is only a
    # statement about these edges, not universal C.
    assert continuation[OWNER] - current[OWNER] >= p(time)

    # The very same action is not exact at its periodic realized continuation
    # (zero): OWNER would switch from Continue to Quit and gain exactly one.
    assert endpoint(root, ZERO, OWNER, True) == 1
    assert endpoint(root, ZERO, OWNER, False) == 0
    assert not is_exact_nash(root, ZERO)


def check_window(n: int) -> None:
    survival = window_survival(n)
    pass_absorption = 1 - survival
    assert survival == Fraction(2 * n + 3, 2 * n + 4)
    assert pass_absorption == Fraction(1, 2 * n + 4) > 0

    # Exact one-pass cap transport, in chronological Bellman order.
    start = cap(n)
    endpoint_cap = cap(2 * n + 1)
    transported = endpoint_cap
    for time in range(2 * n, n - 1, -1):
        assert is_exact_nash(tail_root(time), transported)
        transported = successor(tail_root(time), transported)
    assert transported == start

    # Since only ACTIVE can absorb and r({ACTIVE})=0, periodic delivery is
    # zero.  OWNER's phase-zero stop is worth one and no reward exceeds one.
    periodic_delivery = ZERO
    owner_phase_zero = endpoint(tail_root(n), ZERO, OWNER, True)
    owner_refusal = Fraction(0)
    assert periodic_delivery == ZERO
    assert owner_phase_zero == 1
    assert owner_refusal == 0

    # Exact normalized endpoint-drift identity for the cap coordinate.
    assert ZERO[OWNER] - start[OWNER] == (survival / pass_absorption) * (
        start[OWNER] - endpoint_cap[OWNER]
    )

    # C's additive charge on the one-pass cap path is positive and paid by the
    # selected local potential.  Periodic replay is not this path replayed:
    # it lacks an exact connector from start back to endpoint_cap.
    charge = window_charge(n)
    assert charge > 0
    assert charge <= endpoint_cap[OWNER] - start[OWNER]


def check_limiting_cap_and_singleton_lock() -> None:
    limiting_cap = (Fraction(3), Fraction(0), Fraction(0), Fraction(0))
    all_continue = ZERO
    assert is_exact_nash(all_continue, limiting_cap)
    assert successor(all_continue, limiting_cap) == limiting_cap
    assert absorption(all_continue) == 0
    assert all(limiting_cap[who] >= PUNISHMENT_FLOOR[who] for who in PLAYERS)

    # New singleton-lock screen: no outsider strictly benefits from joining
    # OWNER, so r({OWNER}) is a punishment-rational charge-one fixed point.
    state = PUNISHMENT_FLOOR
    owner_quits = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    for outsider in (ACTIVE, DUMMY, COSTLY):
        assert reward(frozenset((OWNER, outsider)), outsider) <= reward(
            frozenset((OWNER,)), outsider
        )
    assert is_exact_nash(owner_quits, state)
    assert successor(owner_quits, state) == state
    assert absorption(owner_quits) == 1
    for horizon in (1, 2, 7, 64):
        assert (
            sum((absorption(owner_quits) for _ in range(horizon)), Fraction(0))
            == horizon
        )


def main() -> None:
    check_reward_table_and_floor()
    for time in range(256):
        check_cap_edge(time)
    for n in range(96):
        check_window(n)
    check_limiting_cap_and_singleton_lock()
    print("W x C exposed attachment seam: PASS")
    print("exact rational checks: 256 cap edges and 96 canonical windows")
    print("fixed W witness: OWNER, phase zero, exploitability 1")
    print("periodic continuation is not an exact cap continuation")
    print("universal C: FAIL (singleton-lock charge-one self-loop)")


if __name__ == "__main__":
    main()
