"""Exact probe for the T x C exposed-equation witness.

The witness has an exact positive-hazard phantom tail whose augmented caps
are themselves exact finite punishment-floor edges.  It is deliberately not
a full C witness: a separate charge-one exact fixed loop makes the universal
capacity infinite.

All calculations use ``fractions.Fraction``.  The report proves the formulas
for arbitrary dates and arbitrary loop lengths; the finite date sweep here is
only an executable regression for the reward table and local identities.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


OWNER, ACTIVE, DUMMY, COSTLY = range(4)
PLAYERS = (OWNER, ACTIVE, DUMMY, COSTLY)


def coalitions() -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(group)
        for size in range(1, len(PLAYERS) + 1)
        for group in combinations(PLAYERS, size)
    )


COALITIONS = coalitions()


def reward(quitters: frozenset[int], who: int) -> Fraction:
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
    result = Fraction(0)
    for quitters in COALITIONS:
        result += action_probability(fixed_hazards, quitters) * reward(
            quitters, who
        )
    survival = action_probability(fixed_hazards, frozenset())
    return result + survival * continuation[who]


def successor(
    hazards: tuple[Fraction, ...], continuation: tuple[Fraction, ...]
) -> tuple[Fraction, ...]:
    return tuple(
        hazards[who] * endpoint(hazards, continuation, who, True)
        + (1 - hazards[who])
        * endpoint(hazards, continuation, who, False)
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


def debt(time: int) -> tuple[Fraction, ...]:
    return (Fraction(time + 1, time + 2), Fraction(0), Fraction(0), Fraction(0))


def value(time: int) -> tuple[Fraction, ...]:
    return tuple(2 * coordinate for coordinate in debt(time))


def cap(time: int) -> tuple[Fraction, ...]:
    return tuple(
        value(time)[who] + debt(time)[who] for who in PLAYERS
    )


def tail_root(time: int) -> tuple[Fraction, ...]:
    return (Fraction(0), p(time), Fraction(0), Fraction(0))


def check_tail_date(time: int) -> None:
    root = tail_root(time)
    current_value = value(time)
    next_value = value(time + 1)
    current_debt = debt(time)
    next_debt = debt(time + 1)
    current_cap = cap(time)
    next_cap = cap(time + 1)

    assert absorption(root) == p(time)
    assert is_exact_nash(root, next_value)
    assert successor(root, next_value) == current_value

    survival = 1 - p(time)
    assert current_value[OWNER] == survival * next_value[OWNER]
    assert current_debt[OWNER] == survival * next_debt[OWNER]
    assert current_debt[OWNER] == max(
        endpoint(root, next_value, OWNER, True),
        endpoint(root, next_value, OWNER, False)
        + survival * next_debt[OWNER],
    ) - current_value[OWNER]

    for who in (ACTIVE, DUMMY, COSTLY):
        opponents_continue = Fraction(1)
        for other in PLAYERS:
            if other != who:
                opponents_continue *= 1 - root[other]
        update = max(
            endpoint(root, next_value, who, True),
            endpoint(root, next_value, who, False)
            + opponents_continue * next_debt[who],
        ) - current_value[who]
        assert update == current_debt[who] == 0

    # The diagonal seam vanishes, so caps are literal exact edges.
    assert all(root[who] * current_debt[who] == 0 for who in PLAYERS)
    assert is_exact_nash(root, next_cap)
    assert successor(root, next_cap) == current_cap

    # Carrier and T bounds, with chi=(1,0,0,0) and M=3.
    punishment_floor = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    assert all(-3 <= coordinate <= 3 for coordinate in current_cap)
    assert all(
        punishment_floor[who] <= current_cap[who] for who in PLAYERS
    )
    assert Fraction(1, 2) <= current_debt[OWNER] < 1

    # Phi(w)=w_o pays for this selected outward edge w_(t+1) -> w_t.
    assert next_cap[OWNER] - current_cap[OWNER] >= p(time)


def check_unbounded_loop() -> None:
    state = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    owner_quits = (Fraction(1), Fraction(0), Fraction(0), Fraction(0))
    assert is_exact_nash(owner_quits, state)
    assert successor(owner_quits, state) == state
    assert absorption(owner_quits) == 1
    for horizon in (0, 1, 2, 7, 128):
        charge = sum(
            (absorption(owner_quits) for _ in range(horizon)), Fraction()
        )
        assert charge == horizon


def main() -> None:
    assert len(COALITIONS) == 15
    assert max(abs(reward(group, who)) for group in COALITIONS for who in PLAYERS) == 3
    for time in range(128):
        check_tail_date(time)
    check_unbounded_loop()
    print("T x C exact exposed equations: PASS")
    print("four-player rational table and 128 tail dates checked")
    print("augmented caps form exact finite-charge outward edges")
    print("universal C: FAIL (charge-one exact fixed loop)")


if __name__ == "__main__":
    main()
