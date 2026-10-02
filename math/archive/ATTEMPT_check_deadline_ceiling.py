#!/usr/bin/env python3
"""Exact arithmetic checks for the sharp hard-deadline ceiling family.

This checks the displayed finite instances, not the general existence conjecture
or uniqueness theorem.  The accompanying Markdown gives the mathematical proofs.
Run with Python 3.10+; only the standard library is required.
"""
from fractions import Fraction as F
from itertools import product
from typing import Optional

Time = Optional[int]  # None is Never.
Law = dict[Time, F]
Profile = tuple[Law, Law, Law, Law]


def reward(coalition: frozenset[int], x: F) -> tuple[F, F, F, F]:
    if not coalition:
        return (F(0),) * 4
    active = coalition & {0, 1}
    active_payoffs = {
        frozenset(): (F(0), F(0)),
        frozenset({0}): (x, F(-1)),
        frozenset({1}): (F(1), F(-1)),
        frozenset({0, 1}): (F(-1), F(0)),
    }
    a, b = active_payoffs[frozenset(active)]
    return a, b, F(-int(2 in coalition)), F(-int(3 in coalition))


def payoff(profile: Profile, x: F, horizon: Optional[int] = None) -> tuple[F, ...]:
    total = [F(0) for _ in range(4)]
    for law in profile:
        assert sum(law.values()) == 1 and all(p >= 0 for p in law.values())
    for draws in product(*(list(law.items()) for law in profile)):
        times = [t for t, _ in draws]
        weight = F(1)
        for _, mass in draws:
            weight *= mass
        finite = [t for t in times if t is not None]
        if not finite:
            continue
        first = min(finite)
        if horizon is not None:
            if horizon <= 0:
                raise ValueError('horizon must be positive')
            weight *= F(max(0, horizon-first), horizon)
        coalition = frozenset(i for i, t in enumerate(times) if t == first)
        for i, value in enumerate(reward(coalition, x)):
            total[i] += weight * value
    return tuple(total)


def pure_value(profile: Profile, x: F, player: int, time: Time,
               horizon: Optional[int] = None) -> F:
    changed = list(profile)
    changed[player] = {time: F(1)}
    return payoff(tuple(changed), x, horizon)[player]


def ceiling(k: int, x: F) -> F:
    rho = (1+x)/2
    return 1/(1/x + sum((rho**m for m in range(k)), F(0))/2)


def deadline_profile(k: int, x: F) -> Profile:
    if k < 1 or not (0 < x <= 1):
        raise ValueError('require k >= 1 and 0 < x <= 1')
    delta = ceiling(k, x)
    rho = (1+x)/2
    first = {t: F(1, k+1) for t in range(k)}
    first[None] = F(1, k+1)
    second = {t: delta/2 * rho**(k-1-t) for t in range(k)}
    second[None] = delta/x
    return first, second, {None: F(1)}, {None: F(1)}


def check_deadline(k: int, x: F) -> None:
    profile = deadline_profile(k, x)
    u = payoff(profile, x)
    delta = ceiling(k, x)
    assert u == (1-delta/x, -F(k, k+1), F(0), F(0))
    permitted = list(range(k)) + [None]
    unrestricted_representatives = list(range(k+1)) + [None]
    debts = []
    for i in range(4):
        values = [pure_value(profile, x, i, t) for t in permitted]
        assert max(values) == u[i], (k, x, i, 'not deadline Nash')
        for t, mass in profile[i].items():
            if mass:
                assert pure_value(profile, x, i, t) == u[i]
        cap = max(pure_value(profile, x, i, t)
                  for t in unrestricted_representatives)
        debts.append(cap-u[i])
    assert debts == [delta, F(0), F(0), F(0)]
    for t in range(k):
        h = profile[1][t]
        tail = sum((profile[1][z] for z in range(t+1, k)), F(0))
        assert delta == 2*h+(1-x)*tail
    assert delta == x*profile[1][None]


def check_punishment(length: int, x: F) -> None:
    profile: Profile = (
        {t: F(1, length) for t in range(1, length+1)},
        {0: F(1)}, {None: F(1)}, {None: F(1)},
    )
    u = payoff(profile, x)
    assert u == (F(1), F(-1), F(0), F(0))
    representatives = list(range(length+2)) + [None]
    debts = [max(pure_value(profile, x, i, t) for t in representatives)-u[i]
             for i in range(4)]
    assert debts == [F(0), F(1, length), F(0), F(0)]
    for horizon in (length+1, 2*length+3, 10*length+1):
        uh = payoff(profile, x, horizon)
        assert uh == u
        for i in range(4):
            cap = max(pure_value(profile, x, i, t, horizon)
                      for t in representatives)
            assert cap-uh[i] <= F(1, length)+F(length, horizon)


def main() -> None:
    parameters = [F(1, 10), F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(1)]
    count = 0
    for x in parameters:
        for k in range(1, 13):
            check_deadline(k, x)
            check_punishment(k, x)
            count += 1
    assert [ceiling(k, F(1)) for k in (1, 2, 3)] == [F(2, 3), F(1, 2), F(2, 5)]
    print(f'PASS: {count} deadline equilibria and {count} punishment profiles.')
    print('Exact unrestricted pure-time caps and boundary equalities verified.')
    print('This finite computation is not a proof of the four-player conjecture.')


if __name__ == '__main__':
    main()
