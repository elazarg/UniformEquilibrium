#!/usr/bin/env python3
"""Exact finite-law certificates for a four-player quitting-game example.

The checks validate the explicitly constructed approximate profiles. The proof
that *all* exact finite-menu Nash equilibria have late defect 1/2 is in the
accompanying mathematical note, not inferred from this computation.

No third-party packages are required. Python 3.10+.
"""
from __future__ import annotations
from fractions import Fraction as Q
from typing import Sequence

PLAYERS = range(4)
PREV = {1: 3, 2: 1, 3: 2}
NEXT = {1: 2, 2: 3, 3: 1}


def reward(mask: int) -> tuple[Q, ...]:
    """The exact reward table, with mask 0 interpreted as Never payoff zero."""
    if mask == 0:
        return (Q(0),) * 4
    result = [Q(1) if mask & 1 else Q(2)]
    for i in range(1, 4):
        if mask & (1 << i):
            result.append(Q(0))
        elif mask & 1:
            result.append(Q(-1))
        else:
            result.append(Q(2 * bool(mask & (1 << PREV[i]))
                            - bool(mask & (1 << NEXT[i]))))
    return tuple(result)


def validate(laws: Sequence[Sequence[Q]]) -> int:
    if len(laws) != 4:
        raise ValueError('Exactly four laws are required.')
    n = len(laws[0]) - 1
    if n < 1 or any(len(law) != n + 1 for law in laws):
        raise ValueError('Use N finite dates followed by Never, with N >= 1.')
    if any(any(x < 0 for x in law) or sum(law) != 1 for law in laws):
        raise ValueError('Each law must be a probability vector.')
    return n


def payoff(laws: Sequence[Sequence[Q]]) -> tuple[Q, ...]:
    n = validate(laws)
    survive = [Q(1)] * 4
    value = [Q(0)] * 4
    for t in range(n):
        after = [survive[i] - laws[i][t] for i in PLAYERS]
        for mask in range(1, 16):
            mass = Q(1)
            for i in PLAYERS:
                mass *= laws[i][t] if mask & (1 << i) else after[i]
            if mass:
                r = reward(mask)
                for i in PLAYERS:
                    value[i] += mass * r[i]
        survive = after
    return tuple(value)


def certificate(laws: Sequence[Sequence[Q]]) -> dict[str, object]:
    n = validate(laws)
    u = payoff(laws)
    menu, full, never = [], [], []
    for i in PLAYERS:
        candidates = []
        for action in range(n + 1):  # Last entry is Never.
            pure = [Q(0)] * (n + 1)
            pure[action] = Q(1)
            replacement = [list(law) for law in laws]
            replacement[i] = pure
            candidates.append(payoff(replacement)[i])
        w = candidates[-1]
        d = Q(1)
        for j in PLAYERS:
            if j != i:
                d *= laws[j][-1]
        late = w + d * reward(1 << i)[i]
        never.append(w)
        menu.append(max(candidates))
        full.append(max(*candidates, late))
    d0 = laws[1][-1] * laws[2][-1] * laws[3][-1]
    return dict(U=u, B_menu=tuple(menu), B_full=tuple(full),
                E_menu=max(menu[i] - u[i] for i in PLAYERS),
                E_full=max(full[i] - u[i] for i in PLAYERS),
                L0=never[0] + d0 - u[0], D0=d0)


def cyclic_laws(k: int) -> list[list[Q]]:
    if k < 1:
        raise ValueError('k must be positive.')
    n = 3 * k
    laws = [[Q(0)] * (n + 1) for _ in PLAYERS]
    laws[0][-1] = Q(1)
    for i in range(1, 4):
        for block in range(k):
            laws[i][3 * block + i - 1] = Q(1, 2 ** (block + 1))
        laws[i][-1] = Q(1, 2 ** k)
    return laws


def main() -> None:
    print('Coalition, reward')
    for mask in range(1, 16):
        coalition = '{' + ','.join(str(i) for i in PLAYERS if mask & (1 << i)) + '}'
        print(coalition, tuple(int(x) for x in reward(mask)))
    print('\nExact certificates:')
    for k in (1, 2, 3, 4, 6):
        c = certificate(cyclic_laws(k))
        j = Q(1, 8 ** k)
        assert c['U'] == (2 - 2*j, 0, 1-j, 0)
        assert c['B_menu'] == (2 - 2*j, 0, 1, 0)
        assert c['B_full'] == (2-j, 0, 1, 0)
        assert c['E_menu'] == c['E_full'] == c['L0'] == c['D0'] == j
        print(f'K={k}, N={3*k}: {c}')
    print('\nAll exact arithmetic checks passed.')


if __name__ == '__main__':
    main()
