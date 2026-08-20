#!/usr/bin/env python3
"""Exact-rational bounded regressions for the synchronous joint-reset law lift.

All arithmetic uses ``fractions.Fraction``. The program checks the claimed
semiconjugacy and observables on deterministic finite samples; it is not a
proof of the general checked statements.
"""

from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from itertools import product
from random import Random
from typing import Dict, Iterable, Mapping, Optional, Sequence, Tuple


F = Fraction
Vector = Tuple[F, ...]
Semantic = Tuple[Vector, Vector]
Selector = Tuple[bool, ...]  # True = forced-Quit endpoint.
Mode = Tuple[Optional[int], Tuple[Optional[int], ...]]
Distribution = Dict[Mode, F]


def coalition_probability(q: Sequence[F], mask: int) -> F:
    probability = F(1)
    for i, quit_probability in enumerate(q):
        probability *= (
            quit_probability
            if (mask >> i) & 1
            else 1 - quit_probability
        )
    return probability


def opponent_probability(q: Sequence[F], i: int, mask: int) -> F:
    """Return the probability of an opponent mask whose i-th bit is zero."""
    assert ((mask >> i) & 1) == 0
    probability = F(1)
    for j, quit_probability in enumerate(q):
        if j == i:
            continue
        probability *= (
            quit_probability
            if (mask >> j) & 1
            else 1 - quit_probability
        )
    return probability


def initial_semantic(reward: Mapping[int, Vector], n: int) -> Semantic:
    payoff = (F(0),) * n
    cap = tuple(max(F(0), reward[1 << i][i]) for i in range(n))
    return payoff, cap


def endpoints(
    reward: Mapping[int, Vector],
    q: Sequence[F],
    cap: Sequence[F],
    i: int,
) -> Tuple[F, F]:
    n = len(q)
    quit_value = F(0)
    continue_value = F(0)
    opponents = [j for j in range(n) if j != i]

    for bits in range(1 << (n - 1)):
        mask = 0
        for k, j in enumerate(opponents):
            if (bits >> k) & 1:
                mask |= 1 << j
        probability = opponent_probability(q, i, mask)
        quit_value += probability * reward[mask | (1 << i)][i]
        if mask == 0:
            continue_value += probability * cap[i]
        else:
            continue_value += probability * reward[mask][i]

    return quit_value, continue_value


def direct_step(
    reward: Mapping[int, Vector],
    state: Semantic,
    q: Sequence[F],
) -> Tuple[Semantic, Selector]:
    n = len(q)
    payoff, cap = state

    next_payoff = [F(0)] * n
    for mask in range(1 << n):
        probability = coalition_probability(q, mask)
        outcome = payoff if mask == 0 else reward[mask]
        for i in range(n):
            next_payoff[i] += probability * outcome[i]

    next_cap = [F(0)] * n
    selector = [False] * n
    for i in range(n):
        quit_value, continue_value = endpoints(reward, q, cap, i)
        selector[i] = quit_value >= continue_value
        next_cap[i] = quit_value if selector[i] else continue_value

    return (tuple(next_payoff), tuple(next_cap)), tuple(selector)


def elementary_mode(selector: Selector, actual_mask: int, n: int) -> Mode:
    payoff_label: Optional[int] = None if actual_mask == 0 else actual_mask
    cap_labels = []

    for i in range(n):
        opponents = actual_mask & ~(1 << i)
        if selector[i]:
            cap_labels.append(opponents | (1 << i))
        elif opponents == 0:
            cap_labels.append(None)
        else:
            cap_labels.append(opponents)

    return payoff_label, tuple(cap_labels)


def compose(outer: Mode, inner: Mode) -> Mode:
    """Return ``outer ∘ inner``; a nonidentity outer label overwrites."""
    outer_payoff, outer_cap = outer
    inner_payoff, inner_cap = inner
    payoff = inner_payoff if outer_payoff is None else outer_payoff
    cap = tuple(
        inner_cap[i] if outer_cap[i] is None else outer_cap[i]
        for i in range(len(inner_cap))
    )
    return payoff, cap


def mode_support(mode: Mode) -> Tuple[bool, ...]:
    payoff_label, cap_labels = mode
    return (payoff_label is not None,) + tuple(
        label is not None for label in cap_labels
    )


def mode_value(
    reward: Mapping[int, Vector],
    anchor: Semantic,
    mode: Mode,
) -> Semantic:
    anchor_payoff, anchor_cap = anchor
    payoff_label, cap_labels = mode
    payoff = anchor_payoff if payoff_label is None else reward[payoff_label]
    cap = tuple(
        anchor_cap[i] if label is None else reward[label][i]
        for i, label in enumerate(cap_labels)
    )
    return payoff, cap


def project(
    reward: Mapping[int, Vector],
    anchor: Semantic,
    law: Mapping[Mode, F],
) -> Semantic:
    n = len(anchor[0])
    payoff = [F(0)] * n
    cap = [F(0)] * n
    total = F(0)

    for mode, mass in law.items():
        total += mass
        mode_payoff, mode_cap = mode_value(reward, anchor, mode)
        for i in range(n):
            payoff[i] += mass * mode_payoff[i]
            cap[i] += mass * mode_cap[i]

    assert total == 1
    return tuple(payoff), tuple(cap)


def lifted_step(
    law: Mapping[Mode, F],
    q: Sequence[F],
    selector: Selector,
) -> Distribution:
    n = len(q)
    successor: Dict[Mode, F] = defaultdict(F)

    for mode, mass in law.items():
        for actual_mask in range(1 << n):
            probability = coalition_probability(q, actual_mask)
            if probability == 0:
                continue
            elementary = elementary_mode(selector, actual_mask, n)
            successor[compose(elementary, mode)] += mass * probability

    assert sum(successor.values(), F(0)) == 1
    return dict(successor)


def debt(state: Semantic) -> F:
    payoff, cap = state
    return sum(
        (cap_value - payoff_value
         for payoff_value, cap_value in zip(payoff, cap)),
        F(0),
    )


def identity_mass(law: Mapping[Mode, F], coordinate: int) -> F:
    """Identity mass for payoff block -1 or cap coordinate >= 0."""
    if coordinate == -1:
        return sum(
            (mass for (label, _), mass in law.items() if label is None),
            F(0),
        )
    return sum(
        (
            mass
            for (_, cap_labels), mass in law.items()
            if cap_labels[coordinate] is None
        ),
        F(0),
    )


def sample_reward_table(n: int) -> Dict[int, Vector]:
    return {
        mask: tuple(
            F((((mask + 1) * (i + 2) + 3 * i) % 17) - 8, 3)
            for i in range(n)
        )
        for mask in range(1, 1 << n)
    }


def sample_chronology() -> None:
    n = 4
    reward = sample_reward_table(n)
    anchor = initial_semantic(reward, n)
    second_anchor = (
        tuple(F(2 * i - 3, 5) for i in range(n)),
        tuple(F(7 - 3 * i, 4) for i in range(n)),
    )
    roots = [
        (F(1, 5), F(1, 3), F(2, 7), F(1, 2)),
        (F(0), F(3, 8), F(1, 4), F(2, 5)),
        (F(2, 3), F(1, 6), F(0), F(3, 7)),
        (F(1, 9), F(4, 9), F(2, 5), F(1, 8)),
    ]

    identity: Mode = (None, (None,) * n)
    law: Distribution = {identity: F(1)}
    state = anchor
    payoff_identity = F(1)
    cap_identity = [F(1)] * n

    for date, q in enumerate(roots, start=1):
        direct, selector = direct_step(reward, state, q)
        law = lifted_step(law, q, selector)
        lifted = project(reward, anchor, law)
        payoff_identity *= coalition_probability(q, 0)

        for i in range(n):
            if selector[i]:
                cap_identity[i] = F(0)
            else:
                cap_identity[i] *= opponent_probability(q, i, 0)

        assert lifted == direct
        assert identity_mass(law, -1) == payoff_identity
        for i in range(n):
            assert identity_mass(law, i) == cap_identity[i]
        assert debt(lifted) == sum(
            mass * debt(mode_value(reward, anchor, mode))
            for mode, mass in law.items()
        )

        alternate = project(reward, second_anchor, law)
        for i in range(n):
            assert lifted[0][i] - alternate[0][i] == (
                payoff_identity * (anchor[0][i] - second_anchor[0][i])
            )
            assert lifted[1][i] - alternate[1][i] == (
                cap_identity[i] * (anchor[1][i] - second_anchor[1][i])
            )

        state = direct
        print(
            f"date={date} support={len(law)} "
            f"spine={payoff_identity} debt={debt(state)}"
        )


def random_fraction(rng: Random, low: int = -9, high: int = 9) -> F:
    return F(rng.randint(low, high), rng.randint(1, 9))


def random_reward_table(rng: Random, n: int) -> Dict[int, Vector]:
    return {
        mask: tuple(random_fraction(rng) for _ in range(n))
        for mask in range(1, 1 << n)
    }


def random_mode(rng: Random, n: int) -> Mode:
    labels: Tuple[Optional[int], ...] = (None,) + tuple(range(1, 1 << n))
    return (
        rng.choice(labels),
        tuple(rng.choice(labels) for _ in range(n)),
    )


def random_law(rng: Random, n: int) -> Distribution:
    raw: Dict[Mode, int] = defaultdict(int)
    for _ in range(rng.randint(1, 8)):
        raw[random_mode(rng, n)] += rng.randint(1, 12)
    total = sum(raw.values())
    return {mode: F(weight, total) for mode, weight in raw.items()}


def exact_law_sweep() -> int:
    rng = Random(195)
    checked = 0
    for n in range(1, 6):
        for _ in range(30):
            reward = random_reward_table(rng, n)
            anchor: Semantic = (
                tuple(random_fraction(rng) for _ in range(n)),
                tuple(random_fraction(rng) for _ in range(n)),
            )
            law = random_law(rng, n)
            for _ in range(6):
                q = tuple(F(rng.randint(0, 9), 9) for _ in range(n))
                projected = project(reward, anchor, law)
                direct, selector = direct_step(reward, projected, q)
                successor = lifted_step(law, q, selector)
                assert project(reward, anchor, successor) == direct
                checked += 1
    return checked


def syntactic_modes(n: int) -> Iterable[Mode]:
    labels: Tuple[Optional[int], ...] = (None,) + tuple(range(1, 1 << n))
    for entries in product(labels, repeat=n + 1):
        yield entries[0], tuple(entries[1:])


def exhaustive_band_check() -> int:
    modes = list(syntactic_modes(2))
    for mode in modes:
        assert compose(mode, mode) == mode

    checked = 0
    for outer in modes:
        for inner in modes:
            product_mode = compose(outer, inner)
            assert compose(product_mode, outer) == product_mode
            expected_support = tuple(
                a or b
                for a, b in zip(mode_support(outer), mode_support(inner))
            )
            assert mode_support(product_mode) == expected_support
            checked += 1
    return checked


def main() -> None:
    sample_chronology()
    law_cases = exact_law_sweep()
    band_cases = exhaustive_band_check()
    print(f"exact arbitrary-law semiconjugacy cases={law_cases}: PASS")
    print(f"exhaustive two-player band products={band_cases}: PASS")


if __name__ == "__main__":
    main()
