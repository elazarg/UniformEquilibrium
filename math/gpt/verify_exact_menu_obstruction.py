#!/usr/bin/env python3
"""Numerical and exact-algebra checks for a four-player finite-menu obstruction.

The all-equilibria, all-deadlines assertion is proved in the accompanying
mathematical argument, not by this script. This script checks the explicit
families, evaluates every pure finite-menu deviation plus the unrestricted
late deviation and Never, and verifies the algebraic constants exactly.

Requires Python 3.10+ and SymPy. Run:
    python verify_exact_menu_obstruction.py
"""
from __future__ import annotations

import itertools
import math
from typing import Sequence

import sympy as sp

NPLAYERS = 4
CORE_REWARDS = {
    1: (1, 3, 3),
    2: (3, 0, 3),
    4: (3, 3, 0),
    3: (4, 1, 3),
    5: (1, 3, 4),
    6: (3, 4, 1),
    7: (2, 2, 2),
}
Row = tuple[float, float, float, float]


def reward(mask: int) -> tuple[float, ...]:
    """Mask zero also returns the zero Never payoff."""
    if not 0 <= mask < 16:
        raise ValueError("A coalition mask must lie in {0,...,15}.")
    core = mask & 7
    if not core:
        return (0.0,) * 4
    return tuple(float(x) for x in CORE_REWARDS[core]) + (
        0.0 if mask & 8 else 1.0,
    )


def validate(rows: Sequence[Row]) -> None:
    if not rows:
        raise ValueError("The deadline must be positive.")
    if any(len(q) != 4 or any(not 0.0 <= x <= 1.0 for x in q) for q in rows):
        raise ValueError("Each row must contain four probabilities in [0,1].")


def row_mass(q: Row, mask: int) -> float:
    return math.prod(q[i] if mask & (1 << i) else 1.0 - q[i] for i in range(4))


def prescribed_payoff(rows: Sequence[Row]) -> tuple[float, ...]:
    validate(rows)
    survival = 1.0
    value = [0.0] * 4
    for q in rows:
        for mask in range(1, 16):
            mass = survival * row_mass(q, mask)
            r = reward(mask)
            for i in range(4):
                value[i] += mass * r[i]
        survival *= row_mass(q, 0)
    return tuple(value)


def pure_reply_payoffs(rows: Sequence[Row], player: int) -> tuple[list[float], float, float]:
    """Return replies at displayed dates, fresh date N, and Never.

    After the deadline all opponents play Never, so the fresh-date reply
    equals every later finite reply. Maximizing this finite list therefore
    computes the full behavioral best-response cap, not just a truncation.
    """
    validate(rows)
    if player not in range(4):
        raise ValueError("Invalid player.")
    opponents = [j for j in range(4) if j != player]
    live = 1.0
    earlier_reward = 0.0
    dated_values: list[float] = []
    for q in rows:
        quit_value = 0.0
        continue_reward = 0.0
        for actions in itertools.product((False, True), repeat=3):
            mask = sum(1 << j for j, a in zip(opponents, actions) if a)
            mass = math.prod(q[j] if a else 1.0 - q[j]
                             for j, a in zip(opponents, actions))
            quit_value += mass * reward(mask | (1 << player))[player]
            if mask:
                continue_reward += mass * reward(mask)[player]
        dated_values.append(earlier_reward + live * quit_value)
        earlier_reward += live * continue_reward
        live *= math.prod(1.0 - q[j] for j in opponents)
    late_value = earlier_reward + live * reward(1 << player)[player]
    return dated_values, late_value, earlier_reward


def debts(rows: Sequence[Row]) -> tuple[float, float, tuple[float, ...]]:
    u = prescribed_payoff(rows)
    menu_debts = []
    full_debts = []
    for i in range(4):
        displayed, late, never = pure_reply_payoffs(rows, i)
        menu_cap = max(displayed + [never])
        full_cap = max(menu_cap, late)
        menu_debts.append(max(0.0, menu_cap - u[i]))
        full_debts.append(max(0.0, full_cap - u[i]))
    return max(menu_debts), max(full_debts), tuple(full_debts)


def close(actual: float, expected: float, *, label: str) -> None:
    if not math.isclose(actual, expected, rel_tol=5e-10, abs_tol=5e-12):
        raise AssertionError(f"{label}: got {actual:.16g}, expected {expected:.16g}")


def exact_algebra_checks() -> tuple[float, float, float]:
    t = sp.Rational(3, 2) - sp.sqrt(2)
    beta = 7 * t
    survival = (1 - 2 * t) * (1 - t) * (1 - 4 * t)
    assert sp.simplify(4 * t**2 - 12 * t + 1) == 0
    assert sp.simplify((1 - t) * (1 - 4 * t) - beta) == 0
    assert sp.simplify(survival - (35 * sp.sqrt(2) - 49)) == 0
    assert 100 > 49 * 2  # beta > 1/2
    assert 42**2 * 2 > 59**2  # 3(1-beta) > 1

    # Verify the pure-coalition identity behind the one-stage differences.
    solo = (1, 0, 0)
    for i in range(3):
        for mask in range(8):
            if mask & (1 << i):
                continue
            next_bit = int(bool(mask & (1 << ((i + 1) % 3))))
            prev_bit = int(bool(mask & (1 << ((i - 1) % 3))))
            continuation_contribution = solo[i] if not mask else 0
            lhs = reward(mask | (1 << i))[i] - reward(mask)[i]
            rhs = continuation_contribution + next_bit - 2 * prev_bit
            assert lhs == rhs, (i, mask, lhs, rhs)
    return float(t), float(beta), float(survival)


def main() -> None:
    t, beta, survival = exact_algebra_checks()
    last: Row = (2 * t, t, 4 * t, 0.0)
    wait: Row = (0.0, 0.0, 0.0, 0.0)
    pivot: Row = (0.25, 0.0, 0.0, 0.0)

    # The mathematical proof shows these are ALL exact menu equilibria.
    for n in (1, 2, 3, 5, 10, 30, 100):
        rows = [wait] * (n - 1) + [last]
        menu, full, full_by_player = debts(rows)
        close(menu, 0.0, label=f"exact family N={n}: menu debt")
        close(full, beta, label=f"exact family N={n}: full debt")
        for i in range(1, 4):
            close(full_by_player[i], 0.0, label=f"N={n}, player {i}: debt")
        close(math.prod(row_mass(q, 0) for q in rows), survival,
              label=f"exact family N={n}: joint Never mass")

    # Finite approximate equilibria with vanishing unrestricted debt.
    for n in (1, 2, 5, 10, 30):
        menu, full, _ = debts([pivot] * n)
        close(menu, 0.75**n, label=f"approximate family N={n}: menu debt")
        close(full, 0.75**n, label=f"approximate family N={n}: full debt")

    # Check the stationary Bellman and row-perfection equations exactly.
    q = (sp.Rational(1, 4), sp.Integer(0), sp.Integer(0), sp.Integer(0))
    v = (sp.Integer(1), sp.Integer(3), sp.Integer(3), sp.Integer(1))
    for i in range(4):
        opponents = [j for j in range(4) if j != i]
        Q = sp.Integer(0)
        C = sp.Integer(0)
        for actions in itertools.product((False, True), repeat=3):
            mask = sum(1 << j for j, a in zip(opponents, actions) if a)
            mass = sp.prod(q[j] if a else 1 - q[j]
                           for j, a in zip(opponents, actions))
            Q += mass * sp.Integer(int(reward(mask | (1 << i))[i]))
            C += mass * (sp.Integer(int(reward(mask)[i])) if mask else v[i])
        assert sp.simplify(q[i] * Q + (1 - q[i]) * C - v[i]) == 0
        assert Q <= v[i] and C <= v[i]
        if q[i] > 0:
            assert Q == v[i]
        if q[i] < 1:
            assert C == v[i]

    print("Exact algebra, stationary row identities, and finite deviation checks passed.")
    print(f"t = {t:.15g}")
    print(f"beta = {beta:.15g} > 1/2")
    print(f"Joint Never mass of every exact finite-menu equilibrium = {survival:.15g}")
    print("The universal uniqueness and all-equilibria statements require the proof;")
    print("this program does not enumerate or certify all Nash equilibria.")


if __name__ == "__main__":
    main()
