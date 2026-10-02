"""Numerical E3 finite-clock live-branch locator (not a certificate).

For a fixed profile, changing one player's stopping law makes every pure-time
deviation debt affine.  The coordinate minimization is therefore a finite
matrix game.  This script solves that game approximately by Euclidean
mirror-prox, cycles over the four players, and appends one new tail date at a
time.  Exact rational candidates must be checked separately.
"""

from __future__ import annotations

import itertools
import math
from typing import Sequence

import numpy as np


REWARD = np.array(
    [
        (0, 0, 0, 0),
        (1, 5, 0, 0),
        (4, 1, 0, 0),
        (1, 1, 1, 1),
        (0, 0, 1, 4),
        (1, -2.5, 1, 2),
        (0, 1, 1, 1),
        (8, -4, 0, 0),
        (0, 0, 4, 1),
        (1, 0, 1, 1),
        (2, 1, 16, 1),
        (0, 7, 0, 0),
        (1, 1, 1, 1),
        (0, 0, 0, 4),
        (0, 0, 17, 0),
        (-1, -1, -1, -1),
    ],
    dtype=float,
)


def outcome(times: Sequence[int], finite_dates: int) -> int:
    # ``finite_dates`` itself is the tester's first date after the represented
    # support; ``finite_dates + 1`` is the Never sentinel.
    finite = [time for time in times if time <= finite_dates]
    if not finite:
        return 0
    first = min(finite)
    return sum(1 << player for player, time in enumerate(times) if time == first)


def semantics(profile: np.ndarray, finite_dates: int):
    """Prescribed payoff and every pure-time tester value.

    A law has categories ``0,...,finite_dates-1,Never``.  Tester columns are
    the finite dates, one date after the support, and Never.
    """

    never = finite_dates + 1
    categories = list(range(finite_dates)) + [never]
    payoff = np.zeros(4)
    for indices in itertools.product(range(finite_dates + 1), repeat=4):
        probability = math.prod(profile[player, index] for player, index in enumerate(indices))
        if probability:
            times = [categories[index] for index in indices]
            payoff += probability * REWARD[outcome(times, finite_dates)]

    tester = np.empty((4, finite_dates + 2))
    pure_times = list(range(finite_dates)) + [finite_dates, never]
    for player in range(4):
        opponents = [other for other in range(4) if other != player]
        for action, own_time in enumerate(pure_times):
            value = 0.0
            for indices in itertools.product(range(finite_dates + 1), repeat=3):
                times = [0] * 4
                times[player] = own_time
                probability = 1.0
                for other, index in zip(opponents, indices):
                    times[other] = categories[index]
                    probability *= profile[other, index]
                value += probability * REWARD[outcome(times, finite_dates), player]
            tester[player, action] = value
    return payoff, tester


def debt_rows(profile: np.ndarray, finite_dates: int):
    payoff, tester = semantics(profile, finite_dates)
    return payoff, tester, tester - payoff[:, None]


def exploitability(profile: np.ndarray, finite_dates: int):
    payoff, tester, debts = debt_rows(profile, finite_dates)
    return max(0.0, float(debts.max())), payoff, tester, debts


def simplex_projection(vector: np.ndarray) -> np.ndarray:
    ordered = np.sort(vector)[::-1]
    shifted_sums = np.cumsum(ordered) - 1.0
    positive = ordered - shifted_sums / np.arange(1, len(vector) + 1) > 0
    rho = np.nonzero(positive)[0][-1]
    theta = shifted_sums[rho] / (rho + 1.0)
    return np.maximum(vector - theta, 0.0)


def coordinate_matrix(profile: np.ndarray, finite_dates: int, player: int) -> np.ndarray:
    columns = []
    for category in range(finite_dates + 1):
        vertex = profile.copy()
        vertex[player] = 0.0
        vertex[player, category] = 1.0
        _, _, debts = debt_rows(vertex, finite_dates)
        columns.append(np.r_[debts.ravel(), 0.0])
    return np.stack(columns, axis=1)


def solve_matrix_game(
    matrix: np.ndarray, start: np.ndarray, iterations: int = 12000
) -> tuple[np.ndarray, float, float]:
    """Approximately minimize ``max_row matrix[row] dot law``."""

    rows, columns = matrix.shape
    law = np.maximum(start, 1e-10)
    law /= law.sum()
    adversary = np.ones(rows) / rows
    step = 0.9 / max(float(np.linalg.norm(matrix, 2)), 1e-12)
    average_law = np.zeros(columns)
    average_adversary = np.zeros(rows)
    averaging = 0
    for iteration in range(iterations):
        middle_law = simplex_projection(law - step * matrix.T @ adversary)
        middle_adversary = simplex_projection(adversary + step * matrix @ law)
        law = simplex_projection(law - step * matrix.T @ middle_adversary)
        adversary = simplex_projection(adversary + step * matrix @ middle_law)
        if iteration >= iterations // 2:
            average_law += middle_law
            average_adversary += middle_adversary
            averaging += 1
    average_law /= averaging
    average_adversary /= averaging
    upper = float(np.max(matrix @ average_law))
    lower = float(np.min(matrix.T @ average_adversary))
    return average_law, upper, upper - lower


def solve_matrix_game_by_vertices(matrix: np.ndarray) -> tuple[np.ndarray, float]:
    """Float vertex enumeration for the small (at most four-category) LP."""

    categories = matrix.shape[1]
    inequalities = []
    bounds = []
    for row in matrix:
        inequalities.append(np.r_[row[:-1] - row[-1], -1.0])
        bounds.append(-row[-1])
    for category in range(categories - 1):
        inequality = np.zeros(categories)
        inequality[category] = -1.0
        inequalities.append(inequality)
        bounds.append(0.0)
    inequalities.append(np.r_[np.ones(categories - 1), 0.0])
    bounds.append(1.0)
    lhs = np.asarray(inequalities)
    rhs = np.asarray(bounds)
    best = None
    for active in itertools.combinations(range(len(rhs)), categories):
        try:
            point = np.linalg.solve(lhs[list(active)], rhs[list(active)])
        except np.linalg.LinAlgError:
            continue
        if np.max(lhs @ point - rhs) > 3e-9:
            continue
        if best is None or point[-1] < best[-1]:
            best = point
    if best is None:
        raise RuntimeError("coordinate LP vertex enumeration failed")
    law = np.r_[best[:-1], 1.0 - best[:-1].sum()]
    law[np.abs(law) < 1e-12] = 0.0
    return law, float(best[-1])


def optimize_small_exact_coordinates(
    profile: np.ndarray, finite_dates: int, cycles: int = 30
) -> np.ndarray:
    """Coordinate minimization using exhaustive LP vertices (small clocks)."""

    if finite_dates + 1 > 4:
        raise ValueError("vertex mode is intentionally restricted to four categories")
    best_value, _, _, _ = exploitability(profile, finite_dates)
    best_profile = profile.copy()
    print("VERTEX_START", finite_dates, f"{best_value:.12g}", flush=True)
    for cycle in range(cycles):
        previous = value if cycle else best_value
        for player in range(4):
            matrix = coordinate_matrix(profile, finite_dates, player)
            profile[player], _ = solve_matrix_game_by_vertices(matrix)
        value, _, _, _ = exploitability(profile, finite_dates)
        if value < best_value:
            best_value = value
            best_profile = profile.copy()
        print("VERTEX_CYCLE", cycle, f"value={value:.12g}", flush=True)
        if abs(value - previous) < 1e-11 and cycle > 1:
            break
    value, payoff, tester, debts = exploitability(best_profile, finite_dates)
    print("VERTEX_BEST", finite_dates, f"{value:.15g}")
    print(np.array2string(best_profile, precision=12, suppress_small=True))
    print("MAX_DEBT_BY_PLAYER", np.array2string(debts.max(axis=1), precision=12))
    print("ACTIVE_TESTERS", [np.flatnonzero(row >= row.max() - 2e-7).tolist() for row in tester])
    return best_profile


def solve_split_mass_game(
    matrix: np.ndarray,
    start: np.ndarray,
    split: int,
    tail_mass: float,
    iterations: int = 12000,
) -> tuple[np.ndarray, float, float]:
    """Coordinate minimax with prescribed total mass from ``split`` onward."""

    early_matrix = (1.0 - tail_mass) * matrix[:, :split]
    tail_matrix = tail_mass * matrix[:, split:]
    early = np.maximum(start[:split], 1e-10)
    early /= early.sum()
    tail = np.maximum(start[split:], 1e-10)
    tail /= tail.sum()
    adversary = np.ones(matrix.shape[0]) / matrix.shape[0]
    joined = np.concatenate((early_matrix, tail_matrix), axis=1)
    step = 0.9 / max(float(np.linalg.norm(joined, 2)), 1e-12)
    average_early = np.zeros_like(early)
    average_tail = np.zeros_like(tail)
    average_adversary = np.zeros_like(adversary)
    averaging = 0
    for iteration in range(iterations):
        middle_early = simplex_projection(early - step * early_matrix.T @ adversary)
        middle_tail = simplex_projection(tail - step * tail_matrix.T @ adversary)
        middle_adversary = simplex_projection(
            adversary + step * (early_matrix @ early + tail_matrix @ tail)
        )
        early = simplex_projection(early - step * early_matrix.T @ middle_adversary)
        tail = simplex_projection(tail - step * tail_matrix.T @ middle_adversary)
        adversary = simplex_projection(
            adversary
            + step * (early_matrix @ middle_early + tail_matrix @ middle_tail)
        )
        if iteration >= iterations // 2:
            average_early += middle_early
            average_tail += middle_tail
            average_adversary += middle_adversary
            averaging += 1
    average_early /= averaging
    average_tail /= averaging
    average_adversary /= averaging
    law = np.r_[(1.0 - tail_mass) * average_early, tail_mass * average_tail]
    upper = float(np.max(matrix @ law))
    dual_early = float(np.min(early_matrix.T @ average_adversary))
    dual_tail = float(np.min(tail_matrix.T @ average_adversary))
    lower = dual_early + dual_tail
    return law, upper, upper - lower


def optimize_with_live_player3(
    profile: np.ndarray,
    finite_dates: int,
    tail_mass: float,
    cycles: int = 20,
    iterations: int = 12000,
) -> np.ndarray:
    """Cycle coordinate LPs while forcing player 3 to survive beyond date 2."""

    split = 3
    early = profile[3, :split]
    tail = profile[3, split:]
    if early.sum() == 0 or tail.sum() == 0:
        early = np.array((0.8, 1e-9, 0.2))
        tail = np.ones(finite_dates + 1 - split)
    profile[3, :split] = (1.0 - tail_mass) * early / early.sum()
    profile[3, split:] = tail_mass * tail / tail.sum()
    value, _, _, _ = exploitability(profile, finite_dates)
    best_value = value
    best_profile = profile.copy()
    print("LIVE_START", finite_dates, tail_mass, f"{value:.12g}", flush=True)
    for cycle in range(cycles):
        largest_gap = 0.0
        for player in range(4):
            matrix = coordinate_matrix(profile, finite_dates, player)
            if player == 3:
                law, _, gap = solve_split_mass_game(
                    matrix, profile[player], split, tail_mass, iterations
                )
            else:
                law, _, gap = solve_matrix_game(matrix, profile[player], iterations)
            profile[player] = law
            largest_gap = max(largest_gap, gap)
        value, _, _, _ = exploitability(profile, finite_dates)
        if value < best_value:
            best_value = value
            best_profile = profile.copy()
        print(
            "LIVE_CYCLE",
            cycle,
            f"value={value:.12g}",
            f"best={best_value:.12g}",
            f"coordinate_gap<={largest_gap:.3g}",
            flush=True,
        )
    value, payoff, tester, debts = exploitability(best_profile, finite_dates)
    print("LIVE_BEST", finite_dates, tail_mass, f"{value:.15g}")
    print(np.array2string(best_profile, precision=12, suppress_small=True))
    print("MAX_DEBT_BY_PLAYER", np.array2string(debts.max(axis=1), precision=12))
    print("ACTIVE_TESTERS", [np.flatnonzero(row >= row.max() - 2e-7).tolist() for row in tester])
    return best_profile


def optimize(
    profile: np.ndarray,
    finite_dates: int,
    cycles: int = 20,
    iterations: int = 12000,
) -> np.ndarray:
    value, _, _, _ = exploitability(profile, finite_dates)
    print("START", finite_dates, f"{value:.12g}", flush=True)
    for cycle in range(cycles):
        before = value
        largest_gap = 0.0
        for player in range(4):
            matrix = coordinate_matrix(profile, finite_dates, player)
            law, _, gap = solve_matrix_game(matrix, profile[player], iterations)
            profile[player] = law
            largest_gap = max(largest_gap, gap)
        value, payoff, tester, debts = exploitability(profile, finite_dates)
        print(
            "CYCLE",
            cycle,
            f"value={value:.12g}",
            f"coordinate_gap<={largest_gap:.3g}",
            flush=True,
        )
        if before - value < 2e-9 and largest_gap < 2e-6:
            break
    value, payoff, tester, debts = exploitability(profile, finite_dates)
    print("BEST", finite_dates, f"{value:.15g}")
    print("PROFILE")
    print(np.array2string(profile, precision=12, suppress_small=True))
    print("PAYOFF", np.array2string(payoff, precision=12))
    print("MAX_DEBT_BY_PLAYER", np.array2string(debts.max(axis=1), precision=12))
    print("ACTIVE_TESTERS", [np.flatnonzero(row >= row.max() - 2e-7).tolist() for row in tester])
    return profile


def append_tail_date(profile: np.ndarray) -> np.ndarray:
    return np.insert(profile, profile.shape[1] - 1, 0.0, axis=1)


def main() -> None:
    # Exact four-date certificate (7.272), converted to floating point.
    profile = np.array(
        [
            (0, 17 / 60, 43 / 225, 0, 473 / 900),
            (41 / 52, 0, 11 / 65, 11 / 260, 0),
            (16 / 45, 0, 0, 29 / 45, 0),
            (4 / 5, 0, 1 / 5, 0, 0),
        ],
        dtype=float,
    )
    for finite_dates in range(4, 9):
        if profile.shape[1] != finite_dates + 1:
            profile = append_tail_date(profile)
        profile = optimize(profile, finite_dates)


if __name__ == "__main__":
    main()
