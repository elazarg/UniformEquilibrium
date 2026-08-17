#!/usr/bin/env python3
"""Bounded numerical search for four-player quitting counterexample candidates.

The program screens four-player quitting reward tables against necessary-looking
structural filters and then attacks the survivors with a battery of bounded
architecture classes.  A table that survives the battery is a *candidate* only:
the battery searches finitely many parameterized profile families with
floating-point optimization, so failing to find an approximate equilibrium is
bounded numerical evidence and never a proof that no behavioral profile is an
approximate equilibrium.

Everything here is standard-library Python and deterministic given ``--seed``.
"""

from __future__ import annotations

import argparse
import json
import math
import random
import time
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass, field
from itertools import combinations, permutations, product
from typing import Callable, Optional, Sequence

N = 4
PLAYERS = tuple(range(N))
MASKS = tuple(range(1 << N))
NONEMPTY = tuple(range(1, 1 << N))

Vector = tuple[float, ...]
Table = tuple[Vector, ...]  # indexed by coalition mask; entry 0 is the zero row
Hazards = Sequence[Sequence[float]]  # [phase][player]

PAYOFF_LO = -4.0
PAYOFF_HI = 4.0


# --------------------------------------------------------------------------- #
# Reward tables
# --------------------------------------------------------------------------- #


def mask_of(players: Sequence[int]) -> int:
    answer = 0
    for who in players:
        answer |= 1 << who
    return answer


def table_from_dict(entries: dict[tuple[int, ...], Sequence[float]]) -> Table:
    rows: list[Vector] = [(0.0,) * N for _ in MASKS]
    for coalition, payoff in entries.items():
        rows[mask_of(coalition)] = tuple(float(x) for x in payoff)
    return tuple(rows)


def seed_table() -> Table:
    """Solan-Vieille (2001) Section 3 table, players indexed 0..3 for 1..4."""

    return table_from_dict(
        {
            (0,): (1, 4, 0, 0),
            (1,): (4, 1, 0, 0),
            (2,): (0, 0, 1, 4),
            (3,): (0, 0, 4, 1),
            (0, 1): (1, 1, 1, 1),
            (0, 2): (1, 1, 1, 0),
            (0, 3): (1, 0, 1, 1),
            (1, 2): (0, 1, 1, 1),
            (1, 3): (1, 1, 0, 1),
            (2, 3): (1, 1, 1, 1),
            (0, 1, 2): (1, 0, 0, 0),
            (0, 1, 3): (0, 1, 0, 0),
            (0, 2, 3): (0, 0, 0, 1),
            (1, 2, 3): (0, 0, 1, 0),
            (0, 1, 2, 3): (-1, -1, -1, -1),
        }
    )


def table_to_json(table: Table) -> dict[str, list[float]]:
    return {
        "{" + ",".join(str(i + 1) for i in PLAYERS if mask >> i & 1) + "}": list(
            table[mask]
        )
        for mask in NONEMPTY
    }


def solo(table: Table, i: int) -> float:
    """Player ``i``'s payoff when ``i`` quits alone."""

    return table[1 << i][i]


# --------------------------------------------------------------------------- #
# Linear algebra helpers
# --------------------------------------------------------------------------- #


def solve_linear(matrix: list[list[float]], rhs: list[float]) -> Optional[list[float]]:
    """Gaussian elimination with partial pivoting; ``None`` when singular."""

    size = len(rhs)
    aug = [row[:] + [rhs[k]] for k, row in enumerate(matrix)]
    for col in range(size):
        pivot = max(range(col, size), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot][col]) < 1e-12:
            return None
        aug[col], aug[pivot] = aug[pivot], aug[col]
        scale = aug[col][col]
        for j in range(col, size + 1):
            aug[col][j] /= scale
        for r in range(size):
            if r == col:
                continue
            factor = aug[r][col]
            if factor == 0.0:
                continue
            for j in range(col, size + 1):
                aug[r][j] -= factor * aug[col][j]
    return [aug[r][size] for r in range(size)]


def cyclic_solve(constants: Sequence[float], hazards: Sequence[float]) -> list[float]:
    """Solve ``V_t = constants[t] + (1 - hazards[t]) * V_{t+1}`` on a cycle.

    Phases are described by their absorption probability rather than by their
    survival factor.  That is not a stylistic choice.  The optimizers push
    hazards below machine epsilon while chasing the fine-block limit, and there
    ``1 - hazard`` rounds to exactly ``1.0``: the hazard is annihilated, while
    the numerator still carries the true value, so the solve mixes two
    inconsistent pictures and returns nonsense.  It once produced an
    exploitability of ``-0.38``, which is impossible.

    Working from hazards, the total absorption around the cycle is
    ``-expm1(sum log1p(-hazard))``, which keeps full relative accuracy however
    small the hazards are, and the fine-block limit comes out correctly as the
    hazard-weighted average of the phase payoffs.  Absorption counts as absent
    only when it is exactly zero, in which case the cycle never ends and the
    value is the never-absorbed payoff of zero.
    """

    period = len(constants)
    log_survival = 0.0
    numerator = 0.0
    certain = False
    for k in range(period):
        numerator += math.exp(log_survival) * constants[k]
        hazard = hazards[k]
        if hazard >= 1.0:
            certain = True
            break
        if hazard > 0.0:
            log_survival += math.log1p(-hazard)
    absorption = 1.0 if certain else -math.expm1(log_survival)
    head = numerator / absorption if absorption > 0.0 else 0.0
    values = [0.0] * period
    values[0] = head
    for t in range(period - 1, 0, -1):
        follower = values[t + 1] if t + 1 < period else head
        values[t] = constants[t] + (1.0 - hazards[t]) * follower
    return values


# --------------------------------------------------------------------------- #
# Nelder-Mead (pure Python; scipy is not available in this environment)
# --------------------------------------------------------------------------- #


def nelder_mead(
    objective: Callable[[Sequence[float]], float],
    start: Sequence[float],
    step: float = 1.0,
    max_iter: int = 200,
    tol: float = 1e-10,
) -> tuple[list[float], float]:
    size = len(start)
    simplex = [list(start)]
    for i in range(size):
        point = list(start)
        point[i] += step
        simplex.append(point)
    values = [objective(point) for point in simplex]
    for _ in range(max_iter):
        order = sorted(range(size + 1), key=lambda k: values[k])
        simplex = [simplex[k] for k in order]
        values = [values[k] for k in order]
        if values[-1] - values[0] < tol:
            break
        centroid = [
            sum(simplex[k][j] for k in range(size)) / size for j in range(size)
        ]
        worst = simplex[-1]
        reflected = [centroid[j] + (centroid[j] - worst[j]) for j in range(size)]
        value_reflected = objective(reflected)
        if value_reflected < values[0]:
            expanded = [
                centroid[j] + 2.0 * (centroid[j] - worst[j]) for j in range(size)
            ]
            value_expanded = objective(expanded)
            if value_expanded < value_reflected:
                simplex[-1], values[-1] = expanded, value_expanded
            else:
                simplex[-1], values[-1] = reflected, value_reflected
        elif value_reflected < values[-2]:
            simplex[-1], values[-1] = reflected, value_reflected
        else:
            contracted = [
                centroid[j] + 0.5 * (worst[j] - centroid[j]) for j in range(size)
            ]
            value_contracted = objective(contracted)
            if value_contracted < values[-1]:
                simplex[-1], values[-1] = contracted, value_contracted
            else:
                best = simplex[0]
                for k in range(1, size + 1):
                    simplex[k] = [
                        best[j] + 0.5 * (simplex[k][j] - best[j]) for j in range(size)
                    ]
                    values[k] = objective(simplex[k])
    best_index = min(range(size + 1), key=lambda k: values[k])
    return simplex[best_index], values[best_index]


def sigmoid(z: float) -> float:
    if z >= 0.0:
        return 1.0 / (1.0 + math.exp(-min(z, 60.0)))
    return math.exp(max(z, -60.0)) / (1.0 + math.exp(max(z, -60.0)))


def logit(x: float) -> float:
    x = min(max(x, 1e-9), 1.0 - 1e-9)
    return math.log(x / (1.0 - x))


# --------------------------------------------------------------------------- #
# Exact evaluator for periodic per-stage hazard profiles
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class PhaseData:
    """Per-phase quantities of a periodic independent-hazard stage."""

    absorption: float  # probability somebody quits, accurate for tiny hazards
    absorbed: tuple[float, ...]  # expected absorbed payoff, on path
    quit_now: tuple[float, ...]  # deviator i quits this stage (collisions exact)
    others_absorbed: tuple[float, ...]  # deviator i continues, others absorb
    others_absorption: tuple[float, ...]  # probability some opponent of i quits


def stage_absorption(hazard: Sequence[float], skip: Optional[int]) -> float:
    """Probability that somebody other than ``skip`` quits in one stage.

    Computed as ``-expm1(sum log1p(-p))`` rather than ``1 - prod (1 - p)`` so
    that hazards far below machine epsilon survive; the subtractive form rounds
    each factor to one and loses them entirely.
    """

    log_survival = 0.0
    for i in PLAYERS:
        if i == skip:
            continue
        rate = hazard[i]
        if rate >= 1.0:
            return 1.0
        if rate > 0.0:
            log_survival += math.log1p(-rate)
    return -math.expm1(log_survival)


def phase_data(table: Table, hazard: Sequence[float]) -> PhaseData:
    complement = [1.0 - hazard[i] for i in PLAYERS]
    probability = [0.0] * len(MASKS)
    for mask in MASKS:
        value = 1.0
        for i in PLAYERS:
            value *= hazard[i] if mask >> i & 1 else complement[i]
        probability[mask] = value
    absorbed = [0.0] * N
    for mask in NONEMPTY:
        weight = probability[mask]
        if weight == 0.0:
            continue
        row = table[mask]
        for j in PLAYERS:
            absorbed[j] += weight * row[j]
    quit_now = [0.0] * N
    others_absorbed = [0.0] * N
    for i in PLAYERS:
        bit = 1 << i
        for mask in MASKS:
            if mask & bit:
                continue
            weight = 1.0
            for j in PLAYERS:
                if j == i:
                    continue
                weight *= hazard[j] if mask >> j & 1 else complement[j]
            if weight == 0.0:
                continue
            quit_now[i] += weight * table[mask | bit][i]
            if mask:
                others_absorbed[i] += weight * table[mask][i]
    return PhaseData(
        stage_absorption(hazard, None),
        tuple(absorbed),
        tuple(quit_now),
        tuple(others_absorbed),
        tuple(stage_absorption(hazard, i) for i in PLAYERS),
    )


def periodic_exploitability(table: Table, hazards: Hazards) -> float:
    """Exploitability of a periodic hazard profile, exactly.

    On-path values solve the periodic absorption recursion.  Each deviator faces
    a finite phase-indexed optimal-stopping problem, whose value is the maximum
    over the ``2^P`` deterministic phase-indexed stopping policies; that maximum
    is attained by a deterministic Markov policy, so the enumeration is exact up
    to floating point.
    """

    period = len(hazards)
    data = [phase_data(table, hazards[t]) for t in range(period)]
    stage_hazards = [data[t].absorption for t in range(period)]
    on_path = [
        cyclic_solve([data[t].absorbed[j] for t in range(period)], stage_hazards)
        for j in PLAYERS
    ]
    worst = -math.inf
    for i in PLAYERS:
        best_response = [-math.inf] * period
        for policy in range(1 << period):
            constants = []
            policy_hazards = []
            for t in range(period):
                if policy >> t & 1:
                    constants.append(data[t].quit_now[i])
                    policy_hazards.append(1.0)
                else:
                    constants.append(data[t].others_absorbed[i])
                    policy_hazards.append(data[t].others_absorption[i])
            values = cyclic_solve(constants, policy_hazards)
            for t in range(period):
                if values[t] > best_response[t]:
                    best_response[t] = values[t]
        for t in range(period):
            gap = best_response[t] - on_path[i][t]
            if gap > worst:
                worst = gap
    return worst


# --------------------------------------------------------------------------- #
# Attack A: stationary profiles
# --------------------------------------------------------------------------- #

STATIONARY_GRID = (0.0, 0.02, 0.1, 0.3, 0.6, 1.0)


def attack_stationary(table: Table) -> dict:
    best_value = math.inf
    best_point: list[float] = [0.0] * N
    for point in product(STATIONARY_GRID, repeat=N):
        value = periodic_exploitability(table, [list(point)])
        if value < best_value:
            best_value, best_point = value, list(point)

    def objective(z: Sequence[float]) -> float:
        return periodic_exploitability(table, [[sigmoid(v) for v in z]])

    starts = [[logit(x) for x in best_point]]
    starts += [
        [logit(x) for x in point]
        for point in ((0.05,) * N, (0.5,) * N, (0.3, 0.05, 0.3, 0.05), (0.9,) * N)
    ]
    for start in starts:
        point, value = nelder_mead(objective, start, step=1.5, max_iter=250)
        if value < best_value:
            best_value = value
            best_point = [sigmoid(v) for v in point]
    return {"exploitability": best_value, "rates": best_point}


# --------------------------------------------------------------------------- #
# Attack B: one-quitter cyclic (fine-block limit)
# --------------------------------------------------------------------------- #


def cyclic_orders() -> list[tuple[int, ...]]:
    orders: list[tuple[int, ...]] = []
    for size in (2, 3, 4):
        for subset in combinations(PLAYERS, size):
            head = subset[0]
            for rest in permutations(subset[1:]):
                orders.append((head,) + rest)
    return orders


CYCLIC_ORDERS = tuple(cyclic_orders())


def one_quitter_report(
    table: Table, cycle: Sequence[int], rates: Sequence[float]
) -> tuple[float, float]:
    """Return (exact fine-block exploitability, classical IC violation).

    Fine-block limit assumption: within the block assigned to player ``v_k``
    only ``v_k`` quits, so a deviator who quits inside that block never collides
    with ``v_k`` and receives ``r_{{i}}``.
    """

    period = len(cycle)
    rows = [table[1 << cycle[k]] for k in range(period)]
    on_path = [
        cyclic_solve([rates[k] * rows[k][j] for k in range(period)], rates)
        for j in PLAYERS
    ]
    worst = -math.inf
    for i in PLAYERS:
        alone = solo(table, i)
        best_response = [-math.inf] * period
        for policy in range(1 << period):
            constants = []
            policy_hazards = []
            for t in range(period):
                if policy >> t & 1:
                    constants.append(alone)
                    policy_hazards.append(1.0)
                elif cycle[t] == i:
                    constants.append(0.0)
                    policy_hazards.append(0.0)
                else:
                    constants.append(rates[t] * rows[t][i])
                    policy_hazards.append(rates[t])
            values = cyclic_solve(constants, policy_hazards)
            for t in range(period):
                if values[t] > best_response[t]:
                    best_response[t] = values[t]
        for t in range(period):
            worst = max(worst, best_response[t] - on_path[i][t])
    violation = -math.inf
    for t in range(period):
        for i in PLAYERS:
            violation = max(violation, solo(table, i) - on_path[i][t])
        mover = cycle[t]
        follower = on_path[mover][(t + 1) % period]
        violation = max(violation, follower - solo(table, mover))
    return worst, violation


B_STARTS = (0.02, 0.1, 0.4, 0.8)


def attack_one_quitter(table: Table) -> dict:
    best = {"exploitability": math.inf, "cycle": None, "rates": None}
    for cycle in CYCLIC_ORDERS:
        period = len(cycle)

        def objective(z: Sequence[float], cycle=cycle) -> float:
            return one_quitter_report(table, cycle, [sigmoid(v) for v in z])[0]

        for level in B_STARTS:
            start = [logit(level)] * period
            point, value = nelder_mead(objective, start, step=1.5, max_iter=150)
            if value < best["exploitability"]:
                best = {
                    "exploitability": value,
                    "cycle": [c + 1 for c in cycle],
                    "rates": [sigmoid(v) for v in point],
                }
    return best


# --------------------------------------------------------------------------- #
# Attack C: two-quitter periodic schedules
# --------------------------------------------------------------------------- #

PAIRS = tuple(combinations(PLAYERS, 2))


def pair_schedules() -> list[tuple[tuple[int, int], ...]]:
    schedules: list[tuple[tuple[int, int], ...]] = []
    for a in range(len(PAIRS)):
        for b in range(a, len(PAIRS)):
            schedules.append((PAIRS[a], PAIRS[b]))
    for triple in combinations(range(len(PAIRS)), 3):
        for rest in permutations(triple[1:]):
            schedules.append(tuple(PAIRS[k] for k in (triple[0],) + rest))
    return schedules


PAIR_SCHEDULES = tuple(pair_schedules())
C_STARTS = ((0.05, 0.05), (0.3, 0.3), (0.05, 0.5))


def hazards_from_pairs(
    schedule: Sequence[tuple[int, int]], values: Sequence[float]
) -> list[list[float]]:
    hazards = [[0.0] * N for _ in schedule]
    for t, pair in enumerate(schedule):
        hazards[t][pair[0]] = values[2 * t]
        hazards[t][pair[1]] = values[2 * t + 1]
    return hazards


def attack_two_quitter(table: Table) -> dict:
    best = {"exploitability": math.inf, "schedule": None, "hazards": None}
    for schedule in PAIR_SCHEDULES:
        period = len(schedule)

        def objective(z: Sequence[float], schedule=schedule) -> float:
            return periodic_exploitability(
                table, hazards_from_pairs(schedule, [sigmoid(v) for v in z])
            )

        for level in C_STARTS:
            start = [logit(level[k % 2]) for k in range(2 * period)]
            point, value = nelder_mead(objective, start, step=1.5, max_iter=120)
            if value < best["exploitability"]:
                best = {
                    "exploitability": value,
                    "schedule": [
                        [pair[0] + 1, pair[1] + 1] for pair in schedule
                    ],
                    "hazards": hazards_from_pairs(
                        schedule, [sigmoid(v) for v in point]
                    ),
                }
    return best


# --------------------------------------------------------------------------- #
# Attack D: general periodic hazard profiles
# --------------------------------------------------------------------------- #

D_PERIODS = (1, 2, 3, 4, 6)
D_STARTS = (0.02, 0.08, 0.25, 0.5, 0.8)


def attack_general_periodic(table: Table) -> dict:
    best = {"exploitability": math.inf, "period": None, "hazards": None}
    rng = random.Random(0x51_4E_43_53)
    for period in D_PERIODS:

        def objective(z: Sequence[float], period=period) -> float:
            hazards = [
                [sigmoid(z[t * N + i]) for i in PLAYERS] for t in range(period)
            ]
            return periodic_exploitability(table, hazards)

        starts: list[list[float]] = [
            [logit(level)] * (N * period) for level in D_STARTS
        ]
        for _ in range(3):
            starts.append(
                [logit(rng.uniform(0.01, 0.9)) for _ in range(N * period)]
            )
        for start in starts:
            point, value = nelder_mead(objective, start, step=1.5, max_iter=200)
            if value < best["exploitability"]:
                best = {
                    "exploitability": value,
                    "period": period,
                    "hazards": [
                        [sigmoid(point[t * N + i]) for i in PLAYERS]
                        for t in range(period)
                    ],
                }
    return best


# --------------------------------------------------------------------------- #
# Necessary-condition filters
# --------------------------------------------------------------------------- #


def filter_toggle_instability(table: Table, margin: float) -> tuple[bool, list]:
    stable: list[int] = []
    for mask in MASKS:
        found = False
        for i in PLAYERS:
            up = table[mask | (1 << i)][i]
            down = table[mask & ~(1 << i)][i]
            if max(up, down) >= table[mask][i] + margin:
                found = True
                break
        if not found:
            stable.append(mask)
    return not stable, stable


def filter_viable_owner(table: Table, margin: float) -> tuple[bool, list]:
    owners = [i + 1 for i in PLAYERS if solo(table, i) >= margin]
    return bool(owners), owners


def viable_owners(table: Table, margin: float) -> list[int]:
    return [i for i in PLAYERS if solo(table, i) > -margin]


def filter_collider_preemptor(table: Table, margin: float) -> tuple[bool, dict]:
    detail: dict[str, dict] = {}
    ok = True
    for i in viable_owners(table, margin):
        colliders = [
            j + 1
            for j in PLAYERS
            if j != i and table[(1 << i) | (1 << j)][j] >= table[1 << i][j] + margin
        ]
        preemptors = [
            j + 1
            for j in PLAYERS
            if j != i and solo(table, j) >= table[1 << i][j] + margin
        ]
        detail[str(i + 1)] = {"colliders": colliders, "preemptors": preemptors}
        if not colliders or not preemptors:
            ok = False
    return ok, detail


def preemption_edges(table: Table, margin: float) -> dict[int, list[int]]:
    return {
        i: [
            j
            for j in PLAYERS
            if j != i and solo(table, j) >= table[1 << i][j] + margin
        ]
        for i in PLAYERS
    }


def filter_preemption_cycle(table: Table, margin: float) -> tuple[bool, dict]:
    edges = preemption_edges(table, margin)
    owners = viable_owners(table, margin)
    closure = all(edges[i] for i in owners)
    if closure:
        for i in PLAYERS:
            for j in edges[i]:
                if not edges[j]:
                    closure = False
                    break
            if not closure:
                break
    detail = {
        "edges": {str(i + 1): [j + 1 for j in edges[i]] for i in PLAYERS},
        "closure": closure,
        "cycle": None,
    }
    if not closure:
        return False, detail
    reachable: set[int] = set()
    stack = list(owners)
    while stack:
        node = stack.pop()
        if node in reachable:
            continue
        reachable.add(node)
        stack.extend(edges[node])
    colour = {node: 0 for node in reachable}
    found: list[int] = []

    def visit(node: int, path: list[int]) -> bool:
        colour[node] = 1
        for nxt in edges[node]:
            if nxt not in reachable:
                continue
            if colour[nxt] == 1:
                found.extend(path[path.index(nxt) :] + [nxt])
                return True
            if colour[nxt] == 0 and visit(nxt, path + [nxt]):
                return True
        colour[node] = 2
        return False

    for owner in owners:
        if colour.get(owner, 2) == 0 and visit(owner, [owner]):
            break
    detail["cycle"] = [node + 1 for node in found] if found else None
    return bool(found), detail


def normalized_matrix(table: Table) -> list[list[float]]:
    return [[table[1 << j][i] - solo(table, i) for j in PLAYERS] for i in PLAYERS]


def iterated_normal_core(table: Table) -> list[int]:
    matrix = normalized_matrix(table)
    survivors = set(PLAYERS)
    while True:
        removed = {
            i
            for i in survivors
            if not any(matrix[i][j] <= 0.0 for j in survivors if j != i)
        }
        if not removed:
            return sorted(survivors)
        survivors -= removed
        if not survivors:
            return []


def filter_normal_core(table: Table) -> tuple[bool, dict]:
    core = iterated_normal_core(table)
    return len(core) >= 4, {"core": [i + 1 for i in core], "size": len(core)}


def lcp_simplex_screen(table: Table, tol: float = 1e-7) -> Optional[dict]:
    """Heuristic simplex-normalized screen for an obvious equilibrium payoff.

    For every nonempty support ``S`` inside the iterated normal core the square
    system ``sum_j lambda_j r_{{j}}(i) = r_{{i}}(i)`` for ``i in S`` together
    with ``sum_j lambda_j + lambda_0 = 1`` is solved exactly.  The tail weight
    ``lambda_0`` carries payoff zero.  A solution counts when all weights are
    nonnegative, every remaining core player weakly prefers the mixture to
    quitting alone, and every non-core player weakly prefers it to
    ``max(0, r_{{i}}(i))``.

    A strictly positive tail weight is only accepted when every solo-self payoff
    ``r_{{i}}(i)`` is at most zero.  Positive tail weight means the profile
    spends its quitting weight and then continues forever for a payoff of zero,
    which no player with a positive solo-self payoff would sit through, so such
    a mixture is not a strategically consistent screen hit.

    This is a screen, not a formal equilibrium gate.
    """

    core = iterated_normal_core(table)
    if not core:
        return None
    for size in range(1, len(core) + 1):
        for support in combinations(core, size):
            dimension = size + 1
            matrix = [[0.0] * dimension for _ in range(dimension)]
            rhs = [0.0] * dimension
            for row, i in enumerate(support):
                for col, j in enumerate(support):
                    matrix[row][col] = table[1 << j][i]
                rhs[row] = solo(table, i)
            for col in range(dimension):
                matrix[size][col] = 1.0
            rhs[size] = 1.0
            solution = solve_linear(matrix, rhs)
            if solution is None:
                continue
            weights = solution[:size]
            tail = solution[size]
            if tail < -tol or any(w < -tol for w in weights):
                continue
            if tail > tol and any(solo(table, i) > tol for i in PLAYERS):
                continue
            # A positive tail leaves the post-spending continuation at 0, so
            # late-stage incentive compatibility needs every solo-self payoff
            # to be at most 0; otherwise the tail-weighted mixture is not a
            # strategically consistent screen hit.
            if tail > tol and any(solo(table, i) > tol for i in PLAYERS):
                continue
            mixture = [
                sum(weights[col] * table[1 << j][i] for col, j in enumerate(support))
                for i in PLAYERS
            ]
            feasible = True
            for i in PLAYERS:
                if i in support:
                    continue
                floor = solo(table, i) if i in core else max(0.0, solo(table, i))
                if mixture[i] < floor - tol:
                    feasible = False
                    break
            if feasible:
                return {
                    "support": [j + 1 for j in support],
                    "weights": weights,
                    "tail_weight": tail,
                    "payoff": mixture,
                }
    return None


def filter_no_lcp_solution(table: Table) -> tuple[bool, dict]:
    hit = lcp_simplex_screen(table)
    return hit is None, {"solution": hit}


def run_filters(table: Table, margin: float) -> dict:
    toggle_ok, toggle_detail = filter_toggle_instability(table, margin)
    owner_ok, owner_detail = filter_viable_owner(table, margin)
    collide_ok, collide_detail = filter_collider_preemptor(table, margin)
    cycle_ok, cycle_detail = filter_preemption_cycle(table, margin)
    core_ok, core_detail = filter_normal_core(table)
    lcp_ok, lcp_detail = filter_no_lcp_solution(table)
    checks = {
        "1_toggle_instability": {
            "pass": toggle_ok,
            "stable_coalitions": toggle_detail,
        },
        "2_viable_owner": {"pass": owner_ok, "owners": owner_detail},
        "3_collider_and_preemptor": {"pass": collide_ok, "detail": collide_detail},
        "4_preemption_cycle": {"pass": cycle_ok, "detail": cycle_detail},
        "5_iterated_normal_core": {"pass": core_ok, "detail": core_detail},
        "6_no_lcp_solution": {"pass": lcp_ok, "detail": lcp_detail},
    }
    checks["all_1_to_5"] = all(
        checks[key]["pass"]
        for key in (
            "1_toggle_instability",
            "2_viable_owner",
            "3_collider_and_preemptor",
            "4_preemption_cycle",
            "5_iterated_normal_core",
        )
    )
    checks["all_1_to_6"] = checks["all_1_to_5"] and lcp_ok
    return checks


FILTER_NAMES = (
    "1_toggle_instability",
    "2_viable_owner",
    "3_collider_and_preemptor",
    "4_preemption_cycle",
    "5_iterated_normal_core",
    "6_no_lcp_solution",
)


def first_failing_filter(table: Table, margin: float) -> Optional[str]:
    """Filter gate for the hill-climbing loop.

    Returns the name of the first filter the table fails, in numbered order, or
    ``None`` when it passes all six.  Reporting which filter rejected shows
    which necessary condition actually binds on the perturbation kernel.
    """

    if not filter_toggle_instability(table, margin)[0]:
        return FILTER_NAMES[0]
    if not filter_viable_owner(table, margin)[0]:
        return FILTER_NAMES[1]
    if not filter_collider_preemptor(table, margin)[0]:
        return FILTER_NAMES[2]
    if not filter_preemption_cycle(table, margin)[0]:
        return FILTER_NAMES[3]
    if not filter_normal_core(table)[0]:
        return FILTER_NAMES[4]
    if not filter_no_lcp_solution(table)[0]:
        return FILTER_NAMES[5]
    return None


# --------------------------------------------------------------------------- #
# Attack battery
# --------------------------------------------------------------------------- #

ATTACK_ORDER = (
    ("stationary", attack_stationary),
    ("one_quitter_cyclic", attack_one_quitter),
    ("general_periodic", attack_general_periodic),
    ("two_quitter_periodic", attack_two_quitter),
)


def run_battery(table: Table, abandon_at: float = -math.inf) -> dict:
    """Run the battery and report the smallest exploitability found.

    Each attack searches its whole parameterized family, so the value it reports
    is that family's own best found exploitability.  Attacks run cheapest first
    and the remaining ones are skipped once the running minimum drops to
    ``abandon_at``, at which point the caller has already decided the table is
    uninteresting.  Pass ``-inf`` to force the complete breakdown.

    When the battery is abandoned the reported score is only an upper bound on
    the minimum over the whole battery, and the untried attacks are recorded as
    ``null``.
    """

    breakdown: dict[str, Optional[dict]] = {name: None for name, _ in ATTACK_ORDER}
    score = math.inf
    binding = None
    abandoned = False
    for name, attack in ATTACK_ORDER:
        report = attack(table)
        breakdown[name] = report
        if report["exploitability"] < score:
            score = report["exploitability"]
            binding = name
        if score <= abandon_at:
            abandoned = True
            break
    return {
        "score": score,
        "binding_attack": binding,
        "abandoned": abandoned,
        "breakdown": breakdown,
    }


# --------------------------------------------------------------------------- #
# Evaluator self-check
# --------------------------------------------------------------------------- #


def self_check(trials: int = 300, seed: int = 7) -> dict:
    """Cross-validate the periodic evaluator on random tables and profiles.

    Four independent identities are checked:

    * the closed-form on-path recursion agrees with the decomposition of a
      phase into the deviator's own quit branch and continue branch;
    * exploitability is never negative, since the deviator's pure-policy
      maximum dominates his on-path mixture;
    * the same non-negativity holds for the separate one-quitter evaluator; and
    * for period one the policy enumeration reproduces the stationary closed
      form ``max(quit-now value, never value) - on-path value``.

    Half the trials draw hazards log-uniformly down to ``1e-20`` rather than
    uniformly on the unit interval.  That regime is not exotic: the attacks
    optimize freely and Nelder-Mead routinely parks hazards near zero chasing
    the fine-block limit, and it is precisely where the cyclic solve's
    absorption term is delicate.  Uniform draws never reach it, and stopping at
    ``1e-16`` is not enough either -- the failure that motivated the hazard
    formulation needed hazards below machine epsilon, where ``1 - hazard``
    rounds to one.

    The stationary comparison deliberately skips the log-uniform trials.  Its
    reference forms total absorption by subtracting a product of factors from
    one, which is the cancellation the cyclic solve avoids, so below roughly
    ``1e-8`` the reference is the less accurate of the two and the comparison
    would measure the reference's error.  The near-degenerate regime is covered
    instead by the decomposition identity and the two non-negativity identities,
    all of which run on every trial.
    """

    rng = random.Random(seed)
    decomposition = 0.0
    negativity = 0.0
    cyclic_negativity = 0.0
    stationary_gap = 0.0
    stationary_trials = 0
    for trial in range(trials):
        rows = [[0.0] * N for _ in MASKS]
        for mask in NONEMPTY:
            for i in PLAYERS:
                rows[mask][i] = rng.uniform(PAYOFF_LO, PAYOFF_HI)
        table = tuple(tuple(row) for row in rows)
        period = rng.choice((1, 2, 3, 4))
        tiny = trial % 2 == 1

        def draw() -> float:
            if tiny:
                return 10.0 ** rng.uniform(-20.0, 0.0)
            return rng.uniform(0.0, 1.0)

        hazards = [[draw() for _ in PLAYERS] for _ in range(period)]
        cycle_size = rng.choice((2, 3, 4))
        cycle = tuple(rng.sample(PLAYERS, cycle_size))
        cyclic_value = one_quitter_report(
            table, cycle, [draw() for _ in range(cycle_size)]
        )[0]
        cyclic_negativity = max(cyclic_negativity, -cyclic_value)
        data = [phase_data(table, hazards[t]) for t in range(period)]
        stage_hazards = [data[t].absorption for t in range(period)]
        on_path = [
            cyclic_solve(
                [data[t].absorbed[j] for t in range(period)], stage_hazards
            )
            for j in PLAYERS
        ]
        for i in PLAYERS:
            for t in range(period):
                rate = hazards[t][i]
                follower = on_path[i][(t + 1) % period]
                branch = rate * data[t].quit_now[i] + (1.0 - rate) * (
                    data[t].others_absorbed[i]
                    + (1.0 - data[t].others_absorption[i]) * follower
                )
                decomposition = max(decomposition, abs(on_path[i][t] - branch))
        value = periodic_exploitability(table, hazards)
        negativity = max(negativity, -value)
        if period == 1 and not tiny:
            stationary_trials += 1
            rates = hazards[0]
            closed = stationary_closed_form(table, rates)
            stationary_gap = max(stationary_gap, abs(closed - value))
    return {
        "trials": trials,
        "rng_seed": seed,
        "on_path_decomposition_max_error": decomposition,
        "max_negative_exploitability": negativity,
        "max_negative_one_quitter_exploitability": cyclic_negativity,
        "stationary_closed_form_trials": stationary_trials,
        "stationary_closed_form_max_error": stationary_gap,
        "passed": (
            decomposition < 1e-9
            and negativity < 1e-9
            and cyclic_negativity < 1e-9
            and stationary_gap < 1e-9
        ),
    }


def stationary_closed_form(table: Table, rates: Sequence[float]) -> float:
    """Exploitability of a stationary profile, written out independently.

    This duplicates no code from :func:`periodic_exploitability` on purpose: it
    exists only so the self-check compares two separate derivations.
    """

    survive = 1.0
    for i in PLAYERS:
        survive *= 1.0 - rates[i]
    value = [0.0] * N
    for mask in NONEMPTY:
        weight = 1.0
        for i in PLAYERS:
            weight *= rates[i] if mask >> i & 1 else 1.0 - rates[i]
        for j in PLAYERS:
            value[j] += weight * table[mask][j]
    if survive < 1.0:
        value = [v / (1.0 - survive) for v in value]
    else:
        value = [0.0] * N
    worst = -math.inf
    for i in PLAYERS:
        bit = 1 << i
        quit_now = 0.0
        never_numerator = 0.0
        absorbing = 0.0
        for mask in MASKS:
            if mask & bit:
                continue
            weight = 1.0
            for j in PLAYERS:
                if j == i:
                    continue
                weight *= rates[j] if mask >> j & 1 else 1.0 - rates[j]
            quit_now += weight * table[mask | bit][i]
            if mask:
                never_numerator += weight * table[mask][i]
                absorbing += weight
        never = never_numerator / absorbing if absorbing > 1e-15 else 0.0
        worst = max(worst, max(quit_now, never) - value[i])
    return worst


# --------------------------------------------------------------------------- #
# Search
# --------------------------------------------------------------------------- #


def perturb(
    table: Table,
    rng: random.Random,
    sigma: float,
    jump_sigma: float,
    jump_probability: float,
) -> Table:
    """Perturb one to eight entries, occasionally with a much larger step.

    Small steps refine a basin; the chain then stalls in it.  With probability
    ``jump_probability`` the step size is ``jump_sigma`` instead of ``sigma``,
    which is what lets a chain leave a basin without waiting for a restart.
    """

    entries = [(mask, i) for mask in NONEMPTY for i in PLAYERS]
    count = rng.randint(1, 8)
    chosen = rng.sample(entries, count)
    width = jump_sigma if rng.random() < jump_probability else sigma
    rows = [list(row) for row in table]
    for mask, i in chosen:
        value = rows[mask][i] + rng.gauss(0.0, width)
        rows[mask][i] = min(PAYOFF_HI, max(PAYOFF_LO, value))
    return tuple(tuple(row) for row in rows)


@dataclass
class SearchState:
    evaluations: int = 0
    proposals: int = 0
    filter_rejections: int = 0
    restarts: int = 0
    termination: str = "evaluations"
    filter_rejection_counts: dict[str, int] = field(default_factory=dict)
    binding_counts: dict[str, int] = field(default_factory=dict)
    trajectory: list[dict] = field(default_factory=list)


def hill_climb(
    start: Table,
    start_result: dict,
    margin: float,
    sigma: float,
    jump_sigma: float,
    jump_probability: float,
    max_evaluations: int,
    time_budget: float,
    patience: int,
    rng: random.Random,
) -> tuple[Table, dict, SearchState]:
    """Random-restart hill climbing on the battery score.

    A chain accepts a perturbation only when the battery score strictly
    increases.  After ``patience`` consecutive non-improving evaluations the
    chain restarts from the seed table, so the run is a sequence of independent
    ascents rather than one chain stuck in the first basin it reaches.
    """

    state = SearchState()
    current, current_result = start, start_result
    best, best_result = start, start_result
    stale = 0
    deadline = time.time() + time_budget
    while state.evaluations < max_evaluations:
        if time.time() >= deadline:
            state.termination = "time_budget"
            break
        state.proposals += 1
        candidate = perturb(current, rng, sigma, jump_sigma, jump_probability)
        failing = first_failing_filter(candidate, margin)
        if failing is not None:
            state.filter_rejections += 1
            state.filter_rejection_counts[failing] = (
                state.filter_rejection_counts.get(failing, 0) + 1
            )
            continue
        # Abandoning exactly at the incumbent score is sound for the accept
        # decision: a table whose running minimum already sits at or below the
        # incumbent cannot be accepted, because the minimum over the whole
        # battery is no larger.  Every accepted table therefore carries a
        # complete, untruncated battery score.
        result = run_battery(candidate, current_result["score"])
        state.evaluations += 1
        name = result["binding_attack"]
        state.binding_counts[name] = state.binding_counts.get(name, 0) + 1
        if result["score"] > current_result["score"] + 1e-12:
            stale = 0
            current, current_result = candidate, result
            if result["score"] > best_result["score"]:
                best, best_result = candidate, result
            state.trajectory.append(
                {
                    "evaluation": state.evaluations,
                    "score": result["score"],
                    "binding_attack": name,
                    "restart": state.restarts,
                }
            )
        else:
            stale += 1
            if stale >= patience:
                stale = 0
                state.restarts += 1
                current, current_result = start, start_result
    return best, best_result, state


# --------------------------------------------------------------------------- #
# Deep re-attack
# --------------------------------------------------------------------------- #

DEEP_GRID = (0.0, 0.01, 0.03, 0.08, 0.15, 0.3, 0.5, 0.75, 1.0)


def deep_pair_schedules() -> tuple[tuple[tuple[int, int], ...], ...]:
    """Pair schedules for the stress test, including period four.

    The search-time attack C stops at period three.  That gap was not harmless:
    a table survived both the search battery and an earlier version of this
    stress test at about ``0.029``, and adding period-four schedules dropped it
    to ``1.7e-05``.  Every apparent survivor so far has died to a wider schedule
    set, so the set is kept as wide as the runtime allows.
    """

    schedules = list(PAIR_SCHEDULES)
    for quad in combinations(range(len(PAIRS)), 4):
        schedules.append(tuple(PAIRS[k] for k in quad))
    return tuple(schedules)


DEEP_PAIR_SCHEDULES = deep_pair_schedules()


def deep_reattack(table: Table, seed: int = 4041) -> dict:
    """Hammer a single table far harder than the search-time battery.

    The search-time attacks are deliberately cheap, because they run hundreds of
    times.  A table that survives them is only interesting if it also survives a
    search with many more restarts, a finer stationary grid, and periods beyond
    the six the search-time general-periodic attack tries.  This routine is the
    stress test, and its verdict supersedes the search-time score for the one
    table it is pointed at.
    """

    rng = random.Random(seed)
    report: dict[str, dict] = {}

    best_value = math.inf
    best_point: list[float] = [0.0] * N
    for point in product(DEEP_GRID, repeat=N):
        value = periodic_exploitability(table, [list(point)])
        if value < best_value:
            best_value, best_point = value, list(point)
    for _ in range(30):
        start = [logit(rng.uniform(0.005, 0.95)) for _ in PLAYERS]
        point, value = nelder_mead(
            lambda z: periodic_exploitability(table, [[sigmoid(v) for v in z]]),
            start,
            step=1.5,
            max_iter=400,
        )
        if value < best_value:
            best_value, best_point = value, [sigmoid(v) for v in point]
    report["stationary"] = {"exploitability": best_value, "rates": best_point}

    best_value = math.inf
    best_detail: dict = {}
    for cycle in CYCLIC_ORDERS:
        for _ in range(10):
            start = [logit(rng.uniform(0.002, 0.9)) for _ in cycle]
            point, value = nelder_mead(
                lambda z, cycle=cycle: one_quitter_report(
                    table, cycle, [sigmoid(v) for v in z]
                )[0],
                start,
                step=1.5,
                max_iter=300,
            )
            if value < best_value:
                best_value = value
                best_detail = {
                    "cycle": [c + 1 for c in cycle],
                    "rates": [sigmoid(v) for v in point],
                }
    report["one_quitter_cyclic"] = {"exploitability": best_value, **best_detail}

    best_value = math.inf
    best_detail = {}
    for schedule in DEEP_PAIR_SCHEDULES:
        for _ in range(8):
            start = [
                logit(rng.uniform(0.01, 0.9)) for _ in range(2 * len(schedule))
            ]
            point, value = nelder_mead(
                lambda z, schedule=schedule: periodic_exploitability(
                    table, hazards_from_pairs(schedule, [sigmoid(v) for v in z])
                ),
                start,
                step=1.5,
                max_iter=300,
            )
            if value < best_value:
                best_value = value
                best_detail = {
                    "schedule": [[pair[0] + 1, pair[1] + 1] for pair in schedule],
                    "hazards": hazards_from_pairs(
                        schedule, [sigmoid(v) for v in point]
                    ),
                }
    report["two_quitter_periodic"] = {"exploitability": best_value, **best_detail}

    best_value = math.inf
    best_detail = {}
    for period in range(1, 9):
        for _ in range(25):
            start = [logit(rng.uniform(0.005, 0.9)) for _ in range(N * period)]
            point, value = nelder_mead(
                lambda z, period=period: periodic_exploitability(
                    table,
                    [
                        [sigmoid(z[t * N + i]) for i in PLAYERS]
                        for t in range(period)
                    ],
                ),
                start,
                step=1.5,
                max_iter=350,
            )
            if value < best_value:
                best_value = value
                best_detail = {
                    "period": period,
                    "hazards": [
                        [sigmoid(point[t * N + i]) for i in PLAYERS]
                        for t in range(period)
                    ],
                }
    report["general_periodic"] = {"exploitability": best_value, **best_detail}

    score = min(entry["exploitability"] for entry in report.values())
    binding = min(report, key=lambda k: report[k]["exploitability"])
    return {"score": score, "binding_attack": binding, "breakdown": report}


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #


@dataclass(frozen=True)
class ChainRequest:
    """Everything one independent hill-climbing chain needs.

    Chains are pure functions of this record, which is what makes running them
    in separate processes safe and keeps the merged report deterministic.
    """

    seed: int
    margin: float
    sigma: float
    jump_sigma: float
    jump_probability: float
    evaluations: int
    time_budget: float
    patience: int
    start_table: Table
    start_result: dict


def run_chain(request: ChainRequest) -> dict:
    rng = random.Random(request.seed)
    best_table, best_result, state = hill_climb(
        request.start_table,
        request.start_result,
        request.margin,
        request.sigma,
        request.jump_sigma,
        request.jump_probability,
        request.evaluations,
        request.time_budget,
        request.patience,
        rng,
    )
    full = run_battery(best_table)
    deep = deep_reattack(best_table)
    return {
        "seed": request.seed,
        "evaluations": state.evaluations,
        "proposals": state.proposals,
        "filter_rejections": state.filter_rejections,
        "filter_rejection_counts": state.filter_rejection_counts,
        "restarts": state.restarts,
        "termination": state.termination,
        "reproducible_across_machines": state.termination == "evaluations",
        "accepted_trajectory": state.trajectory,
        "best": {
            "table": table_to_json(best_table),
            "search_score": full["score"],
            "binding_attack": full["binding_attack"],
            "breakdown": full["breakdown"],
            "filters": run_filters(best_table, request.margin),
            "deep_reattack": deep,
        },
    }


def table_from_json(entries: dict[str, Sequence[float]]) -> Table:
    rows: list[Vector] = [(0.0,) * N for _ in MASKS]
    for label, payoff in entries.items():
        members = [int(token) - 1 for token in label.strip("{}").split(",")]
        rows[mask_of(members)] = tuple(float(x) for x in payoff)
    return tuple(rows)


def run_reattack(args: argparse.Namespace) -> None:
    started = time.time()
    with open(args.reattack, encoding="utf-8") as handle:
        source = json.load(handle)
    if "best" in source:
        best = source["best"]
    else:
        best = max(
            (chain["best"] for chain in source["chains"]),
            key=lambda entry: entry["search_score"],
        )
    table = table_from_json(best["table"])
    searched = best.get("score", best["search_score"])
    deep = deep_reattack(table)
    payload = {
        "source_file": args.reattack,
        "table": table_to_json(table),
        "filters": run_filters(table, args.margin),
        "search_time_score": searched,
        "deep": deep,
        "kill_epsilon": args.kill,
        "survives_deep_battery": deep["score"] > args.kill,
        "runtime_seconds": time.time() - started,
        "claim": (
            "A deeper bounded search over the same four architecture classes. "
            "Surviving it is still bounded numerical evidence, not a theorem."
        ),
    }
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2)
        handle.write("\n")
    print(f"deep re-attack of {args.reattack}")
    for name, entry in deep["breakdown"].items():
        print(f"  {name}: {entry['exploitability']:.6f}")
    print(
        f"search-time score {searched:.6f} -> deep score {deep['score']:.6f} "
        f"(binding {deep['binding_attack']}); "
        f"survives kill {args.kill}: {payload['survives_deep_battery']}"
    )
    print(f"wrote {args.output}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--margin", type=float, default=0.1, help="filter margin g")
    parser.add_argument(
        "--kill", type=float, default=0.02, help="exploitability that kills a candidate"
    )
    parser.add_argument("--sigma", type=float, default=0.25, help="perturbation sigma")
    parser.add_argument(
        "--jump-sigma",
        type=float,
        default=0.6,
        help="step size of the occasional larger perturbation",
    )
    parser.add_argument(
        "--jump-probability",
        type=float,
        default=0.2,
        help="probability a proposal uses the larger step size",
    )
    parser.add_argument(
        "--evaluations",
        type=int,
        default=500,
        help="evaluation budget per chain",
    )
    parser.add_argument("--time-budget", type=float, default=600.0)
    parser.add_argument(
        "--restart-patience",
        type=int,
        default=40,
        help="non-improving evaluations before the chain restarts from the seed",
    )
    parser.add_argument(
        "--chain-seeds",
        default="40,41,42",
        help="comma-separated RNG seeds, one independent chain each",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=3,
        help="chains to run concurrently; chains are independent and each is "
        "a pure function of its seed, so this changes speed and not results",
    )
    parser.add_argument(
        "--self-check-trials",
        type=int,
        default=300,
        help="random evaluator cross-validation instances",
    )
    parser.add_argument(
        "--output",
        default=(
            "Experiments/singleton_collision_candidate_search/results.json"
        ),
    )
    parser.add_argument(
        "--reattack",
        default=None,
        help=(
            "path of a results file whose best table should be stress tested "
            "instead of running a search"
        ),
    )
    args = parser.parse_args()

    if args.reattack is not None:
        run_reattack(args)
        return

    started = time.time()
    validation = self_check(args.self_check_trials)
    if not validation["passed"]:
        raise SystemExit(f"evaluator self-check failed: {validation}")
    table = seed_table()

    seed_filters = run_filters(table, args.margin)
    seed_battery = run_battery(table)
    seed_ic = {}
    for cycle in CYCLIC_ORDERS:
        report = seed_battery["breakdown"]["one_quitter_cyclic"]
        if report["cycle"] == [c + 1 for c in cycle]:
            seed_ic = {
                "cycle": report["cycle"],
                "classical_violation": one_quitter_report(
                    table, cycle, report["rates"]
                )[1],
            }
    known_pairs = ((0, 2), (1, 3))

    def known_objective(z: Sequence[float]) -> float:
        return periodic_exploitability(
            table, hazards_from_pairs(known_pairs, [sigmoid(v) for v in z])
        )

    known_value = math.inf
    known_point: list[float] = [logit(0.05)] * 4
    for level in (0.01, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7):
        point, value = nelder_mead(
            known_objective, [logit(level)] * 4, step=1.5, max_iter=400
        )
        if value < known_value:
            known_value, known_point = value, point
    seed_known_repair = {
        "schedule": [[1, 3], [2, 4]],
        "exploitability": known_value,
        "hazards": hazards_from_pairs(known_pairs, [sigmoid(v) for v in known_point]),
    }

    seeds = [int(token) for token in args.chain_seeds.split(",") if token.strip()]
    remaining = max(0.0, args.time_budget - (time.time() - started))
    requests = [
        ChainRequest(
            seed=seed,
            margin=args.margin,
            sigma=args.sigma,
            jump_sigma=args.jump_sigma,
            jump_probability=args.jump_probability,
            evaluations=args.evaluations,
            time_budget=remaining,
            patience=args.restart_patience,
            start_table=table,
            start_result=seed_battery,
        )
        for seed in seeds
    ]
    workers = max(1, min(args.workers, len(requests)))
    if workers == 1:
        chains = [run_chain(request) for request in requests]
    else:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            chains = list(pool.map(run_chain, requests))

    totals: dict[str, int] = {}
    for chain in chains:
        for name, count in chain["filter_rejection_counts"].items():
            totals[name] = totals.get(name, 0) + count
    best_chain = max(chains, key=lambda c: c["best"]["deep_reattack"]["score"])
    survivors = [
        chain["seed"]
        for chain in chains
        if chain["best"]["deep_reattack"]["score"] > args.kill
    ]

    payload = {
        "model": {
            "players": N,
            "payoff_clamp": [PAYOFF_LO, PAYOFF_HI],
            "no_quit_payoff": 0.0,
        },
        "parameters": {
            "margin_g": args.margin,
            "kill_epsilon": args.kill,
            "perturbation_sigma": args.sigma,
            "evaluation_budget": args.evaluations,
            "time_budget_seconds": args.time_budget,
            "restart_patience": args.restart_patience,
            "jump_sigma": args.jump_sigma,
            "jump_probability": args.jump_probability,
            "chain_seeds": seeds,
        },
        "evaluator_self_check": validation,
        "seed_table": {
            "source": "Solan-Vieille 2001, Section 3",
            "table": table_to_json(table),
            "filters": seed_filters,
            "battery": seed_battery,
            "one_quitter_classical_violation": seed_ic,
            "known_period_two_repair": seed_known_repair,
        },
        "chains": chains,
        "filter_rejection_histogram": totals,
        "verdict": {
            "best_chain_seed": best_chain["seed"],
            "best_search_score": max(
                chain["best"]["search_score"] for chain in chains
            ),
            "best_deep_score": best_chain["best"]["deep_reattack"]["score"],
            "deep_binding_attack": (
                best_chain["best"]["deep_reattack"]["binding_attack"]
            ),
            "chain_seeds_surviving_deep_battery": survivors,
            "any_candidate_survives": bool(survivors),
        },
        "runtime_seconds": time.time() - started,
        "claim": (
            "Bounded numerical evidence over four parameterized architecture "
            "classes. The search-time battery is cheap and its score is only an "
            "upper bound, so each chain's best table is additionally stress "
            "tested by the deep re-attack, whose verdict supersedes it. A table "
            "surviving even that is a candidate only; no statement about all "
            "behavioral profiles is established."
        ),
    }
    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=False)
        handle.write("\n")
    print(json.dumps(payload["seed_table"]["filters"], indent=2))
    print(
        "evaluator self-check: "
        f"decomposition {validation['on_path_decomposition_max_error']:.2e}, "
        f"negativity {validation['max_negative_exploitability']:.2e}, "
        f"cyclic negativity "
        f"{validation['max_negative_one_quitter_exploitability']:.2e}, "
        f"stationary {validation['stationary_closed_form_max_error']:.2e}"
    )
    print("seed battery:")
    for name, report in seed_battery["breakdown"].items():
        print(f"  {name}: {report['exploitability']:.6f}")
    print(f"known period-2 repair {{1,3}}/{{2,4}}: {known_value:.6f}")
    for chain in chains:
        best = chain["best"]
        deep = best["deep_reattack"]
        print(
            f"chain seed {chain['seed']}: {chain['evaluations']} evaluations, "
            f"{chain['filter_rejections']} filter rejections, "
            f"{chain['restarts']} restarts, on {chain['termination']}; "
            f"search score {best['search_score']:.6f} "
            f"({best['binding_attack']}) -> deep score {deep['score']:.6f} "
            f"({deep['binding_attack']})"
        )
    print(f"filter rejection histogram: {totals}")
    print(
        f"verdict: best deep score "
        f"{payload['verdict']['best_deep_score']:.6f} from seed "
        f"{payload['verdict']['best_chain_seed']}; "
        f"any candidate survives kill {args.kill}: "
        f"{payload['verdict']['any_candidate_survives']}"
    )
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
