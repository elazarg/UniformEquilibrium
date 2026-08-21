"""Attacks A-D and the Nelder-Mead they are optimized with.

Faithful port of the attack battery in
``Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py``:

* **A. stationary** -- full ``6^4`` grid plus Nelder-Mead from the grid optimum
  and four fixed starts;
* **B. one_quitter_cyclic** -- the twenty cycles on subsets of size 2, 3, 4, in
  the fine-block limit, four starts each;
* **C. two_quitter_periodic** -- the 21 period-two and 40 period-three pair
  schedules, three starts each;
* **D. general_periodic** -- free hazards for periods 1, 2, 3, 4, 6 from five
  fixed and three seeded-random starts.

Each attack searches its own parameterized family, so what it reports is that
family's best found exploitability -- an upper bound produced by bounded
floating-point search, never a statement about all behavioral profiles.

Every report additionally carries ``profile``, the hazard matrix in wire form,
so a killing profile can be replayed later by the shared library.  For attacks
A, C and D the profile reproduces the reported number under the shared
evaluator.  Attack B is the exception and says so: it is evaluated in the
fine-block limit, where a deviator quitting inside the scheduled quitter's
block never collides with him, so re-evaluating B's profile with the periodic
evaluator gives a different (collision-exact) number.  B's reports therefore
also carry ``profile_exploitability``, the periodic evaluator's verdict on the
same hazard matrix, which is the number the library uses.
"""

from __future__ import annotations

import math
import random
from itertools import combinations, permutations, product
from typing import Callable, Sequence

from .evaluator import cyclic_solve, periodic_exploitability
from .model import N, PLAYERS, Hazards, Table, hazards_to_wire, solo


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


def _wire(hazards: Hazards) -> dict:
    return hazards_to_wire(hazards)


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
    return {
        "exploitability": best_value,
        "rates": best_point,
        "profile": _wire([best_point]),
    }


def attack_stationary_quick(table: Table) -> dict:
    """Grid plus two short polishes; the quick level's version of attack A."""

    best_value = math.inf
    best_point: list[float] = [0.0] * N
    for point in product(STATIONARY_GRID, repeat=N):
        value = periodic_exploitability(table, [list(point)])
        if value < best_value:
            best_value, best_point = value, list(point)

    def objective(z: Sequence[float]) -> float:
        return periodic_exploitability(table, [[sigmoid(v) for v in z]])

    for start in ([logit(x) for x in best_point], [logit(0.05)] * N):
        point, value = nelder_mead(objective, start, step=1.5, max_iter=60)
        if value < best_value:
            best_value = value
            best_point = [sigmoid(v) for v in point]
    return {
        "exploitability": best_value,
        "rates": best_point,
        "profile": _wire([best_point]),
    }


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


def hazards_from_cycle(
    cycle: Sequence[int], rates: Sequence[float]
) -> list[list[float]]:
    """The literal hazard matrix of a one-quitter schedule.

    Under this matrix collisions are possible where the fine-block limit
    assumes there are none, so the periodic evaluator's verdict on it differs
    from :func:`one_quitter_report`.
    """

    hazards = [[0.0] * N for _ in cycle]
    for t, who in enumerate(cycle):
        hazards[t][who] = rates[t]
    return hazards


B_STARTS = (0.02, 0.1, 0.4, 0.8)


def _one_quitter_result(
    table: Table, cycle: Sequence[int], rates: Sequence[float], value: float
) -> dict:
    hazards = hazards_from_cycle(cycle, rates)
    return {
        "exploitability": value,
        "cycle": [c + 1 for c in cycle],
        "rates": list(rates),
        "profile": _wire(hazards),
        "profile_exploitability": periodic_exploitability(table, hazards),
        "fine_block_limit": True,
    }


def attack_one_quitter(table: Table) -> dict:
    best = {"exploitability": math.inf, "cycle": None, "rates": None}
    best_cycle: Sequence[int] = ()
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
                best_cycle = cycle
    if best["cycle"] is None:
        return best
    return _one_quitter_result(table, best_cycle, best["rates"], best["exploitability"])


def attack_one_quitter_quick(table: Table) -> dict:
    """All twenty cycles, one start each, short polish; the quick version of B."""

    best_value = math.inf
    best_cycle: Sequence[int] = ()
    best_rates: list[float] = []
    for cycle in CYCLIC_ORDERS:
        period = len(cycle)

        def objective(z: Sequence[float], cycle=cycle) -> float:
            return one_quitter_report(table, cycle, [sigmoid(v) for v in z])[0]

        start = [logit(0.1)] * period
        point, value = nelder_mead(objective, start, step=1.5, max_iter=60)
        if value < best_value:
            best_value = value
            best_cycle = cycle
            best_rates = [sigmoid(v) for v in point]
    if not best_cycle:
        return {"exploitability": math.inf, "cycle": None, "rates": None}
    return _one_quitter_result(table, best_cycle, best_rates, best_value)


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
PERIOD_TWO_SCHEDULES = tuple(
    schedule for schedule in PAIR_SCHEDULES if len(schedule) == 2
)
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
    if best["hazards"] is not None:
        best["profile"] = _wire(best["hazards"])
    return best


def attack_two_quitter_quick(table: Table) -> dict:
    """Period-two schedules only, one start each; the quick version of C."""

    best = {"exploitability": math.inf, "schedule": None, "hazards": None}
    for schedule in PERIOD_TWO_SCHEDULES:
        period = len(schedule)

        def objective(z: Sequence[float], schedule=schedule) -> float:
            return periodic_exploitability(
                table, hazards_from_pairs(schedule, [sigmoid(v) for v in z])
            )

        start = [logit(0.05)] * (2 * period)
        point, value = nelder_mead(objective, start, step=1.5, max_iter=60)
        if value < best["exploitability"]:
            best = {
                "exploitability": value,
                "schedule": [[pair[0] + 1, pair[1] + 1] for pair in schedule],
                "hazards": hazards_from_pairs(schedule, [sigmoid(v) for v in point]),
            }
    if best["hazards"] is not None:
        best["profile"] = _wire(best["hazards"])
    return best


# --------------------------------------------------------------------------- #
# Attack D: general periodic hazard profiles
# --------------------------------------------------------------------------- #

D_PERIODS = (1, 2, 3, 4, 6)
D_STARTS = (0.02, 0.08, 0.25, 0.5, 0.8)
D_SEED = 0x51_4E_43_53


def attack_general_periodic(table: Table) -> dict:
    best = {"exploitability": math.inf, "period": None, "hazards": None}
    rng = random.Random(D_SEED)
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
    if best["hazards"] is not None:
        best["profile"] = _wire(best["hazards"])
    return best


QUICK_D_PERIODS = (1, 2)
QUICK_D_STARTS = (0.02, 0.25)


def attack_general_periodic_quick(table: Table) -> dict:
    """Periods one and two, two fixed starts; the quick version of D."""

    best = {"exploitability": math.inf, "period": None, "hazards": None}
    for period in QUICK_D_PERIODS:

        def objective(z: Sequence[float], period=period) -> float:
            hazards = [
                [sigmoid(z[t * N + i]) for i in PLAYERS] for t in range(period)
            ]
            return periodic_exploitability(table, hazards)

        for level in QUICK_D_STARTS:
            start = [logit(level)] * (N * period)
            point, value = nelder_mead(objective, start, step=1.5, max_iter=60)
            if value < best["exploitability"]:
                best = {
                    "exploitability": value,
                    "period": period,
                    "hazards": [
                        [sigmoid(point[t * N + i]) for i in PLAYERS]
                        for t in range(period)
                    ],
                }
    if best["hazards"] is not None:
        best["profile"] = _wire(best["hazards"])
    return best


# --------------------------------------------------------------------------- #
# Deep re-attack
# --------------------------------------------------------------------------- #

DEEP_GRID = (0.0, 0.01, 0.03, 0.08, 0.15, 0.3, 0.5, 0.75, 1.0)
DEEP_SEED = 4041


def deep_pair_schedules() -> tuple[tuple[tuple[int, int], ...], ...]:
    """Pair schedules for the stress test, including period four.

    The search-time attack C stops at period three.  That gap was not harmless:
    a table survived both the search battery and an earlier version of this
    stress test at about ``0.029``, and adding period-four schedules dropped it
    to ``1.7e-05``.
    """

    schedules = list(PAIR_SCHEDULES)
    for quad in combinations(range(len(PAIRS)), 4):
        schedules.append(tuple(PAIRS[k] for k in quad))
    return tuple(schedules)


DEEP_PAIR_SCHEDULES = deep_pair_schedules()


def deep_stationary(table: Table, rng: random.Random) -> dict:
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
    return {
        "exploitability": best_value,
        "rates": best_point,
        "profile": _wire([best_point]),
    }


def deep_one_quitter(table: Table, rng: random.Random) -> dict:
    best_value = math.inf
    best_detail: dict = {}
    best_cycle: Sequence[int] = ()
    best_rates: list[float] = []
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
                best_cycle = cycle
                best_rates = [sigmoid(v) for v in point]
                best_detail = {
                    "cycle": [c + 1 for c in cycle],
                    "rates": best_rates,
                }
    if not best_cycle:
        return {"exploitability": best_value, **best_detail}
    return _one_quitter_result(table, best_cycle, best_rates, best_value)


def deep_two_quitter(table: Table, rng: random.Random) -> dict:
    best_value = math.inf
    best_detail: dict = {}
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
    report = {"exploitability": best_value, **best_detail}
    if best_detail:
        report["profile"] = _wire(best_detail["hazards"])
    return report


def deep_general_periodic(table: Table, rng: random.Random) -> dict:
    best_value = math.inf
    best_detail: dict = {}
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
    report = {"exploitability": best_value, **best_detail}
    if best_detail:
        report["profile"] = _wire(best_detail["hazards"])
    return report


def deep_reattack(table: Table, seed: int = DEEP_SEED) -> dict:
    """Hammer a single table far harder than the search-time battery.

    The search-time attacks are deliberately cheap, because they run hundreds
    of times.  A table that survives them is only interesting if it also
    survives more restarts, a finer stationary grid, and periods beyond the six
    the search-time general-periodic attack tries.  This routine is the stress
    test, and its verdict supersedes the search-time score for the one table it
    is pointed at.  The single ``random.Random(seed)`` stream is shared by the
    four stages in this order, exactly as in the experiment, so the result is
    reproducible only when the whole sequence runs.
    """

    rng = random.Random(seed)
    report = {
        "stationary": deep_stationary(table, rng),
        "one_quitter_cyclic": deep_one_quitter(table, rng),
        "two_quitter_periodic": deep_two_quitter(table, rng),
        "general_periodic": deep_general_periodic(table, rng),
    }
    score = min(entry["exploitability"] for entry in report.values())
    binding = min(report, key=lambda k: report[k]["exploitability"])
    return {"score": score, "binding_attack": binding, "breakdown": report}
