"""Necessary-condition filters 1-6.

Faithful port of the filters in
``Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py``;
the experiment README documents what each one means.  Filters 1-5 are
necessary-looking structural conditions assembled for this screen and filter 6
is an explicit heuristic, so a table a filter rejects has *not* been shown to
admit an approximate equilibrium.  Passing them is a legality gate for the
search, nothing more.
"""

from __future__ import annotations

from itertools import combinations
from typing import Optional

from .model import MARGIN_G, MASKS, PLAYERS, Table, solo


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
    system ``sum_j lambda_j r_{j}(i) = r_{i}(i)`` for ``i in S`` together with
    ``sum_j lambda_j + lambda_0 = 1`` is solved exactly.  The tail weight
    ``lambda_0`` carries payoff zero.  A solution counts when all weights are
    nonnegative, every remaining core player weakly prefers the mixture to
    quitting alone, and every non-core player weakly prefers it to
    ``max(0, r_{i}(i))``.

    A strictly positive tail weight is only accepted when every solo-self payoff
    ``r_{i}(i)`` is at most zero.  Positive tail weight means the profile
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


def run_filters(table: Table, margin: float = MARGIN_G) -> dict:
    """The experiment's filter report, key for key."""

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

def first_failing_filter(table: Table, margin: float = MARGIN_G) -> Optional[str]:
    """Name of the first filter the table fails, in numbered order, else None.

    Reporting which filter rejected shows which necessary condition actually
    binds on a perturbation kernel.
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


def api_report(table: Table, margin: float = MARGIN_G) -> dict:
    """``POST /api/filters`` shape: the six checks plus the overall verdict."""

    checks = run_filters(table, margin)
    # The six keys are the experiment's own FILTER_NAMES, which DESIGN.md
    # settles as the wire names; clients treat them as opaque labels.
    filters = {name: checks[name] for name in FILTER_NAMES}
    return {
        "pass": checks["all_1_to_6"],
        "pass_1_to_5": checks["all_1_to_5"],
        "margin": margin,
        "first_failing": first_failing_filter(table, margin),
        "filters": filters,
    }
