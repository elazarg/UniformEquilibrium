"""E03: finite Livsic/coboundary and path-complete account experiment.

For a finite directed graph, an edge charge is a potential difference exactly
when its sum around every closed walk is zero.  A path-complete account replaces
one potential by a potential on (mode, state), i.e. by the same theorem on a
finite lifted graph.  This script solves the equations over exact rationals and
checks the quantitative effect of sublinearly many unpaid reset edges.
"""

from __future__ import annotations

import json
import math
from collections import defaultdict, deque
from fractions import Fraction
from typing import Hashable, Iterable, NamedTuple


class Edge(NamedTuple):
    source: Hashable
    target: Hashable
    charge: Fraction


def solve_coboundary(vertices: Iterable[Hashable], edges: list[Edge]):
    """Solve H(v)-H(u)=charge(u,v), returning a conflict if inconsistent."""
    adjacency: dict[Hashable, list[tuple[Hashable, Fraction, Edge]]] = defaultdict(list)
    for edge in edges:
        adjacency[edge.source].append((edge.target, edge.charge, edge))
        adjacency[edge.target].append((edge.source, -edge.charge, edge))

    potential: dict[Hashable, Fraction] = {}
    for root in vertices:
        if root in potential:
            continue
        potential[root] = Fraction(0)
        queue = deque([root])
        while queue:
            source = queue.popleft()
            for target, difference, edge in adjacency[source]:
                proposed = potential[source] + difference
                if target not in potential:
                    potential[target] = proposed
                    queue.append(target)
                elif potential[target] != proposed:
                    return None, {
                        "edge": [str(edge.source), str(edge.target), str(edge.charge)],
                        "existing_target_potential": str(potential[target]),
                        "forced_target_potential": str(proposed),
                        "cycle_discrepancy": str(proposed - potential[target]),
                    }
    return potential, None


def verify_solution(edges: list[Edge], potential: dict[Hashable, Fraction]) -> None:
    for edge in edges:
        assert potential[edge.target] - potential[edge.source] == edge.charge


def reset_budget_check(horizon: int) -> dict:
    """A bounded unpaid reset used floor(sqrt(T)) times has o(T) cost."""
    reset_count = math.isqrt(horizon)
    maximum_reset_cost = Fraction(7, 3)
    total_bill = reset_count * maximum_reset_cost
    ratio = float(total_bill / horizon)
    assert reset_count <= math.sqrt(horizon)
    return {
        "horizon": horizon,
        "reset_count": reset_count,
        "maximum_reset_cost": str(maximum_reset_cost),
        "bill_per_stage": ratio,
    }


def run() -> dict:
    triangle = [
        Edge("a", "b", Fraction(2)),
        Edge("b", "c", Fraction(-5)),
        Edge("c", "a", Fraction(3)),
    ]
    triangle_potential, conflict = solve_coboundary(["a", "b", "c"], triangle)
    assert conflict is None and triangle_potential is not None
    verify_solution(triangle, triangle_potential)

    bad_triangle = triangle[:-1] + [Edge("c", "a", Fraction(4))]
    bad_potential, bad_conflict = solve_coboundary(["a", "b", "c"], bad_triangle)
    assert bad_potential is None and bad_conflict is not None

    # A lifted four-node cycle.  Projecting away the mode produces two
    # incompatible charges on the same state displacement 0 -> 1.
    lifted_vertices = [("A", 0), ("A", 1), ("B", 0), ("B", 1)]
    lifted_edges = [
        Edge(("A", 0), ("B", 1), Fraction(2)),
        Edge(("B", 1), ("B", 0), Fraction(2)),
        Edge(("B", 0), ("A", 1), Fraction(-3)),
        Edge(("A", 1), ("A", 0), Fraction(-1)),
    ]
    lifted_potential, lifted_conflict = solve_coboundary(lifted_vertices, lifted_edges)
    assert lifted_conflict is None and lifted_potential is not None
    verify_solution(lifted_edges, lifted_potential)

    projected_edges = [Edge(u[1], v[1], w) for u, v, w in lifted_edges]
    projected_potential, projected_conflict = solve_coboundary([0, 1], projected_edges)
    assert projected_potential is None and projected_conflict is not None

    budgets = [reset_budget_check(h) for h in [100, 10_000, 1_000_000]]
    assert budgets[-1]["bill_per_stage"] < budgets[0]["bill_per_stage"]

    return {
        "experiment": "E03",
        "status": "passed",
        "zero_cycle_potential": {str(k): str(v) for k, v in triangle_potential.items()},
        "nonzero_cycle_conflict": bad_conflict,
        "lifted_path_complete_potential": {
            str(k): str(v) for k, v in lifted_potential.items()
        },
        "projected_single_potential_conflict": projected_conflict,
        "sublinear_reset_budgets": budgets,
        "conclusion": (
            "Path-complete accounts are ordinary coboundaries on a lifted graph; "
            "mode memory can remove a projected holonomy, while o(T) unpaid resets "
            "remain asymptotically harmless."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
