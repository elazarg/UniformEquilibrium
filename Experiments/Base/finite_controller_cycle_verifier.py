"""E28: exact verification of a finite deterministic controller product.

Once a public controller is fixed, a unilateral deviator in a deterministic
product model chooses edges of a finite weighted graph.  Uniformly bounded
prefix gain is equivalent to the absence of a reachable positive cycle.  This
script checks the cycle condition exactly and constructs a potential witness.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json


@dataclass(frozen=True)
class Edge:
    source: str
    target: str
    gain: Fraction
    label: str


def reachable_vertices(start: str, edges: list[Edge]) -> set[str]:
    reached = {start}
    changed = True
    while changed:
        changed = False
        for edge in edges:
            if edge.source in reached and edge.target not in reached:
                reached.add(edge.target)
                changed = True
    return reached


def simple_cycles(start: str, edges: list[Edge]) -> list[tuple[Edge, ...]]:
    """Enumerate reachable directed simple cycles, canonicalized by edge ids."""

    reached = reachable_vertices(start, edges)
    adjacency: dict[str, list[tuple[int, Edge]]] = {vertex: [] for vertex in reached}
    for index, edge in enumerate(edges):
        if edge.source in reached and edge.target in reached:
            adjacency[edge.source].append((index, edge))

    found: dict[tuple[int, ...], tuple[Edge, ...]] = {}

    def canonical(indices: tuple[int, ...]) -> tuple[int, ...]:
        rotations = [indices[k:] + indices[:k] for k in range(len(indices))]
        return min(rotations)

    for root in sorted(reached):
        def visit(vertex: str, seen: set[str], path: list[tuple[int, Edge]]) -> None:
            for index, edge in adjacency[vertex]:
                if edge.target == root:
                    indices = tuple(item[0] for item in path) + (index,)
                    key = canonical(indices)
                    found.setdefault(key, tuple(item[1] for item in path) + (edge,))
                elif edge.target not in seen:
                    visit(edge.target, seen | {edge.target}, path + [(index, edge)])

        visit(root, {root}, [])
    return list(found.values())


def maximum_simple_path_potential(start: str, edges: list[Edge]) -> dict[str, Fraction]:
    """Return max simple-path gain from each reachable vertex, including zero."""

    reached = reachable_vertices(start, edges)
    adjacency: dict[str, list[Edge]] = {vertex: [] for vertex in reached}
    for edge in edges:
        if edge.source in reached and edge.target in reached:
            adjacency[edge.source].append(edge)

    def best(vertex: str, seen: set[str]) -> Fraction:
        value = Fraction(0)
        for edge in adjacency[vertex]:
            if edge.target not in seen:
                value = max(value, edge.gain + best(edge.target, seen | {edge.target}))
        return value

    return {vertex: best(vertex, {vertex}) for vertex in reached}


def verify(start: str, edges: list[Edge]) -> dict[str, object]:
    cycles = simple_cycles(start, edges)
    means = [sum((edge.gain for edge in cycle), Fraction(0)) / len(cycle) for cycle in cycles]
    maximum_mean = max(means) if means else None
    safe = maximum_mean is None or maximum_mean <= 0

    potential = None
    edge_slacks = None
    if safe:
        potential = maximum_simple_path_potential(start, edges)
        # Removing any repeated nonpositive cycle from an optimizing walk cannot
        # lower its weight, so this simple-path potential satisfies every edge.
        edge_slacks = {
            edge.label: potential[edge.source] - potential[edge.target] - edge.gain
            for edge in edges
            if edge.source in potential and edge.target in potential
        }
        assert all(slack >= 0 for slack in edge_slacks.values())

    return {
        "safe": safe,
        "cycle_count": len(cycles),
        "maximum_cycle_mean": None if maximum_mean is None else str(maximum_mean),
        "potential": None if potential is None else {key: str(value) for key, value in potential.items()},
        "minimum_edge_slack": None if not edge_slacks else str(min(edge_slacks.values())),
    }


def run() -> dict[str, object]:
    safe_edges = [
        Edge("q0", "q1", Fraction(2), "advance"),
        Edge("q1", "q0", Fraction(-2), "reset"),
        Edge("q1", "q2", Fraction(1), "probe"),
        Edge("q2", "q1", Fraction(-2), "repay"),
        Edge("q2", "q2", Fraction(0), "wait"),
    ]
    unsafe_edges = safe_edges + [Edge("q2", "q0", Fraction(2), "profitable_restart")]

    safe = verify("q0", safe_edges)
    unsafe = verify("q0", unsafe_edges)
    assert safe["safe"] is True
    assert safe["maximum_cycle_mean"] == "0"
    assert unsafe["safe"] is False
    assert unsafe["maximum_cycle_mean"] == "5/3"

    return {
        "experiment": "E28",
        "status": "passed",
        "safe_product": safe,
        "unsafe_product": unsafe,
        "conclusion": (
            "A fixed deterministic controller product has a short exact audit: reachable positive cycles are deviation witnesses, while their absence yields a potential bounding every prefix gain.  Local verification is finite even when controller synthesis is not."
        ),
        "limitation": (
            "The script treats deterministic product dynamics.  Stochastic products require the corresponding finite-MDP occupation or bias-potential theorem."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
