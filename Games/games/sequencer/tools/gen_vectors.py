#!/usr/bin/env python3
"""Generate hard-coded test vectors for the sequencer's in-browser evaluator.

Every expected number comes from the reference experiment script
``Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py``,
imported read-only via importlib.  The vectors pin the browser port to the
reference: exploitability, per-player gaps, on-path values and best-response
values for every phase.

Run:  python3 Games/games/sequencer/tools/gen_vectors.py
Writes: Games/games/sequencer/vectors.js
"""

from __future__ import annotations

import importlib.util
import json
import math
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
GAMES = HERE.parent.parent.parent
REPO = GAMES.parent
REF = (
    REPO
    / "Experiments"
    / "singleton_collision_candidate_search"
    / "singleton_collision_candidate_search.py"
)

spec = importlib.util.spec_from_file_location("ref_search", REF)
ref = importlib.util.module_from_spec(spec)
assert spec.loader is not None
sys.modules["ref_search"] = ref  # dataclasses resolves cls.__module__ here
spec.loader.exec_module(ref)

N = ref.N
PLAYERS = ref.PLAYERS


def table_rows(table) -> list[list[float]]:
    return [list(row) for row in table]


def evaluate(table, hazards) -> dict:
    """Full evaluation using only reference primitives."""

    period = len(hazards)
    data = [ref.phase_data(table, hazards[t]) for t in range(period)]
    stage = [data[t].absorption for t in range(period)]
    on_path = [
        ref.cyclic_solve([data[t].absorbed[j] for t in range(period)], stage)
        for j in PLAYERS
    ]
    best = [[-math.inf] * period for _ in PLAYERS]
    best_policy = [[0] * period for _ in PLAYERS]
    for i in PLAYERS:
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
            values = ref.cyclic_solve(constants, policy_hazards)
            for t in range(period):
                if values[t] > best[i][t]:
                    best[i][t] = values[t]
                    best_policy[i][t] = policy
    per_player = [max(best[i][t] - on_path[i][t] for t in range(period)) for i in PLAYERS]
    exploitability = max(per_player)
    reference = ref.periodic_exploitability(table, hazards)
    assert exploitability == reference, (exploitability, reference)
    return {
        "exploitability": exploitability,
        "per_player": per_player,
        "on_path": on_path,
        "best_response": best,
        "best_policy": best_policy,
    }


def random_table(rng: random.Random, lo=-4.0, hi=4.0):
    rows = [[0.0] * N for _ in ref.MASKS]
    for mask in ref.NONEMPTY:
        for i in PLAYERS:
            rows[mask][i] = round(rng.uniform(lo, hi), 6)
    return tuple(tuple(row) for row in rows)


def main() -> None:
    rng = random.Random(20260818)
    seed = ref.seed_table()
    cases: list[dict] = []

    def add(name: str, table, hazards, note: str = "") -> None:
        hazards = [[float(h) for h in row] for row in hazards]
        cases.append(
            {
                "name": name,
                "note": note,
                "table": table_rows(table),
                "profile": {"period": len(hazards), "hazards": hazards},
                "expected": evaluate(table, hazards),
            }
        )

    # 1. The Solan-Vieille seed under the known period-two two-quitter repair.
    known_pairs = ((0, 2), (1, 3))

    def known_objective(z):
        return ref.periodic_exploitability(
            table_known, ref.hazards_from_pairs(known_pairs, [ref.sigmoid(v) for v in z])
        )

    table_known = seed
    best_value, best_point = math.inf, [ref.logit(0.05)] * 4
    for level in (0.01, 0.05, 0.1, 0.2, 0.3, 0.5, 0.7):
        point, value = ref.nelder_mead(
            known_objective, [ref.logit(level)] * 4, step=1.5, max_iter=400
        )
        if value < best_value:
            best_value, best_point = value, point
    killing = ref.hazards_from_pairs(known_pairs, [ref.sigmoid(v) for v in best_point])
    add(
        "seed:known-period-2-repair",
        seed,
        killing,
        "Solan-Vieille seed, optimized {1,3}/{2,4} two-quitter schedule",
    )
    add("seed:period-2-coarse", seed, [[0.05, 0.0, 0.05, 0.0], [0.0, 0.05, 0.0, 0.05]])
    add("seed:stationary-uniform", seed, [[0.1, 0.1, 0.1, 0.1]])
    add("seed:stationary-asym", seed, [[0.3, 0.02, 0.5, 0.001]])
    add("seed:all-zero", seed, [[0.0, 0.0, 0.0, 0.0]], "no absorption: value 0")
    add("seed:all-one", seed, [[1.0, 1.0, 1.0, 1.0]], "everybody quits immediately")
    add("seed:one-certain-phase", seed, [[0.01, 0.0, 0.0, 0.0], [0.0, 1.0, 0.0, 0.0]])
    add("seed:tiny-hazards", seed, [[1e-6, 1e-9, 1e-12, 1e-15]], "sub-epsilon regime")
    add(
        "seed:tiny-period-3",
        seed,
        [[1e-18, 0.0, 0.0, 0.0], [0.0, 1e-18, 0.0, 0.0], [0.0, 0.0, 1e-18, 1e-20]],
        "log1p/expm1 accuracy below machine epsilon",
    )
    add(
        "seed:period-8-sparse",
        seed,
        [[0.02 if (t + i) % 4 == 0 else 0.0 for i in PLAYERS] for t in range(8)],
        "period eight, one quitter per phase",
    )

    # 2. The three chain-best tables from the experiment results.
    results = json.loads((REF.parent / "results.json").read_text(encoding="utf-8"))
    for chain in results["chains"]:
        table = ref.table_from_json(chain["best"]["table"])
        tag = f"chain{chain['seed']}"
        add(f"{tag}:stationary-grid", table, [[0.02, 0.1, 0.3, 0.6]])
        deep = chain["best"]["deep_reattack"]["breakdown"]
        best_two = deep["two_quitter_periodic"]
        add(
            f"{tag}:deep-two-quitter",
            table,
            best_two["hazards"],
            "deep re-attack's binding two-quitter schedule",
        )
        gen = deep["general_periodic"]
        add(f"{tag}:deep-general-periodic", table, gen["hazards"])

    # 3. Random tables, random periods, uniform and log-uniform hazards.
    for k in range(9):
        table = random_table(rng)
        period = (k % 8) + 1
        tiny = k % 3 == 2
        hazards = [
            [
                round(10.0 ** rng.uniform(-20.0, -1.0), 22)
                if tiny
                else round(rng.uniform(0.0, 1.0), 6)
                for _ in PLAYERS
            ]
            for _ in range(period)
        ]
        add(
            f"random{k}:period-{period}",
            table,
            hazards,
            "log-uniform hazards" if tiny else "uniform hazards",
        )

    # 4. Degenerate shapes.
    table = random_table(rng)
    add("random-edge:zero-then-certain", table, [[0.0] * N, [0.0, 0.0, 0.0, 1.0]])
    add("random-edge:single-quitter", table, [[0.0, 0.0, 0.25, 0.0]])
    add("random-edge:period-6-mixed", table, [
        [0.5, 0.0, 0.0, 0.0],
        [0.0, 1e-9, 0.0, 0.0],
        [0.0, 0.0, 0.9, 0.0],
        [0.0, 0.0, 0.0, 0.0],
        [1e-3, 1e-3, 1e-3, 1e-3],
        [0.0, 0.0, 0.0, 0.02],
    ])

    lines = [
        "// Generated by tools/gen_vectors.py -- do not edit by hand.",
        "// Expected values come from the reference experiment script:",
        "//   Experiments/singleton_collision_candidate_search/"
        "singleton_collision_candidate_search.py",
        "// One line per vector; see the generator docstring for provenance.",
        "export const VECTORS = [",
    ]
    for case in cases:
        lines.append(" " + json.dumps(case, separators=(",", ":")) + ",")
    lines.append("];")
    out = HERE.parent / "vectors.js"
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"wrote {out} with {len(cases)} vectors")


if __name__ == "__main__":
    main()
