#!/usr/bin/env python3
"""Exact evaluator and floating search for finite-clock Fin4 semantic centers.

This is a research prototype, not an exact global optimizer.  The evaluator
uses Fraction throughout when supplied rational data.  The search layer casts
to float and uses seeded stochastic coordinate/mixing moves.  A numerical
minimum is never reported as a lower certificate.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from dataclasses import dataclass
from fractions import Fraction as Q
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple, Union

Number = Union[Q, float]
Reward = Dict[int, Tuple[Number, Number, Number, Number]]

N = 4


def q(value: int, denominator: int = 1) -> Q:
    return Q(value, denominator)


PAIRED_SINGLETON = (
    (0, 3, -1, -1),
    (3, 0, -1, -1),
    (-1, -1, 0, 3),
    (-1, -1, 3, 0),
)


BOUNDARY_RAW_ROWS = {
    0b0001: (1, 4, 0, 0),
    0b0010: (4, 1, 0, 0),
    0b0100: (0, 0, 1, 4),
    0b1000: (0, 0, 4, 1),
    0b0011: (1, 1, 1, 1),
    0b0101: (1, 1, 1, 0),
    0b1001: (1, 0, 1, 1),
    0b0110: (0, 1, 1, 1),
    0b1010: (1, 1, 0, 1),
    0b1100: (1, 1, 1, 1),
    0b0111: (1, 0, 0, 0),
    0b1011: (0, 1, 0, 0),
    0b1101: (0, 0, 0, 1),
    0b1110: (0, 0, 1, 0),
    0b1111: (-1, -1, -1, -1),
}


# Deterministically stored rational profile found by the floating layer and
# then rechecked entirely with Fraction.  Columns are dates 0,1,2,3,Never.
LAMBDA34_K4_ZERO_PROFILE = [
    [Q(2813, 100000), Q(4133, 100000), Q(85177, 100000), Q(2421, 50000), Q(607, 20000)],
    [Q(11397, 20000), Q(6331, 100000), Q(451, 12500), Q(28839, 100000), Q(4237, 100000)],
    [Q(7651, 50000), Q(13813, 100000), Q(22491, 100000), Q(30061, 100000), Q(18333, 100000)],
    [Q(2739, 10000), Q(17913, 100000), Q(606, 3125), Q(578, 3125), Q(16809, 100000)],
]


def stationary_raw() -> Reward:
    result: Reward = {}
    for mask in range(1, 16):
        if mask & (mask - 1) == 0:
            owner = (mask.bit_length() - 1)
            result[mask] = tuple(Q(PAIRED_SINGLETON[i][owner]) for i in range(N))  # type: ignore[assignment]
        else:
            result[mask] = (Q(-2), Q(-2), Q(-2), Q(-2))
    return result


def boundary_raw() -> Reward:
    return {mask: tuple(Q(x) for x in row) for mask, row in BOUNDARY_RAW_ROWS.items()}  # type: ignore[return-value]


def affine_4pps(lam: Q) -> Reward:
    """The normalized interpolation ((1-lam) stationary + lam boundary)/4."""
    a, b = stationary_raw(), boundary_raw()
    return {
        mask: tuple(((1 - lam) * a[mask][i] + lam * b[mask][i]) / 4 for i in range(N))  # type: ignore[misc]
        for mask in range(1, 16)
    }


def outcome_mask(times: Sequence[int], never: int) -> int:
    finite = [t for t in times if t < never]
    if not finite:
        return 0
    first = min(finite)
    return sum(1 << i for i, t in enumerate(times) if t == first)


def survival_rows(marginals: Sequence[Sequence[Number]]) -> List[List[Number]]:
    """s[i][t] = P(T_i >= t), with finite support 0,...,K-1 and Never=K."""
    K = len(marginals[0]) - 1
    rows: List[List[Number]] = []
    for row in marginals:
        s: List[Number] = [row[0] * 0 for _ in range(K + 1)]
        running: Number = row[K]
        s[K] = running
        for t in range(K - 1, -1, -1):
            running = running + row[t]
            s[t] = running
        rows.append(s)
    return rows


def prescribed_payoff(reward: Reward, marginals: Sequence[Sequence[Number]]) -> List[Number]:
    K = len(marginals[0]) - 1
    surv = survival_rows(marginals)
    zero = marginals[0][0] * 0
    U: List[Number] = [zero for _ in range(N)]
    for mask in range(1, 16):
        mass: Number = zero
        members = [i for i in range(N) if mask & (1 << i)]
        outsiders = [i for i in range(N) if not (mask & (1 << i))]
        for t in range(K):
            term: Number = zero + 1
            for i in members:
                term *= marginals[i][t]
            for j in outsiders:
                term *= surv[j][t + 1]
            mass += term
        for i in range(N):
            U[i] += mass * reward[mask][i]
    return U


def deviation_values(
    reward: Reward, marginals: Sequence[Sequence[Number]], who: int
) -> List[Number]:
    """Pure dates 0,...,K-1, auxiliary after-support K, then Never."""
    K = len(marginals[0]) - 1
    surv = survival_rows(marginals)
    opponents = [j for j in range(N) if j != who]
    zero = marginals[0][0] * 0

    # Distribution of the first opponent coalition at each supported date.
    first: List[Dict[int, Number]] = []
    for t in range(K):
        row: Dict[int, Number] = {}
        for sub in range(1, 1 << len(opponents)):
            mask = 0
            mass: Number = zero + 1
            for k, player in enumerate(opponents):
                if sub & (1 << k):
                    mask |= 1 << player
                    mass *= marginals[player][t]
                else:
                    mass *= surv[player][t + 1]
            row[mask] = mass
        first.append(row)

    all_never: Number = zero + 1
    for j in opponents:
        all_never *= marginals[j][K]

    values: List[Number] = []
    prefix: Number = zero
    for tau in range(K):
        value: Number = prefix
        for mask, mass in first[tau].items():
            value += mass * reward[mask | (1 << who)][who]
        opponents_after: Number = zero + 1
        for j in opponents:
            opponents_after *= surv[j][tau + 1]
        value += opponents_after * reward[1 << who][who]
        values.append(value)
        for mask, mass in first[tau].items():
            prefix += mass * reward[mask][who]

    # Auxiliary finite time K: opponents that quit finitely preempt; if all
    # opponents Never, the deviator quits solo.
    after_support = prefix + all_never * reward[1 << who][who]
    values.append(after_support)
    # Never: finite opponents preempt, while all-Never pays zero.
    values.append(prefix)
    return values


@dataclass
class Semantic:
    U: List[Number]
    B: List[Number]
    values: List[List[Number]]

    @property
    def debts(self) -> List[Number]:
        return [self.B[i] - self.U[i] for i in range(N)]

    @property
    def exploitability(self) -> Number:
        return max([self.U[0] * 0] + self.debts)


def semantic(reward: Reward, marginals: Sequence[Sequence[Number]]) -> Semantic:
    U = prescribed_payoff(reward, marginals)
    values = [deviation_values(reward, marginals, i) for i in range(N)]
    B = [max(row) for row in values]
    return Semantic(U, B, values)


def pure_profile(K: int, times: Sequence[int]) -> List[List[Q]]:
    rows: List[List[Q]] = []
    for time in times:
        row = [Q(0) for _ in range(K + 1)]
        row[time] = Q(1)
        rows.append(row)
    return rows


def normalize_float(row: Sequence[float]) -> List[float]:
    clean = [max(0.0, x) for x in row]
    total = sum(clean)
    if total == 0:
        return [1.0 / len(clean)] * len(clean)
    return [x / total for x in clean]


def random_profile(K: int, rng: random.Random) -> List[List[float]]:
    return [normalize_float([rng.expovariate(1.0) for _ in range(K + 1)]) for _ in range(N)]


def float_reward(reward: Reward) -> Reward:
    return {mask: tuple(float(x) for x in row) for mask, row in reward.items()}  # type: ignore[return-value]


def stochastic_search(
    reward: Reward,
    K: int,
    restarts: int,
    steps: int,
    seed: int,
    extra_starts: Sequence[Sequence[Sequence[float]]] = (),
) -> Tuple[float, List[List[float]], Semantic]:
    """Seeded floating search.  This supplies upper witnesses only."""
    rng = random.Random(seed)
    rfloat = float_reward(reward)
    best_value = math.inf
    best_profile: List[List[float]] = []
    best_sem: Semantic | None = None

    starts: List[List[List[float]]] = []
    # Structural starts: all Never and each pure time/owner.
    starts.append([[0.0] * K + [1.0] for _ in range(N)])
    for owner in range(N):
        p = [[0.0] * K + [1.0] for _ in range(N)]
        p[owner] = [1.0] + [0.0] * K
        starts.append(p)
    starts.extend([[list(row) for row in profile] for profile in extra_starts])
    starts.extend(random_profile(K, rng) for _ in range(max(0, restarts - len(starts))))

    for start in starts:
        profile = [row[:] for row in start]
        sem = semantic(rfloat, profile)
        value = float(sem.exploitability)
        if value < best_value:
            best_value = value
            best_profile = [row[:] for row in profile]
            best_sem = sem
        temperature = 0.25
        for step in range(steps):
            player = rng.randrange(N)
            proposal = [row[:] for row in profile]
            if rng.random() < 0.55:
                target = [0.0] * (K + 1)
                target[rng.randrange(K + 1)] = 1.0
            else:
                target = random_profile(K, rng)[0]
            scale = max(0.005, temperature * (1.0 - step / max(1, steps)))
            alpha = min(1.0, rng.random() * scale)
            proposal[player] = [
                (1.0 - alpha) * profile[player][s] + alpha * target[s]
                for s in range(K + 1)
            ]
            proposed_sem = semantic(rfloat, proposal)
            proposed = float(proposed_sem.exploitability)
            accept = proposed <= value
            if not accept:
                anneal = max(1e-6, 0.02 * (1.0 - step / max(1, steps)))
                accept = rng.random() < math.exp(-(proposed - value) / anneal)
            if accept:
                profile, sem, value = proposal, proposed_sem, proposed
            if value < best_value:
                best_value = value
                best_profile = [row[:] for row in profile]
                best_sem = sem
        # Deterministic one-coordinate polishing toward each vertex.
        improved = True
        rounds = 0
        while improved and rounds < 8:
            improved = False
            rounds += 1
            for player in range(N):
                for date in range(K + 1):
                    for alpha in (0.5, 0.25, 0.1, 0.04, 0.01):
                        proposal = [row[:] for row in profile]
                        proposal[player] = [(1 - alpha) * x for x in proposal[player]]
                        proposal[player][date] += alpha
                        psem = semantic(rfloat, proposal)
                        pvalue = float(psem.exploitability)
                        if pvalue + 1e-13 < value:
                            profile, sem, value = proposal, psem, pvalue
                            improved = True
                            if value < best_value:
                                best_value = value
                                best_profile = [row[:] for row in profile]
                                best_sem = sem
    assert best_sem is not None
    return best_value, best_profile, best_sem


def polynomial_constraint_summary(K: int) -> dict:
    """Exact finite presentation sizes; formulas are those implemented above."""
    variables_x = N * (K + 1)
    semantic_variables = 2 * N
    deviation_candidates = K + 2
    return {
        "players": N,
        "finite_dates": K,
        "marginal_variables": variables_x,
        "semantic_variables": semantic_variables,
        "deviation_value_variables": N * deviation_candidates,
        "simplex_equalities": N,
        "nonnegativity_inequalities": variables_x,
        "prescribed_payoff_equalities": N,
        "deviation_value_equalities": N * deviation_candidates,
        "cap_upper_inequalities": N * deviation_candidates,
        "cap_tight_product_equalities": N,
        "pure_deviations_per_player": {
            "supported_dates": list(range(K)),
            "after_support": K,
            "never": "Never",
        },
        "coalition_probability_formula":
            "sum_t prod_{i in S} x[i,t] prod_{j notin S} survival[j,t+1]",
        "certificate_status":
            "exact rational generator/evaluator; no CAD or global lower solver implemented",
    }


def variable(player: int, time: int, K: int) -> str:
    return f"x{player}_{'N' if time == K else time}"


def add_term(poly: Dict[Tuple[str, ...], Q], monomial: Iterable[str], coefficient: Q) -> None:
    if coefficient == 0:
        return
    key = tuple(sorted(monomial))
    poly[key] = poly.get(key, Q(0)) + coefficient
    if poly[key] == 0:
        del poly[key]


def polynomial_json(poly: Mapping[Tuple[str, ...], Q]) -> list:
    return [
        {"coefficient": str(coefficient), "monomial": list(monomial)}
        for monomial, coefficient in sorted(poly.items())
    ]


def exact_polynomial_system(reward: Reward, K: int) -> dict:
    """Generate, without expansion of the max-product, the exact A_K system."""
    prescribed: List[Dict[Tuple[str, ...], Q]] = [dict() for _ in range(N)]
    for times in itertools.product(range(K + 1), repeat=N):
        mask = outcome_mask(times, K)
        if mask == 0:
            continue
        monomial = [variable(i, times[i], K) for i in range(N)]
        for who in range(N):
            add_term(prescribed[who], monomial, Q(reward[mask][who]))

    deviations: List[List[Dict[Tuple[str, ...], Q]]] = []
    labels: List[Union[int, str]] = list(range(K)) + ["after", "Never"]
    for who in range(N):
        opponents = [i for i in range(N) if i != who]
        player_values: List[Dict[Tuple[str, ...], Q]] = []
        for label in labels:
            poly: Dict[Tuple[str, ...], Q] = {}
            deviator_time = K if label == "after" else K + 1 if label == "Never" else int(label)
            for opponent_times in itertools.product(range(K + 1), repeat=N - 1):
                # Opponent Never is represented by K in marginal variables but
                # by K+1 in chronological comparison, after the auxiliary K.
                chronological = [K + 1] * N
                monomial = []
                chronological[who] = deviator_time
                for player, time in zip(opponents, opponent_times):
                    chronological[player] = K + 1 if time == K else time
                    monomial.append(variable(player, time, K))
                mask = outcome_mask(chronological, K + 1)
                coefficient = Q(0) if mask == 0 else Q(reward[mask][who])
                add_term(poly, monomial, coefficient)
            player_values.append(poly)
        deviations.append(player_values)

    deviation_variables = [
        f"V{i}_{label}" for i in range(N) for label in labels
    ]
    return {
        "variables": [variable(i, t, K) for i in range(N) for t in range(K + 1)]
            + [f"U{i}" for i in range(N)] + [f"B{i}" for i in range(N)]
            + deviation_variables,
        "simplex_equalities": [
            {"sum": [variable(i, t, K) for t in range(K + 1)], "equals": "1"}
            for i in range(N)
        ],
        "nonnegative": [variable(i, t, K) for i in range(N) for t in range(K + 1)],
        "prescribed_equalities": [
            {"lhs": f"U{i}", "rhs": polynomial_json(prescribed[i])} for i in range(N)
        ],
        "deviation_labels": labels,
        "deviation_equalities": [
            {
                "lhs": f"V{i}_{labels[tau]}",
                "rhs": polynomial_json(deviations[i][tau]),
            }
            for i in range(N) for tau in range(K + 2)
        ],
        "cap_upper_inequalities": [
            {"lhs": f"B{i}", "op": ">=", "rhs": f"V{i}_{labels[tau]}"}
            for i in range(N) for tau in range(K + 2)
        ],
        "cap_tight_product_equalities": [
            {
                "product_factors": [
                    {"lhs": f"B{i}", "rhs": f"V{i}_{label}"}
                    for label in labels
                ],
                "equals": "0",
            }
            for i in range(N)
        ],
    }


def namespace_exact_system(system: Mapping[str, object], prefix: str) -> dict:
    """Rename every declared variable and every exact occurrence recursively."""
    variables = [str(name) for name in system["variables"]]  # type: ignore[index]
    renaming = {name: f"{prefix}_{name}" for name in variables}

    def rename(value: object) -> object:
        if isinstance(value, str):
            return renaming.get(value, value)
        if isinstance(value, list):
            return [rename(item) for item in value]
        if isinstance(value, dict):
            return {key: rename(item) for key, item in value.items()}
        return value

    result = rename(dict(system))
    assert isinstance(result, dict)
    return result


def outer_hierarchy_summary(M: int) -> dict:
    centers = []
    totals = {
        "marginal_variables": 0,
        "semantic_variables": 8,  # shared outer z
        "deviation_value_variables": 0,
        "simplex_equalities": 0,
        "nonnegativity_inequalities": 0,
        "prescribed_payoff_equalities": 0,
        "deviation_value_equalities": 0,
        "cap_upper_inequalities": 0,
        "cap_tight_product_equalities": 0,
        "distance_inequalities": 0,
    }
    for m in range(1, M + 1):
        K = 8 * m + 1
        summary = polynomial_constraint_summary(K)
        centers.append({"m": m, "K": K, "delta": str(Q(12, m)), "A_K": summary})
        for key in list(totals):
            if key in summary:
                totals[key] += int(summary[key])
        totals["distance_inequalities"] += 16
    return {
        "M": M,
        "outer_variables": [f"z_U{i}" for i in range(N)] + [f"z_B{i}" for i in range(N)],
        "ambient_box": "-1 <= every z coordinate <= 1",
        "objective": "max(0,max_i(z_Bi-z_Ui))",
        "centers": centers,
        "totals": totals,
    }


def outer_hierarchy_system(reward: Reward, M: int) -> dict:
    result = outer_hierarchy_summary(M)
    result["variables"] = result["outer_variables"] + ["F"]
    result["ambient_box_constraints"] = [
        {"variable": name, "lower": "-1", "upper": "1"}
        for name in result["outer_variables"]
    ]
    result["center_systems"] = [
        {
            "namespace": f"m{m}",
            "m": m,
            "K": 8 * m + 1,
            "delta": str(Q(12, m)),
            "A_K_exact_system": namespace_exact_system(
                exact_polynomial_system(reward, 8 * m + 1), f"m{m}"
            ),
            "distance_inequalities": [
                {
                    "coordinate": f"{kind}{i}",
                    "constraints": [
                        {
                            "lhs": {"sub": [f"z_{kind}{i}", f"m{m}_{kind}{i}"]},
                            "op": "<=",
                            "rhs": str(Q(12, m)),
                        },
                        {
                            "lhs": {"sub": [f"m{m}_{kind}{i}", f"z_{kind}{i}"]},
                            "op": "<=",
                            "rhs": str(Q(12, m)),
                        },
                    ],
                }
                for kind in ("U", "B") for i in range(N)
            ],
        }
        for m in range(1, M + 1)
    ]
    result["objective_graph"] = {
        "F_nonnegative": {"lhs": "F", "op": ">=", "rhs": "0"},
        "debt_upper": [
            {
                "lhs": "F",
                "op": ">=",
                "rhs": {"sub": [f"z_B{i}", f"z_U{i}"]},
            }
            for i in range(N)
        ],
        "tight_product_equality": {
            "product_factors": [
                [{"coefficient": "1", "monomial": ["F"]}]
            ] + [
                [
                    {"coefficient": "1", "monomial": ["F"]},
                    {"coefficient": "-1", "monomial": [f"z_B{i}"]},
                    {"coefficient": "1", "monomial": [f"z_U{i}"]},
                ]
                for i in range(N)
            ],
            "equals": "0",
        },
    }
    return result


def one_shot_nash_midpoint_system(reward: Reward) -> dict:
    """Four-variable semialgebraic reduction proving the universal M<=36 zero.

    The underlying A_1 system has stopping-law actions date 0 and Never.
    Adding U>=V_0,V_Never selects a mixed Nash equilibrium of that finite
    two-action game.  The remaining after-support value is the only genuinely
    unrestricted deviation.  The accompanying exact theorem bounds its debt
    by 2/3 for rewards in [-1,1].
    """
    center = exact_polynomial_system(reward, 1)
    return {
        "description": (
            "exact one-shot Nash center and diagonal midpoint reduction; "
            "existence follows from finite mixed Nash"
        ),
        "A_1_exact_system": center,
        "finite_one_shot_nash_constraints": [
            {"lhs": f"U{i}", "op": ">=", "rhs": f"V{i}_0"}
            for i in range(N)
        ] + [
            {"lhs": f"U{i}", "op": ">=", "rhs": f"V{i}_Never"}
            for i in range(N)
        ],
        "outer_variables": [f"z_U{i}" for i in range(N)]
            + [f"z_B{i}" for i in range(N)],
        "midpoint_equalities": [
            {
                "polynomial_terms": [
                    {"coefficient": "2", "monomial": [f"z_U{i}"]},
                    {"coefficient": "-1", "monomial": [f"U{i}"]},
                    {"coefficient": "-1", "monomial": [f"B{i}"]},
                ],
                "equals": "0",
            }
            for i in range(N)
        ] + [
            {"lhs": f"z_B{i}", "rhs": f"z_U{i}"}
            for i in range(N)
        ],
        "proved_normalized_debt_bound": [
            {"lhs": {"sub": [f"B{i}", f"U{i}"]}, "op": "<=", "rhs": "2/3"}
            for i in range(N)
        ],
        "outer_consequence": {
            "sup_distance_bound": "1/3",
            "radius": "12/m",
            "levels": "every m <= 36",
            "objective_at_midpoint": "0",
            "status": "table-parametric exact theorem, not a numerical certificate",
        },
    }


def all_never_outer_zero_witness(reward: Reward, M: int) -> dict:
    center_profile = pure_profile(1, [1, 1, 1, 1])
    center = semantic(reward, center_profile)
    z_u = [(center.U[i] + center.B[i]) / 2 for i in range(N)]
    z_b = list(z_u)
    distance = max(
        [abs(center.U[i] - z_u[i]) for i in range(N)]
        + [abs(center.B[i] - z_b[i]) for i in range(N)]
    )
    checks = [distance <= Q(12, m) for m in range(1, M + 1)]
    max_m = None if distance == 0 else int(Q(12, 1) // distance)
    return {
        "M": M,
        "center_U": [str(x) for x in center.U],
        "center_B": [str(x) for x in center.B],
        "outer_z_U": [str(x) for x in z_u],
        "outer_z_B": [str(x) for x in z_b],
        "outer_F": "0",
        "sup_distance": str(distance),
        "feasible_every_level_through_M": all(checks),
        "largest_M_certified_by_same_allNever_center": max_m,
        "status": "exact rational R_M zero witness when feasible; proves L_M=0",
    }


def profile_outer_zero_witness(
    reward: Reward, marginals: Sequence[Sequence[Q]], M: int
) -> dict:
    """Exact diagonal R_M witness from one literal finite-clock center.

    If a center has exploitability F, its coordinatewise U/B midpoint is
    diagonal and lies at distance F/2.  A K-date profile embeds literally in
    every A_(8m+1) once K <= 8m+1 by inserting zero-mass dates before Never.
    """
    if M < 1:
        raise ValueError("M must be positive")
    if len(marginals) != N or not marginals:
        raise ValueError("expected four marginal rows")
    width = len(marginals[0])
    if width < 2 or any(len(row) != width for row in marginals):
        raise ValueError("marginal rows must have common finite support plus Never")
    K = width - 1
    if K > 9:
        raise ValueError("this common-center certificate requires K <= K_1 = 9")
    for row in marginals:
        if any(value < 0 for value in row) or sum(row, Q(0)) != 1:
            raise ValueError("each marginal row must be an exact probability simplex point")

    center = semantic(reward, marginals)
    z = [(center.U[i] + center.B[i]) / 2 for i in range(N)]
    distance = max(
        [abs(center.U[i] - z[i]) for i in range(N)]
        + [abs(center.B[i] - z[i]) for i in range(N)]
    )
    feasible = distance <= Q(12, M)
    # Since 12/m decreases in m, checking the final level is necessary and
    # sufficient when the same embedded center is used at every level.
    max_m = None if distance == 0 else int(Q(12, 1) // distance)
    return {
        "M": M,
        "profile_clock_bound": K,
        "profile": [[str(value) for value in row] for row in marginals],
        "center_U": [str(x) for x in center.U],
        "center_B": [str(x) for x in center.B],
        "center_debts": [str(x) for x in center.debts],
        "center_exploitability": str(center.exploitability),
        "outer_z_U": [str(x) for x in z],
        "outer_z_B": [str(x) for x in z],
        "outer_F": "0",
        "sup_distance": str(distance),
        "final_radius": str(Q(12, M)),
        "same_center_embeds_in_every_level": K <= 9,
        "closed_A_K_system_verified": exact_center_system_verifies(
            reward, marginals
        ),
        "feasible_every_level_through_M": feasible,
        "largest_M_certified_by_same_center": max_m,
        "proof_rule": (
            "embed by zero finite-date masses in every A_(8m+1); "
            "the U/B midpoint is diagonal and distance is F(center)/2"
        ),
        "status": "exact rational R_M zero witness when feasible; proves L_M=0",
    }


def rationalize_row(row: Sequence[float], denominator: int) -> List[Q]:
    scaled = [max(0.0, x) * denominator for x in row]
    counts = [int(math.floor(x)) for x in scaled]
    remainder = denominator - sum(counts)
    order = sorted(range(len(row)), key=lambda i: scaled[i] - counts[i], reverse=True)
    for i in order[:remainder]:
        counts[i] += 1
    return [Q(count, denominator) for count in counts]


def parse_fraction(text: str) -> Q:
    return Q(text)


def evaluate_polynomial_json(terms: Sequence[Mapping[str, object]], env: Mapping[str, Q]) -> Q:
    value = Q(0)
    for term in terms:
        coefficient = Q(str(term["coefficient"]))
        product = Q(1)
        for name in term["monomial"]:  # type: ignore[union-attr]
            product *= env[str(name)]
        value += coefficient * product
    return value


def exact_center_system_verifies(
    reward: Reward, marginals: Sequence[Sequence[Q]]
) -> bool:
    """Verify one rational profile against the emitted closed A_K system."""
    K = len(marginals[0]) - 1
    if len(marginals) != N or K < 1:
        return False
    if any(len(row) != K + 1 for row in marginals):
        return False
    if any(any(x < 0 for x in row) or sum(row, Q(0)) != 1 for row in marginals):
        return False
    system = exact_polynomial_system(reward, K)
    env = {
        variable(i, t, K): marginals[i][t]
        for i in range(N) for t in range(K + 1)
    }
    sem = semantic(reward, marginals)
    for i in range(N):
        if evaluate_polynomial_json(system["prescribed_equalities"][i]["rhs"], env) != sem.U[i]:
            return False
    labels = system["deviation_labels"]
    for i in range(N):
        tight = False
        for tau, label in enumerate(labels):
            index = i * (K + 2) + tau
            value = evaluate_polynomial_json(
                system["deviation_equalities"][index]["rhs"], env
            )
            if value != sem.values[i][tau] or sem.B[i] < value:
                return False
            tight = tight or sem.B[i] == value
        if not tight:
            return False
    return True


def period_two_parameter_float() -> float:
    def polynomial(x: float) -> float:
        return 44 * x**4 - 7 * x**3 - 26 * x**2 + x + 3
    lo, hi = 0.74, 0.75
    for _ in range(90):
        mid = (lo + hi) / 2
        if polynomial(mid) < 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def periodic_truncated_profile(K: int, primary: Number, secondary: Number) -> List[List[Number]]:
    rows: List[List[Number]] = []
    for player in range(N):
        continuation = primary if player in (0, 1) else secondary
        parity = 0 if player in (0, 2) else 1
        zero = continuation * 0
        row: List[Number] = [zero for _ in range(K + 1)]
        survival: Number = zero + 1
        for t in range(K):
            if t % 2 == parity:
                row[t] = survival * (1 - continuation)
                survival *= continuation
        row[K] = survival
        rows.append(row)
    return rows


def assert_equal(actual: Number, expected: Number, label: str) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected}, got {actual}")


def self_test() -> dict:
    results = {}

    # All-Never on normalized boundary: U=0; a finite solo deviation pays 1/4.
    rb = affine_4pps(Q(1))
    all_never = pure_profile(2, [2, 2, 2, 2])
    sem = semantic(rb, all_never)
    for i in range(N):
        assert_equal(sem.U[i], Q(0), f"allNever U{i}")
        assert_equal(sem.B[i], Q(1, 4), f"allNever B{i}")
    assert_equal(sem.exploitability, Q(1, 4), "allNever exploitability")
    results["all_never"] = {"U": [str(x) for x in sem.U], "B": [str(x) for x in sem.B]}

    # Late tie: players 0 and 2 quit together at date 2; others Never.
    late_tie = pure_profile(3, [2, 3, 2, 3])
    sem = semantic(rb, late_tie)
    expected = rb[0b0101]
    for i in range(N):
        assert_equal(sem.U[i], expected[i], f"lateTie U{i}")
    results["late_tie"] = {"coalition": "{0,2}", "U": [str(x) for x in sem.U]}

    # Known exact unrestricted equilibrium: stationary completion / 4,
    # player 0 quits at date 0 and everyone else Never.
    rs = affine_4pps(Q(0))
    stationary_eq = pure_profile(1, [0, 1, 1, 1])
    sem = semantic(rs, stationary_eq)
    assert_equal(sem.exploitability, Q(0), "stationary exact equilibrium")
    results["known_equilibrium"] = {
        "U": [str(x) for x in sem.U],
        "B": [str(x) for x in sem.B],
        "exploitability": str(sem.exploitability),
    }

    # After-support differs from Never exactly when all opponents Never.
    values = semantic(rb, all_never).values[0]
    assert_equal(values[2], Q(1, 4), "after-support solo payoff")
    assert_equal(values[3], Q(0), "Never allContinue payoff")
    results["after_support_vs_never"] = {
        "after_support": str(values[2]), "never": str(values[3])
    }

    # Exact sum of every terminal coalition plus all-Never is one.
    rational_profile = [
        [Q(1, 3), Q(1, 6), Q(1, 2)],
        [Q(1, 4), Q(1, 4), Q(1, 2)],
        [Q(1, 5), Q(3, 10), Q(1, 2)],
        [Q(1, 2), Q(1, 4), Q(1, 4)],
    ]
    K = 2
    surv = survival_rows(rational_profile)
    total = Q(0)
    for mask in range(1, 16):
        for t in range(K):
            term = Q(1)
            for i in range(N):
                term *= rational_profile[i][t] if mask & (1 << i) else surv[i][t + 1]
            total += term
    all_n = math.prod(row[K] for row in rational_profile)
    assert_equal(total + all_n, Q(1), "terminal mass ledger")
    results["mass_ledger"] = str(total + all_n)

    # The emitted polynomial constraints evaluate to the exact semantic pair,
    # including the auxiliary after-support and Never candidates.
    system = exact_polynomial_system(rb, K)
    env = {
        variable(i, t, K): rational_profile[i][t]
        for i in range(N) for t in range(K + 1)
    }
    exact = semantic(rb, rational_profile)
    for i in range(N):
        got_u = evaluate_polynomial_json(system["prescribed_equalities"][i]["rhs"], env)
        assert_equal(got_u, exact.U[i], f"generated U polynomial {i}")
        for tau in range(K + 2):
            index = i * (K + 2) + tau
            got_v = evaluate_polynomial_json(system["deviation_equalities"][index]["rhs"], env)
            assert_equal(got_v, exact.values[i][tau], f"generated V polynomial {i},{tau}")
    results["generated_polynomials"] = "match exact U and every finite/after/Never V"

    # Namespacing is literal: declarations, polynomial monomials, semantic
    # equalities, and cap links all use the same prefixed variables.
    namespaced = namespace_exact_system(system, "m7")
    declared = set(namespaced["variables"])
    if len(declared) != len(system["variables"]):
        raise AssertionError("namespaced declarations collided")
    if not all(str(name).startswith("m7_") for name in declared):
        raise AssertionError("unprefixed declaration survived namespacing")
    for equality in namespaced["deviation_equalities"]:
        if equality["lhs"] not in declared:
            raise AssertionError("namespaced V equality has undeclared lhs")
        for term in equality["rhs"]:
            if not set(term["monomial"]).issubset(declared):
                raise AssertionError("unprefixed monomial survived namespacing")
    results["closed_namespaced_system"] = "all declared V and center occurrences linked"

    # First family level not covered by the all-Never midpoint is M=129 at
    # lambda=3/4.  A stored rational K=4 actual center gives an exact zero
    # witness there, and in fact through M=2677.
    r34 = affine_4pps(Q(3, 4))
    all_never_129 = all_never_outer_zero_witness(r34, 129)
    if all_never_129["feasible_every_level_through_M"]:
        raise AssertionError("all-Never should cease certifying lambda=3/4 at M=129")
    profile_129 = profile_outer_zero_witness(r34, LAMBDA34_K4_ZERO_PROFILE, 129)
    if not profile_129["feasible_every_level_through_M"]:
        raise AssertionError("stored K=4 profile should certify R_129 zero")
    assert_equal(
        semantic(r34, LAMBDA34_K4_ZERO_PROFILE).exploitability,
        Q(2868660135241342669, 320000000000000000000),
        "stored lambda=3/4 K4 exploitability",
    )
    if profile_129["largest_M_certified_by_same_center"] != 2677:
        raise AssertionError("unexpected exact zero-certificate range")
    results["first_post_allNever_zero_witness"] = {
        "lambda": "3/4", "M": 129, "clock_bound": 4,
        "largest_M": 2677,
    }
    return results


def scan(args: argparse.Namespace) -> dict:
    rows = []
    for numerator in range(args.lambda_steps + 1):
        lam = Q(numerator, args.lambda_steps)
        reward = affine_4pps(lam)
        previous: List[List[float]] | None = None
        for K in range(1, args.max_k + 1):
            warm = []
            if previous is not None:
                warm = [[row[:-1] + [0.0, row[-1]] for row in previous]]
            value, profile, sem = stochastic_search(
                reward, K, args.restarts, args.steps, args.seed + 1009 * numerator + 97 * K,
                warm,
            )
            previous = profile
            rows.append({
                "lambda": str(lam),
                "K": K,
                "best_exploitability_float": value,
                "debts": [float(x) for x in sem.debts],
                "profile": profile,
                "interpretation": "floating upper witness only",
            })
    return {
        "family": "((1-lambda)*stationaryCompletion + lambda*boundaryReward)/4",
        "normalization": "all rewards in [-1,1]; common paired-singleton normalized solo geometry",
        "search": {
            "seed": args.seed,
            "restarts": args.restarts,
            "steps": args.steps,
            "max_k": args.max_k,
            "lambda_steps": args.lambda_steps,
        },
        "rows": rows,
        "warning": "No row is a lower bound or exact certificate.",
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("self-test")
    dump = sub.add_parser("dump-constraints")
    dump.add_argument("K", type=int)
    dump.add_argument("--full", action="store_true")
    dump.add_argument("--lambda-value", default="1")
    search = sub.add_parser("scan")
    search.add_argument("--max-k", type=int, default=3)
    search.add_argument("--lambda-steps", type=int, default=4)
    search.add_argument("--restarts", type=int, default=14)
    search.add_argument("--steps", type=int, default=2500)
    search.add_argument("--seed", type=int, default=20260826)
    one = sub.add_parser("search-one")
    one.add_argument("--lambda-value", required=True)
    one.add_argument("--K", type=int, required=True)
    one.add_argument("--restarts", type=int, default=30)
    one.add_argument("--steps", type=int, default=5000)
    one.add_argument("--seed", type=int, default=20260826)
    one.add_argument("--denominator", type=int, default=10000)
    periodic = sub.add_parser("period-two-truncation")
    periodic.add_argument("--max-k", type=int, default=32)
    periodic.add_argument("--denominator", type=int, default=1000000)
    outer = sub.add_parser("dump-outer")
    outer.add_argument("M", type=int)
    outer.add_argument("--full", action="store_true")
    outer.add_argument("--lambda-value", default="1")
    witness = sub.add_parser("outer-zero-witness")
    witness.add_argument("--lambda-value", required=True)
    witness.add_argument("--M", type=int, required=True)
    profile_witness = sub.add_parser("profile-zero-witness")
    profile_witness.add_argument(
        "--preset", choices=["lambda34-k4"], default="lambda34-k4"
    )
    profile_witness.add_argument("--M", type=int, required=True)
    one_shot = sub.add_parser("dump-one-shot-universal")
    one_shot.add_argument("--lambda-value", default="3/4")
    args = parser.parse_args()

    if args.command == "self-test":
        print(json.dumps(self_test(), indent=2, sort_keys=True))
    elif args.command == "dump-constraints":
        if args.K < 1:
            raise SystemExit("K must be positive")
        output = polynomial_constraint_summary(args.K)
        if args.full:
            output["exact_system"] = exact_polynomial_system(
                affine_4pps(parse_fraction(args.lambda_value)), args.K
            )
        print(json.dumps(output, indent=2, sort_keys=True))
    elif args.command == "scan":
        print(json.dumps(scan(args), indent=2, sort_keys=True))
    elif args.command == "search-one":
        if args.K < 1 or args.denominator < 1:
            raise SystemExit("K and denominator must be positive")
        lam = parse_fraction(args.lambda_value)
        reward = affine_4pps(lam)
        value, profile, sem = stochastic_search(
            reward, args.K, args.restarts, args.steps, args.seed
        )
        rational_profile = [rationalize_row(row, args.denominator) for row in profile]
        exact_sem = semantic(reward, rational_profile)
        print(json.dumps({
            "lambda": str(lam),
            "K": args.K,
            "floating": {
                "exploitability": value,
                "debts": [float(x) for x in sem.debts],
                "profile": profile,
            },
            "rational_candidate": {
                "denominator": args.denominator,
                "profile": [[str(x) for x in row] for row in rational_profile],
                "U": [str(x) for x in exact_sem.U],
                "B": [str(x) for x in exact_sem.B],
                "debts": [str(x) for x in exact_sem.debts],
                "exploitability": str(exact_sem.exploitability),
                "exploitability_float": float(exact_sem.exploitability),
                "status": "exact upper witness; not a lower certificate",
            },
        }, indent=2, sort_keys=True))
    elif args.command == "period-two-truncation":
        if args.max_k < 1 or args.denominator < 1:
            raise SystemExit("max-k and denominator must be positive")
        a_float = period_two_parameter_float()
        a = Q(a_float).limit_denominator(args.denominator)
        b = (4 * a * a - 1) / (3 * a * a)
        reward = affine_4pps(Q(1))
        rows = []
        K = 1
        while K <= args.max_k:
            profile = periodic_truncated_profile(K, a, b)
            sem = semantic(reward, profile)
            rows.append({
                "K": K,
                "exploitability": str(sem.exploitability),
                "exploitability_float": float(sem.exploitability),
                "Never_masses": [str(row[K]) for row in profile],
                "debts": [str(x) for x in sem.debts],
            })
            K *= 2
        print(json.dumps({
            "a_rational": str(a),
            "a_float": float(a),
            "a_selecting_polynomial_float":
                44 * float(a)**4 - 7 * float(a)**3 - 26 * float(a)**2 + float(a) + 3,
            "b_rational": str(b),
            "rows": rows,
            "status": "exact rational finite-clock upper witnesses; rationalized period-two parameter",
        }, indent=2, sort_keys=True))
    elif args.command == "dump-outer":
        if args.M < 1:
            raise SystemExit("M must be positive")
        output = (
            outer_hierarchy_system(affine_4pps(parse_fraction(args.lambda_value)), args.M)
            if args.full else outer_hierarchy_summary(args.M)
        )
        print(json.dumps(output, indent=2, sort_keys=True))
    elif args.command == "outer-zero-witness":
        if args.M < 1:
            raise SystemExit("M must be positive")
        reward = affine_4pps(parse_fraction(args.lambda_value))
        print(json.dumps(all_never_outer_zero_witness(reward, args.M), indent=2, sort_keys=True))
    elif args.command == "profile-zero-witness":
        if args.M < 1:
            raise SystemExit("M must be positive")
        if args.preset == "lambda34-k4":
            output = profile_outer_zero_witness(
                affine_4pps(Q(3, 4)), LAMBDA34_K4_ZERO_PROFILE, args.M
            )
        else:
            raise SystemExit("unknown preset")
        print(json.dumps(output, indent=2, sort_keys=True))
    elif args.command == "dump-one-shot-universal":
        reward = affine_4pps(parse_fraction(args.lambda_value))
        print(json.dumps(one_shot_nash_midpoint_system(reward), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
