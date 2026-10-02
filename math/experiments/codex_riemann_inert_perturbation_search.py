#!/usr/bin/env python3
"""Targeted floating search around the checked Fin4 cyclic plateau.

This is an exploratory upper-witness search, never a positive-gap certificate.
Every evaluated finite-clock profile has its exact unrestricted pure-time cap:
supported dates, the first date after support, and Never are all included.

The reward chamber preserves the four displayed pure-coalition semantic pairs
and their common cap (1,1,0,0) from FourPlayerCyclicPlateauCandidate.  Only
off-face singleton/collision/preemption entries are mutated.
"""

from __future__ import annotations

import argparse
import math
import random
import sys
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from fin4_quantile_center_prototype import (  # noqa: E402
    Reward,
    Semantic,
    float_reward,
    semantic,
    stochastic_search,
)

N = 4
F, S, H, O = range(4)
PHASE_MASKS = (0b0100, 0b0101, 0b0111, 0b0110)


def plateau_reward() -> Reward:
    result: Reward = {}
    for mask in range(1, 16):
        row: List[float] = []
        for who in range(4):
            if who == O:
                value = -1.0 if mask & (1 << O) else 0.0
            elif who == H:
                value = -1.0 if mask & (1 << H) else 0.0
            elif mask & (1 << H):
                equal = bool(mask & (1 << F)) == bool(mask & (1 << S))
                if who == F:
                    value = 0.0 if equal else 1.0
                else:
                    value = 1.0 if equal else 0.0
            else:
                value = -1.0 if mask & (1 << who) else 0.0
            row.append(value)
        result[mask] = tuple(row)  # type: ignore[assignment]
    return result


BASE = plateau_reward()

# Best quarter-grid table from the first reproducible outer run.  It is only
# a candidate for further falsification.  The local passport error is zero and
# its exact pure-coalition exploitability floor is 1/4.
CANDIDATE_A_ROWS = {
    0b0001: (0.0, 0.0, 0.0, 0.0),
    0b0010: (0.0, -0.75, 0.0, -0.5),
    0b0011: (1.0, 1.0, 0.0, -1.0),
    0b0100: (0.0, 1.0, -1.0, 0.0),
    0b0101: (1.0, 0.0, -1.0, 0.0),
    0b0110: (1.0, 0.0, -1.0, 0.0),
    0b0111: (0.0, 1.0, -1.0, 0.0),
    0b1000: (-0.5, 0.5, 0.75, 1.0),
    0b1001: (0.75, 0.25, 0.25, 0.5),
    0b1010: (-1.0, 0.75, -0.25, 0.25),
    0b1011: (0.75, 1.0, 0.25, 0.0),
    0b1100: (-0.5, 0.75, 0.5, -1.0),
    0b1101: (1.0, 0.0, 1.0, -1.0),
    0b1110: (0.5, -1.0, 0.5, -1.0),
    0b1111: (0.5, 1.0, 0.5, -1.0),
}

CANDIDATE_B_ROWS = {
    0b0001: (-0.25, 0.5, 0.0, 1.0),
    0b0010: (-0.75, 0.75, 0.0, 0.5),
    0b0011: (-0.5, -0.5, 0.0, 0.75),
    0b0100: (0.0, 1.0, -1.0, 0.0),
    0b0101: (1.0, 0.0, -1.0, 0.0),
    0b0110: (1.0, 0.0, -1.0, 0.0),
    0b0111: (0.0, 1.0, -1.0, 0.0),
    0b1000: (-0.25, -0.5, 0.0, 0.5),
    0b1001: (1.0, 0.25, 0.0, -0.75),
    0b1010: (-1.0, 0.5, -0.5, 0.25),
    0b1011: (0.25, 0.75, -0.75, 0.5),
    0b1100: (0.25, -0.25, -0.25, -1.0),
    0b1101: (1.0, 1.0, 1.0, -1.0),
    0b1110: (0.5, 0.25, 0.0, -1.0),
    0b1111: (-0.75, -0.75, 1.0, -1.0),
}

CANDIDATE_C_ROWS = {
    0b0001: (1.0, -0.75, 0.0, 0.5),
    0b0010: (1.0, -0.5, 0.0, -0.25),
    0b0011: (-0.5, 1.0, 0.0, 1.0),
    0b0100: (0.0, 1.0, -1.0, 0.0),
    0b0101: (1.0, 0.0, -1.0, 0.0),
    0b0110: (1.0, 0.0, -1.0, 0.0),
    0b0111: (0.0, 1.0, -1.0, 0.0),
    0b1000: (0.25, 0.5, 0.25, -0.25),
    0b1001: (0.5, -0.75, -0.25, -0.5),
    0b1010: (0.5, -0.25, 0.5, 0.0),
    0b1011: (-0.5, -0.25, 0.0, 0.0),
    0b1100: (0.75, 0.5, 0.25, -1.0),
    0b1101: (0.75, 0.0, 0.25, -1.0),
    0b1110: (0.5, 0.25, 0.5, -1.0),
    0b1111: (0.5, -0.5, 0.0, -1.0),
}


def fixed_coordinate(mask: int, who: int) -> bool:
    # Fix the four plateau rows completely.
    if mask in PHASE_MASKS:
        return True
    # These are the host's leave values from the three nontrivial phase rows.
    if who == H and mask in (0b0001, 0b0010, 0b0011):
        return True
    # These are the observer's join values at the four phase rows.
    if who == O and mask in (0b1100, 0b1101, 0b1110, 0b1111):
        return True
    return False


FREE = [
    (mask, who)
    for mask in range(1, 16)
    for who in range(4)
    if not fixed_coordinate(mask, who)
]


def toggle_payoff(reward: Reward, mask: int, who: int) -> float:
    toggled = mask ^ (1 << who)
    if toggled == 0:
        return 0.0
    return float(reward[toggled][who])


def pure_defect(reward: Reward, mask: int, who: int) -> float:
    current = 0.0 if mask == 0 else float(reward[mask][who])
    return max(0.0, toggle_payoff(reward, mask, who) - current)


def pure_floor(reward: Reward) -> float:
    return min(max(pure_defect(reward, mask, i) for i in range(N)) for mask in range(16))


def passport_error(reward: Reward) -> float:
    expected_debt = (
        (1.0, 0.0, 1.0, 0.0),
        (0.0, 1.0, 1.0, 0.0),
        (1.0, 0.0, 1.0, 0.0),
        (0.0, 1.0, 1.0, 0.0),
    )
    error = 0.0
    for k, mask in enumerate(PHASE_MASKS):
        for i in range(N):
            error = max(error, abs(pure_defect(reward, mask, i) - expected_debt[k][i]))
    return error


def join_gain(reward: Reward, mask_without: int, who: int) -> float:
    current = 0.0 if mask_without == 0 else float(reward[mask_without][who])
    return float(reward[mask_without | (1 << who)][who]) - current


def accepted_persistent_pair(
    reward: Reward, tolerance: float = 1e-10
) -> Tuple[Tuple[int, int], Tuple[float, float]] | None:
    """Find a nondegenerate accepted two-player persistent-base Nash root.

    Pure and fully mixed Nash points of the two-free-player induced game are
    exhaustive away from the equality walls.  The search uses a quarter grid,
    so equality cases are separately visible and are not silently certified.
    """
    players = range(N)
    for a in players:
        for b in range(a + 1, N):
            base = (1 << a) | (1 << b)
            free = [i for i in players if i not in (a, b)]
            c, d = free
            c0 = join_gain(reward, base, c)
            c1 = join_gain(reward, base | (1 << d), c)
            d0 = join_gain(reward, base, d)
            d1 = join_gain(reward, base | (1 << c), d)
            points: List[Tuple[float, float]] = []
            for xc in (0.0, 1.0):
                for xd in (0.0, 1.0):
                    cg = (1 - xd) * c0 + xd * c1
                    dg = (1 - xc) * d0 + xc * d1
                    if (xc == 0 and cg <= tolerance or xc == 1 and cg >= -tolerance) and (
                        xd == 0 and dg <= tolerance or xd == 1 and dg >= -tolerance
                    ):
                        points.append((xc, xd))
            if c0 * c1 < -tolerance and d0 * d1 < -tolerance:
                xd = -c0 / (c1 - c0)
                xc = -d0 / (d1 - d0)
                if tolerance < xc < 1 - tolerance and tolerance < xd < 1 - tolerance:
                    points.append((xc, xd))
            for xc, xd in points:
                stable = True
                for base_player in (a, b):
                    stay = 0.0
                    for cquit, pc in ((0, 1 - xc), (1, xc)):
                        for dquit, pd in ((0, 1 - xd), (1, xd)):
                            mask = base | (cquit << c) | (dquit << d)
                            leave = mask ^ (1 << base_player)
                            stay += pc * pd * (
                                float(reward[mask][base_player])
                                - float(reward[leave][base_player])
                            )
                    if stay < -tolerance:
                        stable = False
                        break
                if stable:
                    return (a, b), (xc, xd)
    return None


def deadline_threat_certificate(
    reward: Reward, tolerance: float = 1e-10
) -> Tuple[int, int] | None:
    """Find the exact two-date profile owner@0, blocker@1, others Never."""
    for owner in range(N):
        solo = float(reward[1 << owner][owner])
        for blocker in range(N):
            if blocker == owner:
                continue
            pair = (1 << owner) | (1 << blocker)
            if solo + tolerance < float(reward[pair][owner]):
                continue
            if solo + tolerance < float(reward[1 << blocker][owner]):
                continue
            stable = True
            for who in range(N):
                if who == owner:
                    continue
                if float(reward[pair if who == blocker else (1 << owner) | (1 << who)][who]) > float(
                    reward[1 << owner][who]
                ) + tolerance:
                    stable = False
                    break
            if stable:
                return owner, blocker
    return None


def stationary_semantic(reward: Reward, rates: Sequence[float]) -> Semantic:
    """Exact infinite-stationary semantics and all-behavior cap."""
    r = float_reward(reward)
    all_continue = math.prod(1.0 - x for x in rates)
    absorption = 1.0 - all_continue
    if absorption <= 1e-15:
        # Literal all-Never.
        U = [0.0] * N
        values = []
        for i in range(N):
            solo = float(r[1 << i][i])
            values.append([solo, 0.0])
        B = [max(v) for v in values]
        return Semantic(U, B, values)

    U = [0.0] * N
    for mask in range(1, 16):
        root_mass = 1.0
        for i in range(N):
            root_mass *= rates[i] if mask & (1 << i) else 1.0 - rates[i]
        outcome_mass = root_mass / absorption
        for i in range(N):
            U[i] += outcome_mass * float(r[mask][i])

    values: List[List[float]] = []
    for i in range(N):
        opponents = [j for j in range(N) if j != i]
        opp_continue = math.prod(1.0 - rates[j] for j in opponents)
        opp_absorb = 1.0 - opp_continue
        quit_value = 0.0
        never_numerator = 0.0
        for sub in range(1 << len(opponents)):
            mask = 0
            mass = 1.0
            for k, j in enumerate(opponents):
                if sub & (1 << k):
                    mask |= 1 << j
                    mass *= rates[j]
                else:
                    mass *= 1.0 - rates[j]
            quit_value += mass * float(r[mask | (1 << i)][i])
            if mask:
                never_numerator += mass * float(r[mask][i])
        if opp_absorb <= 1e-15:
            never_value = 0.0
        else:
            never_value = never_numerator / opp_absorb
        values.append([quit_value, never_value])
    B = [max(v) for v in values]
    return Semantic(U, B, values)


def random_stationary_search(
    reward: Reward, rng: random.Random, samples: int, incumbent: float
) -> Tuple[float, List[float], Semantic]:
    best = incumbent
    best_rates = [0.0] * N
    best_sem = stationary_semantic(reward, best_rates)
    starts = [[0.0] * N, [1.0] * N]
    starts += [[1.0 if i == j else 0.0 for i in range(N)] for j in range(N)]
    random_count = min(32, max(8, samples // 500))
    starts += [[rng.random() for _ in range(N)] for _ in range(random_count)]
    local_steps = max(80, samples // len(starts))
    for rates in starts:
        rates = list(rates)
        sem = stationary_semantic(reward, rates)
        value = float(sem.exploitability)
        local_best = value
        local_rates = list(rates)
        local_sem = sem
        for step in range(local_steps):
            temperature = max(1e-5, 0.04 * (1.0 - step / max(1, local_steps)))
            proposal = list(rates)
            if rng.random() < 0.8:
                i = rng.randrange(N)
                scale = max(0.002, 0.25 * (1.0 - step / max(1, local_steps)))
                proposal[i] = min(1.0, max(0.0, proposal[i] + rng.uniform(-scale, scale)))
            else:
                alpha = rng.random() * max(0.01, 0.3 * (1.0 - step / max(1, local_steps)))
                target = [rng.random() for _ in range(N)]
                proposal = [(1 - alpha) * proposal[i] + alpha * target[i] for i in range(N)]
            proposed_sem = stationary_semantic(reward, proposal)
            proposed = float(proposed_sem.exploitability)
            if proposed < value or rng.random() < math.exp((value - proposed) / temperature):
                rates, sem, value = proposal, proposed_sem, proposed
            if value < local_best:
                local_best, local_rates, local_sem = value, list(rates), sem
        value, rates, sem = local_best, local_rates, local_sem
        if value < best:
            best, best_rates, best_sem = value, list(rates), sem
    return best, best_rates, best_sem


def inner_upper(
    reward: Reward,
    rng: random.Random,
    ks: Sequence[int],
    restarts: int,
    steps: int,
) -> Tuple[float, str, object, Semantic]:
    best, rates, best_sem = random_stationary_search(reward, rng, 240, math.inf)
    kind = "stationary"
    witness: object = rates
    warm: List[List[List[float]]] = []
    for K in ks:
        value, profile, sem = stochastic_search(
            reward,
            K,
            restarts,
            steps,
            rng.randrange(1 << 30),
            extra_starts=warm,
        )
        if value < best:
            best, kind, witness, best_sem = value, f"clock-{K}", profile, sem
        # Embed the best K-clock law at the next supported date count.
        if profile:
            warm = [[row[:-1] + [0.0, row[-1]] for row in profile]]
    return best, kind, witness, best_sem


def clone(reward: Reward) -> Reward:
    return {mask: tuple(float(x) for x in row) for mask, row in reward.items()}  # type: ignore[return-value]


def set_coord(reward: Reward, mask: int, who: int, value: float) -> Reward:
    result = clone(reward)
    row = list(result[mask])
    row[who] = max(-1.0, min(1.0, value))
    result[mask] = tuple(row)  # type: ignore[assignment]
    return result


def initial_candidate(rng: random.Random, grid: float) -> Reward:
    result = clone(BASE)
    for mask, who in FREE:
        result = set_coord(result, mask, who, round(rng.uniform(-1, 1) / grid) * grid)
    # Force the necessary all-Never and first collision chain screens.
    owner = rng.choice((F, S, O))
    result = set_coord(result, 1 << owner, owner, 1.0)
    outsiders = [i for i in range(N) if i != owner]
    joiner = rng.choice(outsiders)
    pair = (1 << owner) | (1 << joiner)
    result = set_coord(result, pair, joiner, 1.0)
    return result


def reward_rows(reward: Reward) -> str:
    rows = []
    for mask in range(1, 16):
        rows.append(f"{mask:04b}: " + " ".join(f"{float(x):+.3f}" for x in reward[mask]))
    return "\n".join(rows)


def run(args: argparse.Namespace) -> None:
    rng = random.Random(args.seed)
    candidates = [initial_candidate(rng, args.grid) for _ in range(args.population)]
    scored: List[Tuple[float, float, Reward, str, object, Semantic]] = []

    for generation in range(args.generations):
        scored.clear()
        for reward in candidates:
            pf = pure_floor(reward)
            pair_certificate = accepted_persistent_pair(reward)
            deadline_certificate = deadline_threat_certificate(reward)
            if pf <= 0 or passport_error(reward) > 1e-9 or (
                args.exclude_persistent_pair and pair_certificate is not None
            ) or (
                args.exclude_deadline_threat and deadline_certificate is not None
            ):
                scored.append((-10.0 + pf, pf, reward, "pure", None, semantic(reward, [[1.0] for _ in range(N)])))
                continue
            upper, kind, witness, sem = inner_upper(
                reward, rng, args.ks, args.restarts, args.steps
            )
            score = min(pf, upper)
            scored.append((score, pf, reward, kind, witness, sem))
        scored.sort(key=lambda x: x[0], reverse=True)
        top = scored[0]
        print(
            f"generation={generation} score={top[0]:.8g} pure={top[1]:.8g} "
            f"upper={float(top[5].exploitability):.8g} witness={top[3]}",
            flush=True,
        )
        if generation + 1 == args.generations:
            break
        elite = scored[: max(2, args.population // 4)]
        next_candidates = [clone(row[2]) for row in elite]
        while len(next_candidates) < args.population:
            parent = clone(rng.choice(elite)[2])
            mutations = 1 + rng.randrange(max(1, args.mutations))
            for _ in range(mutations):
                mask, who = rng.choice(FREE)
                current = float(parent[mask][who])
                delta = rng.choice((-2, -1, 1, 2)) * args.grid
                parent = set_coord(parent, mask, who, round((current + delta) / args.grid) * args.grid)
            next_candidates.append(parent)
        candidates = next_candidates

    score, pf, reward, kind, witness, sem = scored[0]
    print("\nBEST")
    print(f"score={score:.12g} pure_floor={pf:.12g} witness={kind}")
    print(f"persistent_pair={accepted_persistent_pair(reward)}")
    print(f"deadline_threat={deadline_threat_certificate(reward)}")
    print(f"witness_debts={[float(x) for x in sem.debts]}")
    print(reward_rows(reward))
    print("WITNESS")
    print(witness)


def audit_candidate(args: argparse.Namespace) -> None:
    rows = {"A": CANDIDATE_A_ROWS, "B": CANDIDATE_B_ROWS, "C": CANDIDATE_C_ROWS}[args.candidate]
    reward: Reward = {mask: tuple(row) for mask, row in rows.items()}  # type: ignore[assignment]
    rng = random.Random(args.seed)
    print(f"passport_error={passport_error(reward)} pure_floor={pure_floor(reward)}")
    print(f"persistent_pair={accepted_persistent_pair(reward)}")
    print(f"deadline_threat={deadline_threat_certificate(reward)}")
    last_profile: List[List[float]] | None = None
    last_k = 0
    for K in args.ks:
        warm: List[List[List[float]]] = []
        if last_profile is not None and K >= last_k:
            warm = [[row[:last_k] + [0.0] * (K - last_k) + [row[-1]] for row in last_profile]]
        value, profile, sem = stochastic_search(
            reward,
            K,
            args.restarts,
            args.steps,
            rng.randrange(1 << 30),
            extra_starts=warm,
        )
        print(
            f"K={K} upper={value:.12g} debts={[float(x) for x in sem.debts]}",
            flush=True,
        )
        last_profile, last_k = profile, K
    stat, rates, sem = random_stationary_search(reward, rng, 20000, math.inf)
    print(
        f"stationary_upper={stat:.12g} rates={rates} "
        f"debts={[float(x) for x in sem.debts]}"
    )


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=20260828)
    p.add_argument("--population", type=int, default=18)
    p.add_argument("--generations", type=int, default=10)
    p.add_argument("--mutations", type=int, default=5)
    p.add_argument("--grid", type=float, default=0.25)
    p.add_argument("--ks", type=int, nargs="+", default=[1, 2, 3])
    p.add_argument("--restarts", type=int, default=8)
    p.add_argument("--steps", type=int, default=700)
    p.add_argument("--audit-candidate", action="store_true")
    p.add_argument("--candidate", choices=["A", "B", "C"], default="A")
    p.add_argument("--exclude-persistent-pair", action="store_true")
    p.add_argument("--exclude-deadline-threat", action="store_true")
    return p


if __name__ == "__main__":
    args = parser().parse_args()
    if args.audit_candidate:
        audit_candidate(args)
    else:
        run(args)
