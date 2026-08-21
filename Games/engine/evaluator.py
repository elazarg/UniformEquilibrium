"""Exact evaluator for periodic per-stage hazard profiles.

This is a faithful port of the evaluator in
``Experiments/singleton_collision_candidate_search/singleton_collision_candidate_search.py``.
The arithmetic is deliberately kept operation-for-operation identical to the
reference: the attacks are Nelder-Mead searches, so a difference of one unit in
the last place can send an optimizer down a different path, and the parity
tests compare optimizer output as well as evaluator output.

Exactness claim, stated precisely: given the profile, the on-path values and
the deviator's best response are computed by closed-form linear solves rather
than by simulation or truncation, so the only error is floating point.  It says
nothing about profiles outside the searched families.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Optional, Sequence

from .model import MASKS, N, NONEMPTY, PLAYERS, Hazards, Table


def cyclic_solve(constants: Sequence[float], hazards: Sequence[float]) -> list[float]:
    """Solve ``V_t = constants[t] + (1 - hazards[t]) * V_{t+1}`` on a cycle.

    Phases are described by their absorption probability rather than by their
    survival factor.  That is not a stylistic choice.  The optimizers push
    hazards below machine epsilon while chasing the fine-block limit, and there
    ``1 - hazard`` rounds to exactly ``1.0``: the hazard is annihilated, while
    the numerator still carries the true value, so the solve mixes two
    inconsistent pictures and returns nonsense.

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


def on_path_values(table: Table, hazards: Hazards) -> list[list[float]]:
    """On-path value of every player at every phase, ``[player][phase]``."""

    period = len(hazards)
    data = [phase_data(table, hazards[t]) for t in range(period)]
    stage_hazards = [data[t].absorption for t in range(period)]
    return [
        cyclic_solve([data[t].absorbed[j] for t in range(period)], stage_hazards)
        for j in PLAYERS
    ]


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


def evaluate(table: Table, hazards: Hazards) -> dict:
    """Exploitability with the per-player breakdown the portal API reports.

    ``exploitability`` is the same number :func:`periodic_exploitability`
    returns.  The extra fields name the deviation that attains it: for each
    player the phase where the gap is largest, the value of the best stopping
    policy there, and that policy as one boolean per phase (``True`` = quit).
    """

    period = len(hazards)
    data = [phase_data(table, hazards[t]) for t in range(period)]
    stage_hazards = [data[t].absorption for t in range(period)]
    on_path = [
        cyclic_solve([data[t].absorbed[j] for t in range(period)], stage_hazards)
        for j in PLAYERS
    ]
    per_player: list[float] = []
    deviations: list[dict] = []
    for i in PLAYERS:
        best_response = [-math.inf] * period
        best_policy = [0] * period
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
                    best_policy[t] = policy
        gaps = [best_response[t] - on_path[i][t] for t in range(period)]
        worst_phase = max(range(period), key=lambda t: gaps[t])
        per_player.append(max(gaps))
        policy = best_policy[worst_phase]
        deviations.append(
            {
                "player": i,
                "value": best_response[worst_phase],
                "phase": worst_phase,
                "policy": [bool(policy >> t & 1) for t in range(period)],
            }
        )
    return {
        "exploitability": max(per_player),
        "per_player": per_player,
        "on_path": [on_path[i][0] for i in PLAYERS],
        "on_path_by_phase": [list(on_path[i]) for i in PLAYERS],
        "best_deviations": deviations,
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
