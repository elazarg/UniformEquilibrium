"""Rational snapping and exact re-evaluation.

A floating-point kill is a numerical fact about a numerical profile.  Snapping
the hazards to small-denominator fractions and redoing the whole evaluation in
:class:`fractions.Fraction` removes the floating point from the second half of
that sentence: the reported exploitability of the snapped profile is then an
exact rational number, and the comparison against ``eps_kill`` is exact.

That is what the ``exact`` evidence tier means here, and no more.  It is a
statement about one profile on one table -- that this particular profile is an
``eps``-equilibrium spoiler with an exactly computed margin.  It is not a
statement about all profiles, and the table entries are taken as the exact
binary rationals the floats already are, so a table whose intended entries are
decimal is snapped as written, not as intended.

Why the evaluation stays rational: with rational hazards every stage-outcome
probability is a product of rationals, the absorption probability of a cycle is
one minus a product of rationals, and the cyclic recursion is one division by
that absorption.  The stopping-policy enumeration adds only comparisons.  So
the whole evaluator closes over the rationals -- provided it is written with
products rather than with the ``log1p``/``expm1`` form the float evaluator uses
for accuracy near zero, which is exactly what this module does.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Optional, Sequence

from .model import (
    EPS_KILL,
    MASKS,
    N,
    NONEMPTY,
    PLAYERS,
    Hazards,
    Table,
    hazards_to_wire,
)

ZERO = Fraction(0)
ONE = Fraction(1)

#: Denominators tried by :func:`harden`, smallest first.
DEFAULT_DENOMINATORS = (2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 25, 32, 50, 64, 100)

RationalTable = tuple[tuple[Fraction, ...], ...]


def rational_table(table: Table) -> RationalTable:
    """The table with entries as exact rationals (floats are exact already)."""

    return tuple(tuple(Fraction(value) for value in row) for row in table)


def snap(value: float, denominator: int) -> Fraction:
    """Nearest fraction with denominator dividing ``denominator``, clipped."""

    snapped = Fraction(round(value * denominator), denominator)
    return max(ZERO, min(ONE, snapped))


def snap_hazards(hazards: Hazards, denominator: int) -> list[list[Fraction]]:
    return [[snap(value, denominator) for value in row] for row in hazards]


def cyclic_solve_exact(
    constants: Sequence[Fraction], hazards: Sequence[Fraction]
) -> list[Fraction]:
    """Exact ``V_t = constants[t] + (1 - hazards[t]) V_{t+1}`` around a cycle.

    The float evaluator works in log space to keep sub-epsilon hazards alive;
    with rationals there is no such loss, so the survival product is formed
    directly.  Zero total absorption means the cycle never ends, and the value
    is the never-absorbed payoff of zero.
    """

    period = len(constants)
    survival = ONE
    numerator = ZERO
    certain = False
    for k in range(period):
        numerator += survival * constants[k]
        hazard = hazards[k]
        if hazard >= ONE:
            certain = True
            break
        if hazard > ZERO:
            survival *= ONE - hazard
    absorption = ONE if certain else ONE - survival
    head = numerator / absorption if absorption > ZERO else ZERO
    values = [ZERO] * period
    values[0] = head
    for t in range(period - 1, 0, -1):
        follower = values[t + 1] if t + 1 < period else head
        values[t] = constants[t] + (ONE - hazards[t]) * follower
    return values


def _stage_absorption(hazard: Sequence[Fraction], skip: Optional[int]) -> Fraction:
    survival = ONE
    for i in PLAYERS:
        if i == skip:
            continue
        rate = hazard[i]
        if rate >= ONE:
            return ONE
        survival *= ONE - rate
    return ONE - survival


def _phase_data(table: RationalTable, hazard: Sequence[Fraction]) -> dict:
    complement = [ONE - hazard[i] for i in PLAYERS]
    probability = [ZERO] * len(MASKS)
    for mask in MASKS:
        value = ONE
        for i in PLAYERS:
            value *= hazard[i] if mask >> i & 1 else complement[i]
        probability[mask] = value
    absorbed = [ZERO] * N
    for mask in NONEMPTY:
        weight = probability[mask]
        if weight == ZERO:
            continue
        row = table[mask]
        for j in PLAYERS:
            absorbed[j] += weight * row[j]
    quit_now = [ZERO] * N
    others_absorbed = [ZERO] * N
    for i in PLAYERS:
        bit = 1 << i
        for mask in MASKS:
            if mask & bit:
                continue
            weight = ONE
            for j in PLAYERS:
                if j == i:
                    continue
                weight *= hazard[j] if mask >> j & 1 else complement[j]
            if weight == ZERO:
                continue
            quit_now[i] += weight * table[mask | bit][i]
            if mask:
                others_absorbed[i] += weight * table[mask][i]
    return {
        "absorption": _stage_absorption(hazard, None),
        "absorbed": absorbed,
        "quit_now": quit_now,
        "others_absorbed": others_absorbed,
        "others_absorption": [_stage_absorption(hazard, i) for i in PLAYERS],
    }


def exact_exploitability(
    table: RationalTable, hazards: Sequence[Sequence[Fraction]]
) -> Fraction:
    """Exploitability as an exact rational, by the same policy enumeration."""

    period = len(hazards)
    data = [_phase_data(table, hazards[t]) for t in range(period)]
    stage_hazards = [data[t]["absorption"] for t in range(period)]
    on_path = [
        cyclic_solve_exact(
            [data[t]["absorbed"][j] for t in range(period)], stage_hazards
        )
        for j in PLAYERS
    ]
    worst: Optional[Fraction] = None
    for i in PLAYERS:
        best_response: list[Optional[Fraction]] = [None] * period
        for policy in range(1 << period):
            constants = []
            policy_hazards = []
            for t in range(period):
                if policy >> t & 1:
                    constants.append(data[t]["quit_now"][i])
                    policy_hazards.append(ONE)
                else:
                    constants.append(data[t]["others_absorbed"][i])
                    policy_hazards.append(data[t]["others_absorption"][i])
            values = cyclic_solve_exact(constants, policy_hazards)
            for t in range(period):
                if best_response[t] is None or values[t] > best_response[t]:
                    best_response[t] = values[t]
        for t in range(period):
            gap = best_response[t] - on_path[i][t]
            if worst is None or gap > worst:
                worst = gap
    assert worst is not None
    return worst


def exact_exploitability_of(table: Table, hazards: Hazards) -> Fraction:
    """Exact exploitability of an already-rational-valued float profile."""

    rational = [[Fraction(value) for value in row] for row in hazards]
    return exact_exploitability(rational_table(table), rational)


def fractions_to_wire(hazards: Sequence[Sequence[Fraction]]) -> dict:
    return hazards_to_wire([[float(value) for value in row] for row in hazards])


def harden(
    table: Table,
    hazards: Hazards,
    eps_kill: float = EPS_KILL,
    denominators: Iterable[int] = DEFAULT_DENOMINATORS,
) -> dict:
    """Snap a profile to small-denominator hazards and re-verify exactly.

    Denominators are tried smallest first and the first one whose *exact*
    exploitability is at or below ``eps_kill`` wins, so the answer is the
    simplest snapping that still kills.  When none of them does, the report
    says so and returns the snapping that came closest, with ``kills`` false.
    """

    exact_table = rational_table(table)
    threshold = Fraction(eps_kill).limit_denominator(10**9)
    attempts: list[dict] = []
    winner: Optional[dict] = None
    best: Optional[dict] = None
    for denominator in denominators:
        snapped = snap_hazards(hazards, denominator)
        value = exact_exploitability(exact_table, snapped)
        attempt = {
            "denominator": denominator,
            "profile": fractions_to_wire(snapped),
            "hazards_exact": [[str(v) for v in row] for row in snapped],
            "exploitability": float(value),
            "exploitability_exact": str(value),
            "kills": value <= threshold,
        }
        attempts.append(attempt)
        if best is None or value < Fraction(best["exploitability_exact"]):
            best = attempt
        if attempt["kills"] and winner is None:
            winner = attempt
            break
    chosen = winner or best
    return {
        "kills": bool(winner),
        "eps_kill": eps_kill,
        "tier": "exact" if winner else None,
        "denominator": chosen["denominator"] if chosen else None,
        "profile": chosen["profile"] if chosen else None,
        "hazards_exact": chosen["hazards_exact"] if chosen else None,
        "exploitability": chosen["exploitability"] if chosen else None,
        "exploitability_exact": chosen["exploitability_exact"] if chosen else None,
        "attempts": attempts,
        "claim": (
            "Exact rational evaluation of one snapped profile on this table. "
            "It bounds that profile's exploitability exactly; it says nothing "
            "about profiles outside the snapping."
        ),
    }
