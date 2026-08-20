"""Own-set-shift backward-distance upper bound to the exact-cycle strata
`Sigma_L` (P13 slice two, item 3).

## The cited theorem (E64)

`UniformEquilibrium/Quitting/Root/EndpointBackwardStability.lean`,
`exists_exact_of_isεQuittingRootEndpointNash`: every `eps`-complementary root
row is EXACTLY complementary for an own-set-shifted reward table `r'`, with

    |d_i| <= eps                          if coordinate i is pure (x_i in {0,1})
    |d_i| <= eps / min(x_i, 1 - x_i)       if coordinate i is interior

so `‖r - r'‖_inf <= C * eps` with `C = 1` at a pure row and, in general,
`C = max` over interior coordinates `i` of `1 / min(x_i, 1 - x_i)` (the
condition number blowing up as an interior rate approaches a pure endpoint.
Historical cycle-strata discussion is retained only in `TRANSITION.md`. Both
the theorem and this
module are period-ONE / fixed-tail: the row is a single stationary phase
played forever, not a genuinely period-`L` sequence of varying phases (the
cycle-feedback generalization is an open item, not attempted here; no
period-specific search is claimed.

## What "defect" means for a stationary candidate row

For a row `x` with its own self-consistent stationary value `V(x)`
(`filters.stationary_value`) and gap `g_i = Sigma_i(x) - Gamma_i(x, V(x))`
(`filters.gap` -- the exact period-one complementarity gap that
`stationary_row_search` demands be `>= 0`/`<= 0` on either side of `x_i`),
the one-sided VIOLATION at coordinate `i` is

    x_i == 0:            defect_i = max(0,  g_i)   (needs g_i <= 0)
    x_i == 1:             defect_i = max(0, -g_i)   (needs g_i >= 0)
    0 < x_i < 1:          defect_i = |g_i|           (needs g_i == 0, both sides)

and the row's overall defect is `max_i defect_i` -- exactly the smallest
`eps` for which `x` is `eps`-complementary in `IsεQuittingRootEndpointNash`'s
sense (`quittingRootEndpointDifference`'s two clauses correspond to `g_i`'s
two one-sided uses here).  When `defect == 0` the row is an EXACT
complementary stationary row and this module's bound is `0` -- consistent
with `filters.stationary_row_search` finding it directly (see
`validate.py`'s K2 control, reused as a control here too: a weight known to
admit an exact row must score bound `0`).

## Search: reuses slice one's stationary-row grid, exact throughout

The candidate grid is the SAME `filters._small_rationals(denom_bound)` grid
`stationary_row_search` brute-forces.  Every point in the grid is evaluated
EXACTLY (`Fraction` arithmetic) rather than through a float pre-filter:
measured at `denom_bound = 10` (`33^3 = 35937` points, `n = 3`) this
completes in a few seconds (see the dispatch commentary in this module's
validation), so the float exploration pass the P13 item permits ("floats
permitted for exploration; exact re-check at report time") was not needed to
stay inside a sensible runtime budget at the denominators this slice
targets; nothing here is reported from a float computation.

## The per-`L` table is deliberately NOT period-specific

A constant row played forever satisfies every period-`L` recursion the same
way it satisfies the period-one one, so `Sigma_1 subseteq Sigma_L` for every
`L >= 1`.  The best period-one row's own-set-shift bound is therefore a
valid upper bound on the distance to `Sigma_L` for EVERY `L` -- the table
below reports the same number at every `L`, honestly, rather than
fabricating an `L`-specific search this slice does not implement (a
genuinely period-`L` stationary-row search, with `L` independently varying
phases, is the natural next slice; no period-specific search is claimed).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
from typing import Dict, Optional, Sequence, Tuple

from filters import _small_rationals, gap as exact_gap, stationary_value
from weights import Weight, players


@dataclass(frozen=True)
class RowDistance:
    row: Tuple[Fr, ...]
    value: Tuple[Fr, ...]
    gaps: Tuple[Fr, ...]
    defect: Fr
    condition_number: Fr
    bound: Fr  # condition_number * defect


def row_backward_distance(w: Weight, x: Sequence[Fr]) -> Optional[RowDistance]:
    """The own-set-shift bound for a single candidate row `x`: `None` if `x`
    has no stationary value (`x == 0`, the all-continue row -- never
    absorbs)."""
    V = stationary_value(w, x)
    if V is None:
        return None
    n = len(x)
    gaps = [exact_gap(w, x, V, i) for i in range(n)]
    defect = Fr(0)
    for i in range(n):
        if x[i] == 0:
            d = max(Fr(0), gaps[i])
        elif x[i] == 1:
            d = max(Fr(0), -gaps[i])
        else:
            d = abs(gaps[i])
        if d > defect:
            defect = d
    C = Fr(1)
    for i in range(n):
        if 0 < x[i] < 1:
            c_i = Fr(1) / min(x[i], Fr(1) - x[i])
            if c_i > C:
                C = c_i
    return RowDistance(
        row=tuple(x), value=tuple(V), gaps=tuple(gaps),
        defect=defect, condition_number=C, bound=C * defect,
    )


def best_row_backward_distance(w: Weight, denom_bound: int) -> Optional[RowDistance]:
    """Exhaustive exact search over `filters._small_rationals(denom_bound)^n
    \\ {0}` (the same grid `filters.stationary_row_search` uses) for the row
    minimizing the own-set-shift bound `C * defect`.  `None` only if the
    grid is empty (never, for `denom_bound >= 1`) or every row lacks a
    stationary value (only `x == 0`, excluded)."""
    n = players(w)
    grid = _small_rationals(denom_bound)
    best: Optional[RowDistance] = None

    def rows(depth: int, prefix: Tuple[Fr, ...]):
        if depth == n:
            yield prefix
            return
        for v in grid:
            yield from rows(depth + 1, prefix + (v,))

    for x in rows(0, ()):
        if all(xi == 0 for xi in x):
            continue
        rd = row_backward_distance(w, x)
        if rd is None:
            continue
        if best is None or rd.bound < best.bound:
            best = rd
    return best


def backward_distance_table(
    w: Weight, denom_bound: int = 8, max_L: int = 3
) -> Dict[str, object]:
    """Per-weight report: the best period-one own-set-shift bound found at
    `denom_bound`, reported (per the module docstring) as an upper bound on
    the distance to `Sigma_L` for every `L` in `1..max_L`."""
    best = best_row_backward_distance(w, denom_bound)
    if best is None:
        return {
            "denom_bound": denom_bound,
            "best_row": None,
            "distance_upper_bound_by_L": {L: None for L in range(1, max_L + 1)},
            "reason": "grid exhausted with no nonzero row admitting a "
                      "stationary value (should not happen for denom_bound >= 1)",
        }
    return {
        "denom_bound": denom_bound,
        "best_row": {
            "x": [str(v) for v in best.row],
            "V": [str(v) for v in best.value],
            "gaps": [str(v) for v in best.gaps],
            "defect": str(best.defect),
            "condition_number": str(best.condition_number),
            "bound": str(best.bound),
        },
        "distance_upper_bound_by_L": {
            L: str(best.bound) for L in range(1, max_L + 1)
        },
    }
