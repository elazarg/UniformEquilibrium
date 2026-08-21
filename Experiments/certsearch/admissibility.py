"""Filter (2b): admissibility of a period-one solo-quitter cycle (P13, slice
two).

`solo_quitter_lp` (`filters.py`) decides existence of a period-one
complementary row `p * e_i` (owner `i` quits at rate `p in (0,1]`, every
`j != i` silent) -- the no-join Nash test.  Existence of that row is
*strictly weaker* than admissibility of the cycle it generates: the
compiler's actual requirement (`IsQuittingCycleAdmissible`,
`UniformEquilibrium/Quitting/Cycles/AdmissibleCycleTerminalEquilibrium.lean`,
line ~234) is, at every coordinate `who`, EITHER the deleted (opponent)
survival product around the cycle is strictly below one, OR `who`'s own solo
reward `r_who({who})` is nonnegative
(`IsQuittingCycleZeroDeviationMismatchAt`, same file, line ~225):

    (prod_{cyclePhase} deletedSurvival(cyclePhase, who)) < 1  \\/  0 <= r_who({who})

This is the two-player counterexample's whole point
(`UniformEquilibrium/Quitting/Boundary/Repair/DisjunctionCounterexample.lean`):
its witness row exists (Item 2, `witnessBlock_isCyclicContinuationBlock`) but
is not admissible (Item 3, `not_isQuittingCycleAdmissible_witnessBlock`),
because the deleted survival product at the OWNER is exactly one there, not
below it, and the owner's solo value is negative.

## Who is isolated at a solo row, exactly

At the solo row `p * e_i` (`p in (0,1]`, everyone else silent), compute the
deleted survival product at each player `who` -- the product, around the
(period-one) cycle, of `who`'s OPPONENTS continuing:

* `who = i` (the owner): every opponent of `i` is `j != i`, and every such
  `j` is silent (quit probability `0`) at this row, so `i`'s deleted
  survival product is exactly `1`.  `i` is the ISOLATED coordinate here --
  matching `QuittingDisjunctionCounterexample.lean`'s own language ("Coordinate
  2 [the owner, `true`] is isolated at the witness row: its only opponent,
  coordinate 1, continues surely").  Admissibility at `i` therefore reduces
  to the sign condition `r_i({i}) >= 0`.
* `who = j != i`: `j`'s opponents include `i`, who is active (`p > 0`), so
  `j`'s deleted survival product is `1 - p < 1` STRICTLY (the LP's domain is
  `p in (0,1]`, so `p > 0` always -- see `filters.solo_quitter_lp`'s
  `lo_open = True`).  Admissibility at every `j != i` holds AUTOMATICALLY,
  through the first (contraction) branch, regardless of the sign of
  `r_j({j})`, and regardless of which witness `p` the LP happened to report.

So the practical test collapses to a single sign check on the OWNER's own
solo value: a solo row `p * e_i` is admissible iff `r_i({i}) >= 0`, full
stop -- independent of `p`, `n`, or the values at `j != i`.  This module
still computes the full per-player disjunction generically (not just the
owner's shortcut) so a bug in the "j is automatic" reasoning above would
show up as a failing assertion rather than being silently assumed.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from typing import Dict, Sequence

from filters import Certificate, solo_quitter_lp
from weights import Weight, players, solo


def deleted_survival(x: Sequence[Fr], who: int) -> Fr:
    """The deleted (opponent) survival product at `who` for a single-phase
    cycle with quit-probability row `x`: `prod_{j != who} (1 - x_j)`.  This
    is `quittingStationaryFixedOpponentsContinueMass` specialized to a
    period-one (`Fin 1`) cycle, where the "product around the cycle" in
    `IsQuittingCycleZeroDeviationMismatchAt` has exactly one factor."""
    out = Fr(1)
    for j, xj in enumerate(x):
        if j == who:
            continue
        out *= Fr(1) - xj
    return out


def cycle_admissible(w: Weight, x: Sequence[Fr]) -> Certificate:
    """`IsQuittingCycleAdmissible`, specialized to the period-one constant
    row `x` (any row, not just a solo row -- reusable by
    `backward_distance.py`'s stationary-row candidates too): for every
    player `who`, either the deleted survival product at `who` is strictly
    below one, or `who`'s solo value is nonnegative."""
    n = players(w)
    per_player: Dict[int, dict] = {}
    ok = True
    for who in range(n):
        surv = deleted_survival(x, who)
        d_who = solo(w, who)
        contracts = surv < 1
        nonneg_solo = d_who >= 0
        admissible_here = contracts or nonneg_solo
        per_player[who] = {
            "deleted_survival": surv,
            "solo_value": d_who,
            "contracts": contracts,
            "nonneg_solo": nonneg_solo,
            "admissible": admissible_here,
        }
        if not admissible_here:
            ok = False
    return Certificate(ok, {"row": tuple(x), "per_player": per_player})


def solo_row(n: int, i: int, p: Fr) -> Sequence[Fr]:
    """The solo row `p * e_i`: owner `i` quits at rate `p`, every `j != i`
    silent."""
    return tuple(p if j == i else Fr(0) for j in range(n))


def solo_quitter_admissible(w: Weight, i: int) -> Certificate:
    """Filter (2b).  First requires `solo_quitter_lp(w, i)` feasible (a
    period-one complementary row `p * e_i` exists); then decides
    admissibility of the cycle that row generates via `cycle_admissible`.

    If `solo_quitter_lp` is infeasible there is no period-one solo row to
    test admissibility of -- filter (2b) is downstream of filter (2), not a
    replacement for it -- and this returns `ok=False` with
    `detail['not_applicable'] = True` rather than fabricating an answer.
    This is exactly the FTV table's situation: `solo_quitter_lp` fails at
    every coordinate (slice one's `validate.py`), so (2b) never fires there;
    FTV's actual admissible cycle is the period-THREE phase-rotation block
    (`UniformEquilibrium/Quitting/Examples/Cyclic/ThreePlayer/AdmissibleCycle.lean`),
    never a period-one solo row. Its
    separate algebraic screen does not change that period distinction.
    """
    n = players(w)
    lp_cert = solo_quitter_lp(w, i)
    if not lp_cert.ok:
        return Certificate(
            False,
            {
                "not_applicable": True,
                "owner": i,
                "reason": "solo_quitter_lp infeasible: no period-one solo row "
                          "p*e_i exists for this owner, so admissibility (2b) "
                          "does not apply -- it is downstream of filter (2)",
                "lp_certificate": lp_cert.detail,
            },
        )
    p = lp_cert.detail["p_witness"]
    x = solo_row(n, i, p)
    adm_cert = cycle_admissible(w, x)
    detail = dict(adm_cert.detail)
    detail["owner"] = i
    detail["p_witness"] = p
    detail["lp_certificate"] = lp_cert.detail
    return Certificate(adm_cert.ok, detail)
