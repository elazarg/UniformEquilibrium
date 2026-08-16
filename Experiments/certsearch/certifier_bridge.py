"""Filter (4): fixed-period exact-cycle existence, via
`Experiments/certsearch/krawczyk_cycle_certifier.py` (a dyadic-interval
/Krawczyk island... generalized... to quitting-cycle complementarity
systems").  This module does not modify the certifier; it adapts a
`weights.Weight` table into the certifier's own `table(S, i)` calling
convention and drives the certifier's existing branch-and-bound /
Krawczyk building blocks over an arbitrary `weights.Weight`, instead of the
two hardcoded tables (`cyclic_weight` = the Q154 weight, `ftv_reward_div3` =
FTV_WEIGHT/3) the certifier's own `main()` exercises.

P13 (`Experiments/PROPOSALS.md`), integration note: filter (4) must
"consume `krawczyk_cycle_certifier.py`... not rebuild it".  Everything below
is a thin wrapper: `bnb_period1`, `bnb_period2`, `CyclicSystem`,
`krawczyk_operator` and friends are imported unmodified from the certifier
and called exactly as `certificate_B`/`certificate_C`/`certificate_A` call
them, just against a caller-supplied table instead of the module-global one.

## What is, and is not, decided here

* **Period 1 (`period1_certificate`)**: EXHAUSTIVE.  All 26 non-all-continue
  support patterns among `{0, interior, 1}^3` are tested by `bnb_period1`,
  exactly reproducing `certificate_B`'s method for an arbitrary weight.
  `'refuted'` iff every pattern is certified infeasible; `'exists'` iff some
  fully-pinned (no interior coordinate) pattern is exactly feasible -- a
  deterministic point evaluation, not an interval claim, so no Krawczyk step
  is needed there; `'undecided'` otherwise.
* **Period 2 (`period2_certificate`)**: LIMITED, exactly `certificate_C`'s
  "at most one active coordinate per phase" 7x7 = 49-pattern family (of the
  729 total pairs) -- non-exhaustive, inherited as a nonclaim from the
  certifier itself.
* **Period >= 3 (`period_certificate` for `period >= 3`)**: this module does
  NOT attempt general root-finding.  The only period-3 existence route the
  certifier provides is `certificate_A`, hardcoded to the FTV/3 table at a
  hand-supplied center (the doc's own numbers, which solve the system
  exactly).  `ftv_period3_certificate` recognizes an input weight that is a
  positive UNIFORM (not gauge, all-coordinate) rescaling of `FTV_WEIGHT` --
  exactly `weights.FTV_WEIGHT`'s own numbers divided by 3, which is what
  `krawczyk_cycle_certifier.ftv_reward_div3` hardcodes -- and delegates to
  `certificate_A` unmodified; every other weight at period >= 3 is reported
  `'undecided (no candidate center)'`, honestly, rather than guessed at.
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction as Fr
from typing import Optional

_certsearch_dir = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _certsearch_dir)

from krawczyk_cycle_certifier import (  # noqa: E402  (path insert must precede this)
    bnb_period1,
    bnb_period2,
    certificate_A,
    single_active_shapes,
)

from filters import Certificate  # noqa: E402
from weights import FTV_WEIGHT, Weight, players, r as weight_r  # noqa: E402

DEFAULT_EPS = Fr(1, 2 ** 20)  # matches the certifier's own interior search domain


def table_from_weight(w: Weight):
    """Adapt a `weights.Weight` dict into the certifier's `table(S, i)`
    calling convention (`sigma_value`, `gain_value`, etc. all call
    `r(frozenset({...}), i)`)."""
    def table(S, i):
        return weight_r(w, S, i)
    return table


def _require_three_players(w: Weight) -> None:
    if players(w) != 3:
        raise ValueError(
            "certifier_bridge only supports n=3: krawczyk_cycle_certifier's "
            "building blocks (bilinear_coeffs, others(), CyclicSystem's "
            "3-coordinate Jacobian) are hand-specialized to three players"
        )


_ALL_PERIOD1_PATTERNS = [(a, b, c) for a in "01x" for b in "01x" for c in "01x"]


def period1_certificate(
    w: Weight,
    eps: Fr = DEFAULT_EPS,
    max_nodes: int = 50000,
    max_depth: int = 100,
    time_budget: float = 8.0,
) -> Certificate:
    """Generalizes `certificate_B` (E66) to an arbitrary weight: exhaustive
    branch-and-bound exclusion, all 26 non-all-continue support patterns.
    `ok=True` ("refuted": no exact period-one complementary absorbing row)
    iff every pattern is certified infeasible."""
    _require_three_players(w)
    table = table_from_weight(w)
    per_pattern = {}
    certified_infeasible = []
    feasible_witnesses = []
    undecided = []
    for pat in _ALL_PERIOD1_PATTERNS:
        label = "".join(pat)
        if pat == ("0", "0", "0"):
            per_pattern[label] = {
                "verdict": "excluded (all-continue, not absorbing by convention)"
            }
            continue
        verdict, nodes, undec = bnb_period1(
            table, pat, eps, max_nodes, max_depth, time_budget
        )
        per_pattern[label] = {"verdict": verdict, "nodes": nodes, "undecided_leaves": undec}
        if verdict == "infeasible (refuted)":
            assert undec == 0
            certified_infeasible.append(label)
        elif verdict == "feasible":
            feasible_witnesses.append(label)
        else:
            undecided.append(label)

    if feasible_witnesses:
        status = "exists"
    elif undecided:
        status = "undecided"
    else:
        status = "refuted"
    return Certificate(
        status == "refuted",
        {
            "period": 1,
            "status": status,
            "patterns_tested": len(_ALL_PERIOD1_PATTERNS) - 1,
            "certified_infeasible": sorted(certified_infeasible),
            "feasible_witnesses": sorted(feasible_witnesses),
            "undecided_patterns": sorted(undecided),
            "per_pattern": per_pattern,
        },
    )


def period2_certificate(
    w: Weight,
    eps: Fr = DEFAULT_EPS,
    max_nodes: int = 20000,
    max_depth: int = 60,
    time_budget: float = 6.0,
) -> Certificate:
    """Generalizes `certificate_C` to an arbitrary weight: the LIMITED "at
    most one active coordinate per phase" 49-pattern family (of 729 total
    period-2 support-pattern pairs) -- explicitly non-exhaustive, inherited
    unchanged from the certifier."""
    _require_three_players(w)
    table = table_from_weight(w)
    shapes = single_active_shapes()
    all_silent = ("0", "0", "0")
    per_pattern = {}
    certified_infeasible = []
    feasible_witnesses = []
    undecided = []
    for s0 in shapes:
        for s1 in shapes:
            label = "".join(s0) + "/" + "".join(s1)
            if s0 == all_silent and s1 == all_silent:
                per_pattern[label] = {
                    "verdict": "excluded (all-continue in both phases, not "
                               "absorbing by convention)"
                }
                continue
            verdict, nodes, undec = bnb_period2(
                table, s0, s1, eps, max_nodes, max_depth, time_budget
            )
            per_pattern[label] = {"verdict": verdict, "nodes": nodes, "undecided_leaves": undec}
            if verdict == "infeasible (refuted)":
                assert undec == 0
                certified_infeasible.append(label)
            elif verdict == "feasible":
                feasible_witnesses.append(label)
            else:
                undecided.append(label)

    if feasible_witnesses:
        status = "exists"
    elif undecided:
        status = "undecided"
    else:
        status = "refuted"
    total = len(shapes) * len(shapes)
    return Certificate(
        status == "refuted",
        {
            "period": 2,
            "status": status,
            "non_exhaustive": True,
            "family_size": total,
            "total_period2_patterns": 27 * 27,
            "patterns_tested": total - 1,
            "certified_infeasible": sorted(certified_infeasible),
            "feasible_witnesses": sorted(feasible_witnesses),
            "undecided_patterns": sorted(undecided),
            "per_pattern": per_pattern,
        },
    )


def _uniform_rescale_factor(w: Weight, target: Weight) -> Optional[Fr]:
    """If `w == k * target` entrywise for some positive rational `k` (same
    coalition set, same shape -- a uniform, all-coordinate rescale, NOT the
    per-coordinate `gauge_normalize` of `weights.py`), return `k`; else
    `None`."""
    if set(w.keys()) != set(target.keys()):
        return None
    k: Optional[Fr] = None
    for J, vec in target.items():
        wv = w[J]
        for a, b in zip(wv, vec):
            if b == 0:
                if a != 0:
                    return None
                continue
            ratio = a / b
            if k is None:
                k = ratio
            elif ratio != k:
                return None
    if k is None or k <= 0:
        return None
    return k


def ftv_period3_certificate(w: Weight) -> Certificate:
    """The only period->=3 existence route this bridge has: recognize `w` as
    a positive uniform rescale of `weights.FTV_WEIGHT` (e.g. `w ==
    FTV_WEIGHT` itself, `k=1`, or `w == FTV_WEIGHT/3`, `k=1/3`, the exact
    table `krawczyk_cycle_certifier.ftv_reward_div3` hardcodes) and delegate
    to `certificate_A` UNMODIFIED.  `certificate_A` always certifies the
    period-3 phase-rotation cycle for its own hardcoded `ftv_reward_div3`
    table regardless of the recognized scale `k` (uniform positive scaling
    preserves exact complementarity -- the affine-invariance fact recorded
    in `weights.py`'s module docstring), so the certified claim is reported
    against the caller's own `w`, not silently against a rescaled table."""
    _require_three_players(w)
    k = _uniform_rescale_factor(w, FTV_WEIGHT)
    if k is None:
        return Certificate(
            False,
            {
                "period": 3,
                "status": "undecided (no candidate center)",
                "reason": "w is not a recognized positive uniform rescale of "
                          "FTV_WEIGHT; this bridge has no general period->=3 "
                          "root-finder, only the certifier's own hardcoded "
                          "FTV/3 witness (certificate_A)",
            },
        )
    result = certificate_A()
    return Certificate(
        result["status"] == "CERTIFIED",
        {
            "period": 3,
            "status": "exists" if result["status"] == "CERTIFIED" else "undecided",
            "recognized_as": f"FTV_WEIGHT * {k}",
            "certificate_A": result,
        },
    )


def certify_weight(w: Weight, M: int) -> "dict[int, Certificate]":
    """Filter (4)'s top-level entry point: per-period certificates for
    periods `1..M`.  Period 1 and (limited) period 2 are always decided by
    exhaustive/near-exhaustive branch-and-bound; period 3 is decided only
    for FTV-shaped weights (the certifier's only known existence witness);
    periods > 3, and non-FTV-shaped period 3, are reported undecided rather
    than guessed."""
    out: "dict[int, Certificate]" = {}
    if M >= 1:
        out[1] = period1_certificate(w)
    if M >= 2:
        out[2] = period2_certificate(w)
    if M >= 3:
        out[3] = ftv_period3_certificate(w)
        for L in range(4, M + 1):
            out[L] = Certificate(
                False,
                {
                    "period": L,
                    "status": "undecided (not attempted)",
                    "reason": "no root-finding beyond the FTV/3 witness at "
                              "period 3 is implemented in this bridge",
                },
            )
    return out
