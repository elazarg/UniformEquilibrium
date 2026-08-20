"""P13 slice two, item 4: the first real sweep over gauge-normalized rational
three-player quitting weights, through the full escalation of filters (1)
through (4) plus the backward-distance table.

Per `Experiments/certsearch/README.md`'s validation-gate principle: **this
sweep is not evidence of anything until `validate.py` passes.**
`main()` refuses to run unless `validate.py` itself is re-run fresh (as a
subprocess, exit code checked -- not merely "trusted from an earlier
session") and reports success first, printing that fact explicitly before
any sweep number is produced.

## Search space

Gauge-normalized (`weights.gauge_normalize`'s own convention): every
diagonal (solo) entry `r_i({i})` is drawn from `{-1, 0, 1}` -- so every
sampled weight is ALREADY in gauge-normal form by construction, no
post-hoc normalization needed. The 18 remaining ("off-diagonal") entries of
the `n * (2**n - 1) = 21`-entry table (3 singleton off-diagonal entries per
player-pair... concretely 6 singleton off-diagonal + 9 doubleton + 3 triple
= 18) are drawn independently from the signed small-denominator set
`{a/d : 1 <= d <= denom_bound, -d <= a <= d}`.

The FULL space at `denom_bound = 2` (`{-1,-1/2,0,1/2,1}`, 5 values) has size
`3**3 * 5**18` -- computed exactly below and printed alongside the actual
sample count, so "how much of the space a first pass covered" is an honest,
exact fraction, not a hand-wave. Exhaustive enumeration is not attempted:
this is a first RANDOM sweep (seeded, reproducible), stopped by a wall-clock
budget, not a claim of completeness.

## The escalation, and what "survivor" means

For each sampled weight `w`:

1. `is_zero_solo(w)` -- if TRUE, `w` has a uniform equilibrium payoff via
   `exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle`
   (landed). RESOLVED, not a survivor.
2. For every owner `i`: `solo_quitter_admissible(w, i)` (filter 2 + 2b). If
   ADMISSIBLE for some owner, `w` has a uniform equilibrium payoff via the
   same landed disjunction (an admissible cyclic continuation block).
   RESOLVED, not a survivor.
3. `singleton_lcp_feasible` is computed and RECORDED (P13 filter 3) but does
   NOT resolve or eliminate a weight here: this slice has no derivation
   from an LCP witness `lambda` back to an actual candidate row (that
   conversion is Question 154 section-1 machinery not implemented in
   `filters.py`), so treating LCP feasibility as resolving would be
   unearned -- it is reported as a datum only, avoiding the overreach
   `CLAUDE.md`'s "Foundations pass" history warns against.
4. `certifier_bridge.period1_certificate(w)` (filter 4, period 1,
   EXHAUSTIVE over all 26 patterns). If `status == 'exists'`, the
   witnessing pattern is always a fully-pinned `{0,1}^3` row (the only kind
   `bnb_period1` can certify existence for -- see `certifier_bridge.py`'s
   docstring), so it is fed DIRECTLY into `admissibility.cycle_admissible`
   (which is not solo-row-specific -- see its docstring) to decide
   admissibility of THIS non-solo exact cycle too. Admissible: RESOLVED
   (uniform equilibrium via the same theorem, one step further than P13
   asked but a direct consequence of `cycle_admissible` already being
   general -- flagged as a strengthening actually taken). Inadmissible: an
   LP-feasible-but-inadmissible-style witness at a non-solo row; kept as a
   survivor with that fact recorded, escalated further like any other
   survivor.
5. If period 1 is REFUTED or UNDECIDED (and not resolved by step 4), escalate:
   `period2_certificate` (LIMITED family, non-exhaustive) and, only for
   weights recognized as an FTV-shaped positive rescale (essentially never,
   for random samples -- recorded honestly), `ftv_period3_certificate`.
6. Anything not RESOLVED by 1/2/4 is a SURVIVOR: a candidate hole occupant
   or trap seed. `backward_distance.backward_distance_table` is computed for
   every survivor (small `denom_bound`, per-`L` table per that module's
   documented conservative reuse of the period-one bound).

## Runtime cap

`main()` accepts a wall-clock budget (default 120s) and a random seed
(default fixed, for reproducibility); it stops sampling as soon as the
budget is exceeded and reports exactly how many weights were tested.
"""

from __future__ import annotations

import json
import os
import random
import sys
import time
from fractions import Fraction as Fr
from typing import Dict, List, Optional, Tuple

from admissibility import cycle_admissible, solo_quitter_admissible
from backward_distance import backward_distance_table
from certifier_bridge import ftv_period3_certificate, period1_certificate, period2_certificate
from filters import is_zero_solo, singleton_lcp_feasible
from weights import Weight, all_nonempty_coalitions, invariant_matrix, players

_THIS_DIR = os.path.dirname(os.path.abspath(__file__))


def _signed_small_rationals(denom_bound: int) -> List[Fr]:
    vals = set()
    for d in range(1, denom_bound + 1):
        for a in range(-d, d + 1):
            vals.add(Fr(a, d))
    return sorted(vals)


DIAGONAL_CHOICES = (Fr(-1), Fr(0), Fr(1))


def search_space_size(n: int, denom_bound: int) -> int:
    """The exact size of the search space this sweep samples from: `3**n`
    diagonal choices times `|free_choices| ** (n*(2**n-1) - n)` for the
    remaining off-diagonal entries."""
    free = len(_signed_small_rationals(denom_bound))
    total_entries = n * (2 ** n - 1)
    free_entries = total_entries - n
    return (3 ** n) * (free ** free_entries)


def random_gauge_weight(rng: random.Random, n: int, denom_bound: int) -> Weight:
    """A random weight already in gauge-normal form: every diagonal entry
    `r_i({i})` is drawn from `{-1, 0, 1}` (`weights.gauge_normalize`'s own
    target set), every off-diagonal entry from the signed small-denominator
    set at `denom_bound`."""
    diag = {i: rng.choice(DIAGONAL_CHOICES) for i in range(n)}
    free_choices = _signed_small_rationals(denom_bound)
    w: Weight = {}
    for J in all_nonempty_coalitions(n):
        vec = []
        for i in range(n):
            if J == frozenset({i}):
                vec.append(diag[i])
            else:
                vec.append(rng.choice(free_choices))
        w[J] = tuple(vec)
    return w


def _row_from_period1_pattern(pattern_label: str) -> Optional[Tuple[Fr, ...]]:
    """A period1_certificate witness label like '110' is always a fully
    pinned `{0,1}^3` pattern (no 'x') when `status == 'exists'` -- see
    `certifier_bridge.py`'s docstring. `None` if it contains an 'x' (should
    never happen for an 'exists' witness; guarded rather than assumed)."""
    if "x" in pattern_label:
        return None
    return tuple(Fr(int(c)) for c in pattern_label)


def evaluate_weight(
    w: Weight,
    period1_budget: float,
    period2_budget: float,
    max_nodes: int = 5000,
    max_depth: int = 40,
    backward_distance_denom_bound: int = 6,
) -> Dict[str, object]:
    """Run one weight through the full escalation. Returns a dict with
    `resolved` (bool), `reason`, `backward_distance`, and every intermediate
    certificate, regardless of outcome (so a survivor's record is
    self-contained).

    `max_nodes`/`max_depth`/the two time budgets are deliberately smaller
    than `certifier_bridge`'s own defaults (which mirror the certifier's
    original `certificate_B`/`certificate_C` budgets, tuned for a handful of
    named weights, not thousands of random ones): a first sweep trades a
    higher `undecided` rate at the branch-and-bound patterns for keeping
    per-weight cost bounded, honestly reported per pattern rather than
    hidden.

    **Why `backward_distance` is computed and admissibility-checked for
    EVERY not-yet-resolved weight, not just reported after the fact.** A
    real gap was found running this sweep: a period-one row with exactly
    ONE coordinate pinned pure (`x_k = 1`) decouples algebraically -- with
    `c_{-k}(x) = 0` forced, EVERY other player's `Gamma` loses its `V`
    dependence entirely, and `Sigma_i`/`Gamma_i` for each of the other two
    players become univariate LINEAR functions of that player's own rate
    alone (the two other equations decouple from each other, not just from
    `V`). A linear equation over the rationals generically has an exact
    small-denominator root, so this shape produces an EXACT period-one row
    astonishingly often for random small-denominator tables -- and neither
    earlier check catches it: `solo_quitter_lp`/`admissibility.py` only
    search SOLO rows (exactly one nonzero coordinate), and
    `certifier_bridge.period1_certificate`'s branch-and-bound can only ever
    CERTIFY EXISTENCE at a fully-pinned `{0,1}^3` corner, never at a pattern
    with two free ('x') coordinates -- so this row shape is invisible to
    both. `backward_distance`'s independent small-denominator grid search
    DOES find it (defect exactly `0`), and when the found row is also
    ADMISSIBLE (`admissibility.cycle_admissible`), the weight actually has a
    uniform equilibrium payoff via the landed theorem chain and must NOT be
    reported as a survivor. This is checked here, not left to a human
    reading the output."""
    n = players(w)
    record: Dict[str, object] = {}

    zs = is_zero_solo(w)
    record["zero_solo"] = zs.ok
    if zs.ok:
        record["resolved"] = True
        record["reason"] = "zero_solo"
        return record

    admissible_owner = None
    lp_by_owner = {}
    for i in range(n):
        cert = solo_quitter_admissible(w, i)
        lp_by_owner[i] = {
            "lp_feasible": not cert.detail.get("not_applicable", False),
            "admissible": cert.ok,
        }
        if cert.ok:
            admissible_owner = i
    record["solo_admissibility_by_owner"] = lp_by_owner
    if admissible_owner is not None:
        record["resolved"] = True
        record["reason"] = f"admissible_solo_cycle(owner={admissible_owner})"
        return record

    B = invariant_matrix(w)
    lcp = singleton_lcp_feasible(B)
    record["singleton_lcp_feasible"] = lcp.ok  # recorded only, per docstring

    p1 = period1_certificate(
        w, max_nodes=max_nodes, max_depth=max_depth, time_budget=period1_budget
    )
    record["period1"] = {
        "status": p1.detail["status"],
        "certified_infeasible": len(p1.detail["certified_infeasible"]),
        "undecided": len(p1.detail["undecided_patterns"]),
        "feasible_witnesses": p1.detail["feasible_witnesses"],
    }
    if p1.detail["status"] == "exists":
        witness = p1.detail["feasible_witnesses"][0]
        x = _row_from_period1_pattern(witness)
        if x is not None:
            adm = cycle_admissible(w, x)
            record["period1_exists_admissibility"] = {"row": witness, "ok": adm.ok}
            if adm.ok:
                record["resolved"] = True
                record["reason"] = f"admissible_nonsolo_period1_cycle(row={witness})"
                return record
        # inadmissible (or unresolved) non-solo exact cycle: fall through,
        # this weight stays a survivor with the fact recorded above.

    if p1.detail["status"] != "exists":
        p2 = period2_certificate(
            w, max_nodes=max_nodes, max_depth=max_depth, time_budget=period2_budget
        )
        record["period2_limited"] = {
            "status": p2.detail["status"],
            "certified_infeasible": len(p2.detail["certified_infeasible"]),
            "undecided": len(p2.detail["undecided_patterns"]),
        }
        p3 = ftv_period3_certificate(w)
        record["period3_ftv_shaped"] = {"status": p3.detail["status"]}

    bd = backward_distance_table(w, denom_bound=backward_distance_denom_bound, max_L=3)
    record["backward_distance"] = bd
    best_row = bd.get("best_row")
    if best_row is not None and Fr(best_row["defect"]) == 0:
        x = tuple(Fr(v) for v in best_row["x"])
        adm = cycle_admissible(w, x)
        record["backward_distance_row_admissibility"] = {"row": best_row["x"], "ok": adm.ok}
        if adm.ok:
            record["resolved"] = True
            record["reason"] = (
                f"admissible_exact_row_found_by_backward_distance_search"
                f"(row={best_row['x']})"
            )
            return record

    record["resolved"] = False
    record["reason"] = "survivor"
    return record


def run_sweep(
    n_players: int = 3,
    denom_bound: int = 2,
    seed: int = 0,
    time_budget_seconds: float = 120.0,
    period1_time_budget: float = 0.3,
    period2_time_budget: float = 0.25,
    max_nodes: int = 5000,
    max_depth: int = 40,
    backward_distance_denom_bound: int = 8,
) -> Dict[str, object]:
    """`backward_distance_denom_bound = 8`, not the module's own default `6`:
    at `denom_bound = 2` (this sweep's weight-entry grid, `{-1,-1/2,0,1/2,1}`)
    the one-pure-coordinate decoupling documented in `evaluate_weight` can
    force an exact root as coarse as `p/(p-q)` with `|p|,|q| <= 4` in lowest
    terms -- denominator up to `8` -- so a smaller search bound would MISS
    some of those roots and wrongly leave a resolved weight in the survivor
    list. Found and fixed while developing this sweep, not assumed."""
    rng = random.Random(seed)
    space_size = search_space_size(n_players, denom_bound)
    t0 = time.time()
    tested = 0
    resolved_counts: Dict[str, int] = {}
    survivors: List[Dict[str, object]] = []
    seen: set = set()

    while time.time() - t0 < time_budget_seconds:
        w = random_gauge_weight(rng, n_players, denom_bound)
        key = tuple(sorted((tuple(sorted(J)), vec) for J, vec in w.items()))
        if key in seen:
            continue
        seen.add(key)
        tested += 1
        record = evaluate_weight(
            w, period1_time_budget, period2_time_budget,
            max_nodes=max_nodes, max_depth=max_depth,
            backward_distance_denom_bound=backward_distance_denom_bound,
        )
        # `reason` is bucketed by its resolving row's identity where present
        # (e.g. "admissible_solo_cycle(owner=0)") -- collapse to the family
        # name for the summary breakdown, keep full detail per-survivor only.
        reason = record["reason"]
        family = reason.split("(")[0]
        resolved_counts[family] = resolved_counts.get(family, 0) + 1
        if not record["resolved"]:
            survivor_entry = {
                "weight": {
                    "".join(map(str, sorted(J))): [str(v) for v in vec]
                    for J, vec in w.items()
                },
                "record": record,
            }
            survivors.append(survivor_entry)

    elapsed = time.time() - t0
    return {
        "n_players": n_players,
        "denom_bound": denom_bound,
        "seed": seed,
        "time_budget_seconds": time_budget_seconds,
        "elapsed_seconds": elapsed,
        "search_space_size": str(space_size),
        "weights_tested": tested,
        "coverage_fraction": f"{tested / space_size:.3e}" if space_size else "n/a",
        "resolution_breakdown": resolved_counts,
        "survivor_count": len(survivors),
        "survivors": survivors,
    }


def main() -> None:
    # Validation-gate discipline (non-negotiable, per PROPOSALS.md P13 and
    # certsearch/README.md): re-run validate.py fresh, as a subprocess, and
    # refuse to sweep if it fails (nonzero exit code). A subprocess (rather
    # than importing validate as a module, which would also work, since its
    # top-level asserts run as an import side effect) keeps this file's own
    # process untouched by validate.py's global state either way.
    import subprocess

    print("Re-running validate.py before any sweep number is produced...")
    result = subprocess.run([sys.executable, "validate.py"], cwd=_THIS_DIR)
    gate_ok = result.returncode == 0
    print(f"validate.py gate: {'PASSED' if gate_ok else 'FAILED'} (exit code {result.returncode})")
    if not gate_ok:
        print("Refusing to run the sweep: the validation gate did not pass.")
        sys.exit(1)

    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 120.0
    out = run_sweep(time_budget_seconds=budget)
    print(json.dumps(out, indent=2, default=str))


if __name__ == "__main__":
    main()
