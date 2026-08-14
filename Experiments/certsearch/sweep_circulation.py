"""The circulation-certificate sweep (P13-adjacent; new certsearch mode).

Runs `circulation.certify_circulation` over two families:

* the five named reference weights (`weights.NAMED_WEIGHTS`);
* the repaired four-player family `F'(x, eps)` from `questions/Question160-
  TheFourPlayerCyclicFamilyPhaseDiagram.md`'s followup section (transcribed
  below -- see `four_player_family`'s docstring for the exact table and the
  source quotation), on the small rational grid `x in {1/4, 1/2, 1, 2}`,
  `eps in {0, 1/10, 1/2}`.

Per `README.md`'s validation-gate principle: **this sweep is not evidence of
anything until `validate.py` passes.**  `main()` re-runs `validate.py` fresh
(as a subprocess, exit code checked) and refuses to sweep if it fails,
printing the gate verdict first, always, before any sweep number.

Each point is reported with one of three statuses (`circulation
.certify_circulation`'s own three-way split, driven by the floor-honesty
direction documented in `circulation.py`'s module docstring):

* `certified` -- a genuine circulation certificate, found against the sound
  upper bound `chi_upper` (the solo-clipped ceiling `max(0, d_i)`);
* `unsound_only` -- a witness exists against the UNSOUND lower bound
  `chi_lower` (`circulation.chi_trivial_lower_vec`) but not against
  `chi_upper` -- an artifact, not a proof (the true `chi` could sit anywhere
  in `[lo, hi]`);
* `empty_at_searched_depth` -- neither search found anything at `max_L = 3`
  on the `{1/2, 1/3, 2/3}` alpha grid -- never a claim that no certificate
  exists at any length.
"""

from __future__ import annotations

import json
import os
import sys
from fractions import Fraction as Fr
from typing import Dict, List

from circulation import certify_circulation, default_chi_bounds
from weights import NAMED_WEIGHTS, Weight, check_weight

_THIS_DIR = os.path.dirname(os.path.abspath(__file__))


# --------------------------------------------------------------------------
# The repaired four-player family F'(x, eps).
# --------------------------------------------------------------------------

def four_player_family(x: Fr, eps: Fr) -> Weight:
    """`F'(x, eps)`, `questions/Question160-TheFourPlayerCyclicFamilyPhase
    Diagram.md`, "## The repaired family" (the followup section, after the
    original all-zero-triples family was retired for being degenerate):

        I = Z/4, sigma(i) = i + 1.

        solo r({i}): i -> 1, i+1 -> 3, i+2 -> x, i+3 -> 0
            (payoffs read around the cycle FROM the quitter i; so every
            player's OWN solo value, when they are the sole quitter, is the
            offset-0 entry, 1 -- constant in x and eps).
        adjacent pairs r({i, i+1}): i -> 1+eps, i+1 -> 0, both outsiders -> 1
        distance-two pairs r({i, i+2}): members -> 0, both outsiders -> 1
        triples r({i, i+1, i+2}): members -> 0, outsider i+3 -> 1
        full set: the zero vector

    (the distance-two/triple/full-set rows are what changed relative to the
    original, retired family, which zeroed every triple and the full set --
    that degeneracy let a lone continuer earn the same 0 as joining, which
    the repaired outsider-pays-1 pattern above closes).
    """
    n = 4
    solo_table = [Fr(1), Fr(3), x, Fr(0)]
    w: Dict[frozenset, tuple] = {}

    for i in range(n):
        vec = [solo_table[(j - i) % n] for j in range(n)]
        w[frozenset({i})] = tuple(vec)

    for i in range(n):
        succ = (i + 1) % n
        vec = [Fr(0)] * n
        for j in range(n):
            if j == i:
                vec[j] = Fr(1) + eps
            elif j == succ:
                vec[j] = Fr(0)
            else:
                vec[j] = Fr(1)
        w[frozenset({i, succ})] = tuple(vec)

    for pair in (frozenset({0, 2}), frozenset({1, 3})):
        vec = [Fr(0) if j in pair else Fr(1) for j in range(n)]
        w[pair] = tuple(vec)

    for i in range(n):
        triple = frozenset({i, (i + 1) % n, (i + 2) % n})
        vec = [Fr(0) if j in triple else Fr(1) for j in range(n)]
        w[triple] = tuple(vec)

    w[frozenset(range(n))] = tuple(Fr(0) for _ in range(n))

    check_weight(w)
    return w


X_GRID: List[Fr] = [Fr(1, 4), Fr(1, 2), Fr(1, 1), Fr(2, 1)]
EPS_GRID: List[Fr] = [Fr(0), Fr(1, 10), Fr(1, 2)]


def run_sweep(max_L: int = 3) -> Dict[str, object]:
    results: Dict[str, object] = {}

    named: Dict[str, object] = {}
    for name, w in NAMED_WEIGHTS.items():
        lo, hi = default_chi_bounds(w)
        cert = certify_circulation(w, (lo, hi), max_L=max_L)
        named[name] = {
            "chi_lo": [str(v) for v in lo],
            "chi_hi": [str(v) for v in hi],
            "status": cert["status"],
            "detail": cert,
        }
    results["named_weights"] = named

    family: List[Dict[str, object]] = []
    for x in X_GRID:
        for eps in EPS_GRID:
            w = four_player_family(x, eps)
            lo, hi = default_chi_bounds(w)
            cert = certify_circulation(w, (lo, hi), max_L=max_L)
            family.append({
                "x": str(x),
                "eps": str(eps),
                "chi_lo": [str(v) for v in lo],
                "chi_hi": [str(v) for v in hi],
                "status": cert["status"],
                "detail": cert,
            })
    results["four_player_family"] = family

    return results


def main() -> None:
    # Validation-gate discipline (README.md, non-negotiable): re-run
    # validate.py fresh, as a subprocess, and refuse to sweep if it fails.
    # Print the gate verdict FIRST, always, before any sweep number.
    import subprocess

    print("Re-running validate.py before any sweep number is produced...", flush=True)
    result = subprocess.run([sys.executable, "validate.py"], cwd=_THIS_DIR)
    gate_ok = result.returncode == 0
    print(f"validate.py gate: {'PASSED' if gate_ok else 'FAILED'} "
          f"(exit code {result.returncode})", flush=True)
    if not gate_ok:
        print("Refusing to run the sweep: the validation gate did not pass.")
        sys.exit(1)

    max_L = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    out = run_sweep(max_L=max_L)
    print(json.dumps(out, indent=2, default=str))


if __name__ == "__main__":
    main()
