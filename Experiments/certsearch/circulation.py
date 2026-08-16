"""Circulation-certificate search (P13-adjacent; new certsearch mode), for
singleton-face circulation certificates.

A **face-circulation certificate** for a weight `r` and a floor vector
`floor` is a closed cycle of feasible vectors `z^0, ..., z^{L-1}` (`z^L =
z^0`) together with, at each phase `l`, a mixing distribution `lambda^l in
Delta(I)` and a contraction ratio `alpha_l in (0,1)`, such that

    z^{l+1} = alpha_l * z^l + (1 - alpha_l) * u^l,   u^l = sum_k lambda^l_k * w({k})

every `z^l` is above the floor, and every coordinate `i` in the support of
`lambda^l` is pinned: `z^l_i = u^l_i = d_i` (its own solo value).  This is
`UniformEquilibrium/Quitting/Circulation/SingletonFaceCirculation.lean`'s
`FaceCirculationCertificate` structure, machine-checked over an arbitrary
finite index type; **the floor is required on the `z^l` VERTICES only, never
on the raw phase target `u^l`** (`FaceCirculationCertificate.vertex_ge_floor`
quantifies over `vertex`, not over `mixTarget`) -- the trajectory only ever
travels from `z^l` (segment parameter `mu = 1`) down to `z^{l+1}` (`mu =
alpha_l`), never all the way to `u^l` itself (`mu = 0`), so `u^l` can and
generally does dip below the floor at a coordinate outside its phase's
support (see the calibration check below, where `u^0` touches `0` against a
floor of `1/3`).  Getting this backwards -- requiring `u^l >= floor` for
every phase of a length->=2 cycle -- would reject the machine-checked
calibration certificate itself; `search_circulation`'s multi-owner fallback
therefore does NOT filter phase targets by the floor (see
`_solve_phase_target`'s docstring), only the resulting vertices are checked.

At `L = 1` this collapses to `z^0 = u^0` (forced: `z^1 = z^0` and `alpha_0 in
(0,1)` force `z^0 = u^0` regardless of `alpha_0`), so for `L = 1` the floor
DOES apply to `u^0` -- it is the same object as the (only) vertex.  This is
exactly `circulation_L1`'s per-support linear system, per the idea document's
"Why it matters" section: `lambda` supported on `J`, `sum lambda = 1`,
`lambda >= 0`, `(V lambda)_i = d_i` for `i in J`, `V lambda >= floor`, where
`V`'s columns are the solo payoff vectors `v^i = w({i})`.

## Floor honesty: which side of `chi` is sound

The certificate needs `z >= max(d, chi)` with the TRUE min-max `chi_i`.  Two
directions were floated while scoping this module; only one is sound, and
the direction is worth deriving explicitly rather than assumed, because
`slice one`'s own history (see `README.md`'s two recorded discrepancies) is
that a checker's sign/direction is the likely bug, not its arithmetic.

Write `floor_true = max(d, chi)`, and suppose we only know bounds `lo <= chi
<= hi`.

* Substituting the UPPER bound `hi >= chi` gives `floor_used =
  max(d, hi) >= max(d, chi) = floor_true` (since `hi >= chi`, taking the max
  with `d` preserves the inequality).  Requiring `z >= floor_used` is then a
  STRICTLY STRONGER condition than the true requirement `z >= floor_true`:
  any witness found this way automatically satisfies the true floor too.
  This is SOUND -- every reported certificate really is one -- but
  CONSERVATIVE: a genuine certificate whose vertices sit between
  `floor_true` and `floor_used` will be missed.
* Substituting the LOWER bound `lo <= chi` gives `floor_used = max(d, lo) <=
  max(d, chi) = floor_true`.  Requiring `z >= floor_used` is then WEAKER than
  the true requirement: a witness can satisfy `floor_used <= z < floor_true`
  and pass the check while actually violating the real individual-
  rationality floor.  This is UNSOUND -- it can manufacture a certificate
  that is not actually one.

So: **the sound, reportable ("certified") direction uses `hi`, the upper
bound on `chi`; `lo` is informational only** (a search that succeeds against
`lo` but not `hi` is reported `unsound_only` -- a lead, never a proof).  This
matches the unconditional inequality actually proved in the repository:
`UniformEquilibrium/Quitting/Punishment/Floor.lean`'s
`punishmentLevel_quittingGame_le_max` / `QuittingIsolatedPunishmentCeiling
.lean`'s `punishmentLevel_quittingGame_le_quittingPositiveSingletonDebtCap`
prove, with NO hypothesis beyond boundedness, `punishmentLevel <= max(0,
solo)` at every horizon -- an unconditional CEILING (upper bound), never a
floor, on the punishment level that `chi` limits to.  So `chi_upper(w, i) =
max(0, d_i)` (the "solo-clipped ceiling" the idea document's Open section
names) is exactly the sound `hi`.  The same files prove the matching LOWER
bound is NOT available in general (`punishmentLevel_lt
_quittingPositiveSingletonDebtCap`'s two-player counterexample witnesses a
table where the ceiling is not attained from below) -- consistent with `lo`
here being only ever a coarse, always-true bound (`chi_trivial_lower_vec`,
below), never sharp, and never safe to certify against.

## The trivial lower bound

`chi_lower(w, i) = min(0, min_J r_i(J))` over every nonempty coalition `J`
(not just those containing `i`).  This is valid (always `<= chi_i`) by the
same averaging argument `QuittingPunishmentFloor.lean` uses for its own
(sharper, coalition-restricted) floors: every finite-horizon average payoff
to `i` is a weighted mix of `0` (the active-play stage payoff) and table
entries `r_i(J)`, so it can never fall below `min(0, min_J r_i(J))` -- a
strictly cruder bound than the file's own `mIn`/`mOut` (which restrict to
`J` containing/avoiding `i` respectively), used here only because it is
`O(2^n)` to compute and needs no case split, and is never used for
certification (see above), only to detect the `unsound_only` case.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from itertools import combinations, product
from typing import Dict, List, Optional, Sequence, Tuple

from filters import Certificate, _rref_solve
from weights import FTV_WEIGHT, Weight, all_nonempty_coalitions, players, r, solo

# --------------------------------------------------------------------------
# The scaled cyclic weight: FTV_WEIGHT / 3 (Flesch-Thuijsman-Vrieze, scaled).
# `UniformEquilibrium/Quitting/Cycles/WeightedRowMotionSeparation.lean`'s
# `scaledCyclicWeight`; used by `SingletonFaceCirculation.lean`'s
# `cyclicCirculation`, the machine-checked calibration certificate this
# module's `validate.py` positive control reproduces.
# --------------------------------------------------------------------------

SCALED_CYCLIC_WEIGHT: Weight = {
    J: tuple(v / 3 for v in vec) for J, vec in FTV_WEIGHT.items()
}


# --------------------------------------------------------------------------
# The solo-payoff matrix V, and the two chi bounds.
# --------------------------------------------------------------------------

def solo_payoff_matrix(w: Weight) -> List[List[Fr]]:
    """`V[k][i] = r_k({i})`: column `i` is the solo payoff vector `w({i})`.
    `V[i][i] = d_i` on the diagonal, by construction."""
    n = players(w)
    return [[r(w, {i}, k) for i in range(n)] for k in range(n)]


def chi_solo_clipped_ceiling_vec(w: Weight) -> List[Fr]:
    """The sound upper bound `hi`: `chi_upper_i = max(0, d_i)`, the
    "solo-clipped ceiling" -- unconditional, per `QuittingPunishmentFloor
    .lean`'s `punishmentLevel_quittingGame_le_max` (module docstring above
    has the full derivation of why this is the direction to certify
    against)."""
    n = players(w)
    return [max(Fr(0), solo(w, i)) for i in range(n)]


def chi_trivial_lower_vec(w: Weight) -> List[Fr]:
    """The informational-only lower bound `lo`: `chi_lower_i = min(0, min_J
    r_i(J))` over every nonempty coalition `J`.  NEVER sound to certify
    against (module docstring); used only to flag the `unsound_only` search
    outcome."""
    n = players(w)
    out = []
    for i in range(n):
        vals = [r(w, J, i) for J in all_nonempty_coalitions(n)]
        out.append(min(Fr(0), min(vals)))
    return out


def default_chi_bounds(w: Weight) -> Tuple[List[Fr], List[Fr]]:
    """`(lo, hi)`, the pair `certify_circulation` expects."""
    return chi_trivial_lower_vec(w), chi_solo_clipped_ceiling_vec(w)


def floor_vector(d: Sequence[Fr], chi_vec: Sequence[Fr]) -> List[Fr]:
    """`floor_i = max(d_i, chi_i)`."""
    return [max(d[i], chi_vec[i]) for i in range(len(d))]


# --------------------------------------------------------------------------
# The per-phase solve: lambda on a support J pinning V@lambda to d on J.
# --------------------------------------------------------------------------

def _solve_phase_target(
    V: Sequence[Sequence[Fr]],
    d: Sequence[Fr],
    floor: Optional[Sequence[Fr]],
    S: Sequence[int],
    n: int,
) -> Optional[Tuple[List[Fr], List[Fr]]]:
    """The per-phase solve shared by `circulation_L1` (`floor` supplied, per
    the L=1 spec: `(V lambda)_i = d_i` on `S`, `V lambda >= floor`
    EVERYWHERE) and `search_circulation`'s multi-owner fallback (`floor =
    None`: only the on-support pin and the simplex constraints -- see the
    module docstring for why the floor must NOT be baked in there: a
    multi-owner phase's raw target `u^l = V @ lambda^l` at `L >= 2` is never
    itself a cycle vertex, only the CONTRACTED next vertex `z^{l+1}` is, and
    that is checked against the floor separately by `verify_witness`).

    Same exact machinery as `filters._solve_support` (particular solution +
    nullspace basis via exact Gauss-Jordan, remaining degrees of freedom
    pinned by vertex enumeration over combinations of `dim`-many tight
    `lambda_k = 0` facets -- every nonempty bounded polyhedron has such a
    vertex): `S` plays the role of the support, `V` the role of `B`, `d` the
    role of the all-zero right-hand side there.  Returns `(lambda, u = V @
    lambda)` or `None`.
    """
    S = list(S)
    k = len(S)
    M_SS = [[V[i][j] for j in S] for i in S]
    rows = M_SS + [[Fr(1)] * k]
    rhs = [d[i] for i in S] + [Fr(1)]
    solved = _rref_solve(rows, rhs, k)
    if solved is None:
        return None
    particular, basis = solved
    dfree = len(basis)

    def build(t: Sequence[Fr]) -> List[Fr]:
        lam = list(particular)
        for tk, vk in zip(t, basis):
            for c in range(k):
                lam[c] += tk * vk[c]
        return lam

    def full_and_check(lam_S: List[Fr]) -> Optional[Tuple[List[Fr], List[Fr]]]:
        if any(x < 0 for x in lam_S):
            return None
        lam_full = [Fr(0)] * n
        for idx, s_idx in enumerate(S):
            lam_full[s_idx] = lam_S[idx]
        u = [sum(V[i][j] * lam_full[j] for j in S) for i in range(n)]
        if floor is not None and any(u[i] < floor[i] for i in range(n)):
            return None
        return lam_full, u

    if dfree == 0:
        return full_and_check(particular)

    cand = full_and_check(build([Fr(0)] * dfree))
    if cand is not None:
        return cand

    for combo in combinations(range(k), dfree):
        M = [[basis[kk][c] for kk in range(dfree)] for c in combo]
        rhsv = [-particular[c] for c in combo]
        square = _rref_solve(M, rhsv, dfree)
        if square is None:
            continue
        t_particular, t_basis = square
        if t_basis:
            continue  # degenerate combo: not an isolated vertex, skip
        cand = full_and_check(build(t_particular))
        if cand is not None:
            return cand
    return None


# --------------------------------------------------------------------------
# The L = 1 check.
# --------------------------------------------------------------------------

def circulation_L1(w: Weight, chi_vec: Sequence[Fr]) -> Certificate:
    """The `L = 1` circulation check: for each nonempty support `J subseteq
    I` in increasing size, decide whether `lambda in Delta(J)` exists with
    `(V lambda)_i = d_i` for `i in J` and `V lambda >= floor` everywhere
    (`floor_i = max(d_i, chi_vec[i])`).  At `L = 1` the vertex `z^0` and the
    target `u^0` coincide (`z^0 = u^0` is forced by the contraction identity
    regardless of `alpha_0`), so the floor legitimately applies to `V
    lambda` in full, per the module docstring.  Returns the first feasible
    `(J, lambda)`, or an exhaustion certificate.
    """
    n = players(w)
    V = solo_payoff_matrix(w)
    d = [solo(w, i) for i in range(n)]
    floor = floor_vector(d, chi_vec)
    tried: List[Tuple[int, ...]] = []
    for size in range(1, n + 1):
        for J in combinations(range(n), size):
            tried.append(J)
            res = _solve_phase_target(V, d, floor, J, n)
            if res is not None:
                lam, u = res
                return Certificate(
                    True,
                    {
                        "L": 1,
                        "J": list(J),
                        "lambda": [str(x) for x in lam],
                        "u": [str(x) for x in u],
                        "z": [[str(x) for x in u]],
                        "floor": [str(x) for x in floor],
                    },
                )
    return Certificate(
        False,
        {
            "reason": "every nonempty support exhausted at L=1",
            "supports_tried": len(tried),
            "floor": [str(x) for x in floor],
        },
    )


# --------------------------------------------------------------------------
# The cyclic closure of a fixed phase-target / alpha sequence.
# --------------------------------------------------------------------------

DEFAULT_ALPHA_GRID: Tuple[Fr, ...] = (Fr(1, 2), Fr(1, 3), Fr(2, 3))


def _cyclic_close(u_list: Sequence[Sequence[Fr]], alphas: Sequence[Fr], n: int) -> List[List[Fr]]:
    """The unique closed cycle `z^0, ..., z^{L-1}` solving, coordinatewise
    (the contraction ratio `alpha_l` is a SCALAR applied identically to
    every coordinate, so the L-phase recurrence decouples per coordinate),

        z^{l+1 mod L} = alpha_l * z^l + (1 - alpha_l) * u^l.

    Unrolling once around the cycle and solving for `z^0` gives, per
    coordinate `i`,

        z^0_i * (1 - prod_l alpha_l)
          = sum_k (1 - alpha_k) * u^k_i * prod_{j > k} alpha_j,

    which has a unique solution because every `alpha_l in (0, 1)` makes
    `prod_l alpha_l < 1` strictly.  `z^1, ..., z^{L-1}` follow by forward
    substitution.  Hand-verified against the machine-checked FTV/3
    calibration certificate (`validate.py`): this formula reproduces
    `cyclicCirculationVertex`'s `(1/3, 1/3, 2/3)` rotated triangle exactly.
    """
    L = len(u_list)
    prod_alpha = Fr(1)
    for a in alphas:
        prod_alpha *= a
    z0 = [Fr(0)] * n
    for i in range(n):
        acc = Fr(0)
        for k in range(L):
            term = (Fr(1) - alphas[k]) * u_list[k][i]
            tail = Fr(1)
            for j in range(k + 1, L):
                tail *= alphas[j]
            acc += term * tail
        z0[i] = acc / (Fr(1) - prod_alpha)
    zs = [z0]
    for l in range(L - 1):
        z_next = [
            alphas[l] * zs[l][i] + (Fr(1) - alphas[l]) * u_list[l][i] for i in range(n)
        ]
        zs.append(z_next)
    return zs


def verify_witness(
    w: Weight,
    chi_vec: Sequence[Fr],
    phases: Sequence[Tuple[Sequence[int], Fr]],
) -> Certificate:
    """Check ONE explicit candidate circulation certificate exactly.
    `phases` is `[(support_0, alpha_0), ..., (support_{L-1}, alpha_{L-1})]`.
    Singleton supports get their target directly off `V`'s own column
    (always diagonal-consistent, no solve needed); larger supports go
    through `_solve_phase_target` WITHOUT the floor filter (`floor=None`,
    per the module docstring).  Checks the owner pin (`z^l_i = d_i` for every
    `i` in phase `l`'s support) and the floor (`z^l >= floor` for every
    vertex `l`) exactly.  Returns a Certificate with the full witness
    (targets, vertices) whether or not it passes -- callers that only need
    the boolean should still inspect `.detail` on failure.
    """
    n = players(w)
    V = solo_payoff_matrix(w)
    d = [solo(w, i) for i in range(n)]
    floor = floor_vector(d, chi_vec)
    u_list: List[List[Fr]] = []
    for J, _alpha in phases:
        J = tuple(J)
        if len(J) == 1:
            i = J[0]
            u = [V[k][i] for k in range(n)]
        else:
            res = _solve_phase_target(V, d, None, J, n)
            if res is None:
                return Certificate(
                    False,
                    {
                        "reason": f"phase support {list(J)} has no owner-pinned mixture",
                        "phases": [(list(J2), str(a)) for J2, a in phases],
                    },
                )
            _lam, u = res
        u_list.append(u)
    alphas = [a for _J, a in phases]
    zs = _cyclic_close(u_list, alphas, n)
    L = len(phases)

    pin_ok = True
    pin_violations: List[Tuple[int, int, str, str]] = []
    for l in range(L):
        J = tuple(phases[l][0])
        for i in J:
            if zs[l][i] != d[i]:
                pin_ok = False
                pin_violations.append((l, i, str(zs[l][i]), str(d[i])))

    floor_ok = True
    floor_violations: List[Tuple[int, int, str, str]] = []
    for l in range(L):
        for i in range(n):
            if zs[l][i] < floor[i]:
                floor_ok = False
                floor_violations.append((l, i, str(zs[l][i]), str(floor[i])))

    ok = pin_ok and floor_ok
    return Certificate(
        ok,
        {
            "L": L,
            "supports": [list(J) for J, _ in phases],
            "alphas": [str(a) for _, a in phases],
            "u": [[str(x) for x in u] for u in u_list],
            "z": [[str(x) for x in z] for z in zs],
            "floor": [str(x) for x in floor],
            "pin_ok": pin_ok,
            "pin_violations": pin_violations,
            "floor_ok": floor_ok,
            "floor_violations": floor_violations,
        },
    )


# --------------------------------------------------------------------------
# The small-L search: L <= max_L, alpha on a rational grid, supports
# singleton-first.
# --------------------------------------------------------------------------

def search_circulation(
    w: Weight,
    chi_vec: Sequence[Fr],
    max_L: int = 3,
    alpha_grid: Sequence[Fr] = DEFAULT_ALPHA_GRID,
    multi_owner_max_L: int = 2,
    multi_owner_max_support: int = 2,
) -> Certificate:
    """Search circulation certificates of length `1..max_L` against a fixed
    `chi_vec` (the caller picks `hi` or `lo`; `certify_circulation` below is
    the sound-first wrapper that decides which to trust).  `L = 1` is
    answered exactly by `circulation_L1` (exhaustive over every nonempty
    support).  `L >= 2` is a SEARCH, not a decision procedure: singleton
    owner sequences are tried first, exhaustively, over
    `range(n)^L x alpha_grid^L`; only if that finds nothing, and only for
    `L <= multi_owner_max_L`, a bounded multi-owner fallback tries phase
    supports up to size `multi_owner_max_support` (reusing
    `_solve_phase_target` per support, cached once per support since it does
    not depend on `alpha`).  Failure at any `L` means "not found by this
    search", never "provably absent" -- reported as such.
    """
    n = players(w)

    if max_L >= 1:
        cert1 = circulation_L1(w, chi_vec)
        if cert1.ok:
            detail = dict(cert1.detail)
            detail["search"] = "L=1 direct (exhaustive over every support)"
            return Certificate(True, detail)

    combos_tried = 0
    for L in range(2, max_L + 1):
        # -- singleton-first, exhaustive over this grid --------------------
        for owners in product(range(n), repeat=L):
            supports = [(owner,) for owner in owners]
            for alphas in product(alpha_grid, repeat=L):
                combos_tried += 1
                phases = list(zip(supports, alphas))
                cert = verify_witness(w, chi_vec, phases)
                if cert.ok:
                    detail = dict(cert.detail)
                    detail["search"] = "singleton-first grid"
                    detail["combos_tried"] = combos_tried
                    return Certificate(True, detail)

        # -- bounded multi-owner fallback -----------------------------------
        if L <= multi_owner_max_L:
            V = solo_payoff_matrix(w)
            d = [solo(w, i) for i in range(n)]
            candidate_supports: List[Tuple[int, ...]] = [(i,) for i in range(n)]
            for size in range(2, multi_owner_max_support + 1):
                candidate_supports.extend(combinations(range(n), size))
            support_cache: Dict[Tuple[int, ...], bool] = {}
            for S in candidate_supports:
                if len(S) == 1:
                    support_cache[S] = True
                else:
                    support_cache[S] = _solve_phase_target(V, d, None, S, n) is not None
            feasible_supports = [S for S in candidate_supports if support_cache[S]]

            for support_seq in product(feasible_supports, repeat=L):
                if all(len(S) == 1 for S in support_seq):
                    continue  # already tried above
                for alphas in product(alpha_grid, repeat=L):
                    combos_tried += 1
                    phases = list(zip(support_seq, alphas))
                    cert = verify_witness(w, chi_vec, phases)
                    if cert.ok:
                        detail = dict(cert.detail)
                        detail["search"] = "multi-owner fallback (non-exhaustive)"
                        detail["combos_tried"] = combos_tried
                        return Certificate(True, detail)

    return Certificate(
        False,
        {
            "reason": "search exhausted at every L up to max_L with no witness found "
                      "(heuristic exhaustion, not a completeness proof for L >= 2)",
            "max_L": max_L,
            "alpha_grid": [str(a) for a in alpha_grid],
            "combos_tried": combos_tried,
        },
    )


def certify_circulation(
    w: Weight,
    chi_bounds: Tuple[Sequence[Fr], Sequence[Fr]],
    max_L: int = 3,
    alpha_grid: Sequence[Fr] = DEFAULT_ALPHA_GRID,
    **search_kwargs: object,
) -> Dict[str, object]:
    """The three-way status the sweep reports.  `chi_bounds = (lo, hi)`; per
    the module docstring's floor-honesty derivation, only `hi` is sound to
    certify against.  'certified': the search against `hi` succeeded (a
    genuine certificate).  'unsound_only': the search against `hi` failed
    but the search against `lo` succeeded -- an artifact, not a proof (the
    true `chi` could sit anywhere in `[lo, hi]`, and the witness found is
    only known valid if `chi` happens to be at or below the vertices it
    touches).  'empty_at_searched_depth': neither search found anything, at
    this `max_L` and this `alpha_grid` -- never a claim of nonexistence.
    """
    lo, hi = chi_bounds
    cert_hi = search_circulation(w, hi, max_L=max_L, alpha_grid=alpha_grid, **search_kwargs)
    if cert_hi.ok:
        return {"status": "certified", "certificate": cert_hi.detail}
    cert_lo = search_circulation(w, lo, max_L=max_L, alpha_grid=alpha_grid, **search_kwargs)
    if cert_lo.ok:
        return {
            "status": "unsound_only",
            "certificate": cert_lo.detail,
            "note": "found only against the LOWER bound on chi -- NOT sound; "
                    "see circulation.py's module docstring (floor honesty)",
        }
    return {
        "status": "empty_at_searched_depth",
        "hi_search": cert_hi.detail,
        "lo_search": cert_lo.detail,
    }
