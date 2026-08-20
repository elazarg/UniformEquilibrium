"""Exact certificate-producing filters over quitting weights (P13, slice one).

Every function here decides a finite question about a `weights.Weight` using
only `fractions.Fraction` arithmetic, and returns a `Certificate` -- a
witness when the answer is yes, a refutation trace (a blocking coordinate, an
empty interval, an exhausted search space) when the answer is no.  None of
these functions returns a bare `bool`: the whole point of the certificate
discipline is that `validate.py` can print exactly what was found or why the
search failed, rather than trusting a boolean.

Filters implemented (P13's escalating list, items 1-3, plus the stationary
row search used to validate item 3's `Sigma`/`Gamma` formulas):

  1. `is_zero_solo`           -- IsQuittingZeroSolo, literally: every solo
                                  value `r_i({i}) <= 0` (NOT `== 0`; see the
                                  docstring below, this is a common
                                  misreading of the name).
  2. `solo_quitter_lp`        -- QuittingSoloQuitterEquilibrium.lean's
                                  `QuittingSoloQuitterCriterion`: the
                                  no-join affine feasibility test for a
                                  period-one solo-quitter row.
  3. `singleton_lcp_feasible` -- Question 154 section 1, eq. (5): the
                                  normalized singleton LCP, decided by
                                  support-pattern enumeration and exact
                                  Gaussian elimination.
  4. `stationary_row_search`  -- brute-force small-denominator rational
                                  stationary rows, decided by the exact
                                  `Sigma_i`, `Gamma_i` formulas of Question
                                  154 section 1, eqs. (3)-(4), specialized to
                                  a constant row.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction as Fr
from itertools import combinations
from typing import Any, Dict, List, Optional, Sequence, Tuple

from weights import Weight, all_nonempty_coalitions, players, r, solo


@dataclass(frozen=True)
class Certificate:
    """`ok`: the decision.  `detail`: a witness (if `ok`) or a refutation
    trace (if not) -- always inspectable, never discarded."""

    ok: bool
    detail: Dict[str, Any] = field(default_factory=dict)

    def __bool__(self) -> bool:  # convenience only; callers should still
        return self.ok           # print `.detail`, not just branch on this.

    def render(self) -> str:
        lines = [f"  ok = {self.ok}"]
        for k, v in self.detail.items():
            lines.append(f"  {k} = {v}")
        return "\n".join(lines)


# --------------------------------------------------------------------------
# 1. Zero-solo.
# --------------------------------------------------------------------------

def is_zero_solo(w: Weight) -> Certificate:
    """`IsQuittingZeroSolo` (`GameTheory/Concepts/Stochastic/
    QuittingZeroSoloDisjunct.lean`, line ~57): `forall i, r_i({i}) <= 0`.

    This is a NONPOSITIVITY condition, not `r_i({i}) == 0` -- the Lean
    source is explicit ("every coordinate's solo-quitting reward is
    nonpositive").  A weight with all-negative solo values (e.g. Q154's
    `d_i = -1/2`) is zero-solo TRUE; a weight with a single positive solo
    value is zero-solo FALSE regardless of the others.
    """
    n = players(w)
    ds = [solo(w, i) for i in range(n)]
    bad = [i for i in range(n) if ds[i] > 0]
    if bad:
        return Certificate(
            False,
            {
                "solo_values": ds,
                "violating_players": bad,
                "reason": "r_i({i}) > 0 for these i, so IsQuittingZeroSolo fails",
            },
        )
    return Certificate(True, {"solo_values": ds})


# --------------------------------------------------------------------------
# 2. Solo-quitter no-join LP.
# --------------------------------------------------------------------------

def solo_quitter_lp(w: Weight, i: int) -> Certificate:
    """`QuittingSoloQuitterCriterion` (`GameTheory/Concepts/Stochastic/
    QuittingSoloQuitterEquilibrium.lean`, line ~235): does some `p in (0,1]`
    satisfy, for every `j != i`,

        (1 - p) * r_j({j}) + p * r_j({i,j}) <= r_j({i})?

    This is affine in `p` for each `j`; each `j` contributes a half-line (or
    the whole line, or the empty set) of feasible `p`.  Intersect them
    exactly and report the feasible interval, or the first blocking `j`
    whose constraint is infeasible for every `p` in the domain.
    """
    n = players(w)
    lo: Fr = Fr(0)
    lo_open = True     # domain is p in (0, 1]: 0 itself is always excluded.
    hi: Fr = Fr(1)      # always closed: p = 1 is always in the domain.
    tightened_by: List[int] = []
    for j in range(n):
        if j == i:
            continue
        A = r(w, {j}, j)               # r_j({j})
        collision = r(w, {i, j}, j)    # r_j({i,j})
        cap = r(w, {i}, j)             # r_j({i})
        slope = collision - A
        rhs = cap - A                  # constraint: p * slope <= rhs
        if slope == 0:
            if rhs < 0:
                return Certificate(
                    False,
                    {
                        "blocking_player": j,
                        "reason": "constant constraint violated for every p",
                        "r_j({j})": A,
                        "r_j({i,j})": collision,
                        "r_j({i})": cap,
                        "required": f"0 <= {rhs}",
                    },
                )
            continue
        bound = rhs / slope
        if slope > 0:
            if bound < hi:
                hi = bound
                tightened_by.append(j)
        else:
            if bound > lo:
                lo = bound
                lo_open = False
                tightened_by.append(j)
    feasible = (lo < hi) if lo_open else (lo <= hi)
    if feasible:
        p_witness = hi
        return Certificate(
            True,
            {
                "owner": i,
                "interval": f"({lo}, {hi}]" if lo_open else f"[{lo}, {hi}]",
                "p_witness": p_witness,
                "tightened_by": tightened_by,
            },
        )
    return Certificate(
        False,
        {
            "owner": i,
            "reason": "feasible interval is empty",
            "lo": lo,
            "lo_open": lo_open,
            "hi": hi,
        },
    )


# --------------------------------------------------------------------------
# 3. Singleton LCP feasibility, by support-pattern enumeration.
# --------------------------------------------------------------------------

def _rref_solve(
    rows: Sequence[Sequence[Fr]], rhs: Sequence[Fr], ncols: int
) -> Optional[Tuple[List[Fr], List[List[Fr]]]]:
    """Exact Gauss-Jordan elimination over `Fraction`.  Solves `rows @ x =
    rhs`.  Returns `None` if inconsistent, else `(particular, basis)` with
    every solution equal to `particular + sum(t_k * basis[k] for k)` for
    free `t_k in Q`."""
    m = len(rows)
    mat = [list(rows[i]) + [rhs[i]] for i in range(m)]
    pivot_row = 0
    pivots: List[int] = []
    for col in range(ncols):
        piv = None
        for rr in range(pivot_row, m):
            if mat[rr][col] != 0:
                piv = rr
                break
        if piv is None:
            continue
        mat[pivot_row], mat[piv] = mat[piv], mat[pivot_row]
        pv = mat[pivot_row][col]
        mat[pivot_row] = [v / pv for v in mat[pivot_row]]
        for rr in range(m):
            if rr != pivot_row and mat[rr][col] != 0:
                f = mat[rr][col]
                mat[rr] = [mat[rr][k] - f * mat[pivot_row][k] for k in range(ncols + 1)]
        pivots.append(col)
        pivot_row += 1
        if pivot_row == m:
            break
    rank = pivot_row
    for rr in range(rank, m):
        if all(mat[rr][c] == 0 for c in range(ncols)) and mat[rr][ncols] != 0:
            return None
    free_cols = [c for c in range(ncols) if c not in pivots]
    particular = [Fr(0)] * ncols
    for i, col in enumerate(pivots):
        particular[col] = mat[i][ncols]
    basis: List[List[Fr]] = []
    for f in free_cols:
        vec = [Fr(0)] * ncols
        vec[f] = Fr(1)
        for i, col in enumerate(pivots):
            vec[col] = -mat[i][f]
        basis.append(vec)
    return particular, basis


def _solve_support(
    B: Sequence[Sequence[Fr]], S: Sequence[int], n: int
) -> Optional[List[Fr]]:
    """For a fixed nonempty support `S`, find `lambda >= 0` on `S`, summing
    to `1`, with `(B lambda)_i = 0` for `i in S` and `(B lambda)_i >= 0` for
    `i not in S` -- or `None` if no such `lambda` exists.  The on-support
    equations are solved exactly (particular + nullspace basis); any
    remaining free parameters are pinned by vertex enumeration: every
    nonempty bounded polyhedron has a vertex where at least `dim`-many of
    the defining `>= 0` facets are tight, so trying every combination of
    `dim` tight facets (each solved by another exact linear system) is
    complete."""
    S = list(S)
    k = len(S)
    B_SS = [[B[i][j] for j in S] for i in S]
    rows = B_SS + [[Fr(1)] * k]
    rhs = [Fr(0)] * k + [Fr(1)]
    solved = _rref_solve(rows, rhs, k)
    if solved is None:
        return None
    particular, basis = solved
    d = len(basis)

    def build(t: Sequence[Fr]) -> List[Fr]:
        lam = list(particular)
        for tk, vk in zip(t, basis):
            for c in range(k):
                lam[c] += tk * vk[c]
        return lam

    def full_and_check(lam_S: List[Fr]) -> Optional[List[Fr]]:
        if any(x < 0 for x in lam_S):
            return None
        lam_full = [Fr(0)] * n
        for idx, s_idx in enumerate(S):
            lam_full[s_idx] = lam_S[idx]
        for i in range(n):
            if i in S:
                continue
            Blam_i = sum(B[i][j] * lam_full[j] for j in S)
            if Blam_i < 0:
                return None
        return lam_full

    if d == 0:
        return full_and_check(particular)

    # Candidate 0: the particular solution itself (t = 0), a valid extra
    # try even though it need not be a vertex.
    cand = full_and_check(build([Fr(0)] * d))
    if cand is not None:
        return cand

    for combo in combinations(range(k), d):
        M = [[basis[kk][c] for kk in range(d)] for c in combo]
        rhsv = [-particular[c] for c in combo]
        square = _rref_solve(M, rhsv, d)
        if square is None:
            continue
        t_particular, t_basis = square
        if t_basis:
            continue  # degenerate combo: not an isolated vertex, skip
        cand = full_and_check(build(t_particular))
        if cand is not None:
            return cand
    return None


def singleton_lcp_feasible(B: Sequence[Sequence[Fr]]) -> Certificate:
    """Question 154 section 1, eq. (5), by support-pattern enumeration: for
    each nonempty `S subseteq {0,...,n-1}` in increasing size, decide
    whether `lambda in Delta(S)` exists with `(B lambda)_i = 0` for `i in S`
    and `(B lambda)_i >= 0` for `i not in S`.  Returns the first feasible
    `(S, lambda)` found, or an exhaustion certificate listing every support
    tried.
    """
    n = len(B)
    tried: List[Tuple[int, ...]] = []
    for size in range(1, n + 1):
        for S in combinations(range(n), size):
            tried.append(S)
            lam = _solve_support(B, S, n)
            if lam is not None:
                Blam = [sum(B[i][j] * lam[j] for j in range(n)) for i in range(n)]
                return Certificate(
                    True,
                    {"S": S, "lambda": lam, "B@lambda": Blam},
                )
    return Certificate(
        False,
        {"reason": "every nonempty support exhausted", "n": n, "supports_tried": len(tried)},
    )


# --------------------------------------------------------------------------
# 4. Stationary row search (exact period-one complementarity).
# --------------------------------------------------------------------------

def _prod(xs) -> Fr:
    out = Fr(1)
    for x in xs:
        out *= x
    return out


def stationary_value(w: Weight, x: Sequence[Fr]) -> Optional[List[Fr]]:
    """The stationary value of a constant row `x` played forever:

        V_i(x) = sum_{J != empty} a(x)(J) r_i(J) / (1 - c(x))

    (Question 154 section 3, the `2 => 3` construction), where `a(x)(J) =
    prod_{i in J} x_i * prod_{i not in J} (1 - x_i)` and `c(x) = prod_i
    (1 - x_i)`.  `None` if `c(x) = 1` (the all-continue row `x = 0`, which
    never absorbs and has no stationary value)."""
    n = len(x)
    c = _prod(Fr(1) - xi for xi in x)
    if c == 1:
        return None
    total = [Fr(0)] * n
    for J in all_nonempty_coalitions(n):
        weight = _prod(x[j] for j in J) * _prod(
            Fr(1) - x[j] for j in range(n) if j not in J
        )
        if weight == 0:
            continue
        vec = w[J]
        for i in range(n):
            total[i] += weight * vec[i]
    return [t / (Fr(1) - c) for t in total]


def _sigma_i(w: Weight, x: Sequence[Fr], i: int) -> Fr:
    """`Sigma_i(t)`, Question 154 eq. (3), specialized to a constant row:
    the expected payoff to `i` conditioned on `i` quitting this stage."""
    n = len(x)
    others = [j for j in range(n) if j != i]
    total = Fr(0)
    for size in range(0, len(others) + 1):
        for J in combinations(others, size):
            Jset = frozenset(J)
            weight = _prod(x[j] for j in J) * _prod(
                Fr(1) - x[j] for j in others if j not in Jset
            )
            if weight == 0:
                continue
            total += weight * w[Jset | {i}][i]
    return total


def _A_i(w: Weight, x: Sequence[Fr], i: int) -> Fr:
    """`A_i(t)`, Question 154 eq. (4): the expected payoff to `i` from a
    *nonempty* set of opponents quitting while `i` stays, conditioned on `i`
    not quitting this stage."""
    n = len(x)
    others = [j for j in range(n) if j != i]
    total = Fr(0)
    for size in range(1, len(others) + 1):
        for J in combinations(others, size):
            Jset = frozenset(J)
            weight = _prod(x[j] for j in J) * _prod(
                Fr(1) - x[j] for j in others if j not in Jset
            )
            if weight == 0:
                continue
            total += weight * w[Jset][i]
    return total


def _gamma_i(w: Weight, x: Sequence[Fr], V: Sequence[Fr], i: int) -> Fr:
    """`Gamma_i(t) = A_i(t) + c_{-i}(x_t) V_i(t+1)`, Question 154 eq. (4),
    specialized to a stationary row (`V_i(t+1) = V_i(x)`)."""
    n = len(x)
    c_minus_i = _prod(Fr(1) - x[j] for j in range(n) if j != i)
    return _A_i(w, x, i) + c_minus_i * V[i]


def gap(w: Weight, x: Sequence[Fr], V: Sequence[Fr], i: int) -> Fr:
    """`g_i = Sigma_i - Gamma_i`, Question 154 section 1's exact-
    complementarity quantity, for a stationary candidate row `x` and its
    value `V`."""
    return _sigma_i(w, x, i) - _gamma_i(w, x, V, i)


def _small_rationals(denom_bound: int) -> List[Fr]:
    vals = set()
    for d in range(1, denom_bound + 1):
        for a in range(0, d + 1):
            vals.add(Fr(a, d))
    return sorted(vals)


def stationary_row_search(w: Weight, denom_bound: int) -> Certificate:
    """Brute-force search, over `x in ([0,1] cap Q, denominator <=
    denom_bound)^n`, for an exact period-one complementary stationary row:
    some `x != 0` such that, playing `x` forever with its own stationary
    value `V(x)`, both clauses of exact complementarity hold at every `i`:

        x_i > 0  ==>  g_i(x, V(x)) >= 0
        x_i < 1  ==>  g_i(x, V(x)) <= 0

    Returns the first `(x, V, gaps)` found, or an exhaustion certificate.
    `x = 0` (all-continue, no absorption) is skipped: `stationary_value`
    is undefined there.
    """
    n = players(w)
    grid = _small_rationals(denom_bound)
    checked = 0

    def rows(depth: int, prefix: Tuple[Fr, ...]):
        if depth == n:
            yield prefix
            return
        for v in grid:
            yield from rows(depth + 1, prefix + (v,))

    for x in rows(0, ()):
        if all(xi == 0 for xi in x):
            continue
        checked += 1
        V = stationary_value(w, x)
        if V is None:
            continue
        gaps = [gap(w, x, V, i) for i in range(n)]
        ok = True
        for i in range(n):
            if x[i] > 0 and gaps[i] < 0:
                ok = False
                break
            if x[i] < 1 and gaps[i] > 0:
                ok = False
                break
        if ok:
            return Certificate(True, {"x": x, "V": V, "gaps": gaps, "rows_checked": checked})
    return Certificate(
        False,
        {
            "reason": "grid exhausted, no exact complementary stationary row found",
            "denom_bound": denom_bound,
            "rows_checked": checked,
        },
    )
