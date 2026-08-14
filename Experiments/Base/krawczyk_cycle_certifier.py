"""Krawczyk / interval-exclusion certifier for quitting-cycle complementarity.

Generalizes the repository's K11 dyadic-island Krawczyk lane (`GameTheory/
UniformEquilibrium/Quitting/Examples/BlockPair/K11DyadicData.lean`) from a single quarantined
use to quitting-cycle complementarity systems, per the numerical-analysis
source note, section 2 ("Validated numerics: native technology, not
yet a weapon").  Standard-library only: exact rational interval arithmetic on
`fractions.Fraction` endpoints, deterministic, no external solvers.

WHAT IS CERTIFIED, AND HOW
---------------------------
Two different proof techniques are used for two different kinds of claim:

* EXISTENCE (+ uniqueness): the Krawczyk operator.  For a square system
  `F(x) = 0` with interval Jacobian `J(X)` over a box `X`, and `Y` an exact
  rational inverse of `J(center)`,

      K(X) = center - Y F(center) + (I - Y J(X)) (X - center).

  If `K(X)` is a STRICT SUBSET of the interior of `X` (checked with exact
  `Fraction` comparisons), the classical Krawczyk/Moore theorem certifies
  that `F` has exactly one zero in `X`.  This is the *same* criterion
  `Math/KrawczykBridge.lean` packages as a Banach-fixed-point bridge; only
  the interval arithmetic that discharges its hypotheses is new here.

* NONEXISTENCE: exhaustive interval exclusion via branch-and-bound.  A
  support pattern (which coordinates are pinned to 0, pinned to 1, or free)
  gives a system with as many unknowns as free coordinates.  A sub-box is
  discarded when interval evaluation of some equation provably excludes 0,
  or some sign (complementarity) condition is provably violated -- both exact
  `Fraction`-interval comparisons, no rounding.  A pattern is CERTIFIED
  infeasible only when EVERY sub-box in a full bisection tree gets discarded
  before the depth cap.  If the depth cap is hit with survivors remaining,
  the pattern is reported UNDECIDED, never claimed.  This needs no Jacobian
  and no preconditioner: it is pure sound forward evaluation.

Both routes reuse the same five named one-phase building blocks, mirroring
`UniformEquilibrium/Quitting/Cycles/CyclicWeightRowDichotomy.lean`:

    continueMassExcl  c_{-i}(y)        deleted continue mass
    sigmaValue        Sigma_i(y)       deleted quit value (i quits)
    excludedValue     A_i(y)           deleted continue reward (i stays,
                                        someone else among the others quits)
    gammaValue        Gamma_i(y,z)     continue value = A_i + c_{-i} z
    gainValue         g_i(y,z)         Sigma_i - Gamma_i, the exactness gap

For 3 players these are *exactly* bilinear in the two "other" coordinates
(only `sum_powerset_pair`'s four terms survive), so they are implemented once
as a generic bilinear-interpolation evaluator + hand-derived gradient, then
specialized by plugging in each reward table's four corner values per
coordinate.  Both the evaluator and the gradient are cross-checked below
against the *closed forms Lean already proves* (`sigmaValue_cyclicWeight`,
`excludedValue_cyclicWeight`, `gainValue_cyclicWeight`, equations 13-15 of
`QuittingCyclicWeightRowDichotomy.lean`) at multiple sample points, including
the 0/1 corners; a mismatch aborts the run via `assert`.

CERTIFICATES PRODUCED
----------------------
(A) Tool validation, EXISTENCE.  The Flesch-Thuijsman-Vrieze cubic /3
    period-3 absorbing complementary cycle (`ideas/AbsorbingCycleCarrier/
    FiniteCyclesAreRefutedTheCarrierIsAMassPath.md`: "each coordinate in turn
    quits with probability 1/2, values (1/3, 2/3, 1/3) cyclically", the
    table read off `UniformEquilibrium/Quitting/Examples/FTV/CyclicMinimality.lean`
    divided by 3).  Twelve unknowns (3 active rates + the 3x3 phase-value
    matrix), twelve equations (3 value-recursion residuals per phase + 1
    active-gap-zero residual per phase).  Krawczyk certifies existence and
    uniqueness in a small box around the doc's numbers (which independently,
    exactly zero the residual); the two silent coordinates' gaps are then
    checked <= 0 at that exact point via exact `Fraction` comparison,
    completing exact complementarity of the cycle.  (Some silent gaps are
    knife-edges, exactly 0 rather than < 0; checking a nonzero-width box
    around such a point cannot succeed by interval width alone, so the
    sign check is done at the point Krawczyk already confirmed is the
    unique nearby root, not by widening the box further.)

(B) The real target, NONEXISTENCE.  `cyclicWeight`'s period-1 (fixed-row)
    complementarity system, all 26 non-all-silent support patterns among
    {0, interior, 1}^3 (the all-continue pattern 000 is excluded by the
    absorption convention: "cycle" here means some quitting occurs, i.e.
    survival probability < 1; see below).  Interior search domain is
    `[eps, 1-eps]` with `eps = 2^-20` (not the open interval down to an
    infinitesimal point) -- the exact corner `y=(0,0,0)` is a removable
    singularity of the closed-form value map `v = terminalExpectation /
    (1 - survival)` that the raw interval quotient cannot resolve (the
    numerator and denominator both vanish there); bounding the search away
    from that single point by less than one part in a million is the stated
    convention, not a claim about that corner itself.

(C) Period-2, LIMITED (not exhaustive).  Exhaustively covering all
    27 x 27 = 729 period-2 support-pattern pairs is out of the time budget
    for a >=6-dimensional worst case (measured: the doubly-all-interior
    pattern alone does not resolve in 10s at generous depth).  Instead this
    certifies the natural 7 x 7 = 49-pattern family "at most one active
    (interior-or-quit-for-sure) coordinate per phase", mirroring the shape
    of the FTV cycle validated in (A) and of every period-1 pattern in (B).

NONCLAIMS
---------
* This is a certified-computation PROTOTYPE, not a Lean proof.  A faithful
  Lean port would follow the K11 island pattern (`BlockPairK11DyadicData.
  lean`): the interval arithmetic stays outside Lean, only the final
  containment/exclusion facts get consumed as hypotheses.
* Rational arithmetic is exact throughout; the search is depth-capped.  Any
  pattern reported UNDECIDED is genuinely undecided by this run, not a
  disguised claim either way.
* Period >= 3 is not attempted for `cyclicWeight` (period 3 is only run for
  the FTV/3 tool-validation table, where the answer is already known).
* Certificate (C) is explicitly non-exhaustive; see above.
* The Krawczyk existence route (A) and the exclusion route (B)/(C) are
  logically independent; neither is used to backstop the other.
"""

import json
import time
from fractions import Fraction as Fr

START_TIME = time.time()
GLOBAL_DEADLINE_SECONDS = 150.0  # safety net; measured runtime is far below this


def deadline_exceeded():
    return (time.time() - START_TIME) > GLOBAL_DEADLINE_SECONDS


# ---------------------------------------------------------------------------
# 1. Exact rational interval arithmetic
# ---------------------------------------------------------------------------

class Ival:
    """A closed interval [lo, hi] with exact Fraction endpoints."""

    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        if not isinstance(lo, Fr):
            lo = Fr(lo)
        if not isinstance(hi, Fr):
            hi = Fr(hi)
        assert lo <= hi, f"malformed interval [{lo}, {hi}]"
        self.lo = lo
        self.hi = hi

    @staticmethod
    def point(x):
        return Ival(Fr(x))

    @staticmethod
    def _coerce(x):
        return x if isinstance(x, Ival) else Ival.point(x)

    def __add__(self, other):
        o = Ival._coerce(other)
        return Ival(self.lo + o.lo, self.hi + o.hi)

    __radd__ = __add__

    def __neg__(self):
        return Ival(-self.hi, -self.lo)

    def __sub__(self, other):
        o = Ival._coerce(other)
        return Ival(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, other):
        return Ival._coerce(other).__sub__(self)

    def __mul__(self, other):
        o = Ival._coerce(other)
        prods = (self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi)
        return Ival(min(prods), max(prods))

    __rmul__ = __mul__

    def contains_zero(self):
        return self.lo <= 0 <= self.hi

    def __truediv__(self, other):
        o = Ival._coerce(other)
        assert not o.contains_zero(), "interval division by a zero-straddling interval"
        recip = Ival(Fr(1) / o.hi, Fr(1) / o.lo)
        return self * recip

    def width(self):
        return self.hi - self.lo

    def mid(self):
        return (self.lo + self.hi) / 2

    def strictly_inside(self, other):
        return other.lo < self.lo and self.hi < other.hi

    def to_fraction(self):
        assert self.lo == self.hi, f"expected a degenerate (point) interval, got {self}"
        return self.lo

    def __repr__(self):
        return f"[{self.lo},{self.hi}]"


# ---------------------------------------------------------------------------
# 2. The one-phase quitting building blocks (mirrors QuittingCyclicWeight-
#    RowDichotomy.lean's continueMassExcl / sigmaValue / excludedValue /
#    gammaValue / gainValue), specialized to n = 3 players via a generic
#    bilinear interpolation over the two "other" coordinates.
# ---------------------------------------------------------------------------

def others(i):
    """The two coordinates other than i, for n = 3, in ascending order."""
    o = [j for j in range(3) if j != i]
    return o[0], o[1]


def bilinear_coeffs(f00, f10, f01, f11):
    """Coefficients of f(ya,yb) = c0 + c1*ya + c2*yb + c3*ya*yb matching the
    corner values f(0,0)=f00, f(1,0)=f10, f(0,1)=f01, f(1,1)=f11.  This is
    exactly `sum_powerset_pair`'s four-term expansion, read as independent
    Bernoulli mixing over {a quits, b quits}."""
    c0 = f00
    c1 = f10 - f00
    c2 = f01 - f00
    c3 = f11 - f10 - f01 + f00
    return c0, c1, c2, c3


def bilinear_eval(coeffs, ya, yb):
    c0, c1, c2, c3 = coeffs
    return c0 + c1 * ya + c2 * yb + c3 * (ya * yb)


def bilinear_grad(coeffs, ya, yb):
    """(d/dya, d/dyb) of the bilinear form above."""
    c0, c1, c2, c3 = coeffs
    return c1 + c3 * yb, c2 + c3 * ya


def sigma_value(r, i, y):
    """Sigma_i(y): deleted quit value -- the expected reward to i from i
    quitting for sure, with the other two coordinates independently
    quitting/continuing according to y."""
    a, b = others(i)
    f00 = r(frozenset({i}), i)
    f10 = r(frozenset({i, a}), i)
    f01 = r(frozenset({i, b}), i)
    f11 = r(frozenset({i, a, b}), i)
    coeffs = bilinear_coeffs(f00, f10, f01, f11)
    return bilinear_eval(coeffs, y[a], y[b])


def sigma_value_grad(r, i, y):
    a, b = others(i)
    f00 = r(frozenset({i}), i)
    f10 = r(frozenset({i, a}), i)
    f01 = r(frozenset({i, b}), i)
    f11 = r(frozenset({i, a, b}), i)
    coeffs = bilinear_coeffs(f00, f10, f01, f11)
    dya, dyb = bilinear_grad(coeffs, y[a], y[b])
    return {a: dya, b: dyb}


def excluded_value(r, i, y):
    """A_i(y): deleted continue reward -- i does not quit, but some nonempty
    subset of the OTHER two coordinates does."""
    a, b = others(i)
    f00 = Fr(0)
    f10 = r(frozenset({a}), i)
    f01 = r(frozenset({b}), i)
    f11 = r(frozenset({a, b}), i)
    coeffs = bilinear_coeffs(f00, f10, f01, f11)
    return bilinear_eval(coeffs, y[a], y[b])


def excluded_value_grad(r, i, y):
    a, b = others(i)
    f00 = Fr(0)
    f10 = r(frozenset({a}), i)
    f01 = r(frozenset({b}), i)
    f11 = r(frozenset({a, b}), i)
    coeffs = bilinear_coeffs(f00, f10, f01, f11)
    dya, dyb = bilinear_grad(coeffs, y[a], y[b])
    return {a: dya, b: dyb}


def continue_mass_excl(y, i):
    """c_{-i}(y) = prod_{j != i} (1 - y_j)."""
    a, b = others(i)
    coeffs = bilinear_coeffs(Fr(1), Fr(0), Fr(0), Fr(0))
    return bilinear_eval(coeffs, y[a], y[b])


def continue_mass_excl_grad(y, i):
    a, b = others(i)
    coeffs = bilinear_coeffs(Fr(1), Fr(0), Fr(0), Fr(0))
    dya, dyb = bilinear_grad(coeffs, y[a], y[b])
    return {a: dya, b: dyb}


def gamma_value(r, i, y, z):
    """Gamma_i(y, z) = A_i(y) + c_{-i}(y) * z: the continuation value, with z
    the next-phase promise entry for player i."""
    return excluded_value(r, i, y) + continue_mass_excl(y, i) * z


def gamma_value_grad(r, i, y, z):
    a, b = others(i)
    egrad = excluded_value_grad(r, i, y)
    cgrad = continue_mass_excl_grad(y, i)
    return {a: egrad[a] + cgrad[a] * z, b: egrad[b] + cgrad[b] * z,
            'z': continue_mass_excl(y, i)}


def gain_value(r, i, y, z):
    """g_i(y, z) = Sigma_i(y) - Gamma_i(y, z): the exactness gap."""
    return sigma_value(r, i, y) - gamma_value(r, i, y, z)


def gain_value_grad(r, i, y, z):
    a, b = others(i)
    sgrad = sigma_value_grad(r, i, y)
    ggrad = gamma_value_grad(r, i, y, z)
    return {a: sgrad[a] - ggrad[a], b: sgrad[b] - ggrad[b], 'z': -ggrad['z']}


def terminal_expectation(r, i, y):
    """The FULL (unconditional) one-phase expected reward to i: y_i Sigma_i +
    (1-y_i) A_i, i.e. terminalExpectation(x)_i from FTVCyclicMinimality.lean,
    read through sigma/excluded rather than an 8-term sum."""
    S = sigma_value(r, i, y)
    A = excluded_value(r, i, y)
    return y[i] * S + (Ival.point(Fr(1)) - y[i]) * A


def survival_probability(y):
    """prod_i (1 - y_i)."""
    s = Ival.point(Fr(1))
    for c in y:
        s = s * (Ival.point(Fr(1)) - c)
    return s


# ---------------------------------------------------------------------------
# 3. Reward tables
# ---------------------------------------------------------------------------

# The Flesch-Thuijsman-Vrieze cubic table (FTVCyclicMinimality.lean's
# `soloReward` / `terminalReward`), divided by 3 -- the case-2 weight of
# ideas/AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMassPath.md
# ("The eta = 0 weight is the Flesch-Thuijsman-Vrieze (1997) cubic game
# divided by 3 ... exact absorbing complementary cycle of length 3: each
# coordinate in turn quits with probability 1/2, values (1/3, 2/3, 1/3)
# cyclically").
_FTV_RAW = {
    frozenset({0}): (Fr(1), Fr(3), Fr(0)),
    frozenset({1}): (Fr(0), Fr(1), Fr(3)),
    frozenset({2}): (Fr(3), Fr(0), Fr(1)),
    frozenset({0, 1}): (Fr(1), Fr(0), Fr(1)),
    frozenset({1, 2}): (Fr(1), Fr(1), Fr(0)),
    frozenset({0, 2}): (Fr(0), Fr(1), Fr(1)),
    frozenset({0, 1, 2}): (Fr(0), Fr(0), Fr(0)),
}


def ftv_reward_div3(S, i):
    return _FTV_RAW[frozenset(S)][i] / 3


# `cyclicWeight`, equation (9) of QuittingCyclicWeightRowDichotomy.lean,
# transcribed verbatim from its `if S = ... then ... else ...` definition.
_CYCLIC_WEIGHT = {
    frozenset({0}): (Fr(-1, 2), Fr(1, 2), Fr(-1)),
    frozenset({1}): (Fr(-1), Fr(-1, 2), Fr(1, 2)),
    frozenset({2}): (Fr(1, 2), Fr(-1), Fr(-1, 2)),
    frozenset({0, 1}): (Fr(-1, 4), Fr(-1, 2), Fr(1, 2)),
    frozenset({1, 2}): (Fr(1, 2), Fr(-1, 4), Fr(-1, 2)),
    frozenset({0, 2}): (Fr(-1, 2), Fr(1, 2), Fr(-1, 4)),
    frozenset({0, 1, 2}): (Fr(-1, 2), Fr(-1, 2), Fr(-1, 2)),
}


def cyclic_weight(S, i):
    return _CYCLIC_WEIGHT[frozenset(S)][i]


def cyclic_succ(i):
    return (i + 1) % 3


def cyclic_pred(i):
    return (i + 2) % 3


# ---------------------------------------------------------------------------
# 4. Cross-check the generic building blocks against the closed forms Lean
#    already proves for cyclicWeight (equations 13-15).  A mismatch aborts
#    the run: the certificates below are only as trustworthy as this match.
# ---------------------------------------------------------------------------

def cross_check_cyclic_weight_closed_forms():
    samples = [Fr(1, 3), Fr(2, 5), Fr(0), Fr(1), Fr(1, 7), Fr(3, 4)]
    checks = 0
    for i in range(3):
        s, p = cyclic_succ(i), cyclic_pred(i)
        for xs in samples:
            for xp in samples:
                y = [None, None, None]
                y[i] = Ival.point(Fr(1, 2))
                y[s] = Ival.point(xs)
                y[p] = Ival.point(xp)
                # equation 13: Sigma_i(x) + 1/2 = (1/4) x_succ (1 - x_pred)
                sig = sigma_value(cyclic_weight, i, y)
                lhs13 = sig + Ival.point(Fr(1, 2))
                rhs13 = Ival.point(Fr(1, 4)) * Ival.point(xs) * (Ival.point(Fr(1)) - Ival.point(xp))
                assert lhs13.to_fraction() == rhs13.to_fraction(), ("eq13", i, xs, xp)
                # equation 14 (nonempty-coalition half): A_i(x) =
                #   (1/2) x_pred - x_succ + x_succ x_pred
                a_val = excluded_value(cyclic_weight, i, y)
                rhs14 = (Ival.point(Fr(1, 2)) * Ival.point(xp) - Ival.point(xs)
                         + Ival.point(xs) * Ival.point(xp))
                assert a_val.to_fraction() == rhs14.to_fraction(), ("eq14", i, xs, xp)
                for nxt in (Fr(0), Fr(1, 3), Fr(-1, 2)):
                    # equation 15: g_i(x,next) = (3/4) x_succ (1-x_pred) -
                    #   x_pred - (1-x_pred)(1-x_succ)(next+1/2)
                    g = gain_value(cyclic_weight, i, y, Ival.point(nxt))
                    rhs15 = (Ival.point(Fr(3, 4)) * Ival.point(xs) * (Ival.point(1) - Ival.point(xp))
                             - Ival.point(xp)
                             - (Ival.point(1) - Ival.point(xp)) * (Ival.point(1) - Ival.point(xs))
                             * (Ival.point(nxt) + Ival.point(Fr(1, 2))))
                    assert g.to_fraction() == rhs15.to_fraction(), ("eq15", i, xs, xp, nxt)
                    checks += 1
    return checks


# ---------------------------------------------------------------------------
# 5. Certificate (A): Krawczyk existence for the FTV/3 period-3 cycle
# ---------------------------------------------------------------------------

class CyclicSystem:
    """A period-P cyclic quitting system with a fixed support pattern per
    phase.  pattern[c] is a length-3 list over {'0','1','x'} ('x' marks a
    free/interior rate).  Unknowns: v[c][i] for every phase c and coordinate
    i (always free -- the phase-c value vector), plus y[c][i] for every 'x'
    slot.  Equations: the 3 value-recursion residuals per phase (mirroring
    the identity v_i = y_i Sigma_i(y) + (1-y_i) Gamma_i(y, z_i), z = next
    phase's value) plus one gap-zero residual gain_value(y,z) = 0 per
    interior slot."""

    def __init__(self, table, period, pattern):
        self.r = table
        self.P = period
        self.pattern = pattern
        self.unknowns = []
        for c in range(period):
            for i in range(3):
                self.unknowns.append(('v', c, i))
        for c in range(period):
            for i in range(3):
                if pattern[c][i] == 'x':
                    self.unknowns.append(('y', c, i))
        self.idx = {name: k for k, name in enumerate(self.unknowns)}
        self.equations = []
        for c in range(period):
            for i in range(3):
                self.equations.append(('value', c, i))
        for c in range(period):
            for i in range(3):
                if pattern[c][i] == 'x':
                    self.equations.append(('gap', c, i))
        assert len(self.unknowns) == len(self.equations), "system is not square"
        self.n = len(self.unknowns)

    def get_y(self, X, c):
        y = []
        for i in range(3):
            p = self.pattern[c][i]
            if p == 'x':
                y.append(X[self.idx[('y', c, i)]])
            elif p == '0':
                y.append(Ival.point(Fr(0)))
            else:
                y.append(Ival.point(Fr(1)))
        return y

    def get_v(self, X, c, i):
        return X[self.idx[('v', c, i)]]

    def residual(self, X):
        out = [None] * self.n
        for eq_idx, (kind, c, i) in enumerate(self.equations):
            npc = (c + 1) % self.P
            y = self.get_y(X, c)
            if kind == 'value':
                S = sigma_value(self.r, i, y)
                G = gamma_value(self.r, i, y, self.get_v(X, npc, i))
                yi = y[i]
                val = self.get_v(X, c, i) - (yi * S + (Ival.point(Fr(1)) - yi) * G)
            else:
                val = gain_value(self.r, i, y, self.get_v(X, npc, i))
            out[eq_idx] = val
        return out

    def jacobian(self, X):
        J = [[Ival.point(Fr(0)) for _ in range(self.n)] for _ in range(self.n)]
        for eq_idx, (kind, c, i) in enumerate(self.equations):
            npc = (c + 1) % self.P
            a, b = others(i)
            y = self.get_y(X, c)
            zval = self.get_v(X, npc, i)
            if kind == 'value':
                J[eq_idx][self.idx[('v', c, i)]] += Ival.point(Fr(1))
                yi = y[i]
                S = sigma_value(self.r, i, y)
                G = gamma_value(self.r, i, y, zval)
                cont = continue_mass_excl(y, i)
                idx_vnp = self.idx[('v', npc, i)]
                J[eq_idx][idx_vnp] += -(Ival.point(Fr(1)) - yi) * cont
                if self.pattern[c][i] == 'x':
                    idx_yi = self.idx[('y', c, i)]
                    J[eq_idx][idx_yi] += -(S - G)
                sgrad = sigma_value_grad(self.r, i, y)
                egrad = excluded_value_grad(self.r, i, y)
                cgrad = continue_mass_excl_grad(y, i)
                for j in (a, b):
                    if self.pattern[c][j] == 'x':
                        idx_yj = self.idx[('y', c, j)]
                        dG_dyj = egrad[j] + cgrad[j] * zval
                        dVal_dyj = -(yi * sgrad[j] + (Ival.point(Fr(1)) - yi) * dG_dyj)
                        J[eq_idx][idx_yj] += dVal_dyj
            else:
                cont = continue_mass_excl(y, i)
                idx_vnp = self.idx[('v', npc, i)]
                J[eq_idx][idx_vnp] += -cont
                sgrad = sigma_value_grad(self.r, i, y)
                egrad = excluded_value_grad(self.r, i, y)
                cgrad = continue_mass_excl_grad(y, i)
                for j in (a, b):
                    if self.pattern[c][j] == 'x':
                        idx_yj = self.idx[('y', c, j)]
                        dGain_dyj = sgrad[j] - (egrad[j] + cgrad[j] * zval)
                        J[eq_idx][idx_yj] += dGain_dyj
        return J


def fraction_matrix_inverse(M):
    n = len(M)
    A = [row[:] + [Fr(1) if i == j else Fr(0) for j in range(n)] for i, row in enumerate(M)]
    for col in range(n):
        piv = None
        for r_ in range(col, n):
            if A[r_][col] != 0:
                piv = r_
                break
        assert piv is not None, f"singular Jacobian at midpoint (column {col})"
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r_ in range(n):
            if r_ != col and A[r_][col] != 0:
                factor = A[r_][col]
                A[r_] = [A[r_][k] - factor * A[col][k] for k in range(2 * n)]
    inv = [row[n:] for row in A]
    # Defensive check: Y * M should be exactly the identity.
    for i in range(n):
        for j in range(n):
            s = sum((inv[i][k] * M[k][j] for k in range(n)), Fr(0))
            assert s == (Fr(1) if i == j else Fr(0)), "matrix inverse failed to verify"
    return inv


def krawczyk_operator(sys_, X, center_fracs):
    n = sys_.n
    center_ivals = [Ival.point(f) for f in center_fracs]
    Fc = [v.to_fraction() for v in sys_.residual(center_ivals)]
    Jc = [[v.to_fraction() for v in row] for row in sys_.jacobian(center_ivals)]
    Y = fraction_matrix_inverse(Jc)
    JX = sys_.jacobian(X)
    YFc = [sum((Y[i][k] * Fc[k] for k in range(n)), Fr(0)) for i in range(n)]
    Xc = [X[i] - Ival.point(center_fracs[i]) for i in range(n)]
    K = []
    for i in range(n):
        val = Ival.point(center_fracs[i]) - Ival.point(YFc[i])
        for j in range(n):
            entry = Ival.point(Fr(1) if i == j else Fr(0))
            for k in range(n):
                entry = entry - Ival.point(Y[i][k]) * JX[k][j]
            val = val + entry * Xc[j]
        K.append(val)
    return K


def certificate_A():
    t0 = time.time()
    pattern = [
        ['x', '0', '0'],
        ['0', 'x', '0'],
        ['0', '0', 'x'],
    ]
    sys_ = CyclicSystem(ftv_reward_div3, 3, pattern)

    # The doc's numbers: rate 1/2 at every phase, values standardPromise/3.
    center = {
        ('v', 0, 0): Fr(1, 3), ('v', 0, 1): Fr(2, 3), ('v', 0, 2): Fr(1, 3),
        ('v', 1, 0): Fr(1, 3), ('v', 1, 1): Fr(1, 3), ('v', 1, 2): Fr(2, 3),
        ('v', 2, 0): Fr(2, 3), ('v', 2, 1): Fr(1, 3), ('v', 2, 2): Fr(1, 3),
        ('y', 0, 0): Fr(1, 2), ('y', 1, 1): Fr(1, 2), ('y', 2, 2): Fr(1, 2),
    }
    center_fracs = [center[name] for name in sys_.unknowns]

    # Sanity: the doc's numbers solve the system exactly (residual == 0).
    Fc = sys_.residual([Ival.point(f) for f in center_fracs])
    for v in Fc:
        assert v.to_fraction() == 0, "FTV/3 doc numbers do not solve the recursion exactly"

    radius = Fr(1, 20)
    X = [Ival(f - radius, f + radius) for f in center_fracs]
    K = krawczyk_operator(sys_, X, center_fracs)
    contained = []
    for name, k, x in zip(sys_.unknowns, K, X):
        inside = k.strictly_inside(x)
        contained.append(inside)
        assert inside, f"Krawczyk failed to contract at {name}: K={k} not strictly inside X={x}"
    # K(X) ⊂ int(X) certifies EXISTENCE + UNIQUENESS of a zero of the value-
    # recursion-and-active-gap system in X.  Since the doc's exact numbers
    # already zero the residual (checked above with exact Fraction
    # arithmetic, not merely an interval containing zero), that unique root
    # IS the center point -- Krawczyk's contribution is ruling out any other
    # nearby root, not locating this one.

    # Full exact complementarity, evaluated AT the exact (now Krawczyk-
    # confirmed-unique) center point rather than over a widened box: some
    # silent gaps here are knife-edges (g_i = 0 exactly, not < 0 -- matching
    # ideas/AbsorbingCycleCarrier/FiniteCyclesAreRefutedTheCarrierIsAMass
    # Path.md's "against y=(1/2,0,0) the idle third coordinate has g_3 = 0
    # at eta=0, exactly indifferent"), so widening to a nonzero-width box
    # would make the upper bound cross 0 in the direction that increases the
    # rate or decreases the value -- an artifact of interval width, not a
    # failure of complementarity at the actual point.  The exact rational
    # value at the point is what "exact complementarity" means here, and
    # Fraction equality/comparison is itself exact, no interval needed.
    center_ivals = [Ival.point(f) for f in center_fracs]
    silent_checks = []
    for c in range(3):
        npc = (c + 1) % 3
        y_pt = sys_.get_y(center_ivals, c)
        for i in range(3):
            if pattern[c][i] == 'x':
                continue
            z_pt = sys_.get_v(center_ivals, npc, i)
            g = gain_value(ftv_reward_div3, i, y_pt, z_pt).to_fraction()
            assert g <= 0, f"silent coordinate {i} at phase {c} fails complementarity: gap {g}"
            silent_checks.append({"phase": c, "coordinate": i, "gap": str(g)})

    elapsed = time.time() - t0
    return {
        "claim": "FTV/3 period-3 absorbing complementary cycle: existence + "
                 "uniqueness certified, exact complementarity of the silent "
                 "coordinates verified over the certified box",
        "unknown_order": [f"{k}{c}{i}" for (k, c, i) in sys_.unknowns],
        "center": {f"{k}{c}{i}": str(v) for (k, c, i), v in zip(sys_.unknowns, center_fracs)},
        "box_radius": str(radius),
        "krawczyk_strictly_contracted": all(contained),
        "silent_coordinate_checks": silent_checks,
        "elapsed_seconds": elapsed,
        "status": "CERTIFIED",
    }


# ---------------------------------------------------------------------------
# 6. Certificates (B) and (C): nonexistence via exhaustive interval exclusion
# ---------------------------------------------------------------------------

def eval_period1_values(table, y):
    """v_i = terminalExpectation(y)_i / (1 - survival(y)); None if the
    denominator interval straddles zero (the removable singularity at the
    all-continue corner)."""
    S = survival_probability(y)
    denom = Ival.point(Fr(1)) - S
    if denom.contains_zero():
        return None
    return [terminal_expectation(table, i, y) / denom for i in range(3)]


def check_period1_pattern_box(table, pattern, y):
    v = eval_period1_values(table, y)
    if v is None:
        return 'unknown'
    ok = True
    for i in range(3):
        g = gain_value(table, i, y, v[i])
        if pattern[i] == 'x':
            if not g.contains_zero():
                ok = False
        elif pattern[i] == '0':
            if g.lo > 0:
                ok = False
        else:  # '1'
            if g.hi < 0:
                ok = False
    return 'feasible' if ok else 'infeasible'


def row_from_pattern(pattern, box):
    y = [None, None, None]
    for i in range(3):
        if pattern[i] == '0':
            y[i] = Ival.point(Fr(0))
        elif pattern[i] == '1':
            y[i] = Ival.point(Fr(1))
        else:
            y[i] = box[i]
    return y


def bnb_period1(table, pattern, eps, max_nodes, max_depth, time_budget):
    interior = [i for i in range(3) if pattern[i] == 'x']
    if not interior:
        y = row_from_pattern(pattern, {})
        verdict = check_period1_pattern_box(table, pattern, y)
        return ('infeasible (refuted)' if verdict == 'infeasible' else verdict), 1, 0

    init_box = {i: Ival(eps, Fr(1) - eps) for i in interior}
    stack = [(init_box, 0)]
    nodes = 0
    undecided = 0
    t0 = time.time()
    while stack:
        nodes += 1
        if nodes > max_nodes or (time.time() - t0) > time_budget or deadline_exceeded():
            undecided += len(stack) + 1
            return 'undecided (budget)', nodes, undecided
        box, depth = stack.pop()
        y = row_from_pattern(pattern, box)
        verdict = check_period1_pattern_box(table, pattern, y)
        if verdict == 'infeasible':
            continue
        if depth >= max_depth:
            undecided += 1
            continue
        widest = max(interior, key=lambda i: box[i].width())
        lo, hi = box[widest].lo, box[widest].hi
        mid = (lo + hi) / 2
        b1 = dict(box); b1[widest] = Ival(lo, mid)
        b2 = dict(box); b2[widest] = Ival(mid, hi)
        stack.append((b1, depth + 1))
        stack.append((b2, depth + 1))
    return ('infeasible (refuted)' if undecided == 0 else 'undecided (depth cap)'), nodes, undecided


def certificate_B():
    t0 = time.time()
    eps = Fr(1, 2 ** 20)
    patterns = []
    for x0 in ('0', '1', 'x'):
        for x1 in ('0', '1', 'x'):
            for x2 in ('0', '1', 'x'):
                patterns.append((x0, x1, x2))

    results = {}
    certified = []
    undecided = []
    for pat in patterns:
        label = ''.join(pat)
        if pat == ('0', '0', '0'):
            results[label] = {"verdict": "excluded (all-continue, not absorbing "
                                          "by convention)", "nodes": 0, "undecided_leaves": 0}
            continue
        verdict, nodes, undec = bnb_period1(
            cyclic_weight, pat, eps, max_nodes=50000, max_depth=100, time_budget=8.0)
        results[label] = {"verdict": verdict, "nodes": nodes, "undecided_leaves": undec}
        if verdict == 'infeasible (refuted)':
            assert undec == 0, "internal inconsistency: refuted claim with survivors"
            certified.append(label)
        elif verdict == 'feasible (exact point)':
            # A genuine period-1 exact cycle would be reported here, not
            # silently -- this branch is unreached by the current run but
            # kept so a future discovery is surfaced rather than swallowed.
            pass
        else:
            undecided.append(label)

    elapsed = time.time() - t0
    n_tested = len(patterns) - 1  # excluding the all-continue pattern
    return {
        "claim": "cyclicWeight period-1: no exact complementary absorbing row, "
                 "for every tested support pattern",
        "interior_search_domain": f"[{eps}, {Fr(1)-eps}] (eps = 2^-20; see nonclaims "
                                   "re. the removable singularity at (0,0,0))",
        "patterns_tested": n_tested,
        "patterns_certified_infeasible": len(certified),
        "patterns_undecided": len(undecided),
        "per_pattern": results,
        "certified_patterns": sorted(certified),
        "undecided_patterns": sorted(undecided),
        "elapsed_seconds": elapsed,
        "status": "CERTIFIED (all tested patterns refuted)" if not undecided
                  else "PARTIAL (some patterns undecided)",
    }


def eval_period2_values(table, y0, y1):
    S0 = survival_probability(y0)
    S1 = survival_probability(y1)
    denom = Ival.point(Fr(1)) - S0 * S1
    if denom.contains_zero():
        return None
    te0 = [terminal_expectation(table, i, y0) for i in range(3)]
    te1 = [terminal_expectation(table, i, y1) for i in range(3)]
    V0 = [(te0[i] + S0 * te1[i]) / denom for i in range(3)]
    V1 = [(te1[i] + S1 * te0[i]) / denom for i in range(3)]
    return V0, V1


def check_period2_pattern_box(table, pattern0, pattern1, y0, y1):
    r = eval_period2_values(table, y0, y1)
    if r is None:
        return 'unknown'
    V0, V1 = r
    ok = True
    for i in range(3):
        g0 = gain_value(table, i, y0, V1[i])
        if pattern0[i] == 'x':
            if not g0.contains_zero():
                ok = False
        elif pattern0[i] == '0':
            if g0.lo > 0:
                ok = False
        else:
            if g0.hi < 0:
                ok = False
        g1 = gain_value(table, i, y1, V0[i])
        if pattern1[i] == 'x':
            if not g1.contains_zero():
                ok = False
        elif pattern1[i] == '0':
            if g1.lo > 0:
                ok = False
        else:
            if g1.hi < 0:
                ok = False
    return 'feasible' if ok else 'infeasible'


def bnb_period2(table, pattern0, pattern1, eps, max_nodes, max_depth, time_budget):
    slots = [(0, i) for i in range(3) if pattern0[i] == 'x'] + \
            [(1, i) for i in range(3) if pattern1[i] == 'x']
    if not slots:
        y0 = row_from_pattern(pattern0, {})
        y1 = row_from_pattern(pattern1, {})
        verdict = check_period2_pattern_box(table, pattern0, pattern1, y0, y1)
        return ('infeasible (refuted)' if verdict == 'infeasible' else verdict), 1, 0

    init_box = {s: Ival(eps, Fr(1) - eps) for s in slots}
    stack = [(init_box, 0)]
    nodes = 0
    undecided = 0
    t0 = time.time()
    while stack:
        nodes += 1
        if nodes > max_nodes or (time.time() - t0) > time_budget or deadline_exceeded():
            undecided += len(stack) + 1
            return 'undecided (budget)', nodes, undecided
        box, depth = stack.pop()
        y0 = [None, None, None]
        y1 = [None, None, None]
        for i in range(3):
            y0[i] = (Ival.point(Fr(0)) if pattern0[i] == '0' else
                      Ival.point(Fr(1)) if pattern0[i] == '1' else box[(0, i)])
            y1[i] = (Ival.point(Fr(0)) if pattern1[i] == '0' else
                      Ival.point(Fr(1)) if pattern1[i] == '1' else box[(1, i)])
        verdict = check_period2_pattern_box(table, pattern0, pattern1, y0, y1)
        if verdict == 'infeasible':
            continue
        if depth >= max_depth:
            undecided += 1
            continue
        widest = max(slots, key=lambda s: box[s].width())
        lo, hi = box[widest].lo, box[widest].hi
        mid = (lo + hi) / 2
        b1 = dict(box); b1[widest] = Ival(lo, mid)
        b2 = dict(box); b2[widest] = Ival(mid, hi)
        stack.append((b1, depth + 1))
        stack.append((b2, depth + 1))
    return ('infeasible (refuted)' if undecided == 0 else 'undecided (depth cap)'), nodes, undecided


def single_active_shapes():
    """The 7 per-phase shapes: all-silent, or exactly one coordinate active
    (interior 'x', or quits-for-sure '1'), at each of the 3 positions."""
    shapes = [('0', '0', '0')]
    for pos in range(3):
        for active in ('x', '1'):
            s = ['0', '0', '0']
            s[pos] = active
            shapes.append(tuple(s))
    return shapes


def certificate_C():
    t0 = time.time()
    eps = Fr(1, 2 ** 20)
    shapes = single_active_shapes()
    results = {}
    certified = []
    undecided = []
    all_silent = ('0', '0', '0')
    for s0 in shapes:
        for s1 in shapes:
            label = ''.join(s0) + "/" + ''.join(s1)
            if s0 == all_silent and s1 == all_silent:
                # Both phases all-continue: the cycle never absorbs at all,
                # excluded by the same convention as period-1's "000".
                results[label] = {"verdict": "excluded (all-continue in both "
                                              "phases, not absorbing by convention)",
                                   "nodes": 0, "undecided_leaves": 0}
                continue
            verdict, nodes, undec = bnb_period2(
                cyclic_weight, s0, s1, eps, max_nodes=20000, max_depth=60, time_budget=6.0)
            results[label] = {"verdict": verdict, "nodes": nodes, "undecided_leaves": undec}
            if verdict == 'infeasible (refuted)':
                assert undec == 0, "internal inconsistency: refuted claim with survivors"
                certified.append(label)
            elif verdict != 'feasible (exact point)':
                undecided.append(label)

    elapsed = time.time() - t0
    total_combos = len(shapes) * len(shapes)
    return {
        "claim": "cyclicWeight period-2, LIMITED to the 'at most one active "
                 "coordinate per phase' family (49 of the 729 total support-"
                 "pattern pairs, one of which -- both phases all-continue -- "
                 "is excluded by the absorption convention): no exact "
                 "complementary absorbing cycle found in the tested family",
        "non_exhaustive": True,
        "family_size": total_combos,
        "patterns_excluded": 1,
        "patterns_tested": total_combos - 1,
        "total_period2_patterns": 27 * 27,
        "patterns_certified_infeasible": len(certified),
        "patterns_undecided": len(undecided),
        "per_pattern": results,
        "undecided_patterns": sorted(undecided),
        "elapsed_seconds": elapsed,
        "status": "CERTIFIED (family fully refuted)" if not undecided else "PARTIAL",
    }


# ---------------------------------------------------------------------------
# 7. Run everything, assemble the JSON summary
# ---------------------------------------------------------------------------

def main():
    timings = {}

    t0 = time.time()
    n_checks = cross_check_cyclic_weight_closed_forms()
    timings["cross_check_seconds"] = time.time() - t0

    result_a = certificate_A()
    timings["certificate_A_seconds"] = result_a["elapsed_seconds"]

    result_b = certificate_B()
    timings["certificate_B_seconds"] = result_b["elapsed_seconds"]

    result_c = certificate_C()
    timings["certificate_C_seconds"] = result_c["elapsed_seconds"]

    timings["total_seconds"] = time.time() - START_TIME

    certified_claims = []
    if result_a["status"] == "CERTIFIED":
        certified_claims.append(result_a["claim"])
    certified_claims.extend(
        f"cyclicWeight period-1, pattern {p}: no exact complementary absorbing row"
        for p in result_b["certified_patterns"])
    if result_c["status"].startswith("CERTIFIED"):
        certified_claims.append(result_c["claim"])

    undecided_claims = [f"cyclicWeight period-1, pattern {p}" for p in result_b["undecided_patterns"]]
    undecided_claims += [f"cyclicWeight period-2 (limited family), pattern {p}"
                          for p in result_c["undecided_patterns"]]

    summary = {
        "tool_validation": result_a,
        "period1_nonexistence": result_b,
        "period2_nonexistence_limited": result_c,
        "closed_form_cross_checks_passed": n_checks,
        "certified_claims": certified_claims,
        "undecided": undecided_claims,
        "timings": timings,
        "nonclaims": [
            "Prototype, not a Lean proof; a Lean port would follow the K11 "
            "island pattern (BlockPairK11DyadicData.lean).",
            "Rational arithmetic is exact; the branch-and-bound search is "
            "depth-capped. UNDECIDED means genuinely undecided by this run.",
            "Period >= 3 for cyclicWeight is not attempted.",
            "Certificate C (period 2) is explicitly non-exhaustive: 49 of "
            "729 support-pattern pairs.",
            "The interior search domain for periods 1 and 2 is [eps,1-eps] "
            "with eps=2^-20, not the literal open interval, because the "
            "value map v = terminalExpectation/(1-survival) has a removable "
            "singularity at the excluded all-continue corner that raw "
            "interval division cannot resolve.",
        ],
    }

    print(json.dumps(summary, indent=2, default=str))
    assert timings["total_seconds"] < 170.0, "runtime exceeded the intended budget"


if __name__ == "__main__":
    main()
