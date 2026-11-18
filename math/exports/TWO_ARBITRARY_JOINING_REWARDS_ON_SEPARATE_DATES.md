# Two arbitrary joining rewards on a four-player quitting table

Use player bits X=1,Y=2,U=4,V=8. Subtract the own singleton level s_i from each of i's nonempty exit payoffs to give native values. For a nonempty rival set S write P_i(S) for i's native payoff on S and Q_i(S) for its native payoff on S∪{i}; put P_i(∅)=Q_i(∅)=0. The reward at Never and live payoffs are zero. Actions are publicly observed after each date, so the sole live history consists of everyone continuing. Players randomize privately and independently, and every player may replace its entire behavioral stopping law, including by Never. Write Γ_ij=P_i({j}) for distinct i,j and Γ_ii=0. In increasing bitmask order of nonempty rival subsets take

| recipient | passive P | joining Q |
|---|---|---|
| X | 1,3,5,−3,−2,0,−80 | −1,−1,1,−61/20,−1,−3000,−90 |
| Y | 1,−2,2,−2,20,−4,−60 | 0,t,1,q,0,0,2 |
| U | −1,2,2,−2,50,25,60 | 0,9/5,1,−2,0,−19/5,−6 |
| V | 1,−1,9,1,2,30,2 | 0,1,3,1,0,1,0 |

**Theorem.** For every independent choice of t,q∈ℝ the original game has a uniform-equilibrium payoff. All four own levels are arbitrary real numbers. Eight more original absorbing rewards can be changed arbitrarily: for either recipient X or Y, every coalition containing U and V is unused, giving four rewards for each of these recipients. On the intermediate range −1/2≤q≤5 the construction gives an exact terminal Nash calendar of period two, irrespective of t. Beyond this range it uses a sure first-stage quitter. If s_Y,s_V≥0 these sure openings also produce exact terminal Nash.

The same result holds simultaneously over the whole plane when the other tested native entries undergo sufficiently small perturbations satisfying Q_U({V})≤P_U({V}). The other eight entries remain free. The table has equality in that last guard. Its strict side contains a full-dimensional open set. Thus the perturbative statement contains open sets of tables with ten independent unconstrained native reward coordinates, as well as arbitrary own levels. The open set and results are relative to the ordinary sixty reward entries.

## The two-date calendar

Use A=(x,l,u,0) and B=(0,y,0,v), periodically. Take g∈[0,1], write u=(1−g)h and l=gh, and solve in z=(x,h,y,v). The continuation equations will always require these four coordinates strictly between zero and one. Define

    H_X=(1−l)(1−u), H_Y=(1−x)(1−u), H_U=(1−x)(1−l), H_B=(1−y)(1−v),
    p_X=l+3u+lu,       s_X'=−l−u+3lu,      b_X=y−3v,
    p_Y=x−2u+3xu,
    p_U=−x+2l+xl,       s_U'=(9l−4xl)/5,     b_U=2y−2v+25yv,
    p_V=x−l+u+9xl+30lu−38xlu,
    n_V=p_V+H_U(1−u)y.

The symbols s_X',s_U' denote the native immediate Quit offers at A. The four equations and three quiet inequalities are

    p_X+H_X(b_X+H_B s_X')−s_X' = 0,       −2v+(1−v)(p_Y+H_Y qv)−qv = 0,
    p_U+H_U(b_U+H_B s_U')−s_U' = 0,       −2y+(1−y)n_V = 0,
    b_X+H_B s_X'+ y+61v(1−y)/20 ≥ 0,
    b_U+H_B s_U'−(9y−10v−18yv)/5 ≥ 0,
    n_V−(l+u+2xl−xu−lu−2xlu) ≥ 0.

These equations are respectively X at A, Y at B, U at A, V at B, expressing indifference between Quit and always Continue over the two phases. For instance Y at B gets qv by Quit; by Continue she gets −2v+(1−v)(p_Y+H_Y qv). The quiet tests price X and U at B, and V at A, by making their Continue values dominate immediate Quit. Each displayed affine expectation follows by expanding the original product probabilities.

There is a solution z(g) continuous in g on [0,1] for each fixed q∈[−1/2,5], strictly satisfying all three quiet inequalities. The interval verification below also gives p_Y+H_Y qv−xu>0 at g=1. At g=0 leave Y quiet at A. Its Continue value p_Y+H_Y qv then dominates Quit whenever t≤T(0), with

    T(g)=[p_Y+H_Y qv−xu]/[(1−x)u],    0≤g<1.

For g>0 make Y mix at A. The offer of Quit there is xu+(1−x)u t, so its remaining indifference equation is t=T(g). This function is continuous and tends to +∞ as g↑1, since h>0 at the upper endpoint and the limiting numerator is positive. The intermediate value theorem covers every t>T(0) regardless of monotonicity or the sign of T(0). Every recipe selects g<1, so each owner faces a genuinely positive rival hazard in every two-date period. Geometric absorption under all unilateral replacements verifies the conditional optimality recursion even for literal Never, restores each own level and gives the claimed exact original terminal Nash equilibrium. Fixed-target passage to sufficiently long horizon averages follows directly from geometric rival absorption.

## The two sure openings

If q≤−2 take V as the sole sure quitter and the others quiet. U ties at −2; X prefers the passive −3 to −61/20; Y prefers −2 to q. For −2≤q≤−6/13 keep V sure and U quiet, and take odds X=(q+2)/20 and Y=1/20 (these are odds, not hazards). The passive-minus-joining margins for X against V and YV are 1/20 and −1; for Y against V and XV they are −2−q and 20. Thus X,Y are indifferent. U's margin is nonnegative at V and positive at XV,YV,XYV. For sure V, the odds numerator for passive-minus-Quit when its refusal is followed by its own singleton level is X−2Y+6XY≤0 exactly on the indicated range. This covers every q≤−1/2 with room to spare.

If q≥29/6, take Y sure, U quiet, and X,V with hazards 1/4 and 2/3. The passive-minus-Quit margins for X facing Y,YV are 2,−1, and for V facing Y,XY are −2,6. U strictly prefers Continue (each of its margins at Y,XY,YV,XYV is positive). Y's Quit offer is q/2; waiting with its own singleton level on survival gives native 29/12. This covers every q≥5 with room to spare. Neither sure construction uses t.

When a sure owner i unilaterally waits and no rival quits, append perpetual Continue if s_i≥0. Its best continued payoff is s_i and the head tests give exact Nash. For arbitrary signed s_i select instead a distinct blocker j, with P_Y({U})=−2 for Y or P_V({Y})=−1 for V. Have only that blocker use small constant hazard ε on every subsequent date. Waiting passively pays i less than s_i upon absorption, while its own deadline on any reached date gives at most s_i+ε max(0,Q_i({j})). Never encounters the blocker almost surely. Thus all behavioral replacements have terminal excess tending to zero. Other players always face the sure quitter at date one and cannot reach the tail. Prescribed first-exit payoffs are independent of ε, giving an original uniform payoff by quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto. This avoids any hypothesis about punishment-normality.

## Verification of the continuous chart

The supplied verifier evaluates the four displayed polynomials, their derivatives by the product rule, and the quiet guards. No parameter boxes are stored. Divide q∈[−1/2,5] into 512 equal intervals and g∈[0,1] into 256. For each two-dimensional cell with midpoint p_c=(q_c,g_c), use an approximate root z_c and approximate inverse M of its state Jacobian; all are treated as exact dyadic choices. Fixed positive radii r_i (the same for the whole grid) give a trial box Z=z_c+[-r,r]. The code computes, with outward enclosures,

    d=−M E(z_c,p_c)−(M E_p(z_c,p)) (p−p_c),
    C=I−M E_z(Z,p),
    σ_i=Σ_j sup|C_ij| r_j,        η_i=sup|d_i|+σ_i.

Here E is the four-component equation vector and p ranges over the cell in each derivative. The middle formula in d bounds a parameter line integral by the mean-value inequality. The tests give σ_i<r_i, η_i<r_i for every i. Thus z↦z−M E(z,p) is a uniform contraction from Z into itself, M is nonsingular, and each parameter point has a unique root in Z, continuously dependent on p, within η in each coordinate of z_c. Initial-point errors from numerical Newton iteration do not enter these bounds.

On each g-edge shared by consecutive boxes at the same q-grid index, the distance of their centers in each coordinate plus the successor box's η_i is smaller than the preceding r_i. Hence their solutions on the edge coincide by uniqueness in the preceding box. This glues all 256 intervals at each fixed q; globally continuous selection in q is not needed. The code also checks that all Z lie in (0,1)^4, all quiet guards are strictly positive, and the limiting numerator is positive in the top g cells.

All certification operations are interval sums, products, sign reversal and division by positive integers with endpoint rounding outwards by one IEEE binary64 spacing. The actual proof uses only dyadic bounds and the strict tests, independently of the accuracy of the proposed inverse. The mesh has exactly 131072 cells.

## Perturbations and unrestricted entries

For nearby native tables keep the same four scheduled indifferences, defined by the original product expansions, with Y at A not included. None uses t. They remain polynomials in z,q,g with continuously varying coefficients. Run the same finite certificate using the old centers and inverses; all its inclusions, contraction bounds, overlaps, probabilities, quiet guards and the endpoint numerator have strict slack. The Y-at-A Quit offer now equals the sum of its non-U-singleton contributions plus (1−x)u t; at g=1 its non-U-singleton part is x Q_Y({X}). Thus the continued positive endpoint-numerator check and the same interpolation cover every t. The continuity argument here is uniform over q,g on the compact rectangle and does not require perturbing t by a bounded amount.

For the sure branches write G_i(S)=P_i(S)−Q_i(S). For q≤P_Y({V}) V alone still works whenever G_U({V})≥0; both other quiet comparisons follow as above (the Y test can tie). For P_Y({V})≤q≤−1/2 keep V sure. Solve the two indifference equations with the odds of Y given by G_X(V)/(−G_X(YV)) and the odds of X by (q−P_Y(V))/G_Y(XV). All denominators are strictly positive near the center. U's quiet margin is uniformly strict on this compact set since Y's odds stay positive and its margin at YV is strict; the guard G_U(V)≥0 suffices at the solo opening. V's withdrawal comparison is uniformly strict up to q=−1/2: at the center its greatest odds numerator on this interval is −1/400. For q≥5 use the same sure-Y construction with X,V probabilities determined by the two nearby strictly opposite margin pairs. U stays strictly quiet since the sure Y is always present. The coefficient of q in Y's offer is the probability that V is the only quitting rival and stays positive. Its threshold is continuous at 29/6<5. The singleton blockers have strict native margins and persist. These tests establish the simultaneous perturbation claim.

Every support used, including each continuation after a refusal, omits at least one of U,V on every date. A unilateral deviation by X or Y cannot change that property. Hence no prescribed payoff or full cap for recipient X or Y uses its four terminal rewards on coalitions containing both U and V. The other players' incentives involve their own reward coordinates only. This proves full independence of the eight stated entries, without a smallness constraint.

The eight participant rewards to U or V on the same four coalitions can also be decreased independently by arbitrary amounts. None is seen in prescribed play. A unilateral replacement by its recipient can only lose from such a decrease, while every other player's comparison involves only its own rewards. This observation also applies to the sure-owner refusal continuation.

## A calibration without a stationary equilibrium or sure opening

Set all own levels to one, t=100 and q=0, and use all the other displayed entries literally. In the two-period chart one solution has hazards approximately A=(.81431942,.12140788,.04299601,0), B=(0,.45833499,0,.29412550). The uniform interval proof supplies exact roots at these parameter values. The following rational checks compare this game with other known reductions.

There is no winning sure opening, even with a punishment after refusal. In each of the 65 statuses with at least one sure player, assign the other coordinates to zero, one or a mixed interval. For quiet players impose P_i−Q_i≥0, and for mixed players impose equality, since these players face a sure rival. A necessary condition at a sure player is P_i−Q_i+H_i min_T Q_i(T)≤0, where H_i is rival survival and the minimum includes the empty set. The minimum is earned, or exceeded, by quitting immediately after refusing. The checker excludes these 65 systems in 123 rational Bernstein boxes. There is no exact stationary terminal equilibrium either. All-Continue fails at positive own levels. A sole stationary owner j is excluded by some outsider i having Γ_ij<min(0,Q_i({j})). For stationary supports of sizes two, three and four use B_i=P_i−(1−H_i)Q_i. All stationary candidates left after the sure tests have geometric absorption under each deletion, and require B_i≥0, with equality on the support. The checker excludes them in 24, 326 and 125 boxes respectively. Singularities at all-zero hazards are isolated using the additional active equality with row weights 1ᵀΓ_SS⁻¹. The Bernstein convex-hull property then excludes every positive point of the box when this scalar equality has all coefficients strictly positive apart from its zero at the origin.

The three-date theorem with an unrestricted core singleton row requires both twin singleton joining offers of the distinguished player to be nonpositive. For distinguished Y one is 100. For the other possible distinguished player U, the two passive twins would be X,V and P_U({X,V})=50 violates the requisite passive sign. The two-unrestricted-recipient alternating theorem first requires Q_a(T)≥P_a(T) on all nonempty subsets T of its two free rows; screening the twelve candidate ordered (a,b) leaves only (Y,X). Let the two free owners use zero hazards at Y's scheduled phase and use rival hazards (X,U,V)=(1/2,4/5,0) at the other phase. Then the scheduled P_o=Q_o=0,H_o=1 and the other H_p=P_p=1/10, Q_p=202/5. The required implication from A=H_o(P_p+H_p Q_o)−(Q_o−P_o)≥0 to B=P_p+H_p P_o−(1−H_oH_p)Q_p≥0 fails, since A=1/10 and B=−1813/50.

The projected orientation test can fail even after imposing its first-action bounds on the possible payoff. In native units set w=(−267/10,46/75,−9/5,1/50). This is (1/50)Z({X})+(89/300)Z({X,Y,U,V}), with the remaining convex mass at zero, where Z(T)=r(T)−s. At the trial row (0,0,1/50,9/10), the four Quit offers are (−566921/10000,1/5,−9/5,1/50). With m_i the minimum of zero and i's native exit rewards, the lower Wait bounds P_i+H_i m_i are (−7416/25,−193/25,−12/5,−24/25). Thus Quit offers are at most w, equal in the two active rows, and the lower Wait bounds are also at most w. On support YU take the indifference map in odds Φ_Y=102z_U, Φ_U=−z_Y/5. At z_Y=9,z_U=(46/75)/102, its two components equal the projection of w and both joining polynomials are positive. Its pair Jacobian determinant is +102/5, violating the nonpositive pair sign in that orientation test on its own payoff domain. The diagnosed failures refer to these named results. The other 58 coordinates of the example agree with the earlier unrestricted-core-singleton calibration.

## Verification and formalization

The block below runs with Python 3, NumPy and SymPy. Save it as verify.py and run `OPENBLAS_NUM_THREADS=1 python verify.py`. The first part checks every parameter rectangle using outward-rounded binary64 intervals and every required common-edge inclusion. With the displayed grid the greatest normalized contraction, image radius and edge radius are respectively below 0.473, 0.537 and 0.614. The second part uses exact rational arithmetic for the sure and stationary exclusions. Its subscripts index the four players in the order of the table. In a Lean treatment the phase comparisons and the two sure openings are elementary finite identities. The remaining proof obligations are outward interval enclosures for the four polynomial equations, the fixed point and edge gluing for each parameter strip, and the two displayed sign censuses. The terminal-to-uniform semantic endpoint is the checked declaration `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto` in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`. The existence of an equilibrium for arbitrary four-player quitting tables remains open.


```python
import numpy as np

def equations(z, q, g):
    x, h, y, v = z
    l = g * h
    u = (1 - g) * h
    rx = (1 - l) * (1 - u)
    ry = (1 - x) * (1 - u)
    ru = (1 - x) * (1 - l)
    rb = (1 - y) * (1 - v)
    px = l + 3 * u + l * u
    sx = -l - u + 3 * l * u
    bx = y - 3 * v
    py = x - 2 * u + 3 * x * u
    pu = -x + 2 * l + x * l
    su = (9 * l - 4 * x * l) / 5
    bu = 2 * y - 2 * v + 25 * y * v
    pv = x - l + u + 9 * x * l + 30 * l * u - 38 * x * l * u
    sa = pv + ru * (1 - u) * y
    eq = [px + rx * (bx + rb * sx) - sx, -2 * v + (1 - v) * (py + ry * q * v) - q * v, pu + ru * (bu + rb * su) - su, -2 * y + (1 - y) * sa]
    quiet = [bx + rb * sx + y + 61 * v * (1 - y) / 20, bu + rb * su - (9 * y - 10 * v - 18 * y * v) / 5, sa - (l + u + 2 * x * l - x * u - l * u - 2 * x * l * u)]
    return (eq, quiet, py + ry * q * v - x * u)

def newton(z, q, g):
    F = np.stack(equations(z, q, g)[0], axis=-1)
    J = np.stack([np.stack(equations([w + 1j * 1e-20 * (i == j) for j, w in enumerate(z)], q, g)[0], axis=-1).imag / 1e-20 for i in range(4)], axis=-1)
    return z - np.moveaxis(np.linalg.solve(J, F[..., None])[..., 0], -1, 0)

def initials(q, g):
    return np.array([0.65 - 0.05 * q + 0.13 * g, 0.11 - 0.017 * q + 0.06 * g, 0.3 - 0.017 * q + 0.16 * g, 0.248 / (1 + 0.35 * q) + 0.04 * g])

def get(q, g):
    z = initials(q, g)
    for _ in range(18):
        z = newton(z, q, g)
    err = max((np.abs(o).max() for o in equations(z, q, g)[0]))
    if err > 1e-08 or not np.all(np.isfinite(z)):
        raise ValueError(('numeric seed', err, z))
    return z
L = lambda x: np.nextafter(x, -np.inf)
U = lambda x: np.nextafter(x, np.inf)

class Iv:

    def __init__(self, l, h=None):
        self.l = np.asarray(l, dtype=float)
        self.h = self.l if h is None else np.asarray(h, dtype=float)

    def __add__(self, y):
        if isinstance(y, Jet):
            return NotImplemented
        if not isinstance(y, Iv):
            y = Iv(y)
        return Iv(L(self.l + y.l), U(self.h + y.h))
    __radd__ = __add__

    def __neg__(self):
        return Iv(-self.h, -self.l)

    def __sub__(self, y):
        return self + -y

    def __rsub__(self, y):
        return -self + y

    def __mul__(self, y):
        if isinstance(y, Jet):
            return NotImplemented
        if not isinstance(y, Iv):
            y = Iv(y)
        a, b, c, d = (self.l * y.l, self.l * y.h, self.h * y.l, self.h * y.h)
        return Iv(L(np.minimum(np.minimum(a, b), np.minimum(c, d))), U(np.maximum(np.maximum(a, b), np.maximum(c, d))))
    __rmul__ = __mul__

    def __truediv__(self, y):
        assert isinstance(y, int) and y > 0
        return Iv(L(self.l / y), U(self.h / y))

    def mag(self):
        return np.maximum(abs(self.l), abs(self.h))

class Jet:

    def __init__(self, v, d):
        self.v, self.d = (v, d)

    def __neg__(self):
        return Jet(-self.v, [-u for u in self.d])

    def __add__(self, y):
        if isinstance(y, Jet):
            return Jet(self.v + y.v, [a + b for a, b in zip(self.d, y.d)])
        return Jet(self.v + y, self.d)
    __radd__ = __add__

    def __sub__(self, y):
        return self + -y

    def __rsub__(self, y):
        return -self + y

    def __mul__(self, y):
        if isinstance(y, Jet):
            return Jet(self.v * y.v, [self.v * b + y.v * a for a, b in zip(self.d, y.d)])
        return Jet(self.v * y, [a * y for a in self.d])
    __rmul__ = __mul__

    def __truediv__(self, y):
        return Jet(self.v / y, [a / y for a in self.d])

def ident(v):
    return [Jet(c, [Iv(int(i == j)) for j in range(len(v))]) for i, c in enumerate(v)]

def cert(nq, ng, qstart=0, qend=None, ratio=1):
    if qend is None:
        qend = nq
    k, j = np.meshgrid(np.arange(qstart, qend), np.arange(ng), indexing='ij')
    q = Iv(L((11 * k - nq) / (2 * nq)), U((11 * (k + 1) - nq) / (2 * nq)))
    g = Iv(L(j / ng), U((j + 1) / ng))
    qc = (q.l + q.h) / 2
    gc = (g.l + g.h) / 2
    z = get(qc, gc)
    dq = 11 / 2 / nq
    dg = 1 / ng
    radii = 2 * ratio * (np.array([0.14, 0.11, 0.11, 0.2]) * dq + np.array([0.31, 0.09, 0.23, 0.12]) * dg)
    cen = [Iv(c) for c in z]
    box = [c + Iv(-r, r) for c, r in zip(cen, radii)]
    fj, guard, top = equations(ident(box), q, g)
    for b in box:
        assert np.all((b.l > 0) & (b.h < 1))
    for b in guard:
        assert np.all(b.v.l > 0)
    assert np.all(top.v.l[:, -1] > 0)
    jac = np.stack([np.stack(equations([w + 1j * 1e-20 * (i == a) for a, w in enumerate(z)], qc, gc)[0], axis=-1).imag / 1e-20 for i in range(4)], axis=-1)
    inv = np.linalg.inv(jac)
    f0 = equations(cen, Iv(qc), Iv(gc))[0]
    qp, gp = ident([q, g])
    deriv = equations(cen, qp, gp)[0]
    DD = [q - Iv(qc), g - Iv(gc)]

    def dot(row, vec):
        return sum((c * v for c, v in zip(row, vec)), Iv(0))
    contraction = 0
    rel = 0
    glue = 0
    for i, r in enumerate(radii):
        row = [Iv(inv[..., i, j]) for j in range(4)]
        shift = -dot(row, f0) - sum((dot(row, [f.d[j] for f in deriv]) * DD[j] for j in range(2)), Iv(0))
        coeff = [Iv(int(i == j)) - dot(row, [f.d[j] for f in fj]) for j in range(4)]
        scale = sum((Iv(c.mag()) * Iv(rho) for c, rho in zip(coeff, radii)), Iv(0))
        eta = (Iv(shift.mag()) + scale).h
        assert np.all(scale.h < r) and np.all(eta < r)
        contraction = max(contraction, np.max(scale.h / r))
        rel = max(rel, np.max(eta / r))
        dist = (Iv(z[i, :, 1:]) - Iv(z[i, :, :-1])).mag()
        edge = (Iv(dist) + Iv(eta[:, 1:])).h
        assert np.all(edge < r)
        glue = max(glue, np.max(edge / r))
    print(qstart, qend, 'bound', contraction, rel, glue, flush=True)
    return max(contraction, rel, glue) < 1
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import numpy as np
from sympy import Matrix
I = range(4)
rows = [([1, 3, 5, -3, -2, 0, -80], [-1, -1, 1, '-61/20', -1, -3000, -90]), ([1, -2, 2, -2, 20, -4, -60], [0, 100, 1, 0, 0, 0, 2]), ([-1, 2, 2, -2, 50, 25, 60], [0, '9/5', 1, -2, 0, '-19/5', -6]), ([1, -1, 9, 1, 2, 30, 2], [0, 1, 3, 1, 0, 1, 0])]
masks = [[m for m in range(16) if not m >> i & 1] for i in I]
P, Q = [[dict(zip(masks[i], map(F, [0] + rows[i][t]))) for i in I] for t in (0, 1)]
G = Matrix([[0 if i == j else P[i][1 << j] for j in I] for i in I])

def values(z):
    b = []
    c = []
    h = []
    for i in I:
        w = {m: prod((z[j] if m >> j & 1 else 1 - z[j] for j in I if i != j)) for m in masks[i]}
        p = sum((v * P[i][m] for m, v in w.items()))
        q = sum((v * Q[i][m] for m, v in w.items()))
        b.append(p - (1 - w[0]) * q)
        c.append(p - q)
        h.append(w[0])
    return (b, c, h)

def certify(C, pos, neg, zero):
    n = top = 0
    stack = [(C, 0, zero)]
    while stack:
        t, d, at0 = stack.pop()
        n += 1
        top = max(top, d)
        m = t.ndim - 1
        f = t.reshape(-1, t.shape[-1])
        if any(f.max(axis=0)[pos] < 0) or any(f.min(axis=0)[neg] > 0):
            continue
        if at0 and f[0, -1] == 0 and all(f[1:, -1] > 0):
            continue
        assert m and d < 75, (m, d)
        k = d % m
        u = t.swapaxes(0, k)
        if len(u) == 2:
            a, b = u
            e = (a + b) / 2
            halves = ([a, e], [e, b])
        else:
            a, b, c = u
            e = (a + b) / 2
            f = (b + c) / 2
            g = (e + f) / 2
            halves = ([a, e, g], [g, f, c])
        for j, half in enumerate(halves):
            stack.append((np.stack(half).swapaxes(0, k), d + 1, at0 and j == 0))
    return (n, top)

def sure():
    stats = []
    for status in product(range(3), repeat=4):
        if 2 not in status:
            continue
        mix = [i for i in I if status[i] == 1]
        C = []
        for t in product((0, 1), repeat=len(mix)):
            z = list(map(lambda k: F(k == 2), status))
            for i, v in zip(mix, t):
                z[i] = v
            _, c, h = values(z)
            for i in I:
                if status[i] == 2:
                    c[i] += h[i] * min(Q[i].values())
            C.append(c)
        C = np.array(C, dtype=object).reshape((2,) * len(mix) + (4,))
        stats.append(certify(C, [i for i in I if status[i] != 2], [i for i in I if status[i] != 0], False))
    print('sure heads', len(stats), sum((x for x, d in stats)), max((d for x, d in stats)))

def stationary():
    for j in I:
        assert any((G[i, j] < 0 and G[i, j] < Q[i][1 << j] for i in I if i != j))
    for l in (2, 3, 4):
        stats = []
        for S in combinations(I, l):
            W = list(map(F, G.extract(S, S).inv().T * Matrix([1] * l)))
            C = []
            for t in product(range(3), repeat=l):
                z = [F(0)] * 4
                for j, v in zip(S, t):
                    z[j] = F(v, 2)
                b, _, _ = values(z)
                C.append(b + [sum((w * b[i] for i, w in zip(S, W)))])
            C = np.array(C, dtype=object).reshape((3,) * l + (5,))
            for k in range(l):
                b = C.swapaxes(0, k)
                b[1] = 2 * b[1] - (b[0] + b[2]) / 2
            stats.append(certify(C, list(I) + [4], list(S) + [4], True))
        print('stationary supports', l, stats, 'nodes', sum((n for n, d in stats)))
if __name__ == '__main__':
    for k in range(0, 512, 16):
        assert cert(512, 256, k, k + 16)
    sure()
    stationary()
```
