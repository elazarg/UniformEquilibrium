# Three weak quitters under contact-preserving coalition bonuses

This theorem constructs exact stationary behavioral equilibria from raw
singleton signs and bonus slopes for every finite player set containing
three specified players. Participant pair and higher base rewards are
arbitrary. It includes a finite threshold, an explicit choice of slopes
from singleton data alone, signed recipient offsets and a fixed original
uniform-equilibrium target. The original games covered have sufficiently
large, finite coalition bonuses. No transport to the base game at zero
bonus, or solution of arbitrary Fin4, is asserted.

## 1. Exact raw data and theorem

Let I be a finite set containing distinct owners h,i,j. At each live date
owners independently choose Continue or Quit; the first nonempty coalition
absorbs at the specified bounded finite reward vector, paid at subsequent
stages. Live and Never rewards are zero. A unilateral deviation may replace
one entire behavioral strategy, including unbounded dates and Never.

Fix any finite native table Z with Z_a({a})=0 and define
Gamma_ab=Z_a({b}) for different owners. Require only these singleton signs:

    Gamma_hi=-a<0, Gamma_hj=-b<0,
    Gamma_ih=-g<0, Gamma_jh=-k<0,
    Gamma_ij=A>0,  Gamma_ji=B>0.                         (1)

Every participant pair and every higher base coordinate is arbitrary.
Choose positive row slopes rho and put

    Delta=rho_h-rho_i*a/g-rho_j*b/k > 0,
    C=a*A/g+b*B/k > 0,
    t0=C/Delta,
    u0=k*t0/(B+rho_j*t0),
    v0=g*t0/(A+rho_i*t0),
    W0=u0*v0+u0*t0+v0*t0.                               (2)

For each outsider l not in {h,i,j}, require

    Gamma_lh*t0+Gamma_li*u0+Gamma_lj*v0+rho_l*W0>0.      (3)

These are explicit finite arithmetic conditions on raw singleton rewards
and slopes. The numbers in (2) are supplied by the displayed formulas;
no equilibrium, root selection, continuation, or response cap is assumed.

For M>=0 and any signed finite offsets s_a set

    r_a^M(S)=Z_a(S)+rho_a*M*1_{|S minus {a}|>=2}+s_a,
                         S nonempty.                    (4)

**Theorem.** There is a finite-data threshold M0 such that EVERY M>=M0
and EVERY offset vector s admit an exact stationary terminal Nash profile
against all complete behavioral replacements, with exactly h,i,j active and

    q_h=t0/M+O(M^-2), q_i=u0/M+O(M^-2),
    q_j=v0/M+O(M^-2), q_l=0 for outsiders.               (5)

For each fixed game (4), the same profile and its one actual original payoff
work for every positive accuracy. A finite coefficient construction of M0
and the complete deviation/horizon consumer are given below. This is an
eventual family theorem, not backward transport to the base game at M=0.

## 2. Exact small-hazard field

For stationary product hazards define opponent survival H_a, native base
endpoints P_a=E[Z_a(T)] and Q_a=E[Z_a(T union {a})], and
K_a=Pr(|T|>=2), where T is the opponent quitting coalition. Because the
bonus depends only on T, the exact raised stationary field is

    F_a^M=(1-H_a)Q_a-P_a-rho_a*M*H_a*K_a.                (6)

Its sign is the actual Quit-minus-Continue Bellman sign: with joint
absorption d>0 and actual stationary value U,

    Q_a^M-(P_a^M+H_a U_a)=F_a^M/d.

Put epsilon=1/M and set

    q_h=epsilon*t, q_i=epsilon*u, q_j=epsilon*v,
    q_l=0 for every outsider.                           (7)

Each K_a is divisible by epsilon^2, H_a has constant term one, P_a has
zero constant term, and Q_a has zero constant term because Z_a({a})=0.
Thus F_a^M is divisible by epsilon after substitution and every F_a^M/epsilon
extends as a finite polynomial through epsilon=0. In fact (1-H_a)Q_a is
divisible by epsilon^2. Consequently the active limiting fields, in row
order i,j,h, are

    E_i=g*t-A*v-rho_i*t*v,
    E_j=k*t-B*u-rho_j*t*u,
    E_h=a*u+b*v-rho_h*u*v.                              (8)

For ANY outsider the limiting field is

    -Gamma_lh*t-Gamma_li*u-Gamma_lj*v
       -rho_l*(u*v+u*t+v*t).                            (9)

The probability of at least two of three weak opponents has leading
coefficient u*v+u*t+v*t; a three-way collision affects only higher powers.
All additional players have exactly zero hazard, so (8)--(9) apply to any
finite I. Arbitrary higher rewards contribute only higher powers. These
are exact polynomial limits, not a neglected-reward approximation.

## 3. Explicit positive root and nonsingular Jacobian

For t>0 the first two equations of (8) give

    u(t)=k*t/(B+rho_j*t), v(t)=g*t/(A+rho_i*t).

Their substitution into the last equation yields

    E_h=u(t)*v(t)*(C/t-Delta).

It vanishes exactly at the positive t0 in (2), giving u0,v0>0. Along
this solved curve its derivative at t0 is -Delta*u0*v0/t0<0. The
2-by-2 derivative block of (E_i,E_j) with respect to (u,v) has determinant
-(A+rho_i*t0)*(B+rho_j*t0). The Schur complement therefore gives

    det D_(u,v,t)(E_i,E_j,E_h) at (u0,v0,t0)
       =g*k*Delta*t0=g*k*C>0.                           (10)

This proves nonsingularity using only the singleton assumptions.

Apply the implicit function theorem to the polynomial scaled fields
(F_i/epsilon,F_j/epsilon,F_h/epsilon). It gives one analytic root
z(epsilon)=(u(epsilon),v(epsilon),t(epsilon)) near z0=(u0,v0,t0),
for every sufficiently small epsilon>=0. The variables remain positive,
and z(epsilon)-z0=O(epsilon), giving (5). Equation (3) makes every limiting
outsider field (9) strictly negative. A common small epsilon interval keeps
all outsider signs negative. Thus every active equality and every inactive
inequality are satisfied at an actual finite-M profile.

## 4. Finite-data threshold and full original-game consumer

Here is a quantitative choice, avoiding an unspecified IFT radius. Let L
be the Jacobian in (10), K=||L^-1||_infinity, and choose
0<R0<min(1,min(z0)/4). On |epsilon|<=1 and ||z-z0||<=R0, finite absolute
coefficient sums give C0,C1,C2>=1 bounding the epsilon derivative of the
scaled active system, its epsilon/z derivative, and the z-Lipschitz constant
of its z-Jacobian. Put

    r=min(R0,1/(4KC2)),
    epsilon0=min(1,1/(4KC1),r/(2KC0),
                   1/[2 max_v(z0_v+r)]).

The map z -> z-L^-1 E(epsilon,z) is a contraction with constant at most
1/2 on the radius-r ball and moves its center by at most r/2. This proves
one positive root for every epsilon in the interval, with
||z(epsilon)-z0||<=2KC0 epsilon. All hazards in (7) are at most one half.

If there are outsiders, let eta be the minimum of the strictly positive
left sides of (3). Polynomial derivative bounds plus the last displacement
estimate give C3>=1 bounding every outsider's scaled-field change by
C3 epsilon. Add eta/(2C3) to the minimum defining epsilon0. If there are
no outsiders, omit this term. Set M0=epsilon0^-1. Every constant is a finite
function of the raw table and slopes, and is independent of final offsets.

Put c=min(u0,v0,t0)/2>0. The positive root ball ensures each of the three
active hazards is at least c/M. Deleting any owner leaves at least two
active opponents, so opponents alone survive T live dates with probability
at most (1-c/M)^T under every complete unilateral replacement. Iterating
the actual Bellman inequalities leaves a bounded remainder tending to zero;
the policy equalities give the attained payoff. This proves exact terminal
Nash against every behavior, including Never and horizon-dependent choices.

Every such path absorbs almost surely. Signed offsets therefore add the
same constant to every prescribed and deviating terminal payoff, so the
profile is valid in (4) for either sign of s. Expected live duration is
at most M/c. With R=max_(a,S)|r_a^M(S)|, prescribed delivery error and
unilateral excess above the fixed terminal target are each at most
RM/(cN); actual N-stage Nash regret is at most 2RM/(cN). The game,
profile and target are fixed before accuracy. Neither a uniform bound in
M nor a limit target across changing reward tables is asserted.

## 5. Explicit slope choice from singleton data alone

Every table satisfying the six signs (1), with no restriction on the other
entries, admits positive slopes satisfying (2)--(3). Set rho_i=rho_j=1
and rho_h=1+a/g+b/k. Then Delta=1 and all three numbers in (2) are explicit
positive rational functions of the six singleton magnitudes. For each
outsider put S_l=Gamma_lh*t0+Gamma_li*u0+Gamma_lj*v0 and choose

    rho_l=1+max(0,-S_l)/W0.

The expression in (3) is then at least W0>0. Thus these slopes are produced
from singleton data alone, before using any participant or higher reward.
Their eventual threshold still depends on all finite base entries.

In particular, suppose Fin4 singleton signs consist of two disjoint mutual
positive favorite pairs, with every crossing singleton strictly negative.
Choose i,j as one favorite pair and h in the other. Then (1) holds. Hence
EVERY such base table, regardless of ALL participant pair and higher
rewards, has a produced positive contact-preserving bonus direction along
which all sufficiently large games admit the stationary triples above.
This statement concerns the modified games, not the arbitrary original base.

## 6. A finite four-player class outside the positive-joining-pair mechanism

Here is a complete original reward ray, including an explicit finite member.
For owners 0,1,2,3 put

    Gamma=[[0,3,-1,-1],[3,0,-1,-1],[-1,-1,0,3],[-1,-1,3,0]],
    J=[[0,0,2,-2],[0,0,-2,2],[-2,2,0,0],[2,-2,0,0]],
    rho=(1,2,5,3).

Define p_x(empty)=0, p_x({y})=Gamma_xy, and p_x(B)=0 for |B|>=2.
For x outside B, define d_x(empty)=0, d_x({y})=J_xy-Gamma_xy,
and d_x(B)=-1 for |B|=3. The remaining values are

| B | Values for the two outsiders |
| --- | --- |
| 01 | d_2=-1, d_3=-1 |
| 02 | d_1=-1, d_3=+1 |
| 03 | d_1=+1, d_2=-1 |
| 12 | d_0=+1, d_3=-1 |
| 13 | d_0=-1, d_2=+1 |
| 23 | d_0=-1, d_1=-1 |

These data specify all sixty original rewards by

    r_x^M(S)=1+p_x(S minus {x})+1_(x in S)*d_x(S minus {x})
                   +rho_x*M*1_(|S minus {x}|>=2), S nonempty.   (11)

Live and Never rewards are zero. The theorem applies with h=2,i=0,j=1:
a=b=g=k=1, A=B=3, Delta=2, C=6. The root and outsider data are

    (u0,v0,t0)=(1/3,1/2,3), W0=8/3,
    Gamma_32*t0+Gamma_30*u0+Gamma_31*v0+rho_3*W0=97/6.     (12)

Thus support012 is produced. No unordered pair has two positive joining
contacts: favorite pairs have (-3,-3), and each crossing pair has (+3,-1).
Also each hub has only one negative-singleton incoming owner whose joining
contact is positive. Both statements are invariant under positive recipient
scaling and relabeling, and under any alternative bonus representation,
since these bonuses preserve singleton rewards, participant-pair rewards,
and all joining contacts.

The finite threshold is certified as follows. At q=(epsilon*u,epsilon*v,
epsilon*t,0), epsilon=1/M, let F be the exact stationary field. The active
scaled limit is

    (F0,F1,F2)/epsilon -> (t-3v-tv, t-3u-2tu, u+v-5uv).

At (12) its Jacobian determinant is 6 and its inverse infinity norm is
K=23/2. The outsider scaled limit is -97/6. Choose R0=1/100; its center
box lies in |u|<=1, |v|<=1, |t|<=4. Absolute polynomial coefficient bounds
on that larger box and |epsilon|<=1 give

    C0=288, C1=524, C2=332, C3=23080805,
    r=1/15272, epsilon0=10^(-9).                            (13)

The complete exact code in Section 9 reconstructs the sixty rewards and
polynomials. It verifies every contraction, outsider and hazard inequality
from Section 4 using (13). Hence every finite

    M>=10^9                                                (14)

is admitted, including the fully specified rational table M=10^9. This is
not an example depending on an unspecified eventual threshold. For each
such table the target-relative horizon bounds are 6RM/N and actual regret
is at most 12RM/N. All higher base rewards in the general theorem remain
arbitrary; this explicit finite ray is only a calibration.

## 7. An intrinsic obstruction to every full-support stationary profile

For the calibration let mu_q(S) be the independent full quitter-set
probability at q, and let g_x(q)=E[d_x(B)] be the expected joining contact.
Every q in [0,1]^4 satisfies the exact identity

    sum_x (1-q_x)g_x(q)
      =-sum_(|S|=1 or 3)mu_q(S)-2mu_q(01)-2mu_q(23).       (15)

Indeed, singleton-column contact sums are -1; crossing-pair outsider sums
are zero; favorite-pair outsider sums are -2; and each triple has its sole
outsider contact -1. The empty and full coefficients vanish. The code also
checks (15) by exact polynomial expansion.

Let Q_x^M be the expected forced-Quit reward in the raised native table
before the own-one offset. Full-product averaging gives

    sum_x Q_x^M(q)
      =sum_S mu_q(S) sum_x Z_x^M(S union {x}) >= 0         (16)

for M>=1. The sixteen deterministic corner sums prove this: the empty
corner is zero; each singleton gives a zero column sum of J; each pair has
member premiums summing to zero and nonnegative inserted outsider rewards;
and each triple or full set has only nonnegative inserted entries because
rho_x*M+d_x(B)>=0 when |B|>=2. Negative individual pair premiums therefore
do not invalidate the aggregate inequality.

Put H_all=product_x(1-q_x). Since F_x=g_x-H_x Q_x^M,

    sum_x(1-q_x)F_x
      =sum_x(1-q_x)g_x-H_all sum_x Q_x^M.                 (17)

If all four q_x are positive and some q_x<1, the triple event omitting that
mixed owner has positive probability. Thus (15)--(17) give a strictly
negative sum. At a stationary equilibrium every proper positive owner's
F_x vanishes, while every sure owner's multiplier 1-q_x vanishes. This
contradicts (17). If all four owners quit surely, the grand-coalition
joining contact is -1 for every owner, again excluding equilibrium.
The same reasoning applies to the original offsets: deleting any owner
still ensures absorption, so terminal comparisons are translation invariant.

Therefore NO stationary equilibrium of this calibration has all four
hazards positive, for any M>=1. The proper triple produced above escapes
this entire strategy architecture. In conjunction with the invariant
singleton/pair tests, this is a concrete expansion beyond constructions
requiring mutual positive joining or a full-support stationary root.
It is not a characterization of all possible equilibria or of every
unspecified local continuation domain of another method.

## 8. Source correspondence, adapter and scope

The raw adapter is the six singleton sign tests, formulas (2)--(3), finite
coefficient threshold and constructed stationary root. No strategic root,
continuation, response law or equilibrium is supplied as input. The explicit
slope rule in Section 5 uses singleton data alone; the threshold may depend
on every finite base entry. At each fixed finite game the exact Bellman
consumer proves unrestricted terminal Nash and the displayed original
finite-horizon bounds, including every owner's Never option.

The tracked declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` consume a
stationary fixed point, full endpoint Nash, joint absorption and every-owner
opponent contraction. The actual-value identity is
`quittingTerminalPayoff_stationary_eq_rootExpectedPayoff` in
`UniformEquilibrium/Quitting/Stationary/Root.lean`. The proof here supplies
precisely those mathematical inputs. The new raw producer is ordinary
mathematics to be formalized; it is not claimed as a new checked Lean result.

A Lean implementation can separate the exact polynomial expansion, positive
root and Jacobian calculation, quantitative perturbation construction, and
finite-player stationary adapter. The calibration's rational constants and
full-support obstruction are independent finite tests. No general equilibrium
existence statement follows for the unchanged base game at M=0. The slope
condition Delta>0 is substantive; the construction does not assert coverage
when it fails. General four-player quitting-game UE remains open.

## 9. Standalone exact calibration check

The following complete Python code uses SymPy only. Save it as a local
Python file and run it with Python. It checks the literal calibration,
coefficient bounds and full-support obstruction exactly; the finite-player
proof and full behavioral consumer are Sections 1--5.

```python
"""Standalone exact three-weak calibration, threshold and intrinsic obstruction."""
from itertools import combinations, product
import sympy as s

I = tuple(range(4))
R = s.Rational
M = s.Symbol('M', nonnegative=True)
Gamma = s.Matrix([[0, 3, -1, -1], [3, 0, -1, -1],
                  [-1, -1, 0, 3], [-1, -1, 3, 0]])
J = s.Matrix([[0, 0, 2, -2], [0, 0, -2, 2],
              [-2, 2, 0, 0], [2, -2, 0, 0]])
rho = tuple(map(s.Integer, (1, 2, 5, 3)))


def subsets(items, empty=True):
    items = tuple(sorted(items))
    return [frozenset(B) for k in range(0 if empty else 1, len(items) + 1)
            for B in combinations(items, k)]


contacts = {}
for B, sign in zip(combinations(I, 2), (-1, -1, 1, 1, -1, -1)):
    lo, hi = sorted(set(I) - set(B))
    contacts[lo, frozenset(B)] = s.Integer(sign)
    contacts[hi, frozenset(B)] = s.Integer(-sign)
for B in (frozenset((0, 1)), frozenset((2, 3))):
    for i in set(I) - B:
        contacts[i, B] = -s.S.One


def delta(i, B):
    if not B:
        return s.S.Zero
    if len(B) == 1:
        j, = B
        return J[i, j] - Gamma[i, j]
    return contacts[i, B] if len(B) == 2 else -s.S.One


def passive(i, B):
    return Gamma[i, next(iter(B))] if len(B) == 1 else s.S.Zero


Z = {(i, S): passive(i, S - {i}) + (delta(i, S - {i}) if i in S else 0)
     for i in I for S in subsets(I, empty=False)}
ZM = {(i, S): Z[i, S] + (rho[i] * M if len(S - {i}) >= 2 else 0)
      for i in I for S in subsets(I, empty=False)}
assert len(ZM) == 60
assert all(Z[i, frozenset((i,))] == 0 for i in I)
assert all(J[i, j] + J[j, i] == 0 for i, j in combinations(I, 2))
assert all(sum(J[i, j] for i in I) == 0 for j in I)
assert not any(delta(i, frozenset((j,))) > 0 < delta(j, frozenset((i,)))
               for i, j in combinations(I, 2))
# No one-strong hub has two weak incoming joining contacts > 0.
assert all(sum(int(bool(Gamma[i, h] < 0 and delta(i, frozenset((h,))) > 0))
               for i in I if i != h) == 1 for h in I)

q = s.symbols('q0:4')

def fields(hazards):
    gaps, qs, hs = [], [], []
    for i in I:
        weights = {B: s.prod(hazards[j] if j in B else 1 - hazards[j]
                             for j in I if j != i)
                   for B in subsets(set(I) - {i})}
        gaps.append(s.expand(sum(w * delta(i, B) for B, w in weights.items())))
        qs.append(s.expand(sum(w * ZM[i, B | {i}] for B, w in weights.items())))
        hs.append(s.prod(1 - hazards[j] for j in I if j != i))
    return gaps, qs, hs


gap, Q, H = fields(q)
mu = {S: s.prod(q[j] if j in S else 1 - q[j] for j in I) for S in subsets(I)}
negative = -sum(mu[S] for S in subsets(I) if len(S) in (1, 3))
negative -= 2 * (mu[frozenset((0, 1))] + mu[frozenset((2, 3))])
assert s.expand(sum((1 - q[i]) * gap[i] for i in I) - negative) == 0
# Full-product averaging: sum Q >= 0 on the cube for every M >= 1.
for S in subsets(I):
    corner = s.expand(sum(ZM[i, S | {i}] for i in I))
    assert corner.subs(M, 1) >= 0 and s.diff(corner, M) >= 0
assert s.expand(sum(Q) - sum(mu[S] * sum(ZM[i, S | {i}] for i in I)
                            for S in subsets(I))) == 0
print('PASS all full-support stationary roots excluded, for every M>=1.')

# Certified finite membership in the three-weak producer.
eps, u, v, t = s.symbols('eps u v t')
variables = (eps, u, v, t)
hazards = (eps*u, eps*v, eps*t, s.S.Zero)
gs, qq, hh = fields(hazards)
scaled = [s.cancel((gs[i] - hh[i]*qq[i]).subs(M, 1/eps) / eps) for i in I]
assert all(s.denom(f) == 1 for f in scaled)
E = s.Matrix(scaled[:3])
leading = s.Matrix([t - 3*v - t*v, t - 3*u - 2*t*u, u + v - 5*u*v])
assert E.subs(eps, 0) == leading
center = {u: R(1, 3), v: R(1, 2), t: s.Integer(3)}
assert leading.subs(center) == s.zeros(3, 1)
assert scaled[3].subs(eps, 0).subs(center) == -R(97, 6)
z = (u, v, t)
L = leading.jacobian(z).subs(center)
assert L.det() == 6
K = max(sum(abs(L.inv()[i, j]) for j in range(3)) for i in range(3))
R0 = R(1, 100)
assert R0 < min(center.values()) / 4
radii = (1, 1, 1, 4)
def coefficient_bound(f):
    return sum(abs(c) * s.prod(R(radius)**power for radius, power in zip(radii, monomial))
               for monomial, c in s.Poly(s.expand(f), variables).terms())
C0 = max(s.S.One, *(coefficient_bound(s.diff(f, eps)) for f in E))
C1 = max(s.S.One, *(sum(coefficient_bound(s.diff(f, eps, zz)) for zz in z) for f in E))
C2 = max(s.S.One, *(sum(coefficient_bound(s.diff(f, zz, ww)) for zz in z for ww in z) for f in E))
C3 = max(s.S.One, coefficient_bound(s.diff(scaled[3], eps)) + 2*K*C0*sum(coefficient_bound(s.diff(scaled[3], zz)) for zz in z))
r = min(R0, 1/(4*K*C2))
bounds = (s.S.One, 1/(4*K*C1), r/(2*K*C0), 1/(2*max(value+r for value in center.values())), R(97, 6)/(2*C3))
exponent = 1
while R(1, 10**exponent) > min(bounds):
    exponent += 1
epsilon0 = R(1, 10**exponent)
assert K*(C1*epsilon0 + C2*r) <= R(1, 2)
assert K*C0*epsilon0 <= r/2
assert C3*epsilon0 <= R(97, 12)
assert epsilon0*max(value+r for value in center.values()) <= R(1, 2)
assert 10**exponent >= 100
print('PASS exact finite three-weak membership:')
print('center=(1/3,1/2,3), det L=6, K=',K)
print('C0=',C0,'C1=',C1,'C2=',C2,'C3=',C3,'r=',r)
print('epsilon0=',epsilon0,'; M0=10^'+str(exponent))
print('PASS: exact finite calibration, threshold and full-support obstruction.')
```
