# Contact-preserving coalition bonuses produce finite-player uniform equilibria

This is an ordinary-mathematical raw reward theorem for every finite number
of players. It produces an exact stationary equilibrium against complete
unilateral behavioral replacements, including Never, for every sufficiently
large finite bonus. The threshold is determined by finite reward data. The
new producer is not implemented or checked in Lean.

## 1. Data, quantifiers and conclusion

Let I be a finite player set containing distinct players i,j. A quitting
game has one live state. At each live date every player independently chooses
Continue or Quit. The first nonempty quitting coalition S absorbs at the
finite real vector r(S), which is paid at subsequent stages. Live play and
literal Never pay zero. Strategies may depend on the entire observed history;
a deviation replaces one complete behavioral strategy. No public correlation
device or restriction on private clocks is introduced.

Fix ANY finite real table Z_a(S), for every a in I and nonempty S contained
in I, with Z_a({a})=0. Extend it by Z_a(empty)=0. Fix arbitrary rho_a>0.
The only strategic base assumption is

    c_i=Z_i({i,j})-Z_i({j})>0,
    c_j=Z_j({i,j})-Z_j({i})>0.                            (1)

For M>=0 and an arbitrary finite signed vector s define original rewards

    r_a^M(S)=Z_a(S)+rho_a M 1_{|S minus {a}|>=2}+s_a,
                     S nonempty.                        (2)

The native table is the same expression with s=0. The bonus changes both
sides of every comparison between remaining outside a coalition and joining
it by exactly the same amount. No passive-reward sign, participant-reward
sign, singleton-matrix condition, matching, or ordering is assumed.

**Theorem.** There is a finite M0 depending only on Z and rho such that for
EVERY M>=M0 and EVERY signed offset vector s the original game (2) has an
exact stationary terminal Nash profile against ALL complete unilateral
behavioral replacements. The produced profile has q_i,q_j>=1/2. It is
independent of s. After deleting any one player, opponents alone absorb
with survival probability at most 2^(-t) through t live dates.

For each such fixed M,s, one profile and its actual terminal payoff u work
at every accuracy. If R=max_(a,S nonempty)|r_a^M(S)|, prescribed N-stage
average payoff differs from u by at most 2R/N in every coordinate, and
every unilateral N-stage payoff is at most u_a+2R/N. Actual N-stage Nash
regret is therefore at most 4R/N. This supplies one fixed original-game
uniform-equilibrium target, selected before accuracy.

Section 5 gives a finite-data threshold. No root, cap, continuation, policy,
strategic witness, or unspecified equilibrium threshold is an input. The
threshold need not be uniform over changing base rewards. This eventual
statement does not assert equilibrium at M=0 except in the pure-pair case
below, and does not settle the general quitting-game conjecture.

## 2. Exact stationary field

For a proposed independent hazard vector q, let T be the product-distributed
coalition of opponents of owner a. For native rewards define

    H_a=product_(v!=a)(1-q_v),
    P_a^M=E[Z_a(T)+rho_a M 1_{|T|>=2}],
    Q_a^M=E[Z_a(T union {a})+rho_a M 1_{|T|>=2}],
    K_a=Pr(|T|>=2),    g_a=Q_a^0-P_a^0,
    F_a^M=(1-H_a)Q_a^M-P_a^M
         =g_a-H_a Q_a^0-rho_a M H_a K_a.                 (3)

The cancellation in (3) is exact for every opponent coalition, including
simultaneous quits. Each quantity apart from the displayed M is a finite
polynomial in q.

If d=1-product_a(1-q_a)>0, the actual stationary native payoff is

    U_a=[q_a Q_a^M+(1-q_a)P_a^M]/d.

Direct subtraction gives

    Q_a^M-(P_a^M+H_a U_a)=F_a^M/d.                       (4)

Thus the stationary Bellman conditions are F_a=0 for 0<q_a<1,
F_a<=0 for q_a=0, and F_a>=0 for q_a=1. They concern the actual
stationary value, not a freely supplied continuation annotation.

For each outsider a in O=I minus {i,j}, put

    D_a=Z_a({i,j,a})-Z_a({i,j}),    delta_a=D_a/rho_a.

If O is empty or every D_a<=0, choose q_i=q_j=1 and q_a=0 for all
outsiders. The active joining gaps are c_i,c_j>0 and all outsider gaps
are D_a<=0. This is exact Nash for every M>=0, so take M0=0. It absorbs
immediately even after deleting any one player. This covers n=2 and all
nonpositive outsider cases, including zero contacts.

## 3. Scaling at two nearly sure quitters

Otherwise define the nonempty set of ALL maximizers

    delta=max_(a in O) delta_a>0,
    A={a in O: delta_a=delta},
    Delta(A)={p: p_a>=0, sum_(a in A)p_a=1}.

Write epsilon=M^(-1/2). For three positive variables z=(x,y,b) and p
in this simplex, prescribe

    q_i=1-x epsilon,     q_j=1-y epsilon,
    q_a=b epsilon p_a   (a in A),
    q_a=0               (a in O minus A).                (5)

After this substitution, the apparent pole epsilon^(-2) in (3) cancels
exactly. To verify this for arbitrary finite A, put

    W=product_(a in A)(1-epsilon b p_a),
    L=sum_(a in A)p_a product_(v in A minus {a})(1-epsilon b p_v).

For high owner i, H_i=y epsilon W and

    K_i=1-W-y epsilon^2 b L.                             (6)

Indeed epsilon b L is the probability of exactly one weak quitter;
at least two opponents quit either when two weak players quit, or when
exactly one does and j also quits. Since W=1-epsilon b+O(epsilon^2)
on the simplex, H_i K_i is divisible by epsilon^2 with leading quotient
yb. The formula for j has x in place of y. Every outsider's H has both
high-owner factors xy epsilon^2, while its K tends to one. These are finite
polynomial identities, including at every simplex face and for inactive
outsiders; no division by a simplex coordinate occurs.

Denote the resulting polynomial fields by Ftilde. At epsilon=0 they are

    Ftilde_i=c_i-rho_i yb,
    Ftilde_j=c_j-rho_j xb,
    Ftilde_a=D_a-rho_a xy       (a in O).                 (7)

The opponent coalition in the limit is respectively {j}, {i}, and {i,j},
which verifies the remaining terms in (7). The limiting system

    c_i-rho_i yb=0,  c_j-rho_j xb=0,  delta-xy=0

has the positive solution

    x0=sqrt(c_j rho_i delta/(c_i rho_j)),
    y0=sqrt(c_i rho_j delta/(c_j rho_i)),
    b0=sqrt(c_i c_j/(rho_i rho_j delta)).                 (8)

Its Jacobian in z has determinant -2 rho_i rho_j x0 y0 b0, which is
nonzero. All formulas are determined by the given rewards and weights.

## 4. Uniform root and simplex selection

For every p in Delta(A) impose exactly three equations

    E_1=Ftilde_i=0,
    E_2=Ftilde_j=0,
    E_3=sum_(a in A)p_a Ftilde_a/rho_a=0.                (9)

At epsilon=0 the system and its z-Jacobian at z0=(x0,y0,b0) are
independent of p on the WHOLE simplex. Let B be this invertible Jacobian.
On one sufficiently small closed positive ball about z0, for sufficiently
small epsilon>=0, the map

    z -> z-B^(-1)E(epsilon,z,p)

is a self-map with contraction constant at most 1/2, uniformly in p.
Polynomial dependence and compactness of the simplex give these bounds;
Section 5 makes the choices explicitly from finite data. The contraction
theorem yields one continuous solution z(epsilon,p), on the same ball for
every parameter. This does not patch unrelated local implicit branches.

Fix any small positive epsilon. Define the continuous vector

    f_a(p)=Ftilde_a(epsilon,z(epsilon,p),p)/rho_a,  a in A.

Equation (9) gives p dot f(p)=0 exactly. Consider the continuous simplex
self-map

    T_a(p)=(p_a+[f_a(p)]_+)/(1+sum_(v in A)[f_v(p)]_+).   (10)

Brouwer gives p*=T(p*). Let sigma=sum_a[f_a(p*)]_+. The fixed-point
equations are [f_a(p*)]_+=sigma p*_a. If sigma>0, each supported
coordinate has f_a(p*)=sigma p*_a>0, so

    p* dot f(p*)=sigma sum_a(p*_a)^2>0,

a contradiction. Thus every f_a(p*)<=0, and its zero weighted sum forces
f_a(p*)=0 whenever p*_a>0. These are precisely the active and inactive
Nash signs for ALL tied maximizers, including every simplex boundary.

For a in O minus A, the limiting field in (7) at z0 is the strictly
negative number rho_a(delta_a-delta). One common small epsilon bound
preserves all these signs uniformly in p, since there are finitely many
outsiders. Thus the three solved equations and (10) give every required
Bellman condition. The deterministic vector p* merely sets separate
Bernoulli hazards; it is not a shared random choice of a quitter.

## 5. A finite-data threshold

Use induced infinity norms. Put K=||B^(-1)|| and choose

    0<R0<min(1,min(z0)/4).

Finite absolute coefficient sums of the explicitly defined polynomial E
and its derivatives on |epsilon|<=1, ||z-z0||<=R0, 0<=p_a<=1 give finite
constants, chosen at least one, with

    C0 >= sup ||partial_epsilon E||,
    C1 >= sup ||partial_epsilon D_z E||,
    C2 >= a Lipschitz constant of D_z E in z.

Bounds on the ambient parameter cube are valid on its simplex subset.
Constancy of E(0,z0,p)=0 and D_z E(0,z0,p)=B is required only on the
simplex; no constancy off that simplex is asserted. Choose

    r=min(R0,1/(4KC2)),
    epsilon0=min(1,1/(4KC1),r/(2KC0),
                    1/[2 max_v(z0_v+r)]).               (11)

For this ball and interval the contraction derivative norm is at most
K(C1 epsilon0+C2 r)<=1/2, and its displacement at z0 is at most
KC0 epsilon0<=r/2. The ball is invariant and its coordinates positive.
The last bound in (11) makes x epsilon,y epsilon,b epsilon at most 1/2.
Also the contraction estimate gives ||z(epsilon,p)-z0||<=2KC0 epsilon.

If O minus A is nonempty, put

    gamma=min_(a in O minus A)rho_a(delta-delta_a)>0.

Coefficient bounds on the finitely many outsider fields, together with
the preceding displacement estimate, give C3>=1 such that their change
from the limiting fields is at most C3 epsilon, uniformly in p. Explicitly
one may take the maximum of the epsilon-derivative bound plus 2KC0 times
the sum of z-derivative bounds. Add gamma/(2C3) to the minimum (11).
If there is no omitted outsider, omit this bound.

Finally set M0=epsilon0^(-2). All constants are finite functions of the
fixed rewards and rho. No equilibrium or p* enters their definition.
Every M>=M0 corresponds to a positive epsilon within the common interval.
Both high hazards then lie in [1/2,1), each weak hazard in [0,1/2], and
every positive weak hazard is proper. This proves the claimed eventual
quantifier, not just a subsequence tending to infinity.

## 6. Complete behavioral and original-game consumer

For each fixed M>=M0 the produced stationary profile has positive joint
absorption. Formula (4) identifies its actual value U and the endpoint
Nash inequalities. At every live history either action of player a has
continuation value at most U_a, with equality on every prescribed action.
After deleting any one player, at least one of i,j remains and quits
independently with probability at least 1/2 each live date. Opponent
survival is therefore at most 2^(-t), uniformly over any complete
replacement, including Never, arbitrarily late decisions, and strategies
selected separately for different horizons.

Iterating the Bellman inequalities leaves a bounded unresolved continuation
term tending uniformly to zero at this rate. Hence every replacement's
native terminal payoff is at most U_a. Iterating the policy equality
shows that the prescription attains U. This proves full terminal Nash;
the argument is not limited to one-step or stationary deviations.

Every such prescribed or deviating path absorbs almost surely. Adding s_a
to every nonempty reward in row a therefore adds exactly s_a to each of
its expected terminal payoffs, for either sign of s_a. The same profile
is consequently exact terminal Nash for (2). No affine invariance is
asserted for arbitrary profiles with positive nonabsorption probability.

The expected number T of zero-paying live stages, including the absorption
decision, is at most sum_(t>=0)2^(-t)=2 under every replacement. A realized
N-stage average differs from the final absorbing reward by at most
R min(T,N)/N, so its expectation differs by at most 2R/N. Exact terminal
Nash gives both target-relative bounds and their 4R/N regret consequence.
One profile and its one actual target are fixed before accuracy. Positive
recipient scaling also preserves the construction and comparisons.

## 7. A fully specified four-player calibration

Here is an exact base Z, with players 0,1,2,3 and rho=one:

| S | Z_0(S) | Z_1(S) | Z_2(S) | Z_3(S) |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 3 | -1/25 | -69/100 |
| 1 | 2 | 0 | -69/100 | -1/25 |
| 2 | -69/100 | -1/25 | 0 | 5 |
| 3 | -1/25 | -69/100 | 4 | 0 |
| 01 | 1 | 2 | 1 | 1 |
| 02 | 1/100 | 1 | 1/100 | 1 |
| 03 | 1/100 | 1 | 1 | 1/100 |
| 12 | 1 | 1/100 | 1/100 | 1 |
| 13 | 1 | 1/100 | 1 | 1/100 |
| 23 | 1 | 1 | 3 | 4 |
| 012 | 2 | 1/100 | 0 | 1 |
| 013 | 0 | 2 | 1 | 2 |
| 023 | 0 | 1 | 0 | 199/100 |
| 123 | 1 | 2 | 2 | 0 |
| 0123 | 0 | 0 | 0 | 0 |

Choose i=0,j=2. Then c_i=7/10,c_j=1/20, D_1=-99/100 and D_3=99/100.
Only outsider 3 maximizes the normalized contact. The produced support
is exactly {0,2,3}. The center (8) has squared coordinates

    x0^2=99/1400, y0^2=693/50, b0^2=7/198.

Exact bounds are 1/4<x0<1/3, 3<y0<15/4, and 1/6<b0<1/5. Choose
R0=1/100. Its ball lies inside |x|<=1, |y|<=4, |b|<=1. The limiting
Jacobian inverse is

    [ x/(2yb)   -1/(2b)   -1/(2y) ]
    [ -1/(2b)   y/(2xb)   -1/(2x) ]
    [ -1/(2y)   -1/(2x)   b/(2xy) ].

The displayed center bounds give K<64. Using 64 as an upper bound is
valid in every estimate. Direct absolute coefficient sums on the box
|epsilon|<=1, |x|<=1, |y|<=4, |b|<=1 give

    C0=30919/100, C1=64231/100, C2=7312/25,
    C3=101212336069/2500, r=25/1871872.                  (12)

The complete exact arithmetic in Section 9 reconstructs the table and all
four stationary polynomials and verifies these bounds. The rational choice
epsilon0=10^(-10) satisfies every inequality (11), preserves at least
99/100 of negative inactive margin, and makes all hazards legal. Thus

    M0=10^20                                                   (13)

is a sufficient concrete threshold. In particular (2) at M=10^20 and
s_a=1 for all a is one fully specified finite reward table covered here.
The large bound is a conservative proof constant, not a sharp threshold.

This calibration has NO stationary equilibrium in which all four players
have positive Quit hazards, for any M>=0. To see this, write
d_a(T)=Z_a(T union {a})-Z_a(T) and g_a=E[d_a(T)]. The bonus preserves
every d. The table has

    sum_(a notin T)d_a(T)=-1/4   when |T|=1,
    sum_(a notin T)d_a(T)=0      when |T|=2,
    d_a(I minus {a})=-1.

Expanding the independent coalition probabilities therefore gives

    sum_a(1-q_a)g_a
      =-1/4 sum_j q_j product_(v!=j)(1-q_v)
       -sum_a(1-q_a)product_(v!=a)q_v.                  (14)

If all q_a>0 and at least one is less than one, the second sum is strictly
positive, so (14) is negative. All native participant rewards in this table
are nonnegative, including after the bonus. At a stationary Nash point,
each proper active owner has F_a=0, hence g_a=H_a Q_a>=0; sure owners
have zero weight 1-q_a. This contradicts (14). If all q_a=1, each owner
has the negative joining gap -1 and can profitably Continue. Signed row
offsets do not remove this exclusion: with four positive stationary
hazards, opponents absorb almost surely under every replacement, so the
same terminal comparison is preserved.

Thus the new producer genuinely needs a proper subset of active players
on this explicit table. Existence results whose produced stationary
profiles have every player active cannot cover it. This is a restriction
on stationary strategy coverage, not a counterexample to equilibrium:
the constructed stationary triple works at every M>=10^20.

As a simple negative control for omitting outsider conditions, the pure
pair {0,2} is not Nash at ANY bonus: owner 3 has joining gain 99/100.
The weak third hazard in the proof is essential. The proof's simplex step
also retains all positive ties rather than discarding them by perturbation.

## 8. Source correspondence and formalization boundary

The actual-data contribution is the explicit polynomial scaling, uniform
three-variable root, complementarity selection on a finite simplex, and
finite-data threshold. They supply a Bernoulli root, its actual payoff,
all endpoint Nash inequalities, and every-owner opponent contraction.

The existing declarations
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
in `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean` consume
exactly such data for an arbitrary finite player type. The fixed-payoff
identity is represented by
`quittingTerminalPayoff_stationary_eq_rootExpectedPayoff` in
`UniformEquilibrium/Quitting/Stationary/Root.lean`. Those conditional
consumers do not supply the new raw producer or threshold. No new Lean
implementation, instance, build, or unrestricted conjecture closure is
claimed here.

## 9. Complete exact calibration check

The following executable Python uses SymPy for exact rational polynomial
arithmetic. It checks the finite coefficient bounds and numerical threshold;
the general finite-player theorem rests on the proof above.

```python
"""Exact finite threshold for the paired-contact perturbation of the H1 table.

Produces coefficient bounds for the reviewed three-variable contraction proof.
All assertions use rational/symbolic arithmetic; no numerical root is assumed.
"""
from itertools import combinations
import sympy as s

F = s.Rational
players = range(4)
A = [list(map(F, row)) for row in
     [[0, 1, '-.7', '-.05'], [1, 0, '-.05', '-.7'],
      ['-.05', '-.7', 0, 1], ['-.7', '-.05', 1, 0]]]
J = [[F(0) if i == j else (F(i + 1) if j == (i ^ 1) else F(1, 100))
      for j in players] for i in players]
signs = dict(zip(combinations(players, 2), [-1, -1, 1, 1, -1, -1]))
Z = {}
for mask in range(16):
    for i in players:
        opponents = tuple(j for j in players if j != i and mask >> j & 1)
        passive = (F(0) if not opponents else
                   A[i][opponents[0]] + J[i][opponents[0]] if len(opponents) == 1
                   else F(1))
        if not opponents:
            contact = F(0)
        elif len(opponents) == 1:
            contact = -A[i][opponents[0]]
        elif len(opponents) == 3:
            contact = F(-1)
        else:
            contact = signs[opponents] * (1 if i == min(
                j for j in players if j not in opponents) else -1)
        Z[i, mask] = passive + (contact if mask >> i & 1 else 0)
Z[1, 7] = F(1, 100)
Z[3, 13] = F(199, 100)
assert all(Z[i, 1 << i] == 0 for i in players)
assert all(Z[i, mask] >= 0 for i in players for mask in range(1, 16)
           if mask >> i & 1)
assert [Z[i, 5 | (1 << i)] - Z[i, 5] for i in (1, 3)] == [-F(99, 100), F(99, 100)]

eps, ai, aj, b = s.symbols('eps ai aj b')
variables = (eps, ai, aj, b)
q = (1 - ai * eps, 0, 1 - aj * eps, b * eps)
fields = []
for i in players:
    masks = [m for m in range(16) if not m >> i & 1]
    weights = {m: s.prod(q[j] if m >> j & 1 else 1 - q[j]
                         for j in players if j != i) for m in masks}
    H = s.prod(1 - q[j] for j in players if j != i)
    P = sum(weights[m] * Z[i, m] for m in masks)
    Q = sum(weights[m] * Z[i, m | (1 << i)] for m in masks)
    K = sum(weights[m] for m in masks if m.bit_count() >= 2)
    scaled = s.cancel(H * K / eps**2)
    assert s.denom(scaled) == 1
    fields.append(s.expand(Q - P - H * Q - scaled))
E = s.Matrix([fields[0], fields[2], fields[3]])
z = (ai, aj, b)
leading = s.Matrix([F(7, 10) - aj * b, F(1, 20) - ai * b,
                    F(99, 100) - ai * aj])
assert E.subs(eps, 0) == leading
assert fields[1].subs(eps, 0) == -F(99, 100) - ai * aj

# The exact center has squares 99/1400, 693/50, 7/198.
squares = (F(99, 1400), F(693, 50), F(7, 198))
lower = (F(1, 4), F(3), F(1, 6))
upper = (F(1, 3), F(15, 4), F(1, 5))
assert all(lo**2 < sq < hi**2 for lo, sq, hi in zip(lower, squares, upper))
R0 = F(1, 100)
assert R0 < min(lower) / 4
assert all(hi + R0 < box for hi, box in zip(upper, (1, 4, 1)))
L = leading.jacobian(z)
assert s.factor(L.det()) == -2 * ai * aj * b
inverse = s.Matrix([[ai / (2 * aj * b), -1 / (2 * b), -1 / (2 * aj)],
                    [-1 / (2 * b), aj / (2 * ai * b), -1 / (2 * ai)],
                    [-1 / (2 * aj), -1 / (2 * ai), b / (2 * ai * aj)]])
assert s.simplify(L * inverse) == s.eye(3)
row_bounds = [upper[0] / (2 * lower[1] * lower[2]) + 1 / (2 * lower[2]) + 1 / (2 * lower[1]),
              1 / (2 * lower[2]) + upper[1] / (2 * lower[0] * lower[2]) + 1 / (2 * lower[0]),
              1 / (2 * lower[1]) + 1 / (2 * lower[0]) + upper[2] / (2 * lower[0] * lower[1])]
Kbound = F(64)
assert max(row_bounds) < Kbound

def coefficient_bound(expression):
    return sum(abs(coefficient) * s.prod(F(radius)**power for radius, power in
               zip((1, 1, 4, 1), monomial))
               for monomial, coefficient in s.Poly(expression, variables).terms())

C0 = max(F(1), *(coefficient_bound(s.diff(e, eps)) for e in E))
C1 = max(F(1), *(sum(coefficient_bound(s.diff(e, eps, v)) for v in z) for e in E))
C2 = max(F(1), *(sum(coefficient_bound(s.diff(e, v, w)) for v in z for w in z) for e in E))
C3 = max(F(1), coefficient_bound(s.diff(fields[1], eps)) +
         2 * Kbound * C0 * sum(coefficient_bound(s.diff(fields[1], v)) for v in z))
r = min(R0, 1 / (4 * Kbound * C2))
bounds = (F(1), 1 / (4 * Kbound * C1), r / (2 * Kbound * C0),
          F(1, 8), F(198, 100) / (2 * C3))
exponent = 1
while F(1, 10**exponent) > min(bounds):
    exponent += 1
epsilon0 = F(1, 10**exponent)
assert Kbound * (C1 * epsilon0 + C2 * r) <= F(1, 2)
assert Kbound * C0 * epsilon0 <= r / 2
assert C3 * epsilon0 <= F(99, 100)
assert 4 * epsilon0 <= F(1, 2)
M0 = 10**(2 * exponent)
assert M0 >= 10000
print('exact paired-contact base, polynomial extension, center and inverse: PASS')
print('C0 =', C0, 'C1 =', C1, 'C2 =', C2, 'C3 =', C3)
print('K <=', Kbound, 'R0 =', R0, 'r =', r)
print('epsilon0 =', epsilon0, '; valid threshold M0 = 10^' + str(2 * exponent))
print('uniform contraction, inactive gap and all hazard bounds: PASS')
```
