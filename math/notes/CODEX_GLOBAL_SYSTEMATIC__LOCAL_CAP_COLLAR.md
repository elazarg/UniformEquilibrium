# Signed local cap collars exclude absorbing zero faces

Owner: CODEX_GLOBAL_SYSTEMATIC. Proved ordinary mathematics, independently
[reviewed](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_LOCAL_COLLAR_REVIEW.md)
and [adversarially checked](../feedback/CODEX_GLOBAL_SYSTEMATIC__LOCAL_CAP_COLLAR__BY_CODEX_COLLAR_ADVERSARY.md).
The reviews cover the signed-pair generalization at their pinned versions.
Not Lean checked and not exported. This excludes specified boundary faces
from raw reward tests; it does not construct an equilibrium or settle Fin4.

One supported weight now needs positive weighted participant-pair drift,
not individually positive pairs. Caps may have either sign throughout the
proof. This subsumes the earlier local theorem. The signed example below
passes the new tests while EVERY support fails the earlier positive-pair
hypothesis and EVERY weight fails the older
[global weighted-Quit criterion](CODEX_COORDINATOR__WEIGHTED_CAP_ABSORPTION_COERCIVITY.md).
The calibration application and its sparse-face conclusion are retained.

## 1. Native semantics and raw tests

Let n>=2 independent private stopping laws take values in Nat plus Never.
The first nonempty coalition A pays Z(A), with native own singleton,
live, and AllNever rewards zero. Let |Z_i(A)|<=M, M>=1. B_i is the full
cap over every unilateral complete law. Let N_i be the original Never
mass and nu=product N_i. Write Gamma_ij=Z_i({j}), J_ij=Z_i({i,j}) for
i!=j, with both diagonals zero. For q in [0,1]^n, let Q_i(q) be the
forced-Quit polynomial, P_i(q) the passive nonempty-opponent payoff,
and H_i(q)=product_(j!=i)(1-q_j). Let K_abs be the closure of actual
absorbing prescribed-payoff/full-cap pairs, where absorbing means nu=0.

Suppose a probability row z has support S and satisfies:

    z Gamma >= gamma*1,       z J >= mu*1,      gamma,mu>0;       (1)
    {q in [0,1]^n: Q_i(q)<=0 for all i in S}={0}.              (2)

These are raw finite-polynomial tests. Individual participant pairs may
have either sign. The earlier positive-pair hypothesis is a special case:
if J_ij>=m>0 for every i in S and j!=i, then

    (zJ)_j>=m*(1-z_j)>=m*(1-max_i z_i)>0.

The last strict inequality follows from zGamma>0 and Gamma_ii=0, which
forbid singleton support. A finite sufficient test for root isolation is
still available: some a in S has Z_a(A)>0 on every nonsingleton coalition
containing a, and some b in S different from a has J_ba>0. Then Q_a>0
if any opponent of a acts, and Q_b>0 if only a acts.

**Theorem.** Under (1)--(2), there is a table-dependent delta>0 such that
every actual profile satisfies

    max_(i in S) B_i >= delta*(1-nu).                          (3)

Every actual absorbing profile has supported maximum >delta. Thus every
point of the absorbing semantic closure has supported maximum >=delta.
In particular, that closure excludes the face B_i=0 for all i in S,
regardless of all other caps and debts. The augmented closure retaining
N also satisfies (3); a point with supported maximum zero is AllNever,
with all payoffs and caps zero and all N_i=1.

## 2. The signed cap collar and absorption bound

Set kappa=mu/2 and C=1+2M/kappa, and choose

    rho=min(1/4,mu/(3M),gamma/(3M),1/(2C)).

Put s=sum q_i. Singleton-event expansion, with all collision terms
included, gives for every i

    |Q_i-(Jq)_i| <= (3M/2)s^2,
    |P_i-(Gamma q)_i| <= (3M/2)s^2,
    Q_i >= -M s,             |P_i| <= M s.

Thus when s<=rho,

    zQ>=kappa*s,             zP>=gamma*s/2.                   (4)

By (2), compactness gives

    d0=min_(s>=rho) max_(i in S) Q_i(q)>0;     eta=d0/2.

For any actual profile with b=max_S B_i<=eta, Q_i<=B_i forces s<rho.
Writing w=zB, (4) then gives

    0<=kappa*s<=w<=b,
    B_i>=-M w/kappa,
    sum_i z_i|B_i|<=Cw,
    B_i<=A w for i in S,     A=(1+M/kappa)/min_(i in S)z_i.    (5)

For the third inequality, the weighted negative part is at most Ms;
for the fourth, z_i B_i is bounded above by w plus that negative part.
No supported cap is asserted to be nonnegative.

Define

    K=2(A+M/kappa),
    delta=min(eta,eta/K,gamma/(4C),gamma/8)>0.                 (6)

Start with b<=delta. Since s<rho<=1/4, every conditional tail law is
well-defined. Let B^+ be its full caps and v=zB^+. The exact complete
response recursion is

    B_i=max(Q_i,P_i+H_i B_i^+).

As H_i>=1-s>=1/2 and B_i+Ms>=0, it gives

    B_i^+ <= (B_i-P_i)/H_i <= 2(B_i+Ms) <= K w <= eta.

Apply (5) afresh to that actual tail. In particular v>=0 and
sum_i z_i|B_i^+|<=Cv. The Continue branch and (4) yield

    w>=gamma*s/2 + v - s sum_i z_i|B_i^+|
      >=gamma*s/2+(1-Cs)v.

Here 1-Cs>=1/2 and w<=gamma/(4C), so

    0<=v<=w-(gamma/4)s<=w.                                   (7)

For example subtract the resulting upper bound for v from w:
w-v >= s(gamma/2-Cw)/(1-Cs) >= gamma*s/4.

The invariant is supported maximum <=eta and weighted cap <=delta,
not a decreasing supported maximum. Equations (5)--(7) therefore repeat
at every date. Summing gives

    sum_t sum_i q_(t,i)<=4w_initial/gamma,
    1-nu<=4w_initial/gamma<=4b/gamma.

Consequently b<=delta implies nu>=1/2 and proves (3) there. For b>delta,
(3) is immediate. Every actual profile has b>=0 by (2) at its first
root (or Q=0 when that root is zero). Continuous passage gives all
closure statements. Finally |U_i|,|B_i|<=M(1-nu): any own response pays
zero when all opponents use Never, and otherwise its absolute reward is
bounded by M. Thus b=0 forces the AllNever augmented tuple.

## 3. Calibration and the original-level bridge

Use players0,1,2,3, the native singleton matrix

    Gamma=[0,3,-1,3;2,0,1,-3;2,-2,0,-1;-1,-2,1,0],

and additive passive rewards. Every proper nonsingleton participant reward
in rows0,1,2,3 is respectively e,h1,e,h3. The native grand reward is
(10,-2,-e,-1). Assume independently

    0<e,h1,h3<=1/10.

Take S={0,1,3} and z=(9,7,0,8)/24. Direct multiplication gives

    z Gamma=(6,11,6,6)/24,

so gamma=1/4 works. Supported pair rewards are strictly positive, with
m=min(e,h1,h3). Thus mu=m*(1-max z)>0 works in the weighted-pair test.
Every nonsingleton participant reward of player0 is strictly positive,
including its grand reward10. The anchor test in Section1 supplies root
isolation. Every native reward has absolute value at most10, so M=10 works in the general constants.

It follows, for this ENTIRE independent-premium range, that

    max(B0,B1,B3)>=delta*(1-nu),
    max(B0,B1,B3)>=delta  on K_abs.                        (8)

In particular the hard ray(e,h1,h3)=(beta,beta/10,beta) satisfies this
conclusion for every 0<beta<=1/10. The bound depends on the fixed premiums;
no uniform positive lower bound as beta tends to zero is claimed.

The original-level bridge holds more generally. Let ell_i>=0 and set
r_i(A)=ell_i+Z_i(A) on every nonempty coalition, while original live and
Never rewards remain zero. Every finite deadline response absorbs surely,
so its original offer is ell_i plus its native offer. The native Never
offer is the limit of finite deadline offers, since own native singletons
are zero. The original Never offer is that native offer plus
ell_i*(1-opponentNever), and hence is at most ell_i+B_i(native).
Consequently, for EVERY profile,

    B_i(original)=ell_i+B_i(native),
    U_i(original)=ell_i*(1-nu)+U_i(native).

On absorbing profiles, and their semantic closures, both vectors translate
exactly by ell. Thus the calibration with ell_i=1 has no absorbing cap face
B0=B1=B3=1. For arbitrary ell>=0 the corresponding supported face is
B_i=ell_i. This does not shift literal Never payoffs; nonnegative ell is
used in the cap inequality and is part of this bridge's hypothesis.

The proof also allows arbitrary finite passive nonsingleton rewards: only
the singleton drift in Section1 is used, and M then enlarges as necessary.
Likewise, arbitrary finite nonsingleton participant rewards outside row0
and the supported pairs are allowed. This is a boundary-face theorem for
those broader tables, not a new UE existence class.

## 4. Calibration separation from the global weighted-Quit criterion

For the displayed calibration, the older criterion asks for a probability
vector v>=0 with v Gamma strictly positive and

    K_A=sum_i v_i Z_i(A union {i})>0

on EVERY nonempty A. No such v exists throughout 0<e,h1,h3<=1/10.
Let epsilon=max(e,h1,h3). The two triple tests imply

    0<K_023=e(v0+v2)+h3*v3-2v1,       v1<epsilon/2,
    0<K_012=e(v0+v2)+h1*v1-v3,        v3<epsilon.

The positive singleton columns2 and1 then give

    v0<v1+v3<3epsilon/2,
    v2<(3/2)v0-v3<9epsilon/4.

Summing yields 1=sum v_i<21epsilon/4<=21/40, a contradiction.
Thus (8) does not merely instantiate the older globally positive
weighted-Quit test with a different weight.

## 5. A strict signed-pair example and an open family

Use four cyclic labels 0,1,2,3, with subscripts read modulo four. Set

    a=(1/7,1/2,6,6/5),       b=(4/5,2/3,3/5,1/4).

For every coalition A containing i define its participant reward by

    Z_i(A)=[1_(i+1 in A)-a_i 1_(i-1 in A)]
              [1-b_i 1_(i+2 in A)].                           (9)

This includes native own singleton zero. Its Quit polynomials are exactly

    Q_i(q)=(q_(i+1)-a_i q_(i-1))(1-b_i q_(i+2)).              (10)

Every second factor is positive. Thus Q<=0 implies
q1<=a0*q3, q3<=a2*q1 and q2<=a1*q0, q0<=a3*q2. Since a0*a2=6/7<1
and a1*a3=3/5<1, all q vanish. This proves (2).

Take singleton rewards

    Gamma=[0,3,-1,3; 2,0,1,-3; 2,-2,0,-1; -1,-2,1,0]

and choose arbitrary finite passive rewards on larger coalitions.
With z=(13,9,2,6)/30, direct multiplication gives

    z Gamma=(16,23,2,10)/30,
    z J=(1/20,1/30,3/50,1/210).

Hence (1) holds. The theorem excludes the entire all-zero-cap face of
the absorbing carrier for this signed table, regardless of the passive
nonsingleton completion.

No nonempty support can satisfy the previous individual-positive-pair
hypothesis: EVERY row i has J_(i,i-1)=-a_i<0.
Nor can any nonnegative probability weight v pass the older GLOBAL
weighted-Quit criterion K_A=sum_i v_i Z_i(A union {i})>0 for every
nonempty A. The exact four-test identity is

    1619 K_{3}+715 K_{2,3}+500 K_{1,2,3}+1142 K_{0}
       = -166 sum_i v_i = -166.                              (11)

For explicit verification, the four vectors (Z_i(A union {i}))_i are

    A={3}:     (-1/7,0,1,0),
    A={2,3}:   (-1/35,1/3,1,-6/5),
    A={1,2,3}: (6/35,1/3,-5,-9/10),
    A={0}:     (0,-1/2,0,1).

All inequalities used here are strict. The result therefore holds on
an open neighborhood in the native reward space (own singletons fixed
zero), not merely on the factorized family (9). To see stability of (2),
retain strict zJ>0, which uniformly controls every sufficiently small
nonzero root by (4). On the remaining compact root set, max_i Q_i has a
strict positive minimum. Both properties persist under small changes of
all participant coordinates. Strict zGamma>0 persists as well, and (11)
retains a strictly negative combined coefficient in EVERY coordinate,
so no weight can pass the older global test. Every negative participant
pair also stays negative. Passive nonsingleton values remain arbitrary
finite throughout; they only change the collar's numerical constants.

## 6. What this closes and what remains

Every boundary tail in the
[incoming decomposition](CODEX_COORDINATOR__ZERO_OBSERVER_BOUNDARY_REDUCTION.md)
belongs to K_abs. For the calibration, its displayed cap bound directly excludes the
entire face B0=B1=B3=0, including the all-zero endpoint used to produce a
first finite Never-penalty plateau. No realization of that abstract tail,
full Nash property of the incoming head, or global-minimum property of the
tail is needed. The result applies to every pivot's boundary source. The signed example
also excludes all-zero boundary endpoints for every passive nonsingleton
completion, as do all sufficiently small native perturbations described
in Section5. Positive original own levels give a full-dimensional open
family of original tables through the exact bridge in Section3.

It does NOT exclude an actual global partial-Nash minimum, boundaries
with max(B0,B1,B3)>0, or penalty plateaux arising by another mechanism.
It does not make an observer-Nash head a full Nash head. In particular,
the exact partial-Nash control in the
[cap-region note](CODEX_UNEQUAL_GLOBAL__NONNEGATIVE_CAP_ROOT_ACTIVITY.md)
has strictly positive supported caps and is consistent with this theorem.

The relevant source formulas were inspected in
`quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
(`UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`),
`quittingTerminalSemanticPair_rootThenContinuation` and
`quittingTerminalSemanticPrefix`
(`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`). The target
`quittingUniformEquilibriumPayoffConjecture`
(`UniformEquilibrium/Quitting/Conjecture/Basic.lean`) remains open.
No Lean command ran.

The next source question is whether the remaining boundary faces can be
excluded using the observer equalities and the inherited comparison map,
rather than an unconditional cap estimate.
