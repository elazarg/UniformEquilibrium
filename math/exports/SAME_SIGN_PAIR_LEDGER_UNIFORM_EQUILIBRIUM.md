# Same-sign pair traps and simultaneous ledger chambers

## 1. Exact statement

Let I be finite with at least two players. A quitting game has finite real
rewards r_i(S) for every nonempty coalition S, zero live and Never reward,
independent private stopping laws, and unrestricted complete unilateral
behavioral deviations. Put s_i=r_i({i})>=0.

Let W be a finite nonempty family of normalized nonnegative vectors a:
sum_i a_i=1 for every a in W. Define

    H_a(S)=sum_i a_i(r_i(S)-s_i),
    J_a(S)=sum_(i outside S)a_i(r_i(S+i)-r_i(S)),
    f_a(z)=sum_(empty!=S proper) z_S J_a(S),
    z_S=product_(i in S)z_i.

Here S+i means S union {i}. Assume these three raw conditions:

- H_a(S)>=0 for every a in W and every nonempty proper S.
- For every strictly positive odds vector z, some a in W has f_a(z)<=0.
- Some player j satisfies a_j<1 for every a in W.

The odds-cover condition is a quantified polynomial inequality on the raw
reward table and finitely many supplied weights. It supplies no strategy,
continuation, root equilibrium or cap. The third condition is equivalently
that W omits the unit vector e_j for some j. It produces an actual common
seed in the proof; no strategic seed is supplied as an extra assumption.

A proper pair trap is a two-player proper subset A={i,j} such that
r_i(A)>s_i and r_j(A)>s_j. Its joining gaps are

    d_i^A=r_i(A)-r_i({j}),    d_j^A=r_j(A)-r_j({i}).

Higher-support product-lowness means: for every product root q whose
support D is proper and has cardinality at least three, some i in D has
forced-Quit payoff Q_i(q)<=s_i. No condition is imposed on two-player
product roots. A finite sufficient condition is: for every such D, there
is b^D>=0, supported on D, with sum b^D=1 and

    sum_(i in S)b_i^D(r_i(S)-s_i)<=0

for every nonempty S subset D. Call this the higher-support LP condition.

Each of the following hypotheses implies that the infimum of total full
terminal regret over actual independent ABSORBING profiles is zero, hence
that the original game has one fixed uniform-equilibrium payoff. Explicitly,
there is u such that for every epsilon>0 there are one behavioral profile
sigma and an integer N for which, at every horizon T>=N, its expected
average payoff is within epsilon of u in every coordinate, and EVERY
complete unilateral behavioral replacement by i pays at most u_i+epsilon.
The profile and N may depend on epsilon; u may not. The three sufficient
participant hypotheses are:

1. Any finite I: higher-support product-lowness, and
   d_i^A*d_j^A>0 for every proper pair trap.
2. Any finite I: the higher-support LP condition, and
   d_i^A*d_j^A>=0 for every proper pair trap.
3. I has four players: higher-support product-lowness, and
   d_i^A*d_j^A>=0 for every proper pair trap.

**Scalar H/J corollary.** Instead of the three family conditions, it
suffices that some nonzero a>=0 has H_a(S)>=0 and J_a(S)<=0 on every
nonempty proper S. Normalize a and take the singleton family {a}. All
coefficients of f_a are nonpositive, and because |I|>=2 there is a j
with a_j<1. Thus every scalar H/J instance is included.

The class imposing scalar H/J and product-lowness on EVERY proper support
is contained in claim 1: its pair condition excludes every pair trap, so
the new pair hypothesis is vacuous. The theorem permits positive-premium pair traps while
requiring no full-support boxed charge or greatest-core condition. The
finite-ledger version unifies the same chamber argument; only the explicit
scalar witness in Section 7 is claimed as independently new class coverage.

## Conjecture-facing change

This supplies an actual-data equilibrium producer allowing proper pair
supports with both active premiums strictly positive, provided their two
joining gaps have the same weak sign. Proper supports of size at least
three retain a product-low condition. Full-support roots are controlled
by scalar H/J signs or, more generally, a finite odds-dependent choice of
ledger. No full-support premium-low or boxed-charge assumption is made.
The pair-index argument selects a useful full Nash root; the cap chamber
then produces actual absorbing profiles with full behavioral regret tending
to zero. The explicit four-player table in Section 7 satisfies this theorem
while failing the complete raw selections enumerated there. General Fin4,
opposite-strict-sign pair traps, and arbitrary larger proper supports remain
open. The finite-family statement is a unification; the scalar witness is
the separate new-coverage evidence.

## Strategic inputs

The only inputs are the finite reward table, the finite raw ledger weights,
and one of the three participant conditions in Section 1. The finite LP
variant additionally supplies its finite nonnegative weights b^D. These are
reward inequalities, not strategic witnesses. Every strategic object used
in the proof is produced:

- The sole-owner absorbing seed and its full caps are computed in Section 4.
- Finite Nash existence and the ambient degree proof produce a selected root
  at every needed annotation; no root selector is assumed.
- The compact actual payoff/cap carrier and the chamber descent produce a
  diagonal, and therefore actual absorbing approximants.
- Reward continuity returns all approximants to the original fixed table.
- Section 5.3 selects the target before accuracy and controls all unilateral
  behavioral replacements uniformly over every sufficiently long horizon.

No child equilibrium, outsider cap, punishment strategy, supplied
continuation, controller, safe return map, response optimizer, recursive
producer or convergence rate is assumed.

## 2. Definitions, probability mode and exact accounts

At each date before absorption the actions are publicly observed Boolean
Continue/Quit choices, with independent private randomization. The first
nonempty quitter coalition fixes the reward thereafter. No public correlation
is added. Before absorption the only live public history is repeated all Continue.
Thus behavioral strategies are equivalent to independent laws on natural
quit dates plus Never. A complete replacement payoff is affine in its
own law, so its supremum is the supremum over every finite pure deadline
and Never; this is the full behavioral cap, with no attained optimizer
assumed.

Let K be the closure of all actual absorbing pairs (U,B), where U is
prescribed terminal payoff and B is the vector of full caps. Put
M=max(0,max_(S nonempty,i)|r_i(S)|). This common finite bound makes
K nonempty and compact, with B>=U. Any finite
independent prefix preserves actual absorption and, by continuity, K.

For a product root q define

    p_q(S)=product_(i in S)q_i product_(i outside S)(1-q_i),
    c=p_q(empty), alpha_i=product_(j!=i)(1-q_j),
    Q_i=E[r_i(A+i)], b_i=E[r_i(A)1_(A nonempty)],
    C_i=b_i+alpha_i B_i,
    Delta_i=q_i(C_i-Q_i)_+ +(1-q_i)(Q_i-C_i)_+,

where A is the independently drawn opponent quitter set. Prefixing gives

    U_i'=q_i Q_i+(1-q_i)(b_i+alpha_i U_i),
    B_i'=max(Q_i,C_i),
    d_i'=c d_i+Delta_i,       d=B-U.

Write E=max_i d_i and L_a(B)=sum_i a_i(B_i-s_i). For proper-support q
and every a in W,

    E'<=cE+max_i Delta_i,
    L_a(B')=cL_a(B)+sum_(S nonempty)p_q(S)H_a(S)
                                      +sum_i a_i Delta_i.     (1)

If q is a full finite Nash root at continuation B, all Delta_i vanish.
If q is instead Nash at x=B-delta e_k with delta>=0, then

    Delta_i=0 for i!=k,
    0<=Delta_k<=q_k alpha_k delta=p_q({k})delta.               (2)

Indeed the original Continue endpoint exceeds the auxiliary one only at
k, by alpha_k delta. A supported Continue action remains optimal; a
supported Quit action can lose at most that amount. If w is the auxiliary
Nash successor, then

    B_i'=w_i for i!=k,
    B_k'<=w_k+alpha_k delta.                                  (3)

These bounds hold also at sure hazards. No new payoff subsidy is played.

## 3. Selected low-or-sure root at a below-singleton annotation

Assume higher-support product-lowness and the WEAK pair inequalities.
For every continuation x with

    min_i(x_i-s_i)<0,       L_a(x)>0 for EVERY a in W,

there is a full Nash root q such that either some q_i=1, or its auxiliary
successor w has some w_i<=s_i. At a Nash root w_i=max(Q_i,C_i(x)).
The root is nonzero because All Continue is not Nash at a below-singleton
annotation.

### 3.1 Classification of all unacceptable roots

Call a root unacceptable when all q_i<1 and w_i>s_i for every i. Every
active rate is then interior, so its indifference gives Q_i=w_i>s_i.
A full-support unacceptable root would have all hazards interior. Write
z_i=q_i/(1-q_i) and z_S=product_(i in S)z_i. Active indifference gives

    x_i-s_i=sum_(empty!=S subset I-i)z_S[r_i(S+i)-r_i(S)],
    L_a(x)=f_a(z) for EVERY a in W.

The odds cover contradicts simultaneous strict positivity of all L_a(x).
A proper support of size at least three is excluded
by higher-support product-lowness. A singleton support has Q_i=s_i.
Thus every unacceptable root is supported on a proper pair trap {i,j},
with both rates interior.

Set u_i=x_i-s_i and A_i=u_i+d_i^A, and similarly for j. The two
indifference equations are

    q_j A_i=u_i,        q_i A_j=u_j.                            (4)

If d_i^A=0, an interior q_j forces u_i=0. Consequently any source
with x_i!=s_i excludes such a root. The same applies to d_j^A=0.
At all other pair traps the weak product assumption gives a strictly
positive product. Such a pair has at most one interior candidate:

    q_j=u_i/A_i,        q_i=u_j/A_j.                            (5)

### 3.2 A single dense generic annotation set

Exclude every own hyperplane x_i=s_i. For each strict-product pair trap,
also exclude A_i=0 and A_j=0. For every outsider k, substitute (5) into
its full endpoint gap g_k=Q_k-C_k and multiply by A_i A_j. The result
N_{A,k}(x) is a polynomial. Its coefficient of x_k is

    -d_i^A d_j^A != 0,

because the opponent-survival factor is
(1-q_i)(1-q_j)=d_i^A d_j^A/(A_i A_j). Thus N is not the zero
polynomial. Exclude N=0 for every pair and outsider. The complement G of
this finite union is open and dense. One may see density by multiplying
the nonzero polynomials: a nonzero real polynomial cannot vanish on an
open box, by induction on the number of variables.

Only annotations are perturbed. The reward table, ledger data and participant
conditions are fixed. Both min(x-s)<0 and simultaneous L_a(x)>0 are open
constraints; finiteness of W is used here. Every such source can therefore
be approximated from G within their intersection.

### 3.3 Full ambient negative indices

Fix such a generic source and suppose every Nash root is unacceptable.
Finite Nash existence supplies at least one, and (5) gives finitely many,
at most one per pair trap. At each candidate every inactive gap is nonzero
by construction; Nash makes each strictly negative.

Extend the full polynomial gaps to real hazards and form

    F(q)_k=min(1,max(0,q_k+g_k(q))).

Its fixed points are exactly full finite Nash roots. At the candidate the
inactive rows of F are locally zero, and its two active rows are unclipped.
The derivative of identity minus F, after ordering the active pair first,
has block form

    [[0,-A_i,*],[-A_j,0,*],[0,0,Id]].                           (6)

Interiority of u_i/(u_i+d_i^A) implies that A_i and d_i^A have the
same strict sign; likewise for j. Hence A_i A_j>0 and (6) has determinant
-A_i A_j<0. This is the full ambient derivative, including every inactive
coordinate and every higher-coalition term in the starred blocks.

On Omega=(-1,2)^I, F and its straight-line homotopy to the cube center
stay in [0,1]^I. Identity minus that homotopy is nonzero on the boundary,
so its total degree is +1. The derivative in (6) is invertible, so the
candidate is isolated and its local degree is -1, by comparison with its
linearization on a sufficiently small sphere. Disjoint neighborhoods and
degree additivity would make total degree the negative of the nonzero
number of candidates, contradicting +1. Outsider zeros lie in the interior
of Omega, so no boundary half-index is involved.

Therefore an acceptable root exists at every generic source. Approximate
an arbitrary source by generic ones and extract a convergent subsequence of
roots in the compact hazard cube. Nash inequalities are closed. The successor
w_i=max(Q_i,C_i(x)) is continuous jointly in q and x. Thus the finite union
of the sure-coordinate alternative and the low-successor alternative is
closed, and the universally restored conclusion is:

    some q_i=1 OR the auxiliary successor w has some w_i<=s_i. (7)

Nonzeroness persists because the source has a strict singleton deficit.

## 4. Strict-source absorbing chamber

Temporarily impose

    H_a({j})>0 whenever a_j<1, for every a in W.               (8)

Choose j from the common-seed condition a_j<1 for every a in W. The actual
sole-j-Quit0 profile has B_j=s_j and
B_i=max(r_i({j}),r_i({i,j})) for i!=j. Every ledger surplus obeys
L_a(B)>=H_a({j})>0. If its debt is zero we are done; otherwise choose

    0<lambda<=min(1/2, min_(a in W)L_a(B)/E).

For sufficiently small e>0, fix the nonempty compact set

    C_e={(U,B) in K: min_i(B_i-s_i)<=e,
                         L_a(B)>=lambda E for EVERY a in W},
    lambda e < every positive singleton H_a.                (9)

Assume K contains no diagonal. Compactness then gives
g=min_K E>0. Suppose the minimum of E on C_e exceeds e, and choose a
minimizer (U,B). We construct a strict descent or contradict g>0.

If m=min(B-s)<0, apply (7) at x=B. A sure root gives E'=0. Otherwise the
root has some successor cap <=s, and full support is excluded by the odds
cover. It is a nonzero proper exact root. Formula (1) preserves every
ledger inequality in C_e and
gives E'=cE<E, a contradiction.

If 0<m<=e, choose i attaining m and give only i a small positive hazard p.
All other strict Continue margins persist. The only defect is p m, the
owner's cap remains B_i, and

    E'<=(1-p)E+p m<E,
    L_a(B')-lambda E'>=(1-p)(L_a(B)-lambda E)
                         +p[H_a({i})+(a_i-lambda)m].

For a_i<1, (8) and (9) make the bracket positive. For a_i=1, normalized
nonnegativity forces a=e_i and H_a({i})=0; the bracket is
(1-lambda)m>0. Thus every ledger is preserved and C_e is preserved.

Finally m=0. The tied set T is nonempty and proper because every L_a(B)>0.
For every k in T and a in W, one has a_k<1: otherwise a=e_k would give
L_a(B)=0. Fix k in T; then h=min_(a in W)H_a({k})>0. Choose delta>0
so small that

    delta<=e, delta<g, delta<E, lambda delta<h,
    L_a(B-delta e_k)>0 for EVERY a in W.

The annotation x=B-delta e_k is below its kth singleton. Choose the root
from (7). If it is sure, (2) gives E'<=delta<g, impossible for a point of K.
Otherwise the odds cover at x rules out full support. The selected successor
w has a low coordinate, so (3) gives min(B'-s)<=delta<=e. The exact account
and (2) yield

    E'<=cE+p_q({k})delta<=cE+(1-c)delta<E,
    L_a(B')-lambda E'>=c(L_a(B)-lambda E)
                         +p_q({k})[H_a({k})-lambda delta]>=0

for every a in W.

Thus this ORIGINAL-game prefix belongs to C_e and strictly lowers E. No
smallness of its hazards, root convergence to zero, active status of k, or
continuous root selection is assumed. The singleton H payment and the
continuation-lowering defect use exactly the same singleton probability.

All cases contradict the proposed minimum. Hence min_(C_e)E<=e for all
small e, contradicting g>0. Therefore K has a diagonal and actual absorbing
approximants have total regret tending to zero.

## 5. Removing strict H and admitting zero joining gaps

For claim 1, raise every passive singleton reward by epsilon>0, leaving all
participant data unchanged. For every normalized a this adds
epsilon(1-a_j) to H_a({j}) and subtracts it from J_a({j}); all larger
H/J values are unchanged. Thus every odds polynomial f_a weakly decreases,
preserving the odds cover. Higher-support
product-lowness is unchanged. Choose epsilon smaller than every positive
joining gap, with no restriction when there are none; negative gaps stay
negative. Thus each strict common sign is preserved when both gaps decrease
by epsilon. Apply Section 4 and return to
the original fixed table by uniform reward continuity.

For claims 2 and 3, use the following augmented perturbation instead:

- Raise every passive singleton reward by epsilon.
- At every proper pair trap {i,j}, raise r_i({i,j}) and r_j({i,j})
  by epsilon as well.

Own singletons and the complete list of proper pair traps are unchanged.
Both joining gaps of each trap are unchanged, so weak products including
zero remain admissible. Every singleton H_a becomes strict as required.
Pair H_a increases by epsilon(a_i+a_j) at a raised trap, and all other
larger H_a stay fixed. In a singleton J_a row, a term associated with a pair trap has its
inserted and passive reward both raised, so its difference is unchanged;
every other term decreases by epsilon times its nonnegative weight. For
larger S, J_a(S) is unchanged because its passive pair entries are not
edited. Every f_a therefore weakly decreases, preserving the odds cover.

### 5.1 LP preservation for any number of players

Fix a higher proper support D with an LP certificate b. If it contains a
pair trap {i,j}, its pair constraint is

    b_i(r_i({i,j})-s_i)+b_j(r_j({i,j})-s_j)<=0.

Both premiums are strictly positive and b>=0, so b_i=b_j=0. Therefore
the perturbation of that pair changes no weighted constraint. Every raised
participant entry occurs in such a pair, proving preservation of the same
certificate on every higher proper support. This proves claim 2.

### 5.2 Direct higher product-low preservation for Fin4

Let D={i,j,k} be a proper triple containing a pair trap {i,j}. For every
fixed q_i,q_j>0, as q_k decreases to zero,

    Q_i-s_i -> q_j(r_i({i,j})-s_i)>0,
    Q_j-s_j -> q_i(r_j({i,j})-s_j)>0.

Triple product-lowness therefore forces Q_k(q_i,q_j)<=s_k. This endpoint
does not depend on q_k. By continuity the inequality holds on the entire
closed (q_i,q_j) square. At its four corners it says precisely that k is
flat on every participant coalition inside D.

No other pair trap in D can contain this flat k. Thus the only edited pair
in D is {i,j}, and k's participant entries remain unchanged. The same flat
k still supplies triple product-lowness after perturbation. A triple with
no pair trap has no edited participant entry, so its property also persists.
In Fin4 the higher proper supports are exactly the triples. This proves
claim 3, including cases where the original triple condition had no LP
certificate.

The finite LP identity proving higher-support product-lowness is

    sum_(i in D)b_i q_i(Q_i-s_i)
      =sum_(empty!=S subset D)p_q(S)sum_(i in S)b_i(r_i(S)-s_i)<=0.

Every active hazard is positive and the normalized b have positive total,
so not all active Q_i-s_i can be positive.

An entrywise perturbation of size epsilon changes every prescribed payoff
and every full replacement cap by at most epsilon, uniformly over complete
laws. Each regret changes by at most 2epsilon. Absorption is a property of
the laws and is unchanged. Hence absorbing approximate equilibria for the
perturbed tables yield them at the fixed original table as epsilon tends
to zero.

### 5.3 One target and uniform control of all deviations

For completeness the semantic endpoint can be proved directly. Choose
actual profiles sigma^n with total terminal regret tending to zero. Their
bounded payoff vectors have a subsequence U^n tending to one vector u.
Then their full caps B^n also tend to u. Fix one such profile sigma and
player i, and let T_-i be the first opponent quit date, allowing Never.
For a date t, set eta_i(t)=Pr(t<T_-i<infinity), which tends to zero.

Take any complete unilateral deviation and replace all its quit plans
after date t by Never. Its expected terminal payoff equals its expected
reward already absorbed by t, plus a later term of absolute value at most
M eta_i(t). Hence the original deviation's expected reward already
absorbed by t is at most B_i+M eta_i(t), uniformly over the deviation.
Average this inequality over dates t<N. Since absorption rewards persist
and live rewards are zero, every N-stage average deviation payoff is at
most B_i+(M/N)sum_(t<N)eta_i(t). The error tends to zero by Cesaro
convergence, independently of the deviator's complete strategy.

The prescribed N-stage payoff tends to U by bounded convergence of the
absorbed-reward indicators. Given any accuracy, first choose n so that
U^n and B^n are close to the fixed u, and then one horizon threshold for
the prescribed convergence and all finitely many uniform deviation tails.
The same profile sigma^n works for every larger horizon. This proves the
fixed-target uniform-equilibrium conclusion without an assumed absorption
rate or a restriction on unilateral deviations.

## 6. Source correspondence

The following exact Lean declarations are correspondences and reusable
services; the combined raw-family theorem is new ordinary mathematics:

- `quittingContinuationBestResponseValue_rootThenContinuation_eq_max`
  and `quittingRootContinuePayoff_update_add` in
  `UniformEquilibrium/Quitting/Root/TerminalDebtPrefix.lean`.
  The cap recursion has no Nash hypothesis. The neighboring debt theorem
  assumes a root at prescribed payoff U and is not used as if it were a
  theorem for continuation B; Section 2 derives that account directly.
- `pairNash_hasFDerivAt_and_negative_det_of_numerator_avoidance` and
  `dense_quittingPairTieAvoidanceDomain` in
  `UniformEquilibrium/Quitting/Root/PairNashTieAvoidance.lean`, with
  the inactive polynomial numerator in
  `UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean`.
- `exists_exactRoot_singletonSublevel_of_signed_pair_core` in
  `UniformEquilibrium/Quitting/Classification/SignedPairCoreSelectedReturn.lean`.
  Its greatest-core assumption is not supplied here. The new finite-root
  classification instead uses the odds cover to remove full support and higher
  product-lowness to remove every larger proper support.
- `IsSupportwiseQuittingPremiumWeightCertificate` and
  `HasSupportwiseQuittingPremiumBalanceAt` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`.
- `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

The new content is the finite-root classification from the odds cover and
higher-support product-lowness, the exact one-coordinate lowering splice,
the simultaneous actual-cap chamber, and the weak-pair perturbation repairs.
The proof above includes every mathematical step and requires no conference
manuscript as a dependency. No claim of Lean implementation of these combined
steps is made.

## 7. Exact witness beyond the earlier classes

Use unit scalar weights, own rewards 1, and Never reward 0. Equivalently,
use the normalized singleton ledger family {(1/4,1/4,1/4,1/4)}.

| S | r(S), in player order 0,1,2,3 |
| --- | --- |
| 0 | (1,0,4,0) |
| 1 | (0,1,0,4) |
| 2 | (4,0,1,0) |
| 3 | (0,4,0,1) |
| 01 | (-1,1,5/2,3/2) |
| 02 | (3,2,2,2) |
| 03 | (2,3/2,3/2,-1) |
| 12 | (3/2,-3,1,9/2) |
| 13 | (2,0,2,0) |
| 23 | (5/2,3/2,-1,1) |
| 012 | (-1,-1,-1,10) |
| 013 | (-1,-1,10,-1) |
| 023 | (-1,10,-1,-1) |
| 123 | (10,-1,-1,-1) |
| 0123 | (9,9,9,9) |

Singleton H values are all 1; singleton J=(-2,-4,-3,-3).
In pair order 01,02,03,12,13,23, H=(0,5,0,0,0,0) and
J=(-6,-6,-5,-8,-6,-6). Every triple has H=3 and J=-1.
The only proper pair trap is 02, with joining gaps (-1,-2).
The flat-player sets on triples 012,013,023,123 are respectively
{1},{1,3},{3},{1,2,3}. Thus the strict theorem applies.

At any positive product hazards on pair 02, Q_0=1+2q_2>1 and
Q_2=1+q_0>1. Hence proper product-lowness and proper support-flatness
both fail. The theorem is a strict extension of the scalar ledger class
requiring every proper support to be product-low.

### 7.1 Protected, weighted and mixed boxed entrances

For these comparisons, a player i is protected when r_i(S)>=s_i for
every coalition S containing i. A premium trap D is a nonempty support
for which each i in D has some S subset D containing i with r_i(S)>s_i.
A global inserted-premium floor uses a nonzero w>=0 and requires

    W_w(S)=sum_i w_i[r_i(S union {i})-s_i]>=0

for EVERY coalition S, including empty and coalitions outside any trap.
A weighted upper-average test on the full support requires a nonzero
nonnegative weight with nonpositive weighted premium sums on every tested
coalition; the only necessary condition used here is its grand-row test
sum_i w_i[r_i(I)-s_i]<=0. This test is shared by both the inserted-premium
version W_w(S)<=0 and the participant-only version
sum_(i in S)w_i[r_i(S)-s_i]<=0. These predicates are distinct from the
H_a lower ledgers used to prove the theorem.

Every player has a proper-triple participant reward -1, so the maximal
protected set is empty. Grand rewards 9 make the full set a premium trap
and defeat every nonzero weighted upper-average criterion. For any
nonnegative global-floor weight w, the singleton 1 floor requires
-2w_0-w_3>=0, while singleton 3 requires w_0-w_1-2w_2>=0.
Their sum is -w_0-w_1-2w_2-w_3, which is at most -1 after sum w=1.
Thus no nonzero global-floor weight works, including nearby reward closure.
The precise global-floor correspondence is `HasGlobalQuittingWeightedFloor`
and `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
the participant-only upper test is the certificate in Section 6.

For the full-trap boxed raw entrance, define
P(S)=sum_(i outside S)[r_i(S+i)-s_i], with unit-weight J(S) as before.
Its positive coefficients D,G,tau,Lstar must satisfy P({j})<=-D,
J({j})<=-G, P(I-j)<=tau, J(I-j)<=-Lstar, and the strict charge
threshold C=4 sqrt(D/tau)(G+Lstar D/tau)>sum s+4M. Additional
intermediate-coalition restrictions cannot weaken these necessary conditions.
Here the singleton P values are (-1,-3,-2,-2), and singleton J values
are (-2,-4,-3,-3). Every penultimate P is 8 and every penultimate J is
-1. Therefore every coefficient choice has
D<=1, G<=2, tau>=8 and Lstar<=1. Its maximum possible charge satisfies

    C=4 sqrt(D/tau)(G+Lstar D/tau)
       <=17/(2 sqrt(8))<4,

whereas its required threshold is sum s+4M=44 because M=10.
The strict separation persists in a reward neighborhood. This defeats
the full-trap mixed boxed entrance for every coefficient choice; no choice
on the proper pair can repair that failed full-trap obligation.

### 7.2 No exact stationary equilibrium

All passive rewards are nonnegative, so Never guarantees nonnegative
payoff and every equilibrium value is nonnegative. At any sure owner,
its opposite player has strictly negative joining gaps and Continues.
For sure owners j=0,1,2,3, respectively, those four possible gaps are

    (-2,-7/2,-5/2,-1),       (-4,-5/2,-11/2,-1),
    (-1,-5/2,-7/2,-1),       (-4,-5/2,-5/2,-1).

With the opposite player continuing, the predecessor's two possible gaps
are respectively (-1,-5/2), (-1,-5/2), (-3,-5/2), (-1,-5/2), all negative.
The final successor gaps are respectively 1,1,1,2, all positive.
Thus the predecessor Continues and the successor surely Quits. The sure
owner receives respectively -1,-3,-1,-1, instead of 0 from withdrawal.
Thus every stationary equilibrium would have all positive rates below 1.

All-Never fails at own reward 1. A sole active owner fails at its directed
successor. On adjacent supports 01,12,23,30, the successor's Never payoff
is 0 while its Quit endpoint is respectively 1,1,1,1+q_3. Opposite pair
02 fails because player 0 gets 4 from Never but at most 3 from Quit;
opposite pair 13 fails because player 1 gets 4 from Never but at most 1
from Quit. Full support is impossible: every stationary terminal outcome
has nonnegative H, singleton outcomes have strictly positive H, and all
rates are interior, so L(v)>0. Full-support indifference instead gives
L(v)=sum z_S J(S)<=0.

On a triple, active indifference gives v_i=Q_i=b_i/(1-alpha_i), hence
Q_i>=b_i. For support 013 set (a,b,c)=(q_0,q_1,q_3). Flat player 3
gives 1-2a-5b+(7/2)ab>=0, hence a<1/2 and b<=1/5.
Then Q_0=1+c-2b-bc>=3/5, whereas Never for player 0 gives at most
2b<=2/5. For support 123 set (a,b,c)=(q_2,q_3,q_1). Flat player 1
gives 1-4a-5b+(11/2)ab>=0, hence a<1/4 and b<=1/5.
Then Q_2=1-2b>=3/5, whereas Never for player 2 gives at most 2b<=2/5.

For support 012 put (a,b,c)=(q_0,q_1,q_2). The endpoints used are

    Q_0=1-2b+2c-2bc,    b_0=4c-(5/2)bc,
    Q_1=1-4c+2ac,       b_1=2ac.

From Q_1>=b_1 obtain c<=1/4. Active 1 gives
Q_1=2ac/(a+c-ac)<=2c, so c>=1/6. The condition Q_0>=b_0 gives
b<=(1-2c)/(2-c/2)<=8/23. Active 0's stationary residual is

    F_0=b(1-2b)-c[3-(3/2)b]+2c^2(1-b)^2.

Since 3-(3/2)b-2c(1-b)^2>=2397/1058>9/4 on these bounds,
F_0<=1/8-(9/4)c<=-1/4, contradicting active indifference.

For support 023 put (a,b,c)=(q_0,q_2,q_3). Here

    Q_3=1-2a,               b_3=2ab,
    Q_2=1+a-2c-ac,          b_2=4a-(5/2)ac,
    Q_0=1+2b+c-5bc,         b_0=4b-(3/2)bc.

Active 3 implies
b=a(1-2a)/(5a-2a^2-1), with a>=1/4. The condition Q_2>=b_2
gives a<=1/3 and c<=2/13. The derivative of the displayed b expression
is (-8a^2+4a-1)/(5a-2a^2-1)^2<0, so b>=b(1/3)=1/4.
Consequently Q_0<=1+2b, while the numerator
of Never_0-(1+2b), over its positive denominator b+c-bc, is

    b(3-2b)-c[1+(5/2)b-2b^2]
       >=5/8-57/208=73/208>0.

Every support is excluded, so the table has no exact stationary Nash.

### 7.3 No reward closure of exact stationary producers

The singleton comparison matrix Gamma_ij=r_i({j})-s_i is

    Gamma=[0,-1,3,-1; -1,0,-1,3; 3,-1,0,-1; -1,3,-1,0].

The pair principal determinants, in order 01,02,03,12,13,23, are
(-1,-9,-1,-1,-9,-1); every triple principal determinant is 6, and the
full determinant is 45. Thus every principal block of size at least 2 is
invertible; a singleton homogeneous complementary support fails an external
negative entry. Hence Gamma is R0: no nonzero p>=0 satisfies Gamma p>=0
and p_i(Gamma p)_i=0 for every i. Indeed a support of size at least two
would give a kernel vector of its invertible principal block, and singleton
supports were separately excluded. Suppose nearby tables had exact stationary roots q^n.
If a subsequential limit q is nonzero, stationary payoff and endpoint
formulas are continuous there; Bellman optimality and vanishing opponent
survival then imply a limiting exact stationary equilibrium. A sole active
owner separately has no profitable Never deviation because its own reward
is 1. This contradicts Section 7.2.

If q^n tends to zero, normalize p^n=q^n/sum q^n and take p^n tending
to p in the simplex. Singleton terminal masses tend to p, and all larger
terminal masses tend to zero, so v^n tends to 1+Gamma p. Date-zero Quit
gives Gamma p>=0. For every p_i>0, active indifference gives
(Gamma p)_i=0. This contradicts R0. Thus no reward-closure entrance
of the exact stationary producer covers this witness either.

### 7.4 Every persistent-base induced-Nash punishment-floor selection fails

This additional exclusion concerns a named nonstationary compiler, not
only stationary laws. Fix any nonempty persistent base, any disjoint set
of free players, and any induced mixed Nash point. Players in the base
Quit surely; players outside base and free Continue. The compiler also
requires the outsider no-join inequalities and the base-owner leave or
punishment-floor inequalities.

First take singleton base {j}. Induced Nash for free players and outsider
no-join together mean that EVERY nonowner best responds to the sure owner.
The strict cascade in Section 7.2 therefore forces the opposite and
predecessor to Continue and the cyclic successor j+1 to Quit surely.
The owner's immediate Quit value is respectively -1,-3,-1,-1, whereas
its Continue value is r_j({j+1})=0. The successor's sure Quit makes the
owner-deleted survival probability zero. Consequently EVERY continuation
or punishment-floor value disappears from the owner's Continue endpoint.
Its floor excess is respectively 1,3,1,1, strictly positive. No free-set
selection, induced boundary mixture, or alternative punishment tail fixes
that inequality.

For a base of size at least two, every player's opponents already include
a sure quitter. The base-owner leave inequalities, free-player Nash
conditions and outsider no-join inequalities jointly make the entire root
Nash, with continuation irrelevant. The sure-root exclusion in Section 7.2
rules this out. Thus every nonempty base and every induced-Nash selection
in these named persistent-base compilers fails for this table.

The exact correspondence is `quittingSingletonBaseOwnerFloorExcess` and
`nonempty_quittingSingletonBaseCertificate_of_inducedNash` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`,
and `QuittingInducedOwnerChamber` in
`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`.
For larger bases the exact screen is
`quittingPersistentLargeBaseExcess_nonpos_iff` in the first file; its
consumer is `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`.
These comparisons do not assert a census of every supplied nonstationary
certificate in the repository. They establish new complete raw-class
coverage beyond the previous proper-low ledger class and the named strong
protected, weighted, mixed boxed, exact-stationary and persistent-base
induced-Nash punishment-floor entrances.

### 7.5 Additional finite raw screens

The singleton matrix has Gamma_01=Gamma_10=-1. It therefore fails every
raw screen requiring that no pair have two strictly negative singleton
comparison entries, including after relabeling or sufficiently small reward
perturbation.

It also lies outside the fixed participant-row template with own singleton
1, adjacent pair participant values (-1,2), opposite pair participant values
(0,0), triple participant values -1, and only passive rewards and grand
rewards variable. The template's singleton rows have two neighbor entries
0 and one opposite entry P_i>=4. Even allowing player relabeling and
positive recipient-affine transport, the two repeated singleton zeros
force the shift to be 0, and own reward 1 forces the scale to be 1; then
P_i=4. All pair participant entries in that template lie in {-1,0,2},
whereas the witness has r_0(02)=3. No such transport can cover this table.

## 8. Boundary tests

The table in Section 7 is an exact positive test with a negative-negative
pair trap and a grand coalition whose every participant exceeds its own
singleton. The latter directly rejects global product-lowness: at all Quit,
every forced-Quit endpoint is 9>1.

For a zero-gap positive test, change only r_0(02) from 3 to 4. Its pair
trap gaps become (0,-2), H(02) becomes 6, and J({2}) becomes -2. All
other displayed ledger inequalities and triple flatness checks are
unchanged. Thus the weak theorem covers this boundary as well. The generic
selector excludes the degenerate pair at sources with x_0!=s_0; it does not
assign a fictitious nonsingular index to a zero-gap root.

For the zero-ledger boundary, take every nonempty-coalition reward to be 1
in every coordinate. Then s=1 and all H_a=J_a=0; any admissible family
works. Every product Quit endpoint equals its singleton, and the sole-owner
profile already has zero full debt. The proof does not assume a positive
strictness constant at the original table.

The same-sign condition has a genuine local index boundary. With two active
players having s_i=s_j=1, pair participant rewards both 2, and passive
singleton values r_i({j})=0, r_j({i})=3, the gaps are (2,-1).
At x_i=2, x_j=1/2, their interior candidate has q_i=q_j=1/3.
The active derivative determinant is -(3)(-3/2)=9/2>0. It can contribute
positive degree, so the negative-index contradiction cannot simply admit
opposite-sign pairs. This is a limitation of the selector argument, not a
uniform-equilibrium counterexample.

At a lowered annotation, a sure root need not have zero original-game
defect. The proof uses the exact bound E'<=delta and the positive global
minimum g to contradict E'>=g. It does not incorrectly treat auxiliary
Nash as original-game Nash. Likewise, the low-successor alternative is
closed under limits, whereas active ownership of its low coordinate need
not be; no activity claim survives the limiting step without proof.

## 9. Actual-data adapter and semantic consumer

The actual-data adapter proved here starts from any raw table and ledger
family satisfying Section 1. It computes the sole-owner seed, applies the
selected-root lemma at each needed strict-below-singleton source, preserves
all ledger inequalities under literal original-game prefixes, and forces a
diagonal in the closure of actual absorbing payoff/full-cap pairs. Weak
boundaries are returned to the SAME original table by uniform reward
continuity. Every point approximating the diagonal is an actual independent
behavioral profile; the cap controls every complete unilateral replacement.

The direct consumer in Section 5.3 proves the fixed-target uniform conclusion.
The corresponding existing semantic endpoint is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`:
terminal approximate Nash at every positive error yields one uniform payoff
target. The packet supplies its all-errors antecedent and proves the required
probability and agency translation explicitly. Its new adapter and chamber
are ordinary mathematics; no new Lean seal is claimed.

## 10. Lean handoff

Define the finite normalized ledger family and its raw H inequalities,
positive-odds cover, and common-seed guard separately from all strategic
objects. Define higher-support product-lowness by restricting the existing
forced-Quit endpoint predicate to proper supports of cardinality at least 3.
Keep the pair-premium trap and its weak joining-gap product as finite raw
reward conditions. Do not place the selected root, actual seed, cap chamber
or equilibrium conclusion into a hypothesis structure.

The useful proof order is:

1. Derive the exact full-cap prefix account and one-coordinate continuation
   lowering bounds from the cap recursion in Section 6.
2. Adapt the pair inactive-gap polynomials and full ambient negative-index
   lemma to the finite union of proper pair traps, with source hyperplanes
   excluding zero gaps and a closed low-successor alternative.
3. Prove the finite-ledger compact-chamber theorem using the common seed,
   lambda<=1/2, and the three minimum-cap cases.
4. Prove the passive-singleton and pair-participant perturbation lemmas,
   including LP preservation for any finite player set and triple-flat
   forcing for Fin4.
5. Obtain arbitrarily small terminal errors in the original reward table
   and apply the named fixed-target semantic consumer.

Useful finite regression inputs are the full table in Section 7, its
zero-gap variant, the constant reward-1 table, and the opposite-sign local
index calculation. The scalar H/J corollary should be a normalization
wrapper around the family theorem. Start with the narrow relevant root,
classification and terminal modules; this theorem does not require a new
foundational strategy model or a broad repository refactor.

## 11. Scope and nonclaims

This is a complete existence theorem for the stated raw classes. It removes
the proper-pair product-low requirement under same-sign joining gaps and
retains higher-support product-lowness plus scalar or finite-family ledger
conditions. It does not prove those conditions for arbitrary Fin4 rewards,
settle opposite-strict-sign pair traps, or settle the full conjecture.

The proof produces absorbing profiles with regret tending to zero, not an
exact absorbing equilibrium, stationary equilibrium, bounded controller,
publicly correlated profile, quantitative horizon bound, or effective rate
of convergence. The no-stationary and persistent-base calculations concern
the explicit witness and the named complete producer selections; they do
not exclude every supplied nonstationary certificate or every possible
reward transport in the repository. The finite-ledger generalization is
not separately counted as new existence coverage without a stronger
independently audited witness. No unrestricted positive-gap counterexample
is claimed, and none of the new theorem is presented as checked Lean.
