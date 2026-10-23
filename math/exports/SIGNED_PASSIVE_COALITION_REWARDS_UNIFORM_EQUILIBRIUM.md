# Signed passive coalition rewards produce stationary equilibrium

This is an ordinary mathematical raw-table producer, not a Lean-checked
result or a proof for every Fin4 table. All strategic data are produced
from the finite reward conditions below.

## 1. Exact raw-data theorem

Let I be a finite player set of size n>=3. At each live date each owner
independently chooses Continue or Quit with private randomization. The
first nonempty quitting coalition S absorbs at a finite vector r(S).
Live dates and literal Never pay zero. A unilateral replacement may be
any complete behavioral strategy; all conclusions are in expectation.

Fix all singleton rows, let s_i=r_i({i}), and put

    Gamma_ii=0, Gamma_ij=r_i({j})-s_i for i!=j.

Suppose Gamma is invertible and there are signs sigma_i in {-1,1}
such that A=Gamma^(-1)diag(sigma) is strictly positive in every entry.
For each i fix an opponent coalition T_i subset I\{i}
with k_i=|T_i|>=2 and a real a_i>0. These coalition choices may differ
and need not form a partition, matching, or cycle.

**Theorem.** For every finite R>=0 there is L0<infinity such that, for
every L>L0 and every ORIGINAL reward table with the fixed singletons and

    r_i(T_i)=-sigma_i a_i L^(k_i-1)+d_i, |d_i|<=R,
    |r_i(S)|<=R at every OTHER nonsingleton coordinate,

there is a full-support stationary exact terminal Nash equilibrium
against every complete unilateral behavioral replacement. Its actual
terminal value is one fixed original-game uniform-equilibrium target,
and the SAME profile works at every positive accuracy over all
sufficiently long finite horizons. The hazards have q_i=z_i/L with z
in one fixed positive compact set depending only on the fixed singleton
rows, a and the coalition choices, not on the bounded completion or L.

The threshold is uniform when the singletons and a range over any compact
set inside the strict signed-inverse-positive / positive-a conditions, with
the T_i and signs fixed and R bounded. All joining rewards are arbitrary
in the bounded box: no no-join inequalities or strategic quantities are inputs.
Own singleton values may have either sign.

For sigma_i=1 the selected coordinate is a large negative passive
penalty; for sigma_i=-1 it is a large positive passive reward. The signs
act only on the root equations. All best-response and payoff comparisons
are proved in the original utilities; no Nash ordering is reversed.

For Fin4 take T_i equal to the opposite pair, so k_i=2 and the four
passive pair rewards are -sigma_i a_i L plus bounded residuals. All forty other
nonsingleton coordinates, including ALL participant coordinates, remain
arbitrary in the fixed bounded box.

## 2. Exact stationary polynomial, with no payoff normalization

For a stationary hazard vector q let p_i(B) be the product probability
of the opponent coalition B subset I\{i}. Define directly from r

    alpha_i=p_i(empty),
    Q_i=sum_B p_i(B) r_i(B+{i}),
    P_i=sum_(B nonempty) p_i(B) r_i(B),
    H_i(q)=(1-alpha_i)Q_i-P_i.                         (2.1)

These quantities use all relevant simultaneous joining and passive
coordinates. No nonempty-coalition offset is applied to live or Never.
Put t=1/L and q_i=t z_i. The selected passive coordinate contributes
to P_i the term

    [-sigma_i a_i t^(-(k_i-1))+d_i] t^(k_i)
       product_(j in T_i)z_j
       product_(j outside T_i+{i})(1-t z_j).

This is divisible by t; its contribution to H_i/t at t=0 is
sigma_i a_i product_(j in T_i)z_j. The selected coordinate does not occur in
Q_i because EVERY coalition sampled there contains i. Bounded
nonsingletons enter H_i/t only with at least one further power of t.
The original singleton terms contribute
s_i sum_(j!=i)z_j - sum_(j!=i)r_i({j})z_j=-(Gamma z)_i.
Therefore the exact polynomial extension is

    Phi_i(t,z,d)=H_i(tz)/t
       =sigma_i a_i Pcal_i(z)-(Gamma z)_i+t E_i(t,z,d),
    Pcal_i(z)=product_(j in T_i)z_j.                  (2.2)

Here d denotes the entire bounded nonsingleton data. E is an actual
finite polynomial, continuous also in the fixed singleton and a data,
not merely a formal asymptotic remainder. Each Pcal_i is homogeneous
of degree k_i>=2 and strictly positive on the positive orthant.
Set

    F_(t,d)(z)=A[diag(a)Pcal(z)+t diag(sigma)E(t,z,d)].  (2.3)

A fixed point of F is equivalent to Phi=0, hence to the actual finite-L
stationary indifference equations. Indeed Gamma^(-1)=A diag(sigma)
and diag(sigma)^2=identity. No sign is applied to a utility inequality.

## 3. Global fixed-point production on a positive shell

Let b=min A_ij>0, B=max A_ij<infinity, and kappa=b/(2nB).
The set

    K={x in R^I: sum_i x_i=1 and x_i>=kappa}

is nonempty compact convex, since kappa<=1/(2n). If w is nonzero and
coordinatewise nonnegative, then

    (Aw)_i / sum_j(Aw)_j >= b/(nB)=2kappa.             (3.1)

The continuous positive function g(x)=sum_i[A diag(a)Pcal(x)]_i has
0<g_min<=g(x)<=g_max on K. Choose 0<ell<1<u with

    ell*g_max<1/2, u*g_min>2.

Define the compact positive shell Z={rho*x: x in K, ell<=rho<=u}.
Because each degree k_i>=2, at t=0 the total mass satisfies

    sum_i F_0(ell*x)_i <= ell^2*g_max < ell/2,
    sum_i F_0(u*x)_i >= u^2*g_min > 2u.              (3.2)

No common degree is needed. Every component a_i Pcal_i(z) has a positive
minimum on Z. The exact polynomial E is uniformly bounded on the product
of Z, [0,1], and the finite bounded reward cube. Thus for all sufficiently
small t>=0, uniformly over that ENTIRE cube,

    w=diag(a)Pcal(z)+t diag(sigma)E(t,z,d)>0,
    F_(t,d)(rho*x)/sum_i F_(t,d)(rho*x)_i belongs to K,
    sum_i F_(t,d)(ell*x)_i<ell,
    sum_i F_(t,d)(u*x)_i>u.                           (3.3)

The normalized-image inclusion follows from (3.1); the two radial
inequalities follow from uniform convergence and the strict margins
in (3.2). Fix such t>0 and bounded d. If f=F_(t,d)(rho*x) and h=sum_i f_i,
then h>0. With clip the continuous projection onto [ell,u], the map

    (x,rho) -> (f/h, clip(2rho-h))                    (3.4)

takes the compact convex set K x [ell,u] continuously to itself. Brouwer
gives a fixed point. At rho=ell, (3.3) gives h<ell and hence the second
component is strictly above ell. At rho=u it gives h>u and the second
component is strictly below u. Thus ell<rho<u at a fixed point.
The equation clip(2rho-h)=rho then forces h=rho, so the direction equation
gives F_(t,d)(rho*x)=rho*x exactly. Put z=rho*x. Shrink the common t0 if
needed so t0*u<1. We have produced

    kappa*ell <= z_i <= u,
    0<q_i=t z_i<1, H_i(q)=0 for every i.               (3.5)

Take L0=1/t0. This proves the raw production claim for every finite
table in the stated family. No supplied limiting root, derivative
nonsingularity, eigenvector, or sign of E is needed.

For compact singleton/a data, continuity of inversion supplies common
b>0, B<infinity and positive bounds on a. Use one K, uniform extrema
g_min,g_max, and one positive compact shell. The same polynomial bounds
then supply one common t0. The argument does not assert uniformity when
an inverse entry or a_i tends to zero.

An explicit finite coefficient choice is available. Put a_min=min_i a_i,
a_max=max_i a_i and

    g_lo=n^2 b a_min kappa^(n-1), g_hi=n^2 B a_max,
    ell=min(1/2,1/(4g_hi)), u=max(2,4/g_lo),
    m=a_min(ell*kappa)^(n-1).

Since 2<=k_i<=n-1, one has g_lo<=g(x)<=g_hi on K and
a_i Pcal_i(z)>=m on the resulting shell. Expand each component of the
EXACT polynomial E after substituting the fixed singleton and a data,
while retaining the bounded completion variables d, as a finite sum of monomials
c*t^p*product_j z_j^(v_j)*product_l d_l^(w_l), and define

    C_E=1+SUM_(all component monomials)
                  |c| u^(SUM_j v_j) max(1,R)^(SUM_l w_l).

This bounds every |E_i| on t in[0,1], |z_i|<=u and |d_l|<=R. Thus one
valid raw threshold is L0=1/t0, where

    t0=min(1,1/(2u),m/(2C_E),
               ell/(4n^2 B C_E),u/(n^2 B C_E)).       (3.6)

For 0<t<t0, every preimage component in (3.3) exceeds m/2. The total
mass perturbation is at most n^2 B C_E t, while the unperturbed inner
mass is at most ell/4 and outer mass at least4u. Hence the inner mass
is below ell/2 and outer mass above3u. Also q_i<=tu<1/2. This gives
the required threshold by finite coefficient bounds rather than an
unproduced strategic selection or regularity radius.

## 4. Actual values, literal Never and every complete deviation

Fix one produced finite table and hazard vector. Every deleted-opponent
survival mass alpha_i is less than one. The actual stationary policy
payoff is

    U_i=[q_i Q_i+(1-q_i)P_i]/[1-(1-q_i)alpha_i].       (4.1)

Indeed joint absorption is proper and its geometric recursion has this
unique solution. Since H_i=0, equation (2.1) yields

    U_i=Q_i=P_i/(1-alpha_i)=P_i+alpha_i U_i.            (4.2)

A pure deadline d>=0 earns

    P_i(1-alpha_i^d)/(1-alpha_i)+alpha_i^d Q_i=U_i.

Literal Never earns P_i/(1-alpha_i)=U_i. On the unique live history a
complete behavioral replacement is a private mixture of these pure
deadlines and Never, independent of the opponents' seeds. Hence EVERY
unilateral replacement has exactly the prescribed terminal payoff.
This is full behavioral Nash, not merely a stationary comparison.

Let C=max |r_i(S)| for this fixed table. Under any unilateral replacement,
the first opponent quit has expected date plus one 1/(1-alpha_i), and
absorption occurs no later. With the selecting live date paying zero,
the absolute difference between expected terminal and N-stage average
payoff is at most C/[N(1-alpha_i)]. The same bound applies to the
prescribed profile. Thus all finite-horizon gains are at most
2C/[N(1-alpha_i)], and delivery converges to the one fixed U. Choose one
produced profile once per table; neither the profile nor U need depend
on accuracy. This proves the stated original-game UE contract.

## 5. Conjecture-facing change and source distinction

The positive-inverse shell argument is the same general fixed-point
method used for positive PARTICIPANT coalitions. The new source term
is different: a large signed PASSIVE coordinate occurs in -P_i,
whereas a positive participant coordinate occurs in (1-alpha_i)Q_i.
For a passive coalition of size k, the scaling is L^(k-1) and the leading
monomial has degree k. A large positive participant coalition of size k
also uses scaling L^(k-1), but has leading factor
(sum_(j!=i)z_j) product_(j in S\{i})z_j. Either is positive on the shell,
but the previous participant-reward hypothesis does not allow replacing
its selected coordinate by an unbounded passive coordinate.

The new theorem consequently covers entire negative-passive rays with
every participant reward fixed. It requires no sign or pair-sum bound
on those fixed participant rewards. The following exact family also
fails the existing paired-phase and endpoint-pole admission tests.

## 6. A full60 direction outside the older admissions

For Fin4 let mate(i)=i xor1, O(i)=I\{i,mate(i)}, and let
h=(0->2->1->3->0). Set original r_i(S)=1+Z_i(S) for nonempty S.
For i absent from S define

    Z_i({mate(i)})=3, Z_i({j})=-1 for j in O(i),
    Z_i(O(i))=-M,
    Z_i(S)=0 at every other opponent pair or opponent triple.

For i in S define

    Z_i({i})=0, Z_i({i,mate(i)})=0,
    Z_i({i,j})=1 if i=h(j), otherwise -3/2, j in O(i),
    Z_i({i}+O(i))=1000,
    Z_i(S)=-100 at each other containing triple,
    Z_i(I)=-1000.                                    (6.1)

This defines all60 entries. The fixed original own levels are one;
literal AllNever is not Nash. Gamma is the paired3/-1 matrix with

    Gamma^(-1)=(1/15)[[2,7,3,3],[7,2,3,3],
                       [3,3,2,7],[3,3,7,2]]>0.

This entire ray belongs to the theorem with T_i=O(i), a_i=1, residual
d_i=1, and R=1001 for every sufficiently large M. All joining data
remain FIXED. Its positive recruit cycle is h; other joining increments
against a singleton are -3 at a mate and -1/2 at the other cross owner.

The low-passive friendly-pair class with scheduled Pi=0 has c=-3 and
requires each opposite-participant sum <=-6 and each queried triple <=-6.
Here the sum is -1/2 and the queried triple is1000. More strongly, for
ANY common hazard q in(0,1) that solves its active and passive equality
equations, let x=1-q. Inactive native Quit minus Continue is

    q[3/x - x/2 + 1000q]>0.                           (6.2)

Thus its actual common-hazard friendly-pair strategy fails a full cap,
independently of the finite threshold or root selection.

For the three-passive-poles class, write ordered roles (u,v,w,z). Its
necessary guards include A0=Z_u({u,z})-Z_u({z})>0,
B0=Z_u({u,w,z})-Z_u({w,z})<0, d=A0/(A0-B0), and

    F1=(1-d)[Z_z({u,z})-Z_z({u})]
       +d[Z_z({u,w,z})-Z_z({u,w})]<0.

A0>0 forces u=h(z). Choosing w=mate(z) gives B0=1000+M>0 and fails.
The other possibility w=mate(u) gives exactly four role permutations:
(0,2,1,3),(1,3,0,2),(2,1,3,0),(3,0,2,1). All have A0=2, B0=-100,
d=1/51, but

    F1=(-25+1000+M)/51=(M+975)/51>0                  (6.3)

for every M>0. Thus all24 roles fail, without a threshold ambiguity.

The remaining direct selection obstructions are exact for every M>0:

- The universal product-low criterion fails at the full-support product
  root with equal hazard 1/10: EVERY forced-Quit native premium is
  -(1/2)(1/10)(9/10)^2+800(1/10)^2(9/10)-1000(1/10)^3
  =12319/2000>0. This value is independent of M, because passive rewards
  never enter a forced-Quit expectation. The same witness precludes
  every nonzero nonnegative weighted forced-Quit upper-average test on
  the full trap: taking its expectation at this product root is positive.

- No pure quitting coalition is Nash. A singleton recruits h(j); a mate
  pair has leave gain3; a cross pair has a member with leave gain1/2;
  each triple has mate members receiving -100 who can leave for passive
  cross-pair0; and grand members leave -1000 for opponent-triple0.
- Fixing a sure owner j, its mate strictly Continues against every event
  containing j. Then l=mate(h(j)) strictly Continues against {j} and
  {j,h(j)}, with joining gains -1/2 and -100. Finally h(j) Quits surely
  with gain2. This is the entire complementary induced Nash set. The
  owner j then has leave gain1/2 and empty-opponent mass0. Hence EVERY
  punishment floor fails. A persistent multiowner base with its free
  Nash and outsider screens would yield a sure-owner stationary Nash,
  contradicting the same strict elimination.
- Every nonempty proper child S has a directed edge j in S to h(j)
  outside S. The outsider's joining J row at {j} has gain2, whereas
  every available child responder has gain0, -3, or -1/2. No nonnegative
  child weight vector can satisfy that row. Thus all child selections
  and all capped-clock weights fail, including the Never-row relaxation.
- Every pair partition has a negative participant joining increment:
  -3 on each mate pair, and -1/2 for one member of every cross pair.
  Therefore all schedules requiring nonnegative joining increments fail.
  Every cross pair also has a positive increment2, so schedules requiring
  BOTH cross participants below their negative passive singleton fail.
  Every positive singleton pair is a mate pair, with participant0<3,
  excluding a positive-premium friendly seed. In signed-inverse pair
  tests Gamma^(-1)>0 forces all column signs positive, leaving the same
  failed positive-increment requirement.
- The full-set premium trap has size-two joining sum 2(1000+M)>0 at
  either mate pair, violating the required nonpositive intermediate row.
  The own-level capped-participant class fails because it has participant
  rewards2 and1001 above original own1.
- Weighted passive ledgers H_w(S)=sum_i w_i Z_i(S)>=0 at both mate pairs
  would force all nonnegative weights to vanish, since their two outside
  entries are -M and their own participant entries are0.
- No global nonnegative forced-Quit floor weight exists either. Its
  singleton rows would require w_(h(j))>=(3/2)w_(h^(-1)(j)) for each j;
  taking all four gives w_0=w_1=w_2=w_3=0. Every player also has a
  negative participant premium -3/2, so the protected set of players
  with all participant premiums nonnegative is empty. The full set is
  a premium trap, so greatest-core size<=2 or exactly3 criteria fail.
- Every positive singleton-joining edge j -> h(j) reverses strictly on
  background {mate(h(j))}, where its gain is -100. Thus no-strict-
  background-reversal and robust-join-cycle criteria do not apply.
- Gamma's strict reciprocal signs leave no balanced-singleton escort edge.
  Every proper triple has a row with two negative entries, precluding a
  nonnegative inverse. The negative cross2x2 block fails both ordinary Q
  and the homogeneous simplex branch, so projective Q-bar also fails.

The previous positive-participant jackpot rays keep unselected coordinates
bounded and make some participant rewards grow. Here every participant
coordinate is fixed and the only unbounded entries are negative passive
ones. This is a different raw direction, not a different strategy on one
of those previously covered rays. No exclusion of every arbitrary fully
mixed stationary certificate is claimed; this theorem actually produces one.

These are finite admission comparisons and an asymptotic-direction
comparison with participant jackpots. No noncoverage of every isolated
table by an unspecified older large-parameter threshold or qualitative
neighborhood radius is asserted.

## 7. Exact symmetric stationary calibration

The family (6.1) is invariant under h, so equal stationary hazards q
have a common native forced-Quit value and passive absorption contribution

    Q(q)=-(1/2)q x^2+800q^2x-1000q^3,
    P(q)=q x^2-Mq^2x, x=1-q.

Set

    M(q)=[q x^2-(1-x^3)Q(q)]/(q^2 x).                (7.1)

For every sufficiently small positive q this is positive, tends to
infinity, and satisfies M(q)=1/q+1/2+O(q). Equation (7.1) is an exact
equality P=(1-x^3)Q, so all eight stationary endpoints are equal.
This is a calibration, not a strategic input in the theorem. The theorem
produces a stationary root for EVERY sufficiently large M, independently
of any inversion of (7.1). The explicit rational test q=1/100000 has
M(q)>100000 and belongs to all the displayed old-selection exclusions.

The positive leading field test has sigma_i=1 and z=(1,1,1,1): each
Pcal_i(z)=1 and Gamma*z=(1,1,1,1). Keeping sigma_i=1, but taking every
off-diagonal Gamma_ij=-1,
the leading field diag(a)Pcal(z)-Gamma*z is strictly positive for every
z>0, so no positive root exists. Dropping inverse positivity invalidates
this scale of construction; it does not refute equilibrium at other scales.

There is also an exact signed test for ALL16 sign patterns: replace
every nonempty native row Z_i(S) in (6.1) by sigma_i Z_i(S), and keep
original own level1. The new matrix is diag(sigma)Gamma, whose inverse
times diag(sigma) is the same strictly positive matrix displayed above.
Selected passive rewards are 1-sigma_i M. At the rational profile in
(7.1), direct original payoff calculation gives every forced endpoint
and literal Never the value 1+sigma_i Q(q). Thus all sign choices work
without relying on a general utility-reversal invariance principle.

## 8. Adapter, semantic consumer and Lean handoff

The existing stationary endpoint consumer is
`isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts` and
`isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`
(`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`). The
mathematical raw adapter here must produce q, then value=Q, root Nash
from H=0, and alpha_i<1. No strategic object belongs in its input
structure. The proof supplies every one of these premises, and Section4
also proves the all-behavior/uniform conclusion directly.

For a Lean handoff the input structure should contain only the finite
player set, singleton table, signs, invertibility and strict signed-inverse
positivity, coalitions T_i, positive a_i, bounded raw completion and the
threshold comparison. A finite polynomial lemma proves (2.2), including
that every selected passive coordinate is absent from Q_i. The geometric
lemma produces an exact fixed point from the positive inverse, positive
monomials of degrees at least two, and the finite polynomial error bound.
It should return z with the explicit positive bounds, not assume z or
an equilibrium as a field. Bernoulli hazards q=t z then give

1. joint Continue mass product_i(1-q_i)<1;
2. value=Q equal to its actual successor, by (4.1)--(4.2);
3. both pure stationary endpoints equal to value, hence
   `IsεQuittingRootEndpointNash reward value 0 root`;
4. every deleted-opponent Continue mass alpha_i<1.

These are every premise of the existing stationary consumer. The proof
works directly in original signed rewards and keeps one actual payoff
target fixed before accuracy.

The source comparisons use the following exact implemented criteria,
with their needed conditions and failure witnesses stated in Section6:

- `HasProductLowQuittingPremium`
  (`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`)
  and `exists_uniformEquilibriumPayoff_of_productLowPremium`
  (`UniformEquilibrium/Quitting/Classification/Existence/ProductLowPremiumUniformPayoff.lean`):
  the equal-hazard1/10 witness violates the required low active coordinate.
- `CappedClockParentRewardCertificate`
  (`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`):
  every child choice has a literal impossible joining row for all weights.
- `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
  `nonempty_quittingSingletonBaseCertificate_of_inducedNash`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`):
  the complete complementary induced correspondence has leave gain1/2
  and zero coefficient on every punishment floor.
- `nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
  `exists_uniformPayoff_of_persistentBase_inducedNash_signs`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`):
  their free-player, base-leave and outsider signs would contradict the
  complete sure-owner exclusion, including all base/free selections.
- `QuittingInducedOwnerChamber` and `QuittingInducedOwnerNeverChamber`
  (`UniformEquilibrium/Diagnostics/Quitting/InducedOwnerChambers.lean`):
  the same induced-floor failure excludes the former, and original own1
  additionally violates the latter's own-singleton-nonpositive premise.
- `BalancedSingletonCycleCertificate.exists_escortCycle`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`):
  an escort edge would require Gamma_ij<=0<=Gamma_ji for i!=j, impossible
  under the strict reciprocal same signs of the calibration.
- `isProjectiveQMatrix_iff_standard_or_homogeneous` and
  `IsProjectiveQBarMatrix`
  (`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`):
  the negative cross block maps every z>=0 to (-z_1,-z_0). It has neither
  a standard solution at offset(-1,-1) nor a nonzero homogeneous simplex
  solution, so both branches fail on that principal block.
- `finFour_exists_uniformPayoff_of_noStrictBackgroundReversal`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/RobustJoinStrictBackgroundReversal.lean`):
  each positive cycle edge has the explicit strict reversing background.

These library declarations were inspected as source correspondences;
the new coefficient producer and its formalization have not been checked
in Lean. The full response and uniform statements above are ordinary
mathematical proofs, not claims that this new raw theorem is implemented.

## 9. Complete exact calibration program

Run the following self-contained Python3 program. It uses standard-library
rational arithmetic. It verifies all60 original coordinates, every
stationary endpoint and literal Never, all finite selections listed in
the printed summary, the product-low counterwitness, and all16 inverse
column-sign patterns. Its deadline samples supplement Section4's proof
for every complete behavioral replacement.

```python
"""Exact new full60 stationary ray and complete finite selection obstructions."""
from fractions import Fraction as F
from itertools import combinations, permutations, product

I = frozenset(range(4))
SETS = [frozenset(s) for n in range(1, 5) for s in combinations(I, n)]
H = (2, 3, 1, 0)
q, x = F(1, 100000), F(99999, 100000)
quit_native = -q*x*x/2 + 800*q*q*x - 1000*q**3
M = (q*x*x-(1-x**3)*quit_native)/(q*q*x)
assert M > 100000


def mate(i):
    return i ^ 1


def opposite(i):
    return I - {i, mate(i)}


def native(i, s):
    assert s
    if i not in s:
        if len(s) == 1:
            return F(3 if mate(i) in s else -1)
        return -M if s == opposite(i) else F(0)
    if len(s) == 1:
        return F(0)
    if len(s) == 2:
        j = next(iter(s-{i}))
        return F(0) if j == mate(i) else (F(1) if H[j] == i else F(-3, 2))
    if len(s) == 3:
        return F(1000 if s-{i} == opposite(i) else -100)
    return F(-1000)


Z = {(i, s): native(i, s) for i in I for s in SETS}
R = {key: 1+value for key, value in Z.items()}
assert len(R) == 60
for i in I:
    assert R[i, frozenset({i})] == 1
    assert R[i, opposite(i)] == -M+1
    for s in SETS:
        if len(s) >= 2 and s != opposite(i):
            assert abs(R[i, s]) <= 1001


def join(i, s):
    return Z[i, s|{i}]-Z[i, s]


def prob(s, players):
    return q**len(s) * x**(len(players)-len(s))


alpha = x**3
u = 1+quit_native
for i in I:
    others = I-{i}
    coalitions = [frozenset()] + [s for s in SETS if s <= others]
    quit_value = sum(prob(s, others)*R[i, s|{i}] for s in coalitions)
    passive = sum(prob(s, others)*R[i, s] for s in coalitions if s)
    assert quit_value == u
    assert passive/(1-alpha) == u  # literal Never
    assert passive+alpha*u == u  # forced Continue
    prescribed = sum(prob(s, I)*R[i, s] for s in SETS)/(1-x**4)
    assert prescribed == u
    for deadline in range(20):
        assert passive*(1-alpha**deadline)/(1-alpha)+alpha**deadline*quit_value == u
    assert -q*x/2+1000*q*q > -3*q/x  # prior common pair cap fails

for s in SETS:
    gains = []
    for i in I:
        altered = s-{i} if i in s else s|{i}
        gains.append((R[i, altered] if altered else F(0))-R[i, s])
    assert max(gains) > 0
for j in I:
    k, m = H[j], mate(j)
    l = mate(k)
    for s in SETS:
        if j in s and m not in s:
            assert join(m, s) < 0
    assert join(l, frozenset({j})) == F(-1, 2)
    assert join(l, frozenset({j, k})) == -100
    assert join(k, frozenset({j})) == 2
    assert join(j, frozenset({k})) == F(-1, 2)
for child in SETS:
    if child == I:
        continue
    j = next(j for j in child if H[j] not in child)
    assert join(H[j], frozenset({j})) == 2
    assert all(join(i, frozenset({j})) in {-3, F(-1, 2)} for i in child-{j})

for j in (1, 2, 3):
    for pair in (frozenset({0, j}), I-{0, j}):
        a, b = sorted(pair)
        inc = sorted([join(a, frozenset({b})), join(b, frozenset({a}))])
        assert inc == ([-3, -3] if mate(a) == b else [F(-1, 2), 2])
for pair in (frozenset({0, 1}), frozenset({2, 3})):
    assert sum(join(i, pair) for i in I-pair) == 2*(1000+M) > 0
    assert all(Z[i, pair] == 0 for i in pair)
    assert all(Z[i, pair] == -M for i in I-pair)


def z(i, *s):
    return Z[i, frozenset(s)]


possible_roles = []
for a, b, c, d in permutations(I):
    a0, b0 = z(a, a, d)-z(a, d), z(a, a, c, d)-z(a, c, d)
    if not (a0 > 0 and b0 < 0):
        continue
    possible_roles.append((a, b, c, d))
    mixing = a0/(a0-b0)
    f1 = ((1-mixing)*(z(d, a, d)-z(d, a))
          + mixing*(z(d, a, c, d)-z(d, a, c)))
    assert (a0, b0, mixing) == (2, -100, F(1, 51))
    assert f1 == (M+975)/51 > 0
assert possible_roles == [(0, 2, 1, 3), (1, 3, 0, 2), (2, 1, 3, 0), (3, 0, 2, 1)]

G = [[F(0) if i == j else Z[i, frozenset({j})] for j in I] for i in I]
A = [[F(v, 15) for v in row] for row in
     [[2, 7, 3, 3], [7, 2, 3, 3], [3, 3, 2, 7], [3, 3, 7, 2]]]
assert all(sum(G[i][k]*A[k][j] for k in I) == int(i == j) for i in I for j in I)
assert all(sum(G[i]) == 1 for i in I)  # leading root z=(1,1,1,1)
assert all(G[i][j]*G[j][i] > 0 for i in I for j in I if i != j)
for omitted in I:
    assert all(G[mate(omitted)][j] < 0 for j in I-{omitted, mate(omitted)})

# Exact failure of the universal product-low admission, independently of M.
probe = F(1, 10)
probe_value = -probe*(1-probe)**2/2 + 800*probe**2*(1-probe) - 1000*probe**3
assert probe_value == F(12319, 2000) > 0
for i in I:
    others = I-{i}
    menu = [frozenset()] + [s for s in SETS if s <= others]
    forced_premium = sum(probe**len(s)*(1-probe)**(3-len(s))*Z[i, s|{i}] for s in menu)
    assert forced_premium == probe_value
    assert min(Z[i, s] for s in SETS if i in s) < 0
    assert join(H[i], frozenset({i, mate(H[i])})) == -100
traps = [a for a in SETS if all(
    any(s <= a and i in s and Z[i, s] > 0 for s in SETS) for i in a)]
assert traps == [I]

# All16 inverse-column sign patterns, checked in actual original utilities.
for signs in product((-1, 1), repeat=4):
    signed_reward = {(i, s): 1+signs[i]*Z[i, s] for i in I for s in SETS}
    signed_gamma = [[signs[i]*G[i][j] for j in I] for i in I]
    signed_inverse = [[A[i][j]*signs[j] for j in I] for i in I]
    assert all(sum(signed_gamma[i][k]*signed_inverse[k][j] for k in I) == int(i == j)
               for i in I for j in I)
    assert all(signed_inverse[i][j]*signs[j] > 0 for i in I for j in I)
    for i in I:
        assert signed_reward[i, opposite(i)] == 1-signs[i]*M
        for s in SETS:
            if len(s) >= 2 and s != opposite(i):
                assert abs(signed_reward[i, s]) <= 1001
        others = I-{i}
        menu = [frozenset()] + [s for s in SETS if s <= others]
        qi = sum(prob(s, others)*signed_reward[i, s|{i}] for s in menu)
        pi = sum(prob(s, others)*signed_reward[i, s] for s in menu if s)
        ui = 1+signs[i]*quit_native
        assert qi == pi/(1-alpha) == pi+alpha*ui == ui
        policy = sum(prob(s, I)*signed_reward[i, s] for s in SETS)/(1-x**4)
        assert policy == ui
print("PASS full60: bounded arbitrary joining ray, exact stationary policy/Quit/Continue/Never")
print("PASS all15 pure coalitions, all4 induced/punishment sets, all14 proper-child weight rows")
print("PASS all3 pair partitions, all24 pole roles, previous friendly common-hazard cap failure")
print("PASS positive inverse, leading root, trap/ledger/escort/deleted-triple obstructions")
print("PASS product-low exact counterwitness; empty protected set; full premium core")
print("PASS all16 inverse-column sign patterns, original endpoint and Never values")
print("Exact M:", M)
```

## 10. Scope and remaining frontier

The theorem is an actual existence producer on a signed inverse-column
and large passive-coalition reward region, with every bounded joining
completion allowed. It does not cover arbitrary singleton matrices,
arbitrary fixed magnitudes of the selected passive rewards, or the entire
four-player quitting-game conjecture. The positive shell and all tests
concern actual finite tables at fixed L. No changing reward table,
limiting cemetery value, public correlation, or supplied strategic witness
is used to satisfy the equilibrium accuracy quantifier.

