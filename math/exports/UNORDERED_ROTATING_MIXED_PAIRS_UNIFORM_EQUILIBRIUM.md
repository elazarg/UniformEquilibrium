# Rotating mixed-premium pairs with independent passive rewards

This is a complete raw four-player existence theorem in ordinary mathematics.
It produces an exact absorbing periodic terminal Nash profile and one fixed
uniform-equilibrium target. No strategy, root, continuation value, punishment
tail, or cycle certificate is an input. No new Lean verification or general
Fin4 closure is claimed.

## 1. Original game, raw hypotheses, and conclusion

There are four owners I=Z/4Z. At every live date each independently chooses
Continue or Quit using private randomization and the public history. The
first nonempty quitter coalition A absorbs at the finite vector r(A), paid
thereafter. Live dates, including the selecting date, and perpetual Continue
pay zero. Deviations replace one owner's ENTIRE behavioral strategy,
including arbitrary memory, private randomization, delayed quitting and
literal Never. No correlating device or additional observation is used.

Choose arbitrary finite own levels s_i and positive recipient scales lambda_i.
For nonempty coalitions only write

    Z_i(A)=(r_i(A)-s_i)/lambda_i.

This is raw comparison notation; the original live and Never rewards stay
zero. The singleton conditions below force s_i=r_i({i}). Relabelings are
allowed. The theorem has no sign condition on s.

Choose a>2b>0 and arbitrary finite K2,K3. Assume either

    K2>=0, or 2<a/b<=(67+12 sqrt(6))/25.                 (U)

There is no ordering or magnitude restriction on K3. For each i modulo4 require

    Z_i({i})=0,
    Z_i({i-1})=Z_i({i+1})=-b, Z_i({i+2})=a,
    Z_i({i,i+1})=b/2, Z_i({i,i-1})=-b/2,
    Z_i({i+2,i+3})=K2, Z_i({i+1,i+2})=K3,
    Z_i({i,i+2})<=-b,
    Z_i({i,i+2,i+3})<=K2-a-b/2,
    Z_i({i,i+1,i+2})<=K3+b/2.                       (N)

The remaining sixteen nonsingleton coordinates are arbitrary finite
numbers. The displayed twelve participant upper bounds need not be
equalities. The forward participating pair premium is POSITIVE. Moreover,
the final triple cap permits a strictly positive joining increment b/2
against the prescribed passive pair, so the class does not require a
pure adjacent pair to deter both outsiders.

For later comparisons define Gamma_ij=Z_i({j}) and J_ij=Z_i({i,j})
for i!=j, with both diagonals zero.

**Theorem.** Every table satisfying(U) and(N) has an exact proper period-four
terminal Nash profile, with chronological pairs01,12,23,30, against
all complete behavioral replacements. Its actual initial value is a
fixed uniform-equilibrium target. Arbitrary signed own offsets and
positive recipient scales are allowed as proved below.
No strategic root, continuation, rate, or cycle witness is an input.

## 2. Conjecture-facing change, produced inputs, and source correspondence

For every fixed singleton ratio2<a/b<=(67+12 sqrt(6))/25, the admitted
passive region is the ENTIRE plane of independent finite K2,K3. This includes
arbitrarily negative rewards, large opposite signs, and either ordering.
For every singleton ratio a/b>2, the additional half-plane K2>=0 works with
K3 unrestricted. The forward participant premium is positive, and the
second triple cap permits an outsider joining gain b/2 against a pure pair.

The new content is selection of a scalar root with every inactive incentive
valid. A root with active indifference need not satisfy the inactive caps;
one earlier bad-root example also has another root that is valid. The proof
below controls the entire possibly bad interval and selects outside it.
No strategic witness remains assumed. The full60 unequal-passive ray in
Section6 and all-role comparisons in Section7 separate the newly admitted
family from the stated preceding producers. The explicit ratio is a
sufficient threshold, not claimed sharp for the periodic architecture.

The actual root endpoints and policy equations correspond to
`quittingRootSuccessorPayoff` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` and
`IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean`.
The existing exact periodic consumers are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Their three
inputs are the policy recursions, exact phase Nash inequalities, and a
strict opponent-deleted period-survival bound for every owner. All three
are supplied explicitly below. The consumer produces a fixed target,
with the same profile at every accuracy. It does not produce rates from
raw rewards; that production and its complete bounds are the new content.

For the bounded comparisons, the exact source declarations are:

* `CappedClockParentRewardCertificate` in
  `UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`;
* `quittingSingletonBaseOwnerFloorExcess` and
  `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`;
* `QuittingSingletonBaseCertificate.isUniformEquilibriumPayoff` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/SingletonBaseSemanticDispatch.lean`;
* `HasGlobalQuittingWeightedFloor` and `HasWeightedQuittingTrapLeavers` in
  `UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`;
* `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`;
* `IsQuittingSingletonEscortEdge` in
  `UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`; and
* `isProjectiveQMatrix_iff_standard_or_homogeneous` and
  `IsProjectiveQBarMatrix` in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.

These source comparisons do not claim that failure of a sufficient
criterion disproves equilibrium. The direct construction supplies equilibrium.

## 3. Scalar production and the only remaining incentive

For y in(0,1), put

    x=y/(1+y), C=(1-y)/(1+y), V0=by/2, V1=-bx/2,
    V2=a x(1-y)-b(1-x)y+K2 xy+C V1,
    T3=-b x(1-y)+a(1-x)y+K3 xy+C V2,
    Phi=T3-3by/[2(1-y)].

At a root of Phi, set V3=3by/[2(1-y)]. The four phases are01,12,23,30,
with hazards x,y on the displayed ordered pair. The phase-t value for owner i
is V_((i-t) mod4). At phase01 the next rotated value vector is(V3,V0,V1,V2).
The active owner0 has Quit value by/2=V0 and Continue value
-by+(1-y)V3=V0. Owner1 has Quit value-bx/2=V1 and Continue value
-bx+(1-x)V0=V1 because y(1-x)=x. The passive owner2 recursion is
exactly V2, and owner3's is T3=V3. Thus every policy recursion and active
indifference holds without ordering K2,K3.
The owner2 inactive inequality is strictly valid for every y in(0,1):

    g2<=y[-2a(y+1)+by^2-by]/[2(1+y)^2]<0.

For owner3 the three nonempty opponent outcomes have caps b/2,-b,K3+b/2.
The actual gap at these caps is

    g3=(3b/2)x-(a+b)y+a xy-C V2.

The +a xy term is essential; it retains the positive triple joining payoff.
Direct simplification gives

    g3=-y P(y)/(1+y)^3,
    P(y)=(a+b-K2)y^3+2by^2+(a+b+K2)y+2a-2b.       (P)

Thus a root is good precisely when P(y)>=0 at the saturated caps.
Smaller participant rewards only improve the relevant inequalities.
Define

    A(y)=(a+b)y^3+2by^2+(a+b)y+2a-2b,
    H(y)=b(y+2)/[y(1-y)],
    F(y)=H(y)-P(y)/[y(1+y)^2].                     (F)

Direct cancellation gives Phi=xy[K3-F(y)]. In particular the root equation
is K3=F(y), and F tends to negative infinity at0 and positive infinity at1.
The gap formula is valid directly from V2, not an estimate that assumes the
root equation. A(y)>0 on(0,1), so K2>=0 makes P=A+K2 y(1-y^2)>0
everywhere and proves the first alternative of(U).

### 3.1 The unique possible bad interval

Suppose K2<0. Define

    D(y)=A(y)/[y(1-y^2)]
        =-a-b+b/(1+y)+(2a+b)/(1-y)+2(a-b)/y.

It diverges at both endpoints and is strictly convex, since

    D''(y)=2b/(1+y)^3+2(2a+b)/(1-y)^3+4(a-b)/y^3>0.

Consequently either P>=0 everywhere, or there are unique
0<alpha<beta<1 such that P is negative exactly on(alpha,beta).
Indeed P has the sign of D+K2; strict convexity and endpoint divergence
give the complete level-set alternatives, including the double-zero case.
At the two simple boundaries, F(alpha)=H(alpha), F(beta)=H(beta).

Continuity alone proves the following useful general selector:

    K3<=H(alpha) OR K3>=H(beta)  => a good root exists.             (S)

For the first inequality apply the intermediate value theorem on(0,alpha];
for the second apply it on[beta,1). Equality is allowed and gives an
inactive owner indifferent between the endpoints. This is a sufficient
selector, not a necessary condition: F can have extrema within the good
regions beyond their boundary heights.

### 3.2 The endpoint comparison for an entire passive plane

Write r=a/b, s=alpha+beta, p=alpha beta, and z=1-s. Equality of the two
D values gives

    1/(1+s+p)-(2r+1)/(1-s+p)+2(r-1)/p=0.          (E)

First z>0. To see this, put q=1-s+p>0 and t=1+s+p>q.
Equation(E) rearranges to

    2r(q-p)=2q+p-pq/t>0,

because pq/t<p. Hence q-p=z>0; also z<1 since s>0.
Solving(E) now gives the exact identity

    r=(p^2-pz+3p-z^2+2z)/[z(p-z+2)].              (R)

The endpoint height difference has the sign of2-2s-p=2z-p:

    H(alpha)-H(beta)
      =b(beta-alpha)(2z-p)/[p(1-s+p)].             (H)

Assume for contradiction H(alpha)<=H(beta), so p>=2z. Distinct roots give
p<s^2/4=(1-z)^2/4, hence

    0<z<z0:=5-2 sqrt(6).

The following exact subtraction has only positive denominators:

    r-(z+8)/(z+2)
      =(p-2z)(pz+2p-3z+6)/[z(z+2)(p-z+2)]>=0.

The second numerator factor is positive because0<z<1 and p>0. Since
(z+8)/(z+2) is strictly decreasing,

    r >= (z+8)/(z+2) > (z0+8)/(z0+2)
      = (67+12 sqrt(6))/25.

This contradicts(U). Therefore H(alpha)>H(beta) whenever the ratio
alternative of(U) holds. The two ranges in(S) overlap and cover every
real K3. This proves the theorem, including the weak upper ratio boundary.
No continuity in parameters, generic roots, or principal-minor guards are
needed.

At the selected root all sixteen phase inequalities hold. The joint
survival per phase is C, own survival per period is C, and deleted-opponent
survival per period is C^3<1. The direct proof in Section5 therefore supplies
actual full terminal Nash and one fixed uniform target, with signed own
levels. In particular the conclusion concerns all behavioral deviations,
not merely deviations within the four-phase family.

## 4. Actual produced phase certificate

If P>=0 everywhere, the continuity limits for F select any proper root.
Otherwise Section3.2 proves H(alpha)>H(beta). Choose a root in(0,alpha]
when K3<=H(alpha), and a root in[beta,1) when K3>=H(beta). The two
choices cover every real K3; no uniqueness or genericity is required.
At that root owner2 strictly Continues and owner3 weakly Continues.
Both active owners mix between equal endpoints. Rotating the calculations
checks all sixteen phase/player comparisons, including every simultaneous
coalition and every stricter permitted cap. The selected y lies strictly
between0 and1, x=y/(1+y) is proper, and the target is fixed once this
root has been selected. No target depends on the requested accuracy.

## 5. Actual laws, all deviations, and one fixed target

Repeat the four pairs with these fixed hazards and independent private
coins. Joint survival is C per phase, while every owner's survival per
period is C; hence deleted-opponent survival per period is C^3<1.
The Bellman recursion with residual C^(4n) identifies the rotated V
vectors as actual payoffs. Iterating the Continue equality and final Quit
inequality prices every finite deadline; iterating forever prices literal
Never, with vanishing residual bounded by C^(3n). Mixtures price every
complete behavioral replacement. Thus the produced profile is exact
terminal Nash. Arbitrary signed own offsets and positive scales preserve
these comparisons because opponents absorb under every deviation.

If R bounds absolute original rewards, the expected opponent stopping
date plus one is at most4/(1-C^3)+1. The absolute terminal-versus-N-stage
average discrepancy is at most R[4/(1-C^3)+1]/N uniformly over all
deviations. Consequently the same profile gives one fixed uniform target.
The target is its actual initial transformed V, selected before accuracy.

## 6. Full sixty-entry calibration and complete selection tests

Fix a=3,b=1,K2=K>=10,K3=2K and original own levels1. All displayed
entries below are NATIVE; add1 to every recipient to obtain the original
table. The following rules specify all60 coordinates, with indices modulo4:

    singleton i: own0, opposite3, neighbors-1;
    adjacent pair{i,i+1}: recipient i gets1/2,
        recipient i+1 gets-1/2, outsider i+2 getsK and outsider i+3 gets2K;
    opposite pair: every recipient gets-1;
    triple{i,i+1,i+2}: the respective participant values are
        2K+1/2, 1, K-7/2, and the outsider gets100;
    grand coalition: every recipient gets98.             (T)

Equivalently, let F_i(empty)=0, F_i(singleton j)=Gamma_ij,
F_i({i+2,i+3})=K, F_i({i+1,i+2})=2K,
F_i(opposite opponent pair)=-1,
F_i(all three opponents)=100. With Lnext=3/2,Lprevious=1/2,
Lopposite=-4, put

    Z_i(A)=F_i(A\{i})+1_(i in A)sum_(j in A)L_ij
                    +3*1_(A={i,i+1,i+2}).                (T2)

The positive correction in(T2) is essential. It is present in the actual
reward table, not a discarded collision error.

### 6.1 Entire induced Nash correspondences and actual punishment floors

For a sure owner0 let u=q1,v=q2,w=q3. The three complementary owners'
literal Quit-minus-Continue fields, reconstructed from all60 entries, are

    f1=1/2+3v/2-4w,
    f2=-4+u/2+9w/2-3uw,
    f3=3/2-u+v/2-3uv.                                  (F)

They are independent of K and of every continuation because owner0 is
sure. If u>0, supported optimality gives f1>=0, hence
w<=(1+3v)/8<=1/2. Since9/2-3u>0, this implies
f2<=-7/4-u<0, forcing v=0. Then f3=3/2-u>=1/2>0 forces
w=1, contradicting w<=1/2. Thus u=0. Now f3=3/2+v/2>0
forces w=1, after which f2=1/2>0 forces v=1.

Conversely (u,v,w)=(0,1,1) satisfies every complementary Nash
inequality. This proves the ENTIRE correspondence is the single pure
law q=(1,0,1,1), including all boundary and singular possibilities.
Rotations give the other three sure-owner correspondences. The forced
owner's own joining gap at its law is-7/2 and at least one opponent is
sure. The original owner-floor excess is therefore7/2 independently
of the actual punishment value: its opponent-Never coefficient is zero.
No stationary, induced-Nash, or persistent-base punishment selection can
repair this floor. In particular the table has no absorbing stationary
Nash profile containing a sure owner. No absence of fully proper
stationary Nash is asserted here.

### 6.2 Every complete quiet-child selection fails

For nonnegative weights on a nonempty proper child C, the joining rows
of `CappedClockParentRewardCertificate` require, for every nonempty A
inside C and outside owner o,

    sum_(i in C) weight_i [Z_i(A union{i})-Z_i(A)]
       >= Z_o(A union{o})-Z_o(A).                        (Q)

These are the literal J rows from
`UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockPointwiseDomination.lean`.
Each complete child fails one row with all left coefficients nonpositive
and positive right side. The following representatives and their rotations
cover every nonempty proper child:

| Child C | Outside o | Query A | Left coefficients | Right side |
|---|---|---|---|---|
| {0} | 1 | {0} | 0 | 1/2 |
| {0,1} | 3 | {0,1} | (0,0) | 1/2 |
| {0,2} | 1 | {0} | (0,-4) | 1/2 |
| {0,1,2} | 3 | {0,1} | (0,0,-7/2) | 1/2 |

Thus every nonnegative weight choice is excluded, even after dropping
all passive and Never inequalities. A supplied child equilibrium cannot
remove these raw parent inequalities.

### 6.3 Weighted and premium comparisons

The two opposite coalitions have native reward(-1,-1,-1,-1), excluding
every nonzero nonnegative passive-ledger weighting. Summing the four
singleton insertion vectors produces(-1,-1,-1,-1), excluding every
nonzero nonnegative global forced-Quit-floor weighting as well.

All grand premiums are98>0, so the grand product law defeats the product-
low-premium hypothesis and every nonempty ordered nonpositive marked
block choice. Every owner also has a negative participant pair, so there
is no protected player. All four triples and I are exactly the premium
traps; there are no pair traps. In a triple{i-1,i,i+1}, the sum of the
two inserted premiums at singleton{i} is1/2-1/2=0. It cannot satisfy
the strict negative singleton charge required by the boxed/mixed trap
criteria. On the full trap, inserting the two outsiders at opposite
pair{0,2} has total joining increment4>0, which independently violates
the nonpositive intermediate aggregate-leave bound.

The complete24-role preliminary census for the three-passive-pole
producer has no passing role; the exact rational expressions are
evaluated in the checker. This is finite-guard failure, not an inference
from an unknown asymptotic threshold.

### 6.4 Exact produced calibration

At K=92554/6669 the scalar producer has the rational root

    y=9/10, x=9/19, C=1/19,
    V=(9/20,-9/38,6882/1235,27/2).

The complete original table(T) has all phase endpoints and every finite
deadline/Never response checked exactly, including arbitrary signed own
offsets and positive scales. The separate scalar checker verifies the universal identities and a true
all-root obstruction outside the sufficient ratio range.

## 7. Previous-producer comparisons over their full selections

### 7.1 Every pair selection

There are three pair partitions. For01|23 and03|12, both scheduled joining
gaps are positive. However, two owners have a positive unscheduled next-
neighbor participant reward1/2. Thus each partition fails the literal
opposite-phase cap in the weak crossed-matching and general two-pair
join-cap theorems. For02|13, all four scheduled joining gaps equal-4,
so the necessary nonnegative joining comparison itself fails. These
arguments cover every relabeling and weak boundary, not only one schedule.

Every adjacent pair has one participant reward1/2 and the other-1/2;
every opposite pair has both participant rewards-1. Therefore no partition
has nonnegative scheduled participant rewards for all four owners. This
excludes the nonmatching positive-passive inverse and bounded-inverse-
corners classes. The singleton inverse is strictly positive:

    Gamma^-1=(1/15)*[[2,3,7,3],[3,2,3,7],
                     [7,3,2,3],[3,7,3,2]].

Consequently the all-column signed inverse criterion forces every sign to
be positive. Its signed participant condition fails on the same negative
scheduled endpoints under every partition. This statement concerns the
all-column two-pair criterion; the different one-column asymptotic theorem
is treated separately below.

The below-singleton and opposite-sign matching-phase classes require a
scheduled negative-singleton pair whose two normalized participant values
are both below-1, or a common such value on that phase. Every eligible
adjacent pair here has values1/2 and-1/2, both strictly above-1 and unequal.
The row normalization cannot change this: the two equal negative singleton
entries fix the same normalized unit. Hence all such roles fail.

The low-passive friendly-pair theorem can schedule only the positive-Gamma
opposite pairs. Their common participant value is Pi=-1, giving c=Pi-a=-4.
But each recipient's two crossparticipant rewards sum to0, whereas the
old inactive average cap requires at most2c=-8. Thus the class fails
independently of the passive threshold; its actual opposite-pair passive
value-1 also exceeds the required K<-27/2. The positive-joining friendly
pair, funded negative-pair, and global asymmetric favorite-pair classes
fail because the positive-Gamma pairs have participant value-1 rather
than a value above3. The mixed-positive-passive period-two theorem also
needs a positive-Gamma pair with both participant values positive. None
exists, under any role assignment, so its scalar threshold is irrelevant.

### 7.2 Every proper once-per-owner singleton cycle

The literal old four-singleton caps fail, but an exact structural check is
stronger and also handles that theorem's unquantified local neighborhood.
Suppose a periodic word schedules each owner once, with all four hazards
strictly between0 and1, and is exact terminal Nash. At an owner's mixed
solo date its native payoff and its continuation immediately after that
date both equal its own singleton0.

For any consecutive owners i then j in the cyclic word, owner i's value
at j's date is therefore0. The forced-Quit endpoint is q_j*J_ij, forcing
J_ij<=0. At i's date, owner j's next continuation at its own date is0,
so its prescribed value is q_i*Gamma_ji; its forced-Quit endpoint forces
J_ji<=Gamma_ji. Thus every consecutive directed edge must satisfy

    J_ij<=0 and J_ji<=Gamma_ji.                       (1)

If j=i+1, the first condition fails since J_ij=1/2>0. In the reverse
direction the second condition fails since that same reward1/2 exceeds
Gamma_ij=-1. Thus no adjacent edge of the original ring can be a
consecutive calendar edge in either orientation. Only opposite pairs
remain, and those two disjoint edges cannot make a cyclic word containing
all four owners. This excludes all24 orders and every proper positive
rate choice. It does not exclude repeated-owner or jointly active words.

The old four-joint center and rectangle schedule positive-Gamma favorite
pairs with original participant rewards5 and9/2. Here those rewards are0.
The center's stated radius is at most1/2, so it also fails quantitatively
under each singleton-compatible relabeling. The complete four-phase
passive-reward ray requires favorite participant reward above
(5+sqrt(5))/2, again impossible. Fixed monotone-passive and passive-triple
cap chambers require their literal adjacent original participant values
(-1,2), which differ from this ray's(3/2,1/2). No broad exclusion of
unquantified unrelated local neighborhoods is inferred from center data.

### 7.3 Marked blocks, passive bounds, traps and weights

The grand vector has every native coordinate98>0. For every nonempty
marked set and every ordered partition into positively weighted blocks,
the grand coalition meets the first block and has strictly positive
weighted participant sum there. This excludes all149 ordered-subset/block
choices and every positive weight vector. The first owner's universal
participant cap in the four-player passive-bounds theorem already fails
on its next pair, whose participant reward is1/2>0. The finite-player
block version fails on the positive grand vector. No passive-extremum
calculation or preferred marked labeling can restore either premise.

There are no two-owner premium traps: every pair has a nonpositive
participant. Every triple is a trap for K>=10; in fact all its participant
coordinates1,2K+1/2,K-7/2 are positive. Their union is the full greatest
trap. The nonnegative-participant and core-size-at-most-two/three classes
therefore fail their literal sign or core premise. Every owner has a
negative opposite participant pair, so no protected leaver can satisfy
the required global nonnegative participant condition. AllQuit gives
positive native forced-Quit values98 for every owner, falsifying
HasProductLowQuittingPremium directly.

For the proper triple A={j-1,j,j+1}, use the singleton T={j}. The two
outside participant rewards sum to1/2-1/2=0. The mixed-premium-traps
theorem requires this sum to be at most a strictly negative-D_A.
Thus all choices of its positive constants fail. The same proper traps
exclude the proper-support two-ledger class before any weights are chosen.

There are exact weight obstructions over the entire nonnegative cones.
Coalition02 pays native(-1,-1,-1,-1), excluding every nonzero nonnegative
lower coalition ledger. The inserted participant singleton rows satisfy

    sum_j J_ij=-1 for each recipient i.

Summing any proposed global inserted-floor inequalities over the four
singleton sets gives-sum_i lambda_i<0, impossible for nonzero nonnegative
weights. In particular the global floor premise of the trap-weighted
return theorem fails at the full trap. The native singleton columns sum
to(1,1,1,1), similarly excluding any nonzero nonnegative global upper
weight. These are exact cone certificates, not sampled weights.

### 7.4 Singleton geometry and passive poles

Every reciprocal singleton pair has equal signs. Consequently the escort
criteria requiring an opposite-sign pair, the one-negative-pair attached
patterns, and the cyclic-child joint/solo patterns cannot fit any relabeling.
The positive singleton graph is two disjoint opposite pairs, so it has
no directed Hamiltonian cycle or three-cycle. The no-mutually-negative
class does not apply: there are four mutually negative pairs.

Every proper triple contains a recipient whose two off-diagonal entries
are both negative. Such a triple cannot send a nonnegative vector to a
strictly positive vector, and in particular has no nonnegative inverse.
The positive two-owner submatrices have outsiders with strictly negative
passive rows, so their standard passive-child lifts also fail. A negative
adjacent2x2 principal block fails standard Q at a negative constant offset,
and has no nonzero nonnegative homogeneous solution; hence it also fails
the projective standard-or-homogeneous alternative. These are failures of
the proper child/Q-bar criteria, not a claim that the full Gamma is not Q.
Indeed det Gamma=45 and its positive inverse is displayed above.

The exact old three-passive-pole endpoint test was evaluated on all24
role assignments. Only the four rotations of(i,j,k,l)=(0,1,2,3) survive
its first two strict signs. For each, its first joining values and mixing
constant are a=1/2,b=-7/2,c=1/8. The subsequent six guards, in the old
statement's order, are

    (3/2, 1/2, -55/16, -53/16, 15/128, 25/16).

The first four must be negative and the last must be negative. In
particular the first value3/2 defeats every surviving role. These
certificates are independent of K, so the entire K>=10 ray fails all
finite endpoint guards; no unknown asymptotic threshold is used here.

### 7.5 Precise asymptotic limitation

Along K tending to positive infinity, eight passive adjacent-pair rewards
and eight participant triple rewards grow linearly and positively. The
other coordinates remain fixed. The signed passive-coalition theorem,
whose signs are all forced positive by the inverse, requires selected
large negative passive rewards. This is the opposite direction. Its
fixed-background formulation does not imply the present ray.

The positive-inverse coalition-jackpot theorem has one chosen growing
participant coordinate per recipient and all other nonsingleton entries
in a fixed bounded box. Here both a second participant coordinate and
passive coordinates in every recipient row grow at the same linear rate.
No choice of the four designated coordinates makes that background
bounded. The single-column theorem also cannot supply the whole ray from
its stated fixed-background guarantee. Its scale-thick extension does
not change this comparison: the growing participant coordinates here
are triples, so the allowed background is at most order sqrt(K), while
the other growing coordinates have order K. Pair and grand participant
coordinates are fixed, and there is no negative growing participant pole.

These are family-level nonimplications under the old theorems' fixed
parameters. They do not claim that each isolated finite table is outside
every possible unreported asymptotic threshold or unrelated local
implicit-function neighborhood. Reselecting an unbounded residual box
with K supplies no uniform diagonal guarantee. The finite failures in
Sections7.1--7.4 and the explicit unbounded-family distinction should be
retained together, with this caveat, in the coverage conclusion.

### 7.6 The ordered rotating class and the ten-phase reward cube

The preceding ordered rotating producer requires K3<=K2 after some relabeling
and positive recipient normalization. The own singleton fixes each recipient
offset. Its positive next-pair premium forces every consecutive directed
ring edge to follow a positive J entry. Here the only such entry in each row
is its next neighbor, so only the four rotations of the displayed ring are
possible among all24 relabelings. Each rotation has passive roles K2=K and
K3=2K>K. Positive scaling preserves this strict comparison. Thus no ordered
role assignment admits any member of the new ray.

The explicit open reward cube around the earlier equal-passive calibration
also cannot contain this ray after affine recipient normalization. In each
row its two eligible adjacent passive pair rewards differ by at most twice
the cube radius; here they differ by K>=10. Singleton reward differences
fix the row scale near one, independently of K. For the explicit radius
1/100000, the singleton difference4 implies that any scale lies between
4/(4+2/100000) and4/(4-2/100000), so the passive difference bound remains
less than1/1000. The sign margins in the singleton and pair data still force
the same four ring rotations. This excludes the displayed cube, not an
unreported larger implicit-function neighborhood.

The ten-phase full reward cube has a positive-Gamma pair with both
own-normalized participant premiums strictly positive, with margins bounded
away from its radius1/1000000. Every positive-Gamma pair of the present ray
has both participant premiums-1. The sign incompatibility survives all
relabelings and positive recipient scales, so the ten-phase cube and its
one-sided grand-coordinate extension cannot admit this family.

## 8. Exact all-root obstruction and handoff

Take a=4,b=1,K2=-50,K3=181/10, and saturate the twelve participant caps.
The proper scalar roots are the zeros in(0,1) of

    Q(y)=731y^4-339y^3-611y^2+379y-40.

There are exactly three. Exact Sturm counts isolate one each in

    (137797/10^6,137798/10^6),
    (500517/10^6,500518/10^6),
    (807703/10^6,807704/10^6).

The corresponding gap polynomial is P(y)=55y^3+2y^2-45y+6.
It is strictly negative throughout each isolating interval: its endpoint
values are negative and its Sturm root count on each interval is zero.
Thus every proper scalar root has g3>0. All four equations and all root
counts are certified by AppendixA. The other unused rewards
can be assigned arbitrarily, for example zero.

This refutes unrestricted passive-plane production by THIS fixed scalar
architecture for all a>2b. It is not a game counterexample and does not
exclude different rates, supports, or strategies. In particular the earlier
K2=-50,K3=184/9,a=3 example only exhibited one bad root and does not refute
selection: it also has a good root.

The ratio in(U) is not labeled architecture-sharp. At an endpoint-height
equality with z=1-alpha-beta and alpha beta=2z, one has

    r=(z+8)/(z+2), K2/b=2(z^2+4z-3)/[z(z+2)], K3/b=1/z.

The scalar quartic factors, up to a positive constant, as

    [y^2+(z-1)y+2z][(3z+8)y^2+4y+z-4].

The extra positive root can lie outside(alpha,beta), and then is good
despite the endpoint comparison failing. No maximal architecture region
is asserted.

The formalization target is a real-variable selector followed by the finite
four-owner endpoint identities. The selector must produce a root of F(y)=K3
with P(y)>=0; merely producing an active-indifference root is insufficient.
The strict-convexity argument includes the double boundary and the weak upper
ratio endpoint. The consumer should retain the actual +a xy collision term,
all simultaneous outcomes, and the absence of a sign condition on V2.
Instantiate the existing periodic compiler with opponent contraction C^3.
The signed source adapter uses actual absorption under every deviation.

This is a raw existence class, not a complete classification of scalar-root
feasibility or four-player games. The singleton symmetry and twelve participant
caps remain hypotheses. The sixteen other nonsingleton entries are arbitrary.
No absence of stationary equilibrium or necessity of four phases is asserted.
Fin4 remains open. The family-level and unknown-threshold distinctions in
Section7.5 remain part of the coverage statement.

## Appendix A. Exact scalar selection identities and complete failure census

Save this complete block as a Python file and run with Python3 and SymPy.
No repository input is needed.

```python
"""Exact identities and all-root fence for unordered rotating pair selection.

Run with Python and SymPy. No floating point arithmetic is used.
"""

import sympy as S

y, a, b, k2, k3 = S.symbols("y a b k2 k3")
x = y / (1 + y)
C = (1 - y) / (1 + y)
v1 = -b * x / 2
v2 = a * x * (1 - y) - b * (1 - x) * y + k2 * x * y + C * v1
phi = (-b * x * (1 - y) + a * (1 - x) * y + k3 * x * y
       + C * v2 - 3 * b * y / (2 * (1 - y)))
A = (a + b) * y**3 + 2 * b * y**2 + (a + b) * y + 2 * a - 2 * b
P = A + k2 * y * (1 - y**2)
H = b * (y + 2) / (y * (1 - y))
F = H - P / (y * (1 + y)**2)
assert S.factor(phi - x * y * (k3 - F)) == 0
g3 = 3 * b * x / 2 - (a + b) * y + a * x * y - C * v2
assert S.factor(g3 + y * P / (1 + y)**3) == 0
D = A / (y * (1 - y**2))
partial = -a - b + b / (1 + y) + (2 * a + b) / (1 - y) + 2 * (a - b) / y
assert S.factor(D - partial) == 0
convex = 2 * b / (1 + y)**3 + 2 * (2 * a + b) / (1 - y)**3 + 4 * (a - b) / y**3
assert S.factor(S.diff(D, y, 2) - convex) == 0
assert S.limit(F * y, y, 0) == -2 * a + 4 * b
assert S.limit(F * (1 - y), y, 1) == 3 * b

u, v, z, p, r = S.symbols("u v z p r")
height = b * (v - u) * (2 - 2 * u - 2 * v - u * v) / (u * v * (1 - u) * (1 - v))
assert S.factor(H.subs(y, u) - H.subs(y, v) - height) == 0
ss = 1 - z
E = 1 / (1 + ss + p) - (2 * r + 1) / (1 - ss + p) + 2 * (r - 1) / p
R = (p**2 - p * z + 3 * p - z**2 + 2 * z) / (z * (p - z + 2))
assert S.factor(E.subs(r, R)) == 0
increment = (p - 2 * z) * (p * z + 2 * p - 3 * z + 6) / (z * (z + 2) * (p - z + 2))
assert S.factor(R - (z + 8) / (z + 2) - increment) == 0
z0 = 5 - 2 * S.sqrt(6)
threshold = (67 + 12 * S.sqrt(6)) / 25
assert S.simplify((z0 + 8) / (z0 + 2) - threshold) == 0
assert S.simplify(z0**2 - 10 * z0 + 1) == 0

# Endpoint comparison alone does not classify every scalar root.
data = {a: (z + 8) / (z + 2), b: 1,
        k2: 2 * (z**2 + 4 * z - 3) / (z * (z + 2)), k3: 1 / z}
quartic_factor = (y**2 + (z - 1) * y + 2 * z) * ((3 * z + 8) * y**2 + 4 * y + z - 4)
assert S.factor((F - k3).subs(data)
                + quartic_factor / (z * (z + 2) * y * (y - 1) * (y + 1)**2)) == 0

# Every proper scalar root is bad in this exact example.
bad = {a: 4, b: 1, k2: -50, k3: S.Rational(181, 10)}
Q = 731 * y**4 - 339 * y**3 - 611 * y**2 + 379 * y - 40
Pbad = 55 * y**3 + 2 * y**2 - 45 * y + 6
assert S.factor((F - k3).subs(bad) + Q / (10 * y * (y - 1) * (y + 1)**2)) == 0
assert S.expand(P.subs(bad) - Pbad) == 0


def variations(poly, point):
    """Sturm variation at a rational nonroot endpoint."""
    signs = [S.sign(t.subs(y, point)) for t in S.sturm(poly, y)]
    signs = [s for s in signs if s]
    assert all(s in (-1, 1) for s in signs)
    return sum(left != right for left, right in zip(signs, signs[1:]))


def count(poly, left, right):
    assert poly.subs(y, left) != 0 and poly.subs(y, right) != 0
    return variations(poly, left) - variations(poly, right)


assert count(Q, S.Integer(0), S.Integer(1)) == 3
for lo, hi in [(137797, 137798), (500517, 500518), (807703, 807704)]:
    left, right = S.Rational(lo, 10**6), S.Rational(hi, 10**6)
    assert count(Q, left, right) == 1
    assert count(Pbad, left, right) == 0
    assert Pbad.subs(y, left) < 0 and Pbad.subs(y, right) < 0

print("PASS: scalar identities, strict convexity identity, endpoint algebra,")
print("      exact sufficient threshold, and every-root-positive-gap fence.")
```

## Appendix B. Full60 family, complete finite selectors, and full-cap calibration

Save this complete block as a Python file and run with Python3 and SymPy.
No repository input is needed.

```python
"""Exact old-selector audit for the unordered rotating mixed-pair ray.

Run with Python and SymPy. This is contributing coverage evidence, not a
proof of the new periodic producer. The original equal-passive selector audit is extended here to K2=K,K3=2K.
Quiet-child, punishment, and old ordered-role completeness are also checked.
"""

from itertools import combinations, permutations, product
import sympy as s

R = s.Rational
I = tuple(range(4))
tau = s.symbols('tau', nonnegative=True)
K = 10 + tau
COAL = tuple(frozenset(A) for n in range(1, 5)
             for A in combinations(I, n))
G = s.Matrix(4, 4, lambda i, j: 0 if i == j else
             3 if (j-i) % 4 == 2 else -1)
L = s.Matrix(4, 4, lambda i, j: 0 if i == j else
             {1: R(3, 2), 2: -4, 3: R(1, 2)}[(j-i) % 4])


def native(i, A):
    A = frozenset(A)
    if not A:
        return s.Integer(0)
    B = A - {i}
    if not B:
        F = s.Integer(0)
    elif len(B) == 1:
        F = G[i, next(iter(B))]
    elif len(B) == 3:
        F = s.Integer(100)
    else:
        j, k = sorted(B)
        F = (s.Integer(-1) if (k-j) % 2 == 0 else
             K if B == {(i+2) % 4, (i+3) % 4} else 2*K)
    if i not in A:
        return F
    return s.expand(F + sum(L[i, j] for j in B)
                    + (3 if A == {i, (i+1) % 4, (i+2) % 4} else 0))


Z = {(i, A): native(i, A) for i in I for A in COAL}
assert len(Z) == 60
assert all(Z[i, frozenset(I)] == 98 for i in I)
J = s.Matrix(4, 4, lambda i, j: 0 if i == j else native(i, {i, j}))
for i in I:
    assert J[i, (i+1) % 4] == R(1, 2)
    assert J[i, (i-1) % 4] == -R(1, 2)
    assert J[i, (i+2) % 4] == -1
    assert native(i, {i, (i+2) % 4, (i+3) % 4}) == K-R(7, 2)
    assert native(i, {i, (i+1) % 4, (i+2) % 4}) == 2*K+R(1, 2)
    assert native(i, {i, (i+1) % 4, (i+3) % 4}) == 1


def pos(expr):
    p = s.Poly(s.expand(expr), tau)
    return p.eval(0) > 0 and all(c >= 0 for c in p.all_coeffs())


def nonpos(expr):
    return all(c <= 0 for c in s.Poly(s.expand(expr), tau).all_coeffs())


TRAPS = []
for A in COAL:
    if all(any(S <= A and i in S and pos(native(i, S)) for S in COAL)
           for i in A):
        TRAPS.append(A)
assert set(TRAPS) == {A for A in COAL if len(A) >= 3}

# ProductLow fails at AllQuit. Every protected participant candidate fails.
assert all(native(i, I) > 0 for i in I)
assert all(J[i, (i+2) % 4] < 0 for i in I)

# Every nonzero nonnegative global upper weight fails on singleton columns;
# every lower weight fails on a wholly negative opposite-pair reward vector;
# every global inserted floor weight fails after summing its singleton rows.
assert G * s.ones(4, 1) == s.ones(4, 1)
assert J * s.ones(4, 1) == -s.ones(4, 1)
assert all(native(i, {0, 2}) == -1 for i in I)

# A proper triple trap violates the strictly negative singleton charge.
for j in I:
    A = frozenset(((j-1) % 4, j, (j+1) % 4))
    assert A in TRAPS
    assert sum(native(i, {i, j}) for i in A-{j}) == 0


def ordered_partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for blocks in ordered_partitions(rest):
        for k in range(len(blocks)):
            yield blocks[:k] + (blocks[k] | {first},) + blocks[k+1:]
        for k in range(len(blocks)+1):
            yield blocks[:k] + (frozenset((first,)),) + blocks[k:]


count = 0
for C in COAL:
    orders = list(ordered_partitions(sorted(C)))
    assert len(set(orders)) == len(orders)
    for blocks in orders:
        count += 1
        # Every strictly positive weight vector fails on the full coalition.
        assert all(native(i, I) > 0 for i in blocks[0])
assert count == 149

# Passive-bounds' first marked participant condition fails for every owner,
# before checking its observer extrema or threshold.
assert all(native(i, {i, (i+1) % 4}) > 0 for i in I)

PARTITIONS = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
partition_failures = []
for blocks in PARTITIONS:
    mate = {i: next(j for j in B if j != i) for B in blocks for i in B}
    joining = [J[i, mate[i]]-G[i, mate[i]] for i in I]
    cap_failures = [(i, j) for i in I for j in I
                    if j not in (i, mate[i]) and J[i, j] > 0]
    assert any(c < 0 for c in joining) or cap_failures
    assert any(J[i, mate[i]] < 0 for i in I)
    partition_failures.append((blocks, joining, cap_failures))

# All inverse-column signs must be positive; negative scheduled Pi then
# defeats every signed-column partition too.
assert G.det() == 45
assert all(x > 0 for x in G.inv())

# Every once-per-owner proper singleton cycle needs both endpoint bounds on
# each consecutive edge. Every ring edge fails; no all-opposite cycle exists.
singleton_orders = []
for order in permutations(I):
    bad = [(i, j) for i, j in zip(order, order[1:]+order[:1])
           if J[i, j] > 0 or J[j, i] > G[j, i]]
    assert bad
    singleton_orders.append((order, bad))
assert len(singleton_orders) == 24

# Scheduled negative-singleton pairs never have either endpoint below-b,
# and have unequal participant rewards. The old below-singleton and
# opposite-sign paired classes therefore have no relabeling.
for i, j in combinations(I, 2):
    if G[i, j] < 0:
        assert J[i, j] > -1 and J[j, i] > -1
        assert J[i, j] != J[j, i]
    else:
        assert G[i, j] == G[j, i] == 3
        assert J[i, j] == J[j, i] == -1
        # Friendly low-passive producer needs the crossparticipant sum<=-8.
        assert sum(J[i, k] for k in I if k not in (i, j)) == 0

# Frozen mixed-positive producer needs a positive-Gamma pair with both
# participant rewards positive, one above its singleton value.
assert not any(G[i, j] > 0 and G[j, i] > 0 and J[i, j] > 0
               and J[j, i] > 0 for i, j in permutations(I, 2))

# Every proper triple contains a row with only negative off-diagonal
# entries, precluding a nonnegative inverse. Reciprocal signs never differ.
for A in combinations(I, 3):
    assert any(all(G[i, j] < 0 for j in A if j != i) for i in A)
assert all(G[i, j]*G[j, i] > 0 for i, j in combinations(I, 2))


def join(i, A):
    A = frozenset(A)
    return s.simplify(native(i, A | {i})-native(i, A))


pole_rows = []
for i, j, k, l in permutations(I):
    a, b = join(i, {l}), join(i, {k, l})
    assert not (a.has(tau) or b.has(tau))
    if not (a > 0 and b < 0):
        continue
    c = a/(a-b)
    guards = [join(k, {l}), join(k, {i, l}),
              (1-c)*join(j, {l})+c*join(j, {k, l}),
              (1-c)*join(j, {i, l})+c*join(j, {i, k, l}),
              c*((1-c)+c*(1+native(l, {k, l}))-(1+G[l, k])),
              (1-c)*join(l, {i})+c*join(l, {i, k})]
    guards = list(map(s.simplify, guards))
    assert all(not v.has(tau) for v in guards)
    assert not (all(v < 0 for v in guards[:4]) and guards[4] > 0
                and guards[5] < 0)
    pole_rows.append(((i, j, k, l), a, b, c, guards))

if __name__ == '__main__':
    print('PASS: exact full60 unordered ray K2=10+tau,K3=2K2,tau>=0')
    print('PASS: three pair partitions, all24 singleton orders, all149 blocks')
    print('PASS: mixed/low/positive/signed pair and participant-family exclusions')
    print('PASS: global weight obstructions, all proper triple traps')
    print('PASS: all24 old passive-pole roles excluded; surviving first guards:')
    for row in pole_rows:
        print(row)
    print('Pair partition failures:', partition_failures)
    print('No isolated unknown-threshold exclusion is asserted.')


# All fourteen quiet children fail a single literal joining row.
quiet = []
for child in COAL:
    if len(child) == 4:
        continue
    found = None
    for outside in I:
        if outside in child:
            continue
        for A in COAL:
            if not A <= child:
                continue
            coeff = [join(i, A) for i in child]
            rhs = join(outside, A)
            if all(c <= 0 for c in coeff) and rhs > 0:
                found = child, outside, A, coeff, rhs
                break
        if found:
            break
    assert found
    quiet.append(found)
assert len(quiet) == 14

# Complete sure-owner gap identities are independent of both passive levels.
q = s.symbols('q0:4')
fields = []
for i in I:
    O = [j for j in I if j != i]
    gap = 0
    for bits in product((0, 1), repeat=3):
        A = frozenset(j for j, bit in zip(O, bits) if bit)
        mass = s.prod(q[j] if bit else 1-q[j] for j, bit in zip(O, bits))
        gap += mass*join(i, A)
    fields.append(s.expand(gap))
    expected = sum(L[i,j]*q[j] for j in I) + 3*q[(i+1)%4]*q[(i+2)%4]*(1-q[(i-1)%4])
    assert s.expand(gap-expected) == 0
u,v,w = s.symbols('u v w')
sub = {q[0]:1,q[1]:u,q[2]:v,q[3]:w}
f1 = R(1,2)+R(3,2)*v-4*w
f2 = -4+u/2+R(9,2)*w-3*u*w
f3 = R(3,2)-u+v/2-3*u*v
assert [s.expand(fields[i].subs(sub)) for i in (1,2,3)] == [s.expand(f) for f in (f1,f2,f3)]
assert s.expand(f2.subs(w,R(1,2))) == -R(7,4)-u
assert s.expand(f3.subs(v,0)) == R(3,2)-u
for owner in I:
    root = {q[j]: R(j != (owner+1)%4) for j in I}
    assert fields[owner].subs(root) == -R(7,2)
    assert s.prod(1-root[q[j]] for j in I if j != owner) == 0

# Any old ordered class relabeling must preserve positive next-pair edges.
# Row shifts are fixed by the own singleton; positive scales preserve signs.
possible_old_orders = []
for order in permutations(I):
    if all(J[order[i], order[(i+1)%4]] > 0 for i in I):
        possible_old_orders.append(order)
        for i in I:
            owner = order[i]
            old_k2 = native(owner, {order[(i+2)%4], order[(i+3)%4]})
            old_k3 = native(owner, {order[(i+1)%4], order[(i+2)%4]})
            assert old_k2 == K and old_k3 == 2*K and pos(old_k3-old_k2)
assert len(possible_old_orders) == 4

# The ten-phase reward cube has a positive-Gamma pair with both own-normalized
# participant premiums strictly positive. This table has no such pair.
assert not any(G[i,j] > 0 and G[j,i] > 0 and J[i,j] > 0 and J[j,i] > 0
               for i,j in combinations(I,2))

print('PASS: all14 quiet rows, full sure-owner identities/floor excess7/2,')
print('      all24 old ordered roles, and the ten-phase positive-pair requirement.')

# One exact produced profile in the unequal coverage ray, including complete
# finite-deadline and literal-Never prices under signed recipient offsets.
kk = R(92554,6669)
yy, xx = R(9,10), R(9,19)
sur = R(1,19)
assert kk > 10
vals = (R(9,20), -R(9,38), R(6882,1235), R(27,2))
table0 = {(i,A): z.subs(tau,kk-10) for (i,A),z in Z.items()}


def endpoints(table, hazards, owner):
    others = [j for j in I if j != owner]
    passive = quit = 0
    for bits in product((0,1), repeat=3):
        A = frozenset(j for j,bit in zip(others,bits) if bit)
        mass = s.prod(hazards[j] if bit else 1-hazards[j]
                      for j,bit in zip(others,bits))
        if A:
            passive += mass*table[owner,A]
        quit += mass*table[owner,A|{owner}]
    return passive, quit, s.prod(1-hazards[j] for j in others)


for signed in (False,True):
    offsets = (R(-3),R(2),-R(1,2),R(7,3)) if signed else (R(0),)*4
    scales = (R(2),R(1,3),R(5,2),R(7,4)) if signed else (R(1),)*4
    table = {(i,A): offsets[i]+scales[i]*z for (i,A),z in table0.items()}
    values = [[offsets[i]+scales[i]*vals[(i-t)%4] for i in I] for t in I]
    hazards = []
    for t in I:
        q = [R(0)]*4
        q[t], q[(t+1)%4] = xx, yy
        hazards.append(q)
        for i in I:
            passive,quit,H = endpoints(table,q,i)
            continuation = passive+H*values[(t+1)%4][i]
            assert continuation == values[t][i]
            if i in (t,(t+1)%4):
                assert quit == continuation
            else:
                assert quit < continuation
    for start in I:
        for i in I:
            total, reach = 0, 1
            for n in range(20):
                t = (start+n)%4
                passive,quit,H = endpoints(table,hazards[t],i)
                assert total+reach*quit <= values[start][i]
                total += reach*passive
                reach *= H
                assert total+reach*values[(t+1)%4][i] == values[start][i]
            assert reach == sur**15
            total, reach = 0, 1
            for n in range(4):
                passive,quit,H = endpoints(table,hazards[(start+n)%4],i)
                total += reach*passive
                reach *= H
            assert reach == sur**3
            assert total/(1-reach) == values[start][i]
print('PASS: exact unequal-ray K2=92554/6669,K3=2K2; all phases/deadlines/Never,')
print('      including signed offsets and independent positive row scales.')
```
