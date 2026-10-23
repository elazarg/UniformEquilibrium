# Bounded inverse corners produce proper two-pair equilibria

Complete ordinary mathematics. The result below is a finite raw reward
class, not an arbitrary-game theorem or a new Lean verification. All four
passive pair increments may have either sign. A finite sixteen-corner
test on a PRECOMPUTED bounded matrix box replaces global inverse closure.
The resulting proper independent periodic profile is exact terminal Nash
against every unilateral behavioral replacement and supplies one fixed
uniform-equilibrium payoff target.

## 1. Exact raw statement

There are four owners I={0,1,2,3}. Every nonempty quitting coalition S
absorbs at a finite signed vector r(S). Live play and AllNever pay zero.
Randomization is private and independent. The first finite tied coalition
determines the payoff. A unilateral replacement is unrestricted behavioral
play, equivalently an arbitrary private stopping law on natural dates and
literal Never along the unique live history.

Schedule A={0,2} and B={1,3}. Set

    m=(02)(13), f=(01)(23), g=(03)(12).

Thus m(i) is the scheduled mate and O(i)={f(i),g(i)} the opposite pair.
Define from the ORIGINAL reward table

    s_i=r_i({i}),
    Gamma_ii=0, Gamma_ij=r_i({j})-s_i for j!=i,
    Pi_i=r_i({i,m(i)})-s_i,
    K_i=r_i(O(i))-s_i,
    c_i=Pi_i-Gamma_i,m(i).

Own levels are arbitrary signed numbers. Assume ONLY

    Pi_i>=0 and c_i>0 for every i.                         (1)

The four K_i are arbitrary finite signed inputs, subject to the finite
corner condition below. No scheduled-singleton sign or matching sign graph
is assumed. Compute, in this order,

    G=max_(i,j)|Gamma_ij|,
    cmin=min_i c_i, cmax=max_i c_i, Pmax=max_i Pi_i,
    Kplus=max_i max(K_i,0), Kminus=max_i max(-K_i,0),
    R=1+8 max(G,Kplus)/cmin,
    T_i=max(K_i,0) R.                                     (2)

For four formal variables t_i define

    B_Gamma(t)=Gamma+SUM_i t_i E_i,f(i),
    D(t)=det B_Gamma(t), A_ij(t)=(adj B_Gamma(t))_ij.        (3)

Let V be the sixteen vertices t_i in{0,T_i}. Repeated vertices when
T_i=0 cause no problem. Require det Gamma!=0 and, with the COMPUTED sign
sigma=sign(det Gamma) in{+1,-1}, the finite tests

    sigma D(v)>0 and sigma A_ij(v)>0
       for EVERY v in V and EVERY i,j.                    (4)

These are finite literal determinant and minor inequalities, with no
strategic object as an input. In particular they are not a claim about
an unbounded matrix family. Put

    dmin=min_v sigma D(v), dmax=max_v sigma D(v),
    amin=min_(v,i,j) sigma A_ij(v),
    amax=max_(v,i,j) sigma A_ij(v),
    lower=amin/dmax, upper=amax/dmin,
    kappa=lower/(4 upper), Q=3cmax+Pmax+Kminus,
    rmin=min(1,R/2,1/(32 upper Q)),
    ell_i=c_i kappa rmin/2.                                (5)

All these numbers are finite and the required denominators are positive.
The final hypotheses are twelve actual joining caps

    r_i({i} union W)<=s_i+ell_i
       for every i and every nonempty W subset O(i).       (6)

Every unmentioned coordinate is arbitrary finite data. There are
twenty-four free nonsingleton coordinates: eight passive cross-pair
entries, twelve unused triple entries, and four grand entries. The capped
entries have no lower bound. The sixty original reward coordinates are
not normalized by changing the live or AllNever payoff.

THEOREM. Every table satisfying (1),(4),(6) has a produced proper
period-two exact terminal Nash profile: owners0,2 mix at phase A and
owners1,3 at phase B. All opponents absorb geometrically after deleting
any one owner. The same profile supplies its actual initial-phase value
as a fixed uniform-equilibrium payoff target at every positive accuracy.
Relabelings give the corresponding relabeled theorem.

## 2. Sixteen finite corners and bounded inverse positivity

Each determinant and adjugate entry in (3) is affine in each variable
separately. Each variable changes only ONE matrix entry, and the
determinant expansion uses at most one entry from that row. The same is
true for every cofactor, whether or not that row is present. Thus all
these functions are multiaffine.

On the box 0<=t_i<=T_i, a multiaffine function is the convex combination
of its vertex values with product linear-interpolation weights. If an
axis has T_i=0, drop that axis and interpolate over the remaining ones;
the sixteen tests simply repeat the necessary vertices. Therefore (4)
implies throughout this ENTIRE bounded box

    dmin<=sigma D(t)<=dmax,
    amin<=sigma A_ij(t)<=amax.

In particular every matrix there is invertible and

    lower<=B_Gamma(t)^-1_ij<=upper,                       (7)

with strictly positive entries. Both determinant signs are allowed;
normalizing determinant and adjugate by the SAME sign is essential.
At t=0 this includes Gamma^-1>0. Consequently G>0, R>1, Q>0,
0<lower<=upper, 0<kappa<=1/4 and 0<rmin<R. None of these constants
depends on an eventual selected root.

## 3. Exact original passive equations

For X>0 put q_i=X_i/(1+X_i). The scheduled and inactive templates are

    V_i=s_i+Pi_i q_m(i), W_i=s_i+c_i X_m(i).                (8)

The scheduled Quit endpoint is V_i and the Continue endpoint with NEXT
phase annotation W_i is also V_i, since

    q_m(i)(s_i+Gamma_i,m(i))+(1-q_m(i))W_i=V_i.

Write O(i)={j,k}. The inactive Continue endpoint with next annotation
V_i equals W_i exactly when

    c_i X_m(i)(1+X_j)(1+X_k)
       =Gamma_ij X_j+Gamma_ik X_k+K_i X_jX_k
                                  +Pi_i X_m(i)/(1+X_m(i)). (9)

This retains every simultaneous opposite-pair exit. Define K_i^+ and
K_i^- as the positive and negative parts, and

    N_i(X)=c_i X_m(i)(X_j+X_k+X_jX_k)
            +Pi_i X_m(i)^2/(1+X_m(i))+K_i^- X_jX_k,
    B(X)=Gamma+SUM_i K_i^+ X_g(i) E_i,f(i).                (10)

Then (9) is equivalent to B(X)X=N(X). The moved positive term in row i
is EXACTLY K_i^+ X_f(i)X_g(i). No approximation or choice made after
solving the game is involved. Every N_i is nonnegative on X>=0 and
strictly positive on X>0. On the cube 0<=X_i<=R, its actual matrix
variables satisfy 0<=K_i^+X_g(i)<=T_i. Hence

    F(X)=B(X)^-1 N(X)                                      (11)

is continuous there, strictly positive for X>0, and satisfies the
entry bounds (7). No inverse outside that cube will be used.

## 4. Coercivity before choosing the angular cone

Suppose X>0 is in the cube and F(X)=eta X for 0<eta<=1. Then
N=eta BX>0, so BX=N/eta>=N. Let L=max_i X_i and choose l with X_l=L.
In row i=m(l), put S=X_j+X_k and P=X_jX_k for O(i)={j,k}. The zero
singleton diagonal and the bound on the other singleton entries give

    (c_i L-G)S+(c_i L+K_i^- -K_i^+)P
                    +Pi_i L^2/(1+L)<=Gamma_i,l L.         (12)

If L>=2 max(G,Kplus)/cmin, the first two coefficients are nonnegative.
Dropping those terms yields Pi_i L/(1+L)<=Gamma_i,l. A negative right
side is impossible because Pi_i>=0. If Gamma_i,l=0, c_i>0 implies
Pi_i>0 and again gives a contradiction. If Gamma_i,l>0, the same
inequality and c_i=Pi_i-Gamma_i,l imply

    c_i L<=Gamma_i,l<=G, hence L<=G/cmin,

contradicting the assumed lower bound. Every such scaled eigenpoint
therefore satisfies

    max_i X_i<2 max(G,Kplus)/cmin, SUM_i X_i<R.             (13)

This includes arbitrarily small positive eta. It is a bound for ALL
relevant scaled eigenpoints, not merely for exact roots. R in (2) was
chosen BEFORE any inverse bounds. Only matrices in the bounded cube
are needed to rule out an outer-boundary eigenpoint.

## 5. Compact global root production

Let Delta={x_i>=kappa, SUM_i x_i=1}. It is a nonempty compact convex
simplex. On the cube, (7) gives

    lower SUM_i N_i(X)<=F_l(X)<=upper SUM_i N_i(X).

Thus F(X)/SUM_i F_i(X) has every coordinate at least kappa whenever
X>0. For x in Delta and 0<r<=1, each x_i<=1, and

    N_i(rx)<=Q r^2,
    SUM_i F_i(rx)<=16 upper Q r^2.                       (14)

The three c terms contribute at most 3cmax r^2, the nonnegative Pi
term at most Pmax r^2, and the negative passive term at most Kminus r^2.
At the precomputed rmin, the final sum is at most rmin/2.

On Delta times[rmin,R] apply Brouwer to the continuous map

    (x,r) |-> (F(rx)/SUM_i F_i(rx),
       clamp_[rmin,R](r+1-SUM_i F_i(rx)/r)).               (15)

Every used point rx lies in the bounded cube. A fixed point cannot
have r=rmin because its radial expression is strictly larger. If
r=R, the clamp identity gives SUM_i F_i(Rx)<=R. The angular identity
then gives F(Rx)=eta Rx with 0<eta<=1, contradicting (13). At an
interior fixed radius, the radial equality gives SUM_i F_i(rx)=r;
the angular equality therefore gives F(rx)=rx.

This produces X>0 with B(X)X=N(X), SUM_i X_i in(rmin,R), and

    X_i>=kappa rmin for every i.                          (16)

The proof is a global compact producer and does not assume a strategic
root or merely verify supplied odds. The finite-rectangle hypothesis
has been used exactly on its stated domain.

## 6. All responses and one original uniform target

Use the four produced proper hazards q_i in the two scheduled phases.
Equations (8)--(10) prove BOTH scheduled action endpoints tie and every
inactive Continue endpoint equals W_i. The raw caps (6), including the
empty opposite coalition with payoff s_i, give the ENTIRE inactive
Quit endpoint at most s_i+ell_i. By (16),

    W_i>=s_i+c_i kappa rmin=s_i+2ell_i.

Thus all sixteen phase action endpoints satisfy the required Nash
inequalities with next-phase values, including all joining pairs and
triples and arbitrary signed own offsets.

After deleting any owner i, its opponents' one-cycle survival is
rho_i=PRODUCT_(j!=i)(1-q_j)<1. Joint survival is smaller than one too.
Iterating the exact policy recursion identifies the templates with the
ACTUAL terminal values. Iterating the endpoint upper bound under any
unilateral behavioral strategy leaves a bounded remainder times rho_i^n.
It vanishes uniformly over the replacement. This prices every finite
deadline, literal Never and every complete mixed or behavioral response,
not just alternative periodic hazards.

Opponents' stopping has a geometric mean bound independent of the
deviator. The N-stage average-payoff error relative to terminal payoff
is therefore O(1/N), uniformly for all unilateral replacements and
for prescribed play. The SAME profile witnesses every positive accuracy
at sufficiently large horizons. Its actual initial phase value is ONE
fixed uniform-equilibrium payoff target, chosen before accuracy.

Arbitrary row offsets are valid here because every prescribed or
unilaterally deviating play faces surely absorbing opponents. They do
not change live or AllNever rewards. The actual target uses the
original s_i in (8), not a normalized game's payoff convention.
For an already certified table, positive recipient rescaling and
arbitrary recipient offsets transport the SAME profile and the affine
target. This is semantic closure of the produced strategy, not a claim
that the conservative G/cmin box or its literal corner tests are
invariant under independent recipient rescaling.

## 7. Explicit open all-positive-passive calibration

Use the literal zero-diagonal singleton matrix

    Gamma=[[0,-4,10,-10],
           [6,0,-9,-1/10],
           [-10,12,0,11],
           [6,-8,-1/10,0]].                              (17)

Its determinant is2130, and its inverse is

    [[6601/17750,727/1775,6067/17750,116/355],
     [235/852,65/213,18/71,25/213],
     [1318/5325,172/1065,402/1775,46/213],
     [66/1775,14/355,222/1775,12/71]].                    (18)

Every entry is positive. There is NO unordered pair with BOTH directed
singleton comparisons positive. There are two overlapping directed
positive three-cycles. Set Pi_i=13 for every i and K_i=10^-6 for every i.
Then

    c=(3,131/10,23,21), R=33, Q=82,
    T_i=33*10^-6.

At Gamma the least adjugate entry is396/5 and the largest is4362/5.
Every box entry differs from Gamma by at most delta=33*10^-6, and has
absolute value below13. Telescoping each determinant product bounds
the determinant error by96 delta 13^3<7. Telescoping the six products
in each three-by-three cofactor bounds every adjugate error by
18 delta 13^2<101/1000. Thus at ALL sixteen corners

    2123<D<2137, 79<A_ij<873.

The actual raw constants (5) consequently obey

    lower>1/30, upper<1/2, kappa>1/60,
    rmin>1/1312, min_i ell_i>1/52480>2*10^-6.             (19)

This verifies all corner hypotheses and cap allowances BEFORE solving
for the hazards. All four passive increments are strictly positive;
they do not give a pure scheduled-pair exit in the completion below.

Here is the complete sixty-coordinate table. Set all own values1 and
each opponent singleton to1+Gamma_ij. At scheduled pairs02 and13,
each participant's reward is14 and each passive recipient's is1+10^-6.
At each of the four cross pairs, participants receive1+2*10^-6 and
passive recipients receive-1. At each triple its passive recipient
receives-1; its queried inactive participant receives1+2*10^-6, namely
row0 at013, row1 at012, row2 at123 and row3 at023. The other two
participants each receive-2. Every grand reward is-3.

These rules are disjoint and specify all sixty coordinates. Every cap
is strict by (19), so continuity of all finite vertex tests and positive
raw constants gives a FULL sixty-coordinate open neighborhood of this
table in the theorem's region. Positivity of all four K_i persists.

No nonempty pure date-zero absorbing coalition is Nash. At a singleton
choose an observer with negative Gamma in that column: its participant
reward is above its own1 while its passive singleton is below1. Such an
observer exists in every column of (17). At a scheduled pair an outside
owner joins, raising1+10^-6 to1+2*10^-6. At cross pairs01,03,12,23,
respectively owners1,3,2,2 withdraw to their positive passive singleton,
whose increment is6,6,12,11 instead of2*10^-6. Each triple contains a
full scheduled pair; either member of that pair withdraws from-2 to
the passive cross-pair reward-1. At the grand coalition any owner
withdraws from-3 to its passive triple reward-1. All fifteen coalitions
are covered by strict deviations. AllNever fails because own values1
are positive. No absence of arbitrary stationary mixed Nash is claimed.

## 8. Exact bounded prior-criterion comparisons

The following comparisons concern the complete table in Section7 and
ALL finite selections indicated, including relabelings and positive
row-affine maps. They are not hypotheses of the theorem or a universal
strategy-class census. The existence proof is independent of them.

There is no mutual-positive singleton pair in (17), so no positive
favorite MATCHING exists. This rejects every selection of strict or
weak matching-sign sources and the common positive-mate asymmetric
paired families, including their small open boxes and affine images.
Row0 has TWO negative opponent singletons, so the ordered paired raw
region allowing at most one below-own singleton per row also fails
under every schedule. The only mutual-negative pair is13, so no perfect
matching has ALL scheduled singleton comparisons negative. Thus the
old constant-positive-inverse producer requiring that sign fails for
ALL three scheduled pair partitions.

Every participant pair reward in this complete table is strictly above
its own singleton. Hence every partition violates its own-level
inactive pair caps, including the broad own-level two-pair joining
criterion and the own-level signed-inverse variants. With the positive
inverse (18), every sign in a strictly positive signed inverse is
forced positive. On schedule02|13 all passive K are positive, failing
the nonpositive passive test. On the other two partitions, a scheduled
cross pair has a positive passive singleton comparison6,11 or12 and
participant increment2*10^-6, failing the required joining increment.
This exhausts signs and pair partitions of the constant signed test.

The earlier global coefficient condition is strictly stronger than the
present bounded condition. Every single directed off-diagonal update
Gamma+tE_ab has a NEGATIVE adjugate linear coefficient. Here is a
complete twelve-edge witness list; the middle item is its adjugate entry:

    01;(0,1);-11/10     02;(1,3);-65
    03;(0,2);-72        10;(1,0);-11/10
    12;(0,0);-88        13;(0,0);-6/5
    20;(1,0);-1/100     21;(0,1);-1
    23;(0,3);-36        30;(2,1);-76
    31;(0,0);-99        32;(0,0);-6/5.                  (20)

Consequently EVERY two-update global nonnegative-coefficient selection
fails, regardless of its schedule, designated rows or opposite-column
placements. Setting its other update to zero already witnesses failure.
The bounded sixteen-vertex test nevertheless passes by (19).

Every proper three-player singleton child is invertible, since
det Gamma_(T,T)=det Gamma*(Gamma^-1)_oo>0. Block inversion gives its
literal outside inverse row

    Gamma_oT Gamma_TT^-1
       =-(Gamma^-1)_oT/(Gamma^-1)_oo<0.                  (21)

Thus ALL four raw child outside-factorization selections fail, including
the children whose actual inverses are positive. The full nonnegative-
inverse criterion requiring NEGATIVE determinant fails because2130>0.
These statements do not exclude every child strategy or punishment tail.

For weighted singleton insertion put d_ij=r_i(ij)-r_i(j), d_ii=0, and
v=Gamma^-1 1>0. From (18),

    v=(12869/8875,811/852,4534/5325,658/1775).

Because all cross participant increments are positive and scheduled
increments are13, (Gamma v)_i=1 gives

    (dv)_i>=13v_m(i)-1>=13*(658/1775)-1>0.              (22)

No nonzero nonnegative row weights w can therefore satisfy w^T d<=0.
This excludes every weighting in the insertion guards requiring those
inequalities. Every pair has positive participant premiums, so the
proper-flat and greatest-premium-core shortcuts also fail their literal
pair tests; no choice of nonnegative weights changes those comparisons.

Every weak-unit ordered joining selection fails. A singleton test
suffices unless the relevant positive singleton comparison lies on a
cross pair. The four exceptions (receiver,partner) are(1,0),(3,0),
(2,1),(2,3). For the first two use full passive opponent coalition02,
and for the last two use13: joining raises the passive premium10^-6
to2*10^-6. The guard's outsider input is the chosen coalition with
the selected partner removed. This
exhausts all twelve ordered choices. Every instant no-join candidate
fails at its mate because c_i>0. For positive-rate owner-solo geometric candidates
0,1,2,3, use observers2,0,1,0 respectively: their passive singleton
comparison is negative and their forced-Quit mixture is nonnegative
at EVERY scalar rate, since their own centered reward is zero and
the pair participant premium is positive. Thus every positive exact solo
rate fails; rate zero is AllNever, already excluded by own values1.
No claim about all mixed stationary profiles follows.

Unknown overlap with arbitrary stationary laws, arbitrary punishment
tails, local implicit neighborhoods and existential jackpot thresholds
remains open. No pointwise noncoverage is inferred from a shape mismatch.

## 9. Scope, boundaries and exact source correspondence

If all K_i<=0, all corners coincide at Gamma. Condition(4) is then
EXACTLY Gamma^-1>0, with either determinant sign, and no extra global
coefficient or scheduled-singleton sign restriction. All sufficiently
small positive K_i also pass for any fixed positive-inverse Gamma by
finite continuity, with c and Pi fixed. The explicit positive-determinant
calibration above proves nonredundancy against the finite tested raw
criteria. The negative-determinant part overlaps a known general UE
criterion, and is not presented as a new existence class on its own.

The previously sufficient global nonnegative coefficient conditions
imply their bounded-corner special case when only two K_i are positive.
Thus those classes remain included. The new ingredient is replacing
unbounded closure by finitely tested inverse positivity on the actual
precomputed coercivity box. The compact angular/radial construction,
raw coercivity and phase consumer are reused mathematical principles.

The determinant and adjugate tests are substantive: a positive inverse
at Gamma alone need not stay positive over a nontrivial update box.
For the concrete Gamma in (17), det(Gamma+tE_01)=2130+(1175/2)t
while its adjugate entry(0,1) is4362/5-(11/10)t. At t=1000 the
determinant is589630>0 and this adjugate entry is-1138/5<0, so the
updated inverse actually has a negative entry despite (18).
The corner tests enforce exactly the needed bounded region. Merely
testing the eventual unknown strategy point would not be a raw producer.
Signed determinants must be normalized together with their adjugates.
Degenerate zero-length axes are permitted, as explained in Section2.
If c_i=0 or Pi_i<0, the coercivity or positive-numerator proof can fail;
no extension across either boundary is asserted. The caps in (6) may
hold with equality, while open-neighborhood claims use strict versions.

The exact strategic compiler is
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. It needs
exact policy, Nash with NEXT phase values, and playerwise opponent-cycle
contraction, all produced above. It handles arbitrary behavioral
deviations and one fixed original uniform target. No stronger hypothesis
about every player quitting at every date is used.

The existing scalar root theorem
`exists_positive_odds_of_positive_inverse` in
`MathUE/LinearProgramming/PositiveInverseTwoPairOdds.lean` assumes negative
scheduled singleton entries and nonpositive K. Its proof uses the
scheduled sign to derive the strict gap c_i>0. The present raw theorem
does not require that extra sign, includes all four positive updates
under the bounded-corner test, and supplies explicit pre-root joining
allowances. Its proof does not claim that the old supplied theorem
already has these weaker hypotheses.

Relevant exact finite guards are
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`,
`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple` and
`exists_labeledCycle_uniformPayoff_of_raw_strictInverse_triple` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`,
`RawRegion.eq_partner_of_singleton_lt` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`,
`RawSource`, `WeakRawSource` and `InverseRawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`,
`QuittingWeakUnitJoining` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitRawGuards.lean`,
`IsQuittingInstantNoJoin` in
`UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean`, and
`isεAsymptoticNash_soloStationary_exact_iff` in
`UniformEquilibrium/Quitting/Punishment/OwnerSoloCertification.lean`.
Their literal hypotheses, not arbitrary strategy-class converses, are
the comparisons made in Section8.

## 10. Lean handoff and unresolved scope

Formalize the finite multiaffine vertex bound including zero axes and
the common determinant sign. Then derive bounded inverse entry estimates,
the positive numerator and exact passive equations, the scaled-eigenpoint
bound on the precomputed cube, and the compact annulus producer. The
root and cap allowances must be OUTPUTS of these raw lemmas, not fields
of a certificate. The produced phase roots and vectors then instantiate
the existing periodic compiler directly. Verify the exact calibration,
all sixteen corners and every listed finite guard selection first.

This is a raw reward-class producer with a complete consumer. It is not
a proof that arbitrary positive-inverse games meet the joining caps or
corner tests, not an arbitrary-source adapter from hypothetical no UE,
and not a solution of the four-player conjecture. No new Lean theorem,
implementation, build, commit or export is claimed here.
