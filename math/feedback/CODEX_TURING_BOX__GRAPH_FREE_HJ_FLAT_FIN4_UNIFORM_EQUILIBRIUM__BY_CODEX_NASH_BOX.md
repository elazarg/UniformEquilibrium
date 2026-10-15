# Independent adversarial review of graph-free H/J-flat Fin4 existence

Reviewer: CODEX_NASH_BOX.

Reviewed the complete frozen candidate
`notes/CODEX_TURING_BOX__GRAPH_FREE_HJ_FLAT_FIN4_UNIFORM_EQUILIBRIUM.md`,
SHA-256
`0140a9eb121dff1ff140cde52f7e733e9066b4dfeb1abc07914c72dd4ad1e927`.
This review is independent ordinary mathematics, not a Lean build or an
export. I did not edit the candidate or consult another review's proof
verdict. The source audit below is static inspection under the displayed
imports; it does not claim a new kernel check.

## 1. Separate verdicts

SOUNDNESS: affirmative. I found no unresolved mathematical objection to
the stated raw-table theorem. The proof supplies its strategic witnesses
and reaches the full original-game fixed-target uniform-payoff endpoint,
not merely a finite-menu equilibrium or a child-game certificate. The
paid non-Nash triangle branch is sound, including product equality.

COVERAGE: not established by this frozen candidate. Removing the old
sink/receiver graph guard and strict-seed requirement genuinely enlarges
those raw predicates, but does not by itself show new UE coverage beyond
all implemented producers and accepted packets. The displayed calibration
table is already covered. An exact witness outside the complete selection
sets of the applicable producers is still needed before export. This is
separate from proof correctness, and is not an objection to the theorem
as an ordinary mathematical implication.

## 2. Claim and semantic boundary checked

There are exactly four players, arbitrary finite real terminal rewards,
zero live and Never payoff, independent private randomization, and one
unrestricted behavioral replacement at a time. Own singleton rewards are
nonnegative. A nonzero nonnegative weight vector satisfies H>=0 and J<=0
on EVERY nonempty proper coalition, and every proper active set has a
participant flat on all its participant subrows. The conclusion is the
existence of ONE original target before accuracy, with profiles and
horizon thresholds allowed to depend on accuracy, and expected-payoff
delivery and deviation control at ALL later finite horizons.

I checked the reduction to complete independent deadline laws, including
literal Never. Conditioning on surviving public history does not provide
correlation: each player's counterfactual all-Continue private path gives
one stopping law, independently of the other private paths. A behavioral
replacement supplies another such law. Its terminal payoff is affine in
that law, so the cap is the supremum of all pure finite deadlines and
Never. No optimizing deadline need exist.

The carrier is the closure of ALL actual payoff/full-cap pairs. It is not
convexified, restricted to a root family, or declared to consist of actual
profiles. Fixed-root prefixing is continuous and preserves this carrier.
Selecting one root after a minimizing point has been fixed does not need
a continuous Nash selector.

## 3. Arbitrary-root identities and Nash preservation

For the cap-root gap g_i=Q_i-(b_i+alpha_i B_i), direct subtraction gives

    d_i'=c d_i+q_i(-g_i)_+ +(1-q_i)(g_i)_+.

This is valid off Nash and at zero/sure hazards. It uses the CAP B_i,
not the prescribed payoff U_i, in the root defect. Weighted summation
then gives the stated exact L ledger. In particular the non-Nash payment
has the favorable sign +sum a_i Delta_i; discarding it in the later
lower bound is legitimate because the weights are nonnegative.

I independently recomputed complete finite-date/Late/Never caps for 80
rational finite-law tests, with arbitrary signed reward tables and root
probabilities including zero and one. Direct prefixing matched (3), the
coordinate debt identity (4), and the proper-support weighted ledger (5)
exactly, using rational arithmetic. These finite tests are a falsification
attempt, not a replacement for the displayed general algebra.

The strict seed has the full caps in (6). Its owner can also choose Never,
which is why s_j>=0 is used. This produces positive L and, unless already
diagonal, a fixed positive lambda. The constrained chamber is compact and
nonempty. No global-minimum theorem is being substituted for its own
constrained minimum.

At full interior support, dividing by the positive opponent Continue
probability and regrouping the weighted insertion terms really yields
L(B)=sum z_S J(S)<=0. This contradicts L>=lambda E>0. Sure hazards instead
give a diagonal by exact debt contraction, so no odds division is made
there. The remaining support is proper, and the supplied flat participant
has Q_i<=s_i. Supported Nash optimality gives B_i'=Q_i and retains the
low-cap face. Proper-coalition H then retains the SAME lambda chamber.
All Continue fixes the pair only in the relevant Nash case B>=s.

## 4. Both triangle alternatives and perturbation contradictions

The sink calculation includes EVERY inactive outsider. Strict outside
cap margins permit one common small owner rate. For a universal
recipient, the hypothesis that zero is the only original root implies
that every selected perturbed Nash root tends to zero: otherwise compactness
and the closed finite Nash inequalities supply a nonzero original limit.
Outside tied labels are exactly inactive near zero. The recipient's
strictly positive linear gap dominates the quadratic remainder, and its
added Quit bonus forces rate one. This contradicts convergence to zero.
The proof does not incorrectly declare a perturbation limit nonzero.

For a bare triangle, I checked all three column inequalities for the
displayed w. If P>N, eta and sigma make w-transpose h strictly positive
in every column, including when a reverse coefficient is zero. Thus the
weighted original gap is nonnegative in a neighborhood of zero, and the
positive bonuses make some perturbed gap strictly positive there. Again
rate one contradicts convergence to zero. Arbitrarily bad higher-order
coalition coefficients do not invalidate this local contradiction; their
finite quadratic bound is all that is used.

For N>=P, the interval in (10) is nonempty exactly as claimed, all z
coordinates are positive, and h z<=0 with its flat-player coordinate
zero. The tied flat-player gap expands EXACTLY as

    -n_0 q_1+p_0 q_2+
      [r_0(T)-r_0({1,2})+n_0-p_0]q_1q_2.

Consequently (11) makes it zero, not just O(tau^2). Flatness then gives
B_0'=Q_0=C_0<=s_0 and retains the low face even at a completely weak
flat boundary. The other tied positive gaps are O(tau^2); negative
gaps are O(tau) but are multiplied by the played Quit probability
O(tau). Thus EVERY tied defect is O(tau^2). The outsider has a strictly
negative gap near zero and zero own rate, so its FULL defect is exactly
zero. Its debt, including all future responses, contracts by c.

The loss of E is linear because E>0, whereas its added defect is
quadratic. The strict singleton H payment is also linear and pays
lambda Delta_max. Equation (13) therefore retains the same chamber
without changing its seed or lambda. Product equality P=N causes no
division by zero or missing linear term: the strict SINGLETON H, not
strict product separation, supplies the payment. Cyclically relabeling
the flat participant to zero works for either directed orientation.

Exact falsification tests included both orientations of the following
finite triangle calibrations, with tied continuation (1,1,1) and an
outside cap4. Own rewards are1, pair participants and triple participants
are0, and a child's pair-passive reward is1.

- Forward gains2 and reverse losses1 give
  g_i=2q_(i-1)-q_(i+1)-2q_(i-1)q_(i+1). Rates1/2 on the triangle give
  an exact nonzero full root; the fourth player's gap is strictly negative.
- Forward gains1 and reverse losses2 give the linear gaps
  g_i=q_(i-1)-2q_(i+1). The corrected rates (tau,tau,2tau) have one
  zero gap and defects (0,3tau^2,2tau^2,0), up to the relabeling.
  This tests the prefix algebra at a formal continuation; I do not
  assert that this particular continuation is an actual carrier point.

These are concrete checks of the two finite mechanisms, not assertions
that the imposed small classes exhaust equilibria.

## 5. Exact frozen-table and degenerate-boundary checks

Rational enumeration of every proper coalition confirmed all of Section9's
H/J values and the listed flat witnesses. For the actual law with player0
sure Quit1 and everybody else Never, direct full deadline/Late/Never
enumeration gives U=(1,-1,1,4), B=(1,1,1,4), E=2,L=3. The sure-owner1
date0 seed has E=1,L=5/4, so the displayed point really lies in its
lambda=5/4 chamber.

At tau=1/100, the corrected equality-product prefix gives exactly

    Delta=(0,1/495000,1/990000,0),
    E'=960499/495000<2,
    B_0'=Q_0=C_0<=1,
    L(B')>=(5/4)E'.

I also checked the zero-own-singleton version obtained by subtracting1
from every nonempty reward entry, and the one-hot weights (0,0,0,1).
They satisfy the raw guards. No positive own reward or positive lower
bound on every weight enters the proof. The all-zero reward table with
a one-hot weight is another exact zero-H/zero-own boundary.

The passive-SINGLETON perturbation is correctly distinguished from
perturbing all passive entries. It leaves every participant-flat
comparison literal, preserves H/J on larger coalitions, and changes
singleton H/J by the stated opposite amounts. At most one A_*-a_j
vanishes, so at least three singleton H values become strict. The
intermediate theorem therefore applies without preserving insertion
graphs. These assertions were also checked with exact rational epsilon
on the zero-own and one-hot boundary tables.

For the reward limit, the same complete laws and replacements are
available at both numerical tables. Every terminal payoff changes by
at most epsilon, hence every full cap by at most epsilon and every
regret by at most2epsilon. The delta/4 plus delta/2 allocation is valid.
The all-errors terminal compiler selects one ORIGINAL target; nearby
targets need not converge along an author-chosen sequence. There is
no hidden game-uniform rate or synchronization of nearby equilibria.

## 6. Bounded named-source audit

I opened the following declarations and their relevant definitions/imports.
Their hypotheses match the uses above.

- `quittingTerminalSemanticCarrier`,
  `exists_terminalProfile_sequence_tendsto_semanticPair`,
  `quittingTerminalSemanticCarrier_isCompact`,
  `continuous_quittingTerminalSemanticPrefix`, and
  `quittingTerminalSemanticPrefix_mem_carrier` in
  `UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean`.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_add_capDefect`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CapDebtBellmanReduction.lean`,
  and `quittingRootCoordinateNashDefect_eq_actionProbability_mul_posPart`
  in `UniformEquilibrium/Quitting/Root/NashDefect.lean`.
- `abs_quittingRootEndpointDifference_sub_solo_sub_tail_sub_collisionFlow_le`
  in `UniformEquilibrium/Quitting/Root/FirstOrderProductFlow.lean`:
  its extra linear baseline mismatch vanishes on the tied coordinates;
  it is not an unconditional quadratic estimate away from them.
- `quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash`
  and `quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash`
  in `UniformEquilibrium/Quitting/Root/CapNashRootStack.lean`.
- `isUniformEquilibriumPayoff_of_diagonal_mem_terminalSemanticCarrier`
  in `UniformEquilibrium/Quitting/Classification/Existence/UniformPayoffTerminalSemanticCarrier.lean`.
  It has no missing stationarity, positivity, graph or safe-child premise.
- `abs_quittingContinuationBestResponseValue_sub_le_of_reward_close`,
  `abs_quittingTerminalExploitability_sub_le_of_reward_close`, and
  `exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
  in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`;
  `quittingGame_exists_uniformEquilibriumPayoff_of_arbitrarily_close_rewards`
  in `UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/UniformPayoffExistenceClosure.lean`;
  and `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors`
  in `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.

No paper theorem is needed for the new raw argument. No strategic input
remains unproduced: the seed, lambda, chamber minimizer, full roots or
paid prefix, actual approximating profiles, and fixed original target
are all produced by the proof or these named consumers.

## 7. Coverage obstruction and next required evidence

The displayed Section9 table has NO premium trap. In particular players1,
2 and3 never receive a participant reward above their own singleton1.
Thus `HasWeightedQuittingTrapLeavers` is vacuous for this table, and
`exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`
already gives its UE. I checked the predicate in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`
and the strict consumer in
`UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversUniformPayoff.lean`.

A simple attempted repair is to change the grand row to(2,2,2,2).
That preserves the candidate's guards and creates a full premium trap,
but still does NOT give new coverage. Child012 has a symmetric exact
stationary equilibrium at the unique q in(0,1) satisfying

    q^3-4q^2+6q-2=0,
    U_0=U_1=U_2=(1-q)^2.

For each child player, Q=(1-q)^2 and the opponent-only absorbing
account is q^2, so the stationary indifference equation is exactly
the displayed polynomial. The child is proper. Player3 gets at least3
on every child absorption, but at most2 whenever it quits, including
the changed grand row. Thus Never is strictly optimal against this
child law, including every finite deadline, and the full game is already
solved by quiet extension. The original calibration has the same route
with joining bound1. This is an actual supplied child equilibrium and
complete outside-cap comparison, not just failure/success of one
pointwise screen.

I also compared the raw guards with the accepted sink/receiver and
two-ledger proper-support packets. The old graph restriction really
rejects the bare triangle here, and its original strict seed is absent
on the constant-one zero-H example. But both examples already have UE
by other means. Consequently neither demonstrates the export gate's
new-counterexample-class requirement. My coverage verdict remains
open, not negative for the whole new class, pending an independently
checkable nonredundancy witness. This does not delay or weaken the
affirmative soundness verdict for the frozen hash above.

## 8. Focused coverage addendum: the four-entry witness

Reviewed ONLY Sections42.1--42.8 of
`notes/CODEX_TURING_BOX__STATE_INFORMATION_AND_RELAXATION.md`, frozen
full-file SHA-256
`32be5d0091ac83e4938917362b4fd57852e040cd4a708bd9160b6313ce5fe815`,
and the bounded named sources/accepted packets identified below. Both
this hash and the original proof hash were rechecked before writing.
I did not read Section38, another review, or revise either snapshot.

SOUNDNESS: the original proof verdict remains affirmative; this task
does not repeat that audit. COVERAGE: affirmative for the bounded
whole-selection comparisons below. The four-entry table is a valid
nonredundancy witness relative to those named implemented producers
and accepted raw packets. It repairs the calibration-table limitation
in Section7 of this review. I found no unresolved mathematical objection
to Sections42.1--42.8. The nonstationary/transport comparisons omitted
from that section's explicit inventory are supplied below, rather than
being inferred from stationary nonexistence. This is not a theorem of
noncoverage by every conceivable verifier, longer calendar, or unknown
distant implicit-function neighborhood.

### 8.1 Literal data, guards, and exact finite checks

The table checked is precisely

    0:   (1,0,4,0)          1:   (0,1,0,4)
    2:   (4,0,1,0)          3:   (0,4,0,1)
    01:  (-1,2,3/2,3/2)    02:  (5,2,0,2)
    03:  (2,3/2,3/2,-1)    12:  (3/2,-3,1,9/2)
    13:  (2,0,2,0)         23:  (3/2,3/2,-1,2)
    012: (-1,-1,-1,10)     013: (-1,-1,10,-1)
    023: (-1,10,-1,-1)     123: (10,-1,-1,-1)
    0123:(9,9,9,9).

I independently recomputed all fourteen proper H/J values, all proper
flat-participant tests, and all twelve directed insertion differences
using exact rational arithmetic. They match42.1. In particular the
insertion graph is exactly0→1→2→0 and2→3→0, with positive gaps2,1,1,2,2
in that order. The three reverse gaps on012 are strictly negative.
Thus bare012 defeats BOTH old graph guards under every weight and
relabeling, and continues to do so throughout a reward neighborhood.
The relevant accepted packets are
`TWO_LEDGER_PROPER_SUPPORT_CHAMBER_UNIFORM_EQUILIBRIUM.md` and
`SINK_OR_RECEIVER_CAP_CHAMBER_UNIFORM_EQUILIBRIUM.md`.

The unmodified starting table is the first packet's Section6 table,
whose adjacent outsiders are3/2 and opposite outsiders2. It is NOT the
accepted passive-triple packet's literal table, whose pair outsiders
are1. The four changed entries and the retired eight-entry variant
have not been conflated.

### 8.2 Sure owners: entire induced selections

For owners0,1,2,3 respectively, the first forced-Continue player's
four pure-corner joining gaps are

    owner0, player2: (-4,-5/2,-5/2,-1),
    owner1, player3: (-4,-11/2,-5/2,-1),
    owner2, player1: (-3,-5/2,-3,-1),
    owner3, player1: (-4,-5/2,-5/2,-1).

These multiaffine strict inequalities force Continue at EVERY induced
mixed Nash point. The subsequent strict forcing for owners0,1,3 gives
exactly the roots stated in42.2, and their owner Quit values-1,-3,-1
are below Continue0. For owner2 the remaining game really has gaps
1-(7/2)y and2-5x. Its complete Nash set is
(1,0),(0,1),(2/5,2/7), not merely a set of tested candidates.
The owner2 endpoint triples(Q,b,alpha) are exactly

    (0,4,0), (-1,0,0), (1/7,46/35,3/7).

All fail Q>=b+alpha B for every B>=0. Passive rewards are nonnegative,
so actual full caps and actual punishment lower values are nonnegative.
This checks the original full-floor semantics, not an invented floor
restriction. It excludes ANY full Nash root with a sure player at any
nonnegative continuation, hence any persistent-base completion whose
conclusion supplies such a root. It says nothing about arbitrary
unrealized signed continuations or producers not requiring a Nash root.

Inspected definitions: `quittingPersistentBaseUtility`,
`quittingPersistentBaseNashSet`, and
`quittingPersistentBaseRootOfProfile` in
`UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`;
and `singletonBase_inducedNash_floorExcess_semantics` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/LargeBaseStationarySemanticHandoff.lean`.

### 8.3 Protected, weighted, boxed, and reward-closure comparisons

The protected-set exclusion is literal: every player has a participant
triple reward-1 below its own1, while grand9 makes the full set a trap.
Thus the maximal protected set is empty and no common/protected/support-
specific leaver selection, including weak leave, can serve this trap.
I checked `IsCommonQuittingPremiumLeaver`,
`HasProtectedParticipantPremiums`, and
`HasSupportSpecificQuittingLeavers` in the respectively named files under
`UniformEquilibrium/Quitting/Classification/`, together with the weak
consumer `exists_uniformEquilibriumPayoff_of_supportSpecific_weakLeave`
in `Classification/Existence/SupportSpecificQuittingPremiumLeaversRewardClosure.lean`.

The global weighted-floor definition tests ALL coalitions and includes
already-present players. Its two singleton inequalities really are
-2w0-w3>=0 and w0-w1-2w2>=0; they force every nonnegative weight to0.
Equivalently, their sum is

    -w0-w1-2w2-w3>=0.

After normalizing sum w=1 this has a strict negative margin, so weights
escaping to infinity or to the boundary cannot repair it in a sequence
of nearby tables. The full trap persists nearby. Thus the strict and
weak `HasWeightedQuittingTrapLeavers` producers AND their reward closure
do not cover this table. The grand surplus8 sum w also rejects every
nonzero nonnegative global weighted upper-average choice.

The author's additional boxed observation is valid and stronger than
the snapshot's J({2})=0 observation. Directly from
`quittingTrapInsertedPremiumSum` and the `singleton` field of
`QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`,

    P_I({2})=(5-1)+(-3-1)+(2-1)=1,

whereas the field requires P_I({2})<=-delta with delta>0. No coefficient
choice or threshold works. This is an OPEN obstruction, and therefore
also excludes reward closure of this boxed raw class. It likewise
rejects the full-trap branch of the accepted
`MIXED_PREMIUM_TRAPS_UNIFORM_EQUILIBRIUM.md` packet, not just its choice
of numerical constants. At the all-Quit root every active Quit payoff
is9>1, so `HasProductLowQuittingPremium` also fails, as does any support-
local alternative requiring the same all-root low condition or these
boxed coefficients on the full trap. The actual product-low
definition was checked in `Classification/ProductLowQuittingPremium.lean`;
the boxed whole-trap selector is `HasBoxedQuittingNashCharges` in
`Classification/BoxedQuittingNashChargeReturn.lean`.

### 8.4 All children and all five raw withdrawal kinds

For the thirteen nonempty proper children other than012, the stated
sole-owner profiles are exact unrestricted child Nash, have zero child
debt and zero joint-Never mass, and give some omitted player a strictly
profitable root join. I checked every prescribed owner against every
other child member. Internal joining gaps are strictly negative in
every nonsingleton test, and the own singleton is positive. Consequently
these are whole-certificate falsifiers with arbitrary finite debt weights
and Never slack, and they persist for nearby tables. They do NOT assert
that every child equilibrium has an unsafe lift.

For child012, at A={2} the source's actual future and joining rows give

    1<=-3lambda0+lambda1+nonpositive withdrawal,
    2<=lambda0-3lambda1+nonpositive withdrawal.

The omitted terms have the claimed signs for ALL five kinds, not just
the patient case. A nonmember's withdrawal gain is0. The member2 gain
is its applicable restart floor minus own1. The patient floor is at
most max(1,0)=1; deadline/cancellation floor is at most0; evaluated
security uses a nonpositive floor; terminal security is the maximum of
the zero floor and a security value at most the singleton. Hence every
member2 gain is nonpositive. Future weights are either nonnegative or0.
Adding gives3<=-2lambda0-2lambda1<=0. This uses no N row, so arbitrary
Never residual does not help. Capped-clock weights are a special case.

This obstruction also persists nearby: the two summed advance
coefficients remain strictly negative, the member2 coefficient remains
identically0, the restart-floor bound remains valid while its singleton
stays positive, and the summed left side stays positive. Thus reward
closure of these named raw F/J classes cannot bypass the exclusion.
It does not exclude a conditional consumer supplied with some favorable
actual child equilibrium and a different, non-universal comparison.

Definitions checked: `WithdrawalFutureJoinKind.gain`, `futureWeight`,
and `WithdrawalFutureJoinRewardCertificate` in
`Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`;
`patientWithdrawalFloor` in `PatientWithdrawalRaw.lean`;
`deadlineWithdrawalGainFloor` and `deadlineWithdrawalZeroFloor` in
`DeadlineWithdrawalRaw.lean`;
`deadlineSecurityGainFloorWithRestart` in
`DeadlineWithdrawalRestartPointwiseCore.lean`; and
`deadlineWithdrawalSecurityValue_le_singleton` and
`deadlineWithdrawalSecurityFloor` in `DeadlineWithdrawalSecurityLP.lean`.
The existing outside-debt consumers named in42.5 retain the actual full
caps and Never residual; they do not weaken these tests.

### 8.5 Quotients and stationary support proof

Exact independent enumeration of all fifteen partitions leaves precisely
the seven singleton-row-compatible partitions in42.6. I recomputed all
six nondiscrete residual witnesses, including the edited pair entries;
each listed rational value is correct. Here F=(1-alpha)Q-b agrees with
the actual zero-discount `quittingDiscountedDisplacement`, not just a
singleton linearization. The eight other partitions already fail a
necessary block-row sum. Representatives cannot rescue a nonsurjective
map, because the required section forces surjectivity.

The discrete determinant is45 and its inverse is the displayed strictly
positive matrix. Each triple determinant is6 and has negative inverse
diagonal entries. The homogeneous support census proves R0. At offset
ones the complete strict solution census has index1-4+4=1, exactly as
stated. Thus neither the degree-not-one exit nor the negative-determinant
nonnegative-inverse response quotient exit applies. The finite strict
row/residual/determinant witnesses also persist nearby; a varying
partition cannot evade a finite census. Sources checked are
`Stationary/ResponseInvariantQuotient.lean`,
`Stationary/DiscountedDisplacement.lean`, and
`Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.

I tried to falsify42.7 support by support. It passes. Sure hazards are
excluded by8.2; nonzero stationary laws absorb almost surely, so the
full-support H expectation is strictly positive while active odds give
L(v)=sum z_S J(S)<=0. All one/two-player support endpoint tests are
correct. The three flat-player and middle-player calculations on013,
023,123 use their literal rows, not a false rotation symmetry. On012
the six displayed Q/b polynomials are correct. In particular the exact
F0 expansion is correct, and the inequalities b<=1/2, a<=2/7,
5/26<=c<=9/26 imply the stated F0<=-29/208<0. No finite-support,
stationary-tail attainment, or restricted deviation hypothesis was added.

This excludes every raw producer whose conclusion actually supplies an
exact stationary product Nash, including the accepted
`RAW_ENDPOINT_THREE_PASSIVE_POLES_UNIFORM_EQUILIBRIUM.md` endpoint class.
It does NOT exclude genuinely nonstationary producers. Nor should exact
stationary nonexistence alone be described as a positive stationary or
unrestricted gap.

For the specific reward-closure comparison with EXACT stationary
producers, there is also a short compactness check. Suppose nearby
tables had exact stationary roots q^n. If a subsequential root limit is
nonzero, the actual stationary payoff formula is continuous there;
the endpoint Nash inequalities and the Never floor pass to the limit
and give an exact stationary Nash of this table, impossible. If q^n→0,
normalize p^n=q^n/sum q^n and take p in the simplex. Singleton terminal
masses tend to p, and higher-coalition masses tend to0, so v→s+Gamma p.
The date-zero Quit bound gives Gamma p>=0; for p_i>0, interior active
indifference gives (Gamma p)_i=0. This is a nonzero homogeneous
complementary vector, contradicting R0. Thus the present table is not
even in reward closure of exact-stationary producers. This bounded
comparison uses the actual nonnegative limiting Never floor; it makes
no claim about arbitrary supplied nonstationary approximants.

### 8.6 Nonstationary paired/matching and four-singleton calendars

These checks are additional to the snapshot's stationary exclusion.
The bounded entry points came from `docs/TOOLKIT.md`'s paired-cycle,
crossed-matching, below-singleton, and signed-four-cycle entries, and
`docs/FRONTIER.md`'s established signed-four-player source boundary.

`PairedCycle.RawRegion.eq_partner_of_singleton_lt` in
`Cycles/PairedCycleSchedule.lean` permits only ONE below-own singleton
quitter per recipient. Here every row has TWO such quitters. Therefore
every schedule fails that raw region, including positive recipient-
affine images and relabelings; those preserve the signs of singleton
differences. No higher collision entry is silently ignored.

For ALL strict/weak/inverse crossed-matching sources and their joining-
cap or below-singleton counterparts there is a particularly simple
literal collision obstruction. Player0 has TWO distinct participant
pair rewards above its own singleton: r0(02)=5 and r0(03)=2. A pair
schedule can put at most one of2,3 with0. The other is off-schedule and
violates the required off-schedule participant cap at1 (or strictly
below1 for the below-singleton family). This checks EVERY pair partition,
including arbitrary proper hazards, not a selected symmetric solution.
It applies to `RawSource`, `WeakRawSource`, `InverseRawSource`, and
`ScheduledPairCapSource` in `Cycles/CrossedMatchingPhaseSource.lean`,
and `RawFamily` in `Cycles/BelowSingletonJointPhaseSource.lean`.
The strict margins also exclude their weak/reward-closure versions.
The positive-affine table-membership obstruction is invariant; no
claim that arbitrary payoff translations preserve Never is being made.

The accepted `FOUR_PHASE_PASSIVE_REWARD_RAY_UNIFORM_EQUILIBRIUM.md`
family requires a scheduled pair with BOTH participant premiums
strictly positive. Every pair of the present table has a participant
strictly BELOW its own singleton. Hence no relabeling or positive
recipient-affine image of that family applies, nor its reward closure.

For the positive four-SINGLETON word, with each player owning exactly
one date and all four hazards proper and positive, every cyclic ordering
also fails. This is a whole owner-field comparison, independent of
stationary nonexistence. There are two cases:

- If favorites0 and2 are adjacent in the cyclic order, inspect player0
  at owner2's phase. If2 follows0, owner0 indifference makes that phase's
  Continue value1, whereas Quit gives1+4q2. If2 precedes0, Continue is
  1+3q2 and Quit1+4q2. The gain is positive in either case.
- Otherwise the order is0123 or0321 up to rotation. The singleton rows
  are unchanged, so the COMPLETE owner-indifference field is the one
  solved in Section7.5 of the accepted passive-triple packet:
  E_l=u_l[4-4u_(l+1)+u_(l+1)u_(l+2)]-1=0.
  Subtracting opposite equations has strictly positive coefficient
  determinant, forcing u0=u2 and u1=u3; the remaining difference forces
  all u equal. The unique proper solution is u=(3-sqrt(5))/2.
  At owner2, player0's actual Continue value is1/u and its literal
  edited Quit endpoint is5-4u. Their difference is
  2-3u=(3sqrt(5)-5)/2>0.

Thus the MODIFIED pair rows were tested afresh. The named raw
`SignedFourCycleSingletonData` producer, both spectral branches, already
fails its required positive predecessor four-cycle: Gamma's positive
graph is just an opposite matching. The data and branch guards were
checked in `Cycles/SignedFourCycleRewardAdapter.lean` and
`Cycles/SignedFourCycleLargerRewardAdapter.lean`; the balanced compiler's
actual fields were checked in `Cycles/BalancedSingletonCertificate.lean`.
This does not exclude longer singleton calendars, repeated owners,
mixed solo/joint words, or every conditional cycle certificate.

Two other named raw entrances cannot be overlooked: the two-pair
group-exclusion reward bounds in `Paths/TwoPairGroupExclusion.lean`
require the grand row's pair-average surplus to be nonpositive, whereas
it is8; the cross-mass reward bounds in
`Paths/TwoPairCrossMassRewardExclusion.lean` require the designated
recipient's favorable SINGLETON surplus3 to be nonpositive, because
their sole favorable indicator is a PAIR. Every label choice fails.
The raw cyclic-child joint-phase table and its singleton exits require
a positive directed child three-cycle, absent from the opposite-
matching Gamma; I checked the actual `RawTable` in
`Cycles/CyclicChildJointPhaseSource.lean`, not just a verbal graph screen.

### 8.7 Passive-triple transport and final scope

Literal nonmembership in the accepted
`PASSIVE_TRIPLE_CAP_CHAMBER_UNIFORM_EQUILIBRIUM.md` family is not by
itself a transport exclusion. Here the stronger check is available.
In each source recipient row, singleton entries are own1, favorite4,
and two neighbors0. For a positive recipient-affine image to have the
current singleton rows, its scale and shift must satisfy scale+shift=1
and shift=0, hence scale=1. The favorite is forced by the unique positive
singleton difference. This holds separately for EVERY recipient and
every allowable relabeling. Thus transport cannot alter the source's
allowed participant pair values-1,0,2 into the present5. The same
argument works for pure recipient scaling, and for a proposed source
sequence converging to this table: its singleton data force the scales
and shifts to converge to1 and0. Finite relabelings permit a fixed
subsequence, and the pair discrepancy persists. Variable unbounded
triple/grand parameters cannot repair a prescribed pair coordinate.

The raw graph-free theorem therefore has an exact admissible table
outside all the applicable whole selectors audited here. The bounded
frontier/source check found no existing raw producer or accepted packet
covering it. The export-facing statement should retain precisely this
named scope, the distinct graph and singleton-matrix conventions, and
the distinction between universal quiet certificates and favorable
selected child equilibria. It should not claim unknown-method
noncoverage or infer an unrestricted no-equilibrium gap. No Lean check,
export, commit, or push was performed by this reviewer.
