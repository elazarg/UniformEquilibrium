# Independent review of the below-floor matching producer

Identity: CODEX_NOETHER. Ordinary mathematics; no new Lean claim.

Latest additional review: the independent Section45/H1–H12 verdict and
complete sure-base/universal-quiet-transport checks are recorded at the end.
The earlier Section29 and standalone verdicts below are unchanged.

Status: **accepted, with no unresolved mathematical objection.** The tested
surface is §29, from “A negative scheduled-premium arm of the matching
two-phase producer” through EOF, in
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, at whole-file SHA256

    84cf88f403ed0004abc2c7bf107f0d9b8e5b4b5312a9ef14da9ebdbafedc31d9

I read all of that surface, independently recomputed its exact finite data,
and attempted to falsify the root, strategy and coverage implications.
Sections 1–28 are not covered by this verdict. No other conference review
was read. I did not export, edit Lean, compile, stage, commit or push.

## Exact claim checked

Four players independently Continue/Quit at simultaneous live dates, with
public histories, zero live-stage and Never rewards, and fifteen finite
signed terminal reward vectors. Unilateral deviations replace any entire
behavioral strategy. Let f=(01)(23), a=(02)(13), and o=f∘a. Own levels
s_i are arbitrary signed reals, b_i>0, and H>2. The singleton gaps are
Hb_i at f(i) and−b_i at a(i),o(i). Both scheduled-pair participant
increments are Πb_i and passive increments Kb_i, where

    Π<−1,       K<(7Π+10−2H)/2.

The twelve cross-pair/triple joining rewards are at most
s_i−4(−Π−1)b_i/3; all other entries are free. The claim produces one
proper period-two exact terminal Nash profile and one fixed uniform target,
with the same profile at every accuracy. A separate claim gives a full
sixty-coordinate neighborhood of its H=3,Π=−11/10,K=−179/60 table,
using actual four-odds equations rather than normalized equalities.

## Valid root and original-game steps

The cubic P has P(1/2)<0 and P(1)=H−2>0, so a root t∈(1/2,1)
exists. A root below1/2 is neither selected nor needed. Set q=1−t.
The displayed U_i=s_i+qΠb_i and W_i=s_i+q(Π+1)b_i/t exactly solve
both active endpoints and the passive Continue identity. W_i<s_i is
intentional. Against the stronger caps its passive advantage is at least

    q b_i[(1+t)4(−Π−1)/3−(−Π−1)/t]>0,

because t(1+t)>3/4. Every simultaneous unilateral coalition is included.
The large100 entries belong to the other scheduled members at their triple,
not to the unilateral deviator; the grand coalition is unreachable under one
deviation. No terminal entry was incorrectly omitted or translated away.

Joint survival t⁴ realizes the two vectors by bounded policy iteration even
for signed values. Opponent-deleted survival t³ removes the bounded remainder
under every behavioral deviation, including Never, randomized histories and
arbitrarily late stopping. The finite-horizon error2M[1+2/(1−t³)]/N
and regret twice that are valid. The target is selected before accuracy;
the same original-game profile works for every sufficiently large horizon.

I rechecked the exact signatures of
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. Their
policy, root-Nash and deleted-opponent contraction inputs are all produced.
The direct proof also gives the full semantic result. No no-UE-to-Q
hypothesis, sign assumption on own rewards, or supplied strategic certificate
is needed for this below-floor producer.

## Exact fixture, Jacobian and neighborhood

Independent rational arithmetic confirms every one of the sixteen endpoints:
active Quit and Continue19/30; passive Continue19/20; passive Quit1/3;
margin37/60. The actual equations E vanish at X=(1/2)1. The displayed
Jacobian is correct, with eigenvalues79/72,−307/72,−41/72,269/72 and
determinant267486337/26873856. It is nonsingular without a supplied
implicit-function premise.

For T_r(X)=X−J⁻¹E(X,r), the derivative at the center is zero. Continuity
on a compact positive ball gives a uniform derivative norm at most1/2 for
nearby reward tables; shrinking that neighborhood also makes center movement
at most half the radius. This is a self-map and contraction on a complete
ball. Its iterations produce a unique root there, approaching the center
root continuously. All hazards remain proper and all four actual passive
gaps stay strict. This proves a genuine full reward-space UE neighborhood;
it imposes no singleton, pair or cap equality nearby. Global root uniqueness
or strategy-class completeness is not asserted.

The proper-three exclusion is correct. Its player2 equation forces
0<x<1/1001 and10/11<a<1. The displayed F and ∂_aF recompute exactly;
concavity gives ∂_aF>0, and F(10/11,c) has minimum29/33. Thus Never
strictly dominates Quit for player1 in every prospective support012 profile.
Klein permutations handle all four supports. No full-support or sure-boundary
stationary nonexistence follows.

This exclusion is robust. For a reward perturbation δ≤1/1000, player2
gives |1−(11/10)a−x/2+(503/5)ax|≤2δ. It forces x<11/1006 and
a>9/10. The same derivative argument gives

    F≥F(9/10,c)=(64c²−512c+621)/200≥173/200.

Since D≤1, the center Never-minus-Quit gap is at least173/200. Perturbing
each endpoint by at most δ leaves it positive. A smaller full reward
neighborhood thus excludes the actual proper-three local source
`PairedCubicStationaryExample.exists_local_stationary_branch` in
`UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`.

## Actual raw coverage, not another conditional interface

The accepted arbitrary-K theorem in
`exports/CROSSED_MATCHING_UNIFORM_EQUILIBRIUM.md` does not cover this fixture.
Favorite signs force f under every relabeling. Scheduled02/13 fails
participant comparison−1/10≥0; scheduled03/12 has participant comparison
but outsider triple reward100>1, violating its actual caps. Both failures
have strict slack and persist under small perturbations and positive affine
row transports. All pair premiums are negative, so no partition meets the
separate Π≥0 inverse criterion. Its pure-pair arm also fails: every pure
coalition has an explicit profitable deviation.

I confirmed that the only premium trap is the full set. Greatest-core
two/three criteria do not apply. Forced Quit at hazard(1/10)1 is
(24739,24729,24719,24709)/10000, violating product-low and supportwise
nonpositive premium balance. Negative grand premiums exclude every protected
player and every nonzero nonnegative weighted forced-Quit floor. At T=01,
the boxed/mixed-trap insertion sum198>0 violates their actual intermediate
charge condition. Singleton terminal tests force Γᵀλ≤0 for a nonnegative
weighted terminal upper bound, but row sum1 forces λ=0. This contradicts
the hypotheses of `exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.

The full Γ has determinant45, positive inverse and R₀ degree+1, not the
negative-determinant inverse exit. Harmful principal pairs are not Q or
homogeneous admissible; all triple inverse diagonals are−1/6. I inspected
the exact hypotheses of `r0Degree_eq_sign_det_of_nonnegative_inverse`
(`MathUE/LinearProgramming/NonnegativeInverseDegree.lean`),
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse`
(`UniformEquilibrium/Quitting/Classification/LCP/NonnegativeInverseCriterion.lean`),
and `exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`).
These are failures of named sufficient conditions, not claims of nonexistence.

Every proper child also fails the actual accepted nonnegative quiet F/J
criterion, not merely a supplied-child verifier. If S cuts an o-pair,
choose j∈S,k=o(j)∉S and A={j}. Outsider join gain is1/2; child joining
gains are0,−7/2,−1/10, so no nonnegative weights satisfy J. If S cuts
neither o-pair, S=03 or12, and at A=S any outsider gains100 while all
child joining gains are zero. This excludes every child in
`exports/NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md`. The exact Nash,
zero-Never child witnesses additionally falsify universal debt-plus-Never
families, including the exact consumer
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess`
(`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`).
It does not imply that every separately chosen quiet-child profile is unsafe.

The quotient, singleton sign, crossed weak polynomial/one-sided guard,
conditional range and visible affine period-three comparisons are valid.
The actual range definition `IsQuittingConditionalFaceGapRange`
(`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`)
requires ContinueUpper≥4 while its lower Quit mixture is at most1, for
every blocker. The exact center `overlappingPeriodThreeRewardRow` and
`IsInvisibleRewardCoordinate` in their named cyclic example files confirm
that all participant pair coordinates are visible and center at own level1;
their normalized gap is tiny in that cylinder but at least1/2 here, under
every relabeling and positive affine row transport.

Two additional raw screens fail strictly: influence1→0 is−9/2 at∅ but
1001/10 at{2}. This contradicts `SignConsistentQuittingInfluence`
(`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`)
and `IsAffineQuittingMembershipGain`
(`UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`).
It excludes their raw potential/influence branches and persists nearby.

## Scope and handoff

The proof passes the substantive gate: it removes a previously surviving
open original-table neighborhood beyond the strongest accepted matching
criterion and compared actual raw producers. It does not merely verify an
externally supplied root. It does not settle arbitrary Fin4 or assert
absence of all stationary, periodic or selected-child equilibria. No new
L/A/C seal is justified. The math-unicode skill affects notation only.

A future standalone packet must include the complete original-game proof
and named-source coverage, and receive its own byte-bound assembly verdict.
The current §29 mathematical candidate is accepted at the hash above.

## Separate final standalone verdict

**Accepted for mathematical export, with no unresolved objection.** The
separately tested artifact is the complete 660-line file
`exports/BELOW_SINGLETON_JOINT_PHASE_UNIFORM_EQUILIBRIUM.md`, SHA256

    6b75ada2ad8e675fd32216d0f1d98fbfdfee6ef5a47d0b7ca8aed05eb2d0e3ca

I read the entire standalone and checked its assembly against the accepted
§29 proof and independent coverage strengthenings above. It includes the
raw-family scalar producer, all sixteen endpoints, actual signed terminal
values, all behavioral/Never deviations, one fixed target and all-large-
horizon bounds, and the separate full-coordinate contraction theorem. No
root, continuity certificate or strategic object remains an unproduced input.
The full mixed-strategy raw coverage evidence, direct quiet joining rows,
influence/potential failures and robust proper-three exclusion are present.

The simplified robustness argument is correct: for a≤9/10, the center
Q₂* affine in x has both endpoints at least1/100, contradicting
|Q₂*|≤2/1000. This directly supplies the same a>9/10 bound as the
independent derivation. The proof still asserts neither full-support nor
sure-boundary stationary nonexistence.

I separately checked the new wrong-root boundary. Its cubic factorization
is exact, the second proper root lies below1/20, its formal W<−9/10
while actual passive Quit>13/15, so it fails Nash. The selected2/3 root
instead has passive Quit25/27 and gap13/540. This valid falsifier prevents
inflating the raw theorem to arbitrary cubic-root selection.

The scalar equality-stratum family and the one full-coordinate neighborhood
remain distinct conclusions. The packet gives real new UE coverage beyond
the accepted arbitrary-K matching class, not a supplied-certificate interface.
New content remains ordinary mathematics and carries no new L/A/C assertion.
This is the independent final mathematical acceptance of these exact bytes.

## Independent Section45 hybrid-class review

**Accepted as ordinary mathematics, with no unresolved proof objection.**
The exact surface checked is Section45, H1–H12, of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, whole-file SHA256

    6a32c34b7c6d4da99abc197598d06dc386755f9e5420e6ee963d966122020220

This is a new review of that frozen surface, not an extension of the
earlier Section29 verdict to intervening sections. I read all H1–H12,
recomputed all sixty original reward entries and the finite certificate
data, and attempted to falsify the arbitrary-table theorem at quiet,
partly-sure, all-sure and interior roots. No Lean build or edit, export,
staging, commit or push was performed. The reviewed raw adapter is not
asserted to be implemented in Lean.

### Claim and exact consumer

Four players use independent private behavioral randomization at live
dates; complete unilateral behavioral replacements are allowed. The first
nonempty quitting coalition absorbs at its original reward vector; live
play and Never pay zero. Own singleton rewards are nonnegative. For EACH
premium trap A, there is either a nonzero nonnegative support-local weight
whose inserted-premium average is nonpositive at EVERY S⊆A, or the stated
three-cardinality-layer boxed charge coefficients with strict threshold
above ∑[i∈A]s_i+|A|M. Weights and certificate types may differ with A.
The conclusion is one original-game uniform-equilibrium payoff, selected
before accuracy, against unrestricted deviations and all sufficiently
large horizons. It is not completeness of a stationary or periodic class.

I checked the exact declarations
`HasBoxedSelectedSingletonSublevelReturn` in
`UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`
and
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_of_reward_bound` in
`UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.
The predicate asks for ONE exact full root at every boxed annotation
strictly below some own singleton, returning below some own singleton.
It does not demand every root return or a continuous selector. The theorem
requires own nonnegativity, a coordinate reward bound M, M<B and
B≤quittingRewardBound+2. The proposed common box has exactly these inputs.
Its conclusion is the original fixed-target uniform-payoff contract, not
merely terminal Nash or finite-horizon equilibrium with varying targets.

### Universal root proof and attempted falsifiers

H5 is correct with arbitrary zero weights, quiet coordinates and sure
coordinates. Summing the complete product law over the player's own
coordinate gives the forced-Quit opponent law. Thus the inserted average
weights Q_i−s_i, not q_i(Q_i−s_i). It needs no division or Nash assumption.
The existing `quittingWeightedQuitPremium_eq_fullCoalitionAverage` in
`Classification/WeightedQuittingTrapLeavers.lean` has this precise algebraic
scope. A nonzero nonnegative weight makes an all-strictly-positive active
Quit-premium vector impossible. A nontrap support likewise supplies one
owner whose entire forced-Quit coalition inventory is at most its singleton.

H6 is also valid on the whole cube. The empty outcome contributes
c∑(s_i−v_i), and each nonempty proper coalition contributes its actual
leave sum. At a partly-sure CHARGE root c=0; a nonsure active i gives
strictly positive mass to A\{i}, making the right side negative while
Nash makes the left side nonnegative. At the all-sure point both sides of
H6 vanish, but the separate individual erased-support inequality supplies
a strictly profitable withdrawal. No sure case survives into the odds
calculation. The singleton-support case is handled by the nontrap arm;
no charge threshold is illicitly used at cardinality one or two.

For an interior charge support, division by positive Continue probabilities
gives H7 exactly: each missing player's own-zero term disappears, and the
inserted premiums collect by proper nonempty coalition. The next-to-top
elementary symmetric bound E≤U^(m−1)/m^(m−2) is correct for m=3,4.
The averaging proof also covers a boundary maximizer: at least m−1 positive
coordinates are necessary for E>0, so the pair-equalization coefficient
is positive whenever it is needed. There is no unproved strict convexity
or maximum-at-equal-points assertion hiding a zero coefficient.

H9 uses the full exact Nash identities only on active proper hazards, where
they are indifferent. Its charge bound is strict because E>(d/τ)U and
g,ℓ>0. Quiet-player inequalities are not replaced by subgame Nash: only
necessary supported inequalities were used to exclude a bad FULL root.
The same calculation is the support-local theorem
`QuittingTrapChargeCoefficients.threshold_lt_singletonSourceCharge` in
`Classification/BoxedQuittingNashChargeOdds.lean`; it does not require that
other traps carry charge coefficients.

There are finitely many traps, so the strict threshold margins allow ONE
M<B<M+2 for all selected charge supports. At every boxed v with some
v_i<s_i, finite-game Nash existence supplies a root; all Continue is not
Nash because i's solo Quit gains s_i−v_i>0. Thus an absorbing full root
exists, and the proved universal return supplies the selected predicate.
No realized actual tail, positive uniform absorption bound, maximum-debt
source, differentiable Nash selection or punishment-value assumption is
silently introduced. These were the principal attempted falsifiers, and
none invalidated the theorem.

### Exact fixture and original H10–H11 comparisons

All fifteen H8 payoff rows were independently entered and checked. The
complete trap list is 012,013,023,123,I; no pair is a trap. All fifteen
nonempty full-support H coefficients, all twelve triple singleton (P,L)
pairs, all twelve triple penultimate (P,L) pairs and C₃=53265 agree exactly.
M=200,B=201 satisfy the actual consumer; there is no floating-point premise.
The pure-escape inventory also agrees. In H10(1), the witness should be
read as an absorbing **product action profile**, not an exact Nash root:
the sure triple is deliberately not Nash. This is harmless for the actual
definition `HasProductLowQuittingPremium`, which quantifies over all product
profiles, but the wording distinction prevents a misleading source reading.

The ProductLow, whole-core boxed-charge, participant-weight balance,
protected/common/support-specific leaver and weighted global lower-floor
failures are valid over their complete stated selection sets. In particular
P_I(T)=6 for EVERY pair T defeats any full-core charge coefficient choice,
and grand premiums −201 defeat every nonzero nonnegative global lower-floor
weight. Positive triple participant premiums defeat every participant-only
support weighting. The upper inserted identity is genuinely different.

The exact Γλ witness is (1,6,1,1)/9 for λ=(2,1,5,1)/9. The stated stationary
small-hazard numerator estimate is sound, so this is not an all-profile
prescribed-payoff-deficit class. It also excludes every nonnegative weighted
terminal upper chamber: the singleton tests would imply wᵀΓ≤0, incompatible
with Γλ>0 for nonzero w≥0. I inspected the exact raw theorem
`exists_uniformEquilibriumPayoff_of_nonnegativeWeightChamber` in
`Diagnostics/Quitting/TerminalSemanticNonnegativeWeightChamber.lean`.

The full-core deadlock equality and all24-labeling audit are valid. The four
distinct offdiagonal row multisets force the only Γ automorphism to be
identity. The actual raw structure `IsDeadlockRationalJointBlockCompletion` in
`Classification/LCP/FullCore/DeadlockRationalPolyhedralBlock.lean` requires
the WHOLE pair13 vector equal the own baseline. The fixture's (5,−1,5,−200)
fails that field. Arbitrary completion debt bounds are not mistaken for UE.

### Complete sure-base and true-punishment exclusion

The true unrestricted independent-opponent punishment value is P_i=−4
for EVERY i. Never earns at least −4 against any opponents: each passive
singleton, passive pair, omitted triple and Never reward is at least −4.
Opponents all surely Quit at date0 in I\{i}; i can then only receive −4 by
Continue/Never or −200 by joining the grand coalition. This is an actual
punishment, without public correlation or a nominal floor.

Stronger: at ANY continuation annotation v, no FULL exact finite root has
ANY sure coordinate. Here is an independent direct proof, covering all
supports and all free-rate choices.

If at least three players are sure, choose three of them. For a member,
the Quit-minus-Continue gap is −1−195p<0, where p is the fourth hazard;
three sure gives triple4 versus passive pair5, and four sure gives grand
−200 versus omitted triple−4. Such a sure player is not best responding.

If exactly two a,b are sure, let x,y be the other hazards. Each sure
member's gap is the convex combination of its directed pair joining gap,
two copies of −1, and −196, with weights
(1−x)(1−y),x(1−y),(1−x)y,xy. The two directed pair gaps, in pair order,
are

    01:(−204,−203), 02:(1,−203), 03:(−204,1),
    12:(−202,1),   13:(1,−199), 23:(−200,−202).

EVERY pair has a member whose four coefficients are strictly negative.
Thus no exact root has two sure coordinates, even with arbitrary other
rates or arbitrary v.

If exactly z is sure, each free player's action gap is a convex combination
of its directed joining gap against {z}, two copies of −1 and −196.
Exactly one free player f(z) has positive first coefficient, equal1:

    f(0)=3, f(3)=1, f(1)=2, f(2)=0.

The other two free players have a uniformly strictly negative gap and hence
must Continue. With both quiet, f(z)'s gap is1, forcing f(z) surely Quit.
This contradicts the already excluded two-sure case. The annotation drops
out because every free player's opponents include a sure quitter, and the
final owner comparison has the newly forced sure opponent. No own-floor
condition on v was used.

This covers the COMPLETE selections in the named persistent-base producers,
not only a chosen base/free carrier. I read `quittingPersistentBaseNashSet`
in `UniformEquilibrium/Quitting/Root/PersistentBaseInducedGame.lean`,
`nonempty_quittingPersistentBaseCertificate_of_inducedNash` and
`exists_uniformPayoff_of_persistentBase_inducedNash_signs` in
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseNashSemanticAdapter.lean`,
and `quittingSingletonBaseOwnerFloorExcess_nonpos_iff` and
`exists_uniformPayoff_or_singletonBase_pos_gap` in
`Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
For base size≥2, the induced Nash, base-leave and outsider-join fields yield
a full exact root, with continuation irrelevant. For a singleton base, the
owner-floor field is exactly its Continue inequality at its TRUE P_z;
free and outsider inequalities are screened by the sure owner. Thus every
accepted carrier would give a prohibited full root at a suitable v.
The exact predicate `HasQuittingPunishmentVectorNashRootWithSureQuitter`
in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`
likewise fails over all owner/root choices. This does NOT exclude proper
stationary roots, proper quiet roots or arbitrary selected continuations.

### All proper children fail universal quiet-transport certificates

The same f is one directed four-cycle. Every nonempty proper child S cuts
an edge z→k=f(z), with z∈S and k∉S: a nonempty subset closed under f would
contain all four players. Within that child, prescribe z surely at date0
and every other child player Never. This is an EXACT unrestricted terminal
child Nash profile. Owner z earns1, while any late/ Never withdrawal earns0;
each other child player has a strictly negative date0 joining gain because
its only positive joining partner is the omitted k. Later moves do not
change date0 absorption. Mixtures of deadlines give no additional gain.
All child debts are zero and child joint Never is zero, but quiet parent
outsider k gains1 by joining at date0.

Consequently, for EVERY proper child selection, there are no fixed finite
nonnegative debt weights and Never residual making a bound

    d_k(quiet(p)) ≤ ∑[i∈S]c_i d_i(p)+ρ Q_child(p)

hold for EVERY actual child profile p. This directly falsifies every
advancing F/J certificate and every one of the five withdrawal kinds,
over all weights and all child choices, using the exact universal theorem
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`Classification/QuietExtension/WithdrawalFutureJoinDebt.lean` and the literal
raw structure `WithdrawalFutureJoinRewardCertificate` in
`Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`. It likewise
blocks the corresponding universal capped-clock domination transports.
All14 child countertests were independently enumerated exactly.

This is NOT noncoverage by an EXISTENTIAL selected-child equilibrium
producer. Another child root or continuation could still be safe; the
proof neither estimates those choices nor claims every quiet lift has a
gap. A separately supplied stationary/child/periodic certificate remains
a verifier, not a universally excluded strategy class. The no-sure theorem
above is also not a substitute for a census of all proper quiet roots.

### Other applicable raw screens and Γ source alignment

Every pair has a strictly negative directed joining gap. Thus every pair
partition fails the scheduled-member inequality of
`exports/TWO_PAIR_JOIN_CAP_UNIFORM_EQUILIBRIUM.md`; every partition also has
an opposite-pair participant triple4>own1, violating its cross caps.
Rows0 and1 of Γ each have TWO positive offdiagonal entries, so no relabeling
meets strict or weak exclusive crossed matching. The symmetric/below-floor
and opposite-sign matching families require that same singleton matching
pattern and therefore fail before parameter selection. The signed-inverse
column family fails because Γ⁻¹ column1 has a zero, while columns2 and3
have mixed signs. In fact

    Γ⁻¹=(1/25)[[8,5,9,3],[3,5,−6,−2],
               [14,15,−3,24],[10,0,5,10]], detΓ=25.

It also fails the nonnegative-inverse/negative-determinant raw criterion
`exists_uniformEquilibriumPayoff_of_nonnegative_singletonInverse` in
`Classification/LCP/NonnegativeInverseCriterion.lean`. No positive Γ cycle
of length four exists: row2's only positive predecessor is0, row3's is2;
a four-cycle would require row1's predecessor3, whose gap is−3. This
excludes all orderings of both signed-four-cycle eigenvalue branches.
The literal conditional range adapter fails for every blocker: its
ContinueUpper is at least passive pair5, whereas QuitWithoutLower≤own1
and QuitWithLower≤grand−200. Their nonnegative lower-hazard mixture is≤1.
I checked `IsQuittingConditionalFaceGapRange` in
`Classification/Existence/ConditionalFaceGapRange.lean`.

As a further attempted singleton-only retirement, all principal determinants
of order≥2 are nonzero: pair list (−6,2,3,2,−6,1), triple list (10,−3,5,8),
full25. Each Γ column has a negative coordinate, so no homogeneous LCP
solution can have singleton support; nonzero principal determinants exclude
larger homogeneous supports. For positive anchor a=(1,2,3,5), exact principal
inverse candidate enumeration at offset−a gives the sole admissible support
023, candidate z=(3,0,8,3), with inactive row1 slack3 and determinant5.
Thus the R₀ degree is1 by
`r0Degree_eq_sum_admissible_inverse_supports` in
`MathUE/LinearProgramming/FiniteSupportDegree.lean`, and Γ is StandardQ by
`isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`.
I inspected those exact declarations and recomputed all support candidates;
this is ordinary exact mathematics, not a new Lean-checked fixture instance.
Hence generic homogeneous, non-Q and degree-not-one UE exits do not retire
the fixture. The full normal core named in H11 excludes a hidden proper-core
inverse route. This remains a bounded relevant-producer audit, not a survey
or a claim that all possible actual equilibrium verifiers have been excluded.

### Value verdict and next assembly boundary

The theorem gives a real raw arbitrary-table class and a concrete fixed-target
consumer, not another supplied-object interface. The fixture proves that
supportwise assembly can succeed where ProductLow and whole-core boxed
charges each fail, and the relevant complete-selection checks above found
no existing raw producer that retires it. This is export-level mathematical
value as a strict counterexample-class restriction and new class UE coverage,
not a solution of arbitrary Fin4 and not a full known-class noncoverage seal.
Wider existential quiet/controller noncoverage remains UNPROVED and is not
needed for the theorem. No new L/A/C seal is justified.

The reported 1/100 open-chamber supplement was not in the frozen H1–H12
surface and receives no separate byte-bound verdict here. It may be added
with its explicit finite slack proof before standalone assembly review.
Any standalone export artifact must carry the complete arbitrary-table
proof, original semantics, named consumer and scoped coverage record, and
receive its own final-artifact review. The math-unicode skill changes only
notation in this review, not mathematics or its acceptance criteria.

## Final standalone hybrid-class verdict

**Accepted for mathematical export, with no unresolved mathematical or
semantic objection.** The exact final artifact is
`exports/MIXED_SUPPORT_UPPER_OR_CHARGE_UNIFORM_EQUILIBRIUM.md`,
624 lines, SHA256

    1f342e9ee028c79f37d8b95868fa659aa628e0a65670316a7295716775fbc2f3

I read the complete standalone, Sections1–13, before giving this verdict.
The preceding whole-class review checked the exact arbitrary-table
root-return theorem and source consumer; this assembly keeps their inputs
and conclusions intact. The new finite supplements below were checked
independently, not accepted merely because the notebook passed earlier.

One semantic correction was required: the first reviewed assembly said the
quitting reward was paid at the live coalition-selecting date. The actual
`quittingGame` definition in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`
pays zero at that live date and r(S) only at subsequent absorbed dates.
The author corrected this sentence. Restoring just that sentence in a
read-only stream recovers the initially reviewed SHA256
fd713f854fb9277b2b6cc889f10e1e261f22028b1335af38fa28f752799d19a6,
so all remaining assembly bytes are unchanged. The final statement now
uses the exact original semantics. The root-game continuation identities
are terminal-value identities and require no change.

The full sixty-coordinate open chamber of radius1/100 passes. A pair always
retains a participant near−200, even when its other participant was exactly
at its singleton in the center; therefore no new pair trap can appear.
Every triple retains positive participant premiums, yielding precisely the
same five traps. Nonempty full-support H changes by at most8η; singleton
triple P,L by at most4η; penultimate P,L by at most2η. The fixed slack
coefficients (200,4,197,1/2) satisfy every strict charge inequality and
give C₃=33300. With fixed B=201, M<B<M+2 and every boxed threshold input
hold. Thus this is a genuinely open arbitrary-sixty-coordinate UE class,
not an equality-preserving perturbation or a carried old minimum.

The true punishment P=−4 and the all-annotation no-sure-root proof pass
exactly as in the independent derivation above. The robustness argument
for the no-sure theorem also passes: favorite pair gaps remain positive,
all other pair gaps stay negative, and all triple-versus-passive-pair and
grand-versus-omitted-triple coefficients stay negative. This is uniform
in the annotation because each relevant comparison is screened by a sure
opponent. The fixed true-P value is asserted only for the center table;
the packet does not falsely keep P=−4 throughout the perturbation ball.

The complete inverse-principal table, determinants and inactive residuals
were recomputed. At offset−(1,2,3,5), only support023 is admissible, its
candidate is (3,0,8,3), inactive slack is3 and determinant is5. Empty and
singleton supports are impossible; every other displayed support fails
positivity or residual feasibility. All homogeneous supports are excluded
by negative columns and nonsingular principal matrices. Consequently the
named finite-support degree theorem gives degree1, and the named nonzero-
degree theorem gives StandardQ. The source-level theorem hypotheses are
all explicitly supplied, but the fixture instance has not been newly
checked in Lean.

Selection scope is accurate. The induced Nash sets are not called empty:
only their accepted Nash-plus-base-leave/outsider-join or singleton TRUE-
floor combinations are excluded by the full no-sure-root theorem.
Section12 excludes universal child-debt/Never transports for every proper
child, with an explicit restriction to S∪{k} for the cut outsider. It does
not infer failure of an existential safe-child producer, all quiet profiles,
or all proper stationary/periodic equilibria. The pure-triple ProductLow
witness is now correctly named a product action profile, not a Nash root.
The boxed/weighted/deadlock comparisons retain their complete raw selections
without turning a supplied-object verifier into a producer.

The final artifact is self-contained ordinary mathematics and has real
raw-class UE/strict counterexample-restriction value. It settles neither
arbitrary Fin4 nor the general stochastic-game conjecture, and it carries
no additional L/A/C evidence claim. I did not edit the packet, export it,
edit or build Lean, stage, commit or push. This is the final byte-bound
independent acceptance of the hash above.

## Focused independent Section 50 / SA1–SA11 review

Reviewed the COMPLETE Section 50 of
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, heading through EOF,
final section SHA256
`751097321e6ec2cbdca761ec94a55a4275be3a99800e26a760d9bf86844e4773`.
The first reviewed bytes had section hash `4d60149d…`; the author then
made only the ordered-cut/raw-prefix clarification described below.
I read those changes and independently checked the final section hash.
This is a focused ordinary-mathematical PASS for the combined source
theorem, not another whole-artifact gate or a UE verdict.

### Exact accepted common-source conclusion

Assuming some signed Fin4 no-UE table exists, the construction produces
ONE fresh unit-cube table with positive true unweighted SUM gap, all
canonical 82 exclusions, all included mixed-cohort exclusions, and
ALL-original-minimum debt rigidity. At EVERY minimum's retained
old-calendar marked representation, the prescribed outcome is random,
there is no prescribed mass strictly before the earliest point of the
UNION of ALL active cap sets, and that point is a finite isolated
positive-mixture first collision with at least two positive own atoms.

These restrictions allow multiple, infinite and accumulating active sets.
They allow sure root owners. They do not assume a tail minimum or root
Nash. The separately proved HR theorem applies at this SAME final table
because its inputs are precisely the preserved canonical exclusions,
rigidity, positive actual minimum, and fresh same-table normality. HR
does not require the particular numerical endpoint used to select its
earlier table. No minimizing law or debt vector is transported between
the two selections.

Here "marked representation" must retain its stated producer meaning:
the old-calendar compactification with complete cap convergence and
bounded-density signed transport. The proof does not cover an arbitrary
abstract ordered product law merely assigned the same payoff/cap pair.
Within the produced class, the universal representation quantifier is
correct; it does not depend on one favorable selected cap.

### Complete target and actual deterministic-outcome consumer

The endpoint assigns every one of the sixty coordinates exactly once.
The old-zero branch choices are load-bearing: lower joins equal to zero
move negative, while grand withdrawals equal to zero move positive.
The new lower-positive joins and positive grand withdrawals therefore
have exactly the stated old sign cohorts. Positive recipient scaling
preserves them, with no need for full-table ordered-difference genericity.

I checked all old canonical contacts, including C singleton with mixed
signs, C pair, the opposite C triple/withdrawal sign, individual joins,
all passive floors including Never, and own-minus-grand. Their positive
contacts target at least one. For the additional labels V_A, the values
are exactly |E_A|/2+2|Z_A| for pairs, |E_A|/2+|Z_A| for triples and
|E_A| for grand. Every included label thus targets at least one, strictly
above Ω≤4/5. No positive-only replacement of a C sum is made.

The coefficient bound eight gives 16α label motion. The full new gap
lies in [Ω−16α,Ω], and 32α<σ separates every old noncontact. This covers
EVERY moving new minimizer. Choosing a regular recipient scale afterward
preserves every finite gap, gives all-family rigidity on the fixed old
carrier, and finally concerns unweighted minimizers at the fixed fresh
table. It is not a derivative of one chosen active tester.

For deterministic nonempty coalition A with at least two members,
independence forces its members pure at the same finite clock, with all
outsiders strictly later. The full cap is the root-versus-withdrawal
maximum for members and the passive-versus-join maximum for outsiders.
Earlier singleton tests are strictly inactive by the tracked cap margin.
Thus the entire semantic pair is EXACTLY that of the literal date-zero
pure-A profile with outsiders Never. This equality, rather than old-chart
atom insertion, licenses the actual nonlocal replacement.

The mixed-cohort label equals actual total debt when there are at least
two indebted members or any indebted outsider. The target prices all
those possibilities, including paid outsider joins. Zero indebted
members/outsiders gives zero debt. The remaining case is exactly one
indebted member and no indebted outsider. Releasing that member to Never
with probability ρ reduces its debt to (1−ρ)δ. Every other member's
strict root-versus-wait gap survives uniform 2Mρ response changes,
including the pair's newly reachable late responses. Every outsider
still faces a retained sure date-zero member, so ALL late and Never
replies remain its prescribed passive payoff and its root join stays
strictly worse. The whole debt is exactly (1−ρ)δ, a contradiction.
This repair uses no punishment hypothesis.

Singleton deterministic absorption has U_h=s_h and is excluded by the
strict prescribed margin; deterministic Never forces all laws Never
and zero debt. All deterministic outcome labels are therefore consumed,
not merely coalitions with every member unhappy.

### All-active head box and original support collapse

For each fixed ordered cut u<a<τ, the head targets have positive old mass
and bounded legal likelihood factors of both signs. Their raw prefixes
contain WHOLE original atom intervals. The strong prefix-indicator limit
and bounded old densities give weak-* transport; unchanged products and
ALL moving test kernels realize the full payoff/cap pair in the original
carrier. Nothing is inherited from an arbitrary zero-mass insertion.

Every nonoriginal opponent-product term includes an exit ≤u. Consequently
the SAME positive affine transform acts on EVERY response above a,
including Never and all accumulating active points. The compact lower
set has no active response and a strict gap. This stabilizes the ENTIRE
old cap set, not just a representative branch. The summed polynomial is
actual debt on a two-sided neighborhood, hence constant by minimality.
All-family debt rigidity then makes each individual selected-regret
polynomial constant. Its remote endpoint remains only algebraic.

For one head owner, its conditional payoff is its singleton and individual
constancy forces ORIGINAL U_h=s_h. I reread
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`
under its stated imports. Its full hypotheses are indeed actual carrier,
global SUM minimum, four players, positive bound and total debt, and all
reward coordinates bounded. Its conclusion gives U_h−s_h≥δ−d_h+δ²/8>0
at the FINAL table. No singleton-sign or Nash-tail premise is present.
Thus the sole-head arm is eliminated, not left as a last-sure residual.

With at least two head owners, another conditioned head screens both
the given owner's late prescribed branch and its selected response.
Their raw regret is zero. Since preactive prescribed mass gives strictly
positive ORIGINAL debt, polynomial constancy forces its ORIGINAL head
probability to be one. A non-head owner's selected polynomial vanishes
at the all-head endpoint, so it cannot carry any preactive mass. Hence
each nonempty head set is the entire preactive set P, and every member
of P is sure by that cut.

The original draft's decreasing "regular cut" wording could be misread as
RAW endpoints approaching an isolated retained midpoint, which is
impossible. The final bytes fix this: ordered clock cuts pull back to
whole-atom RIGHT prefixes; those raw boundaries may remain constant.
An isolated lower support endpoint is handled by ONE cut in its right
clock gap. A nonisolated endpoint uses decreasing ordered null cuts.
In either case the ORIGINAL P laws are pure at one common finite date
strictly before τ, and all outsiders are later. This deterministic
outcome contradicts the preceding actual consumer. No endpoint cap is
declared actual merely because its selected polynomial was constant.

### First-root boundary and countertests

Once all original mass is at or after τ, earliest Never means all laws
Never and contradicts positive debt. A zero-mixture finite τ would pay
its earliest owner exactly its singleton and violate the cap margin.
Thus τ is a retained isolated finite atom and the first prescribed stage.

If only one owner has a root atom, the sure-root case violates its
prescribed margin. In the nonsure case, the original-calendar conditional
suffix has positive surviving masses and an actual carrier subsequence;
its total debt is at least δ, not assumed equal to δ. The displayed
ledger uses all suffix replies for lower bounds on nonowner caps and
the exact owner cap max(s_h,b_h). The strict quadratic cap margin gives
δ≥(1−q)D_tail+q(B_h−s_h)>δ. This genuinely excludes the sole-root atom
without treating its conditioned suffix as Nash or minimal.

I recalculated the complete sixty-coordinate coefficient fixture. Its
actual global gap is zero because all own singletons are zero and
all-Never has debt zero. At coefficient level 1/2 the stated C contact,
five two-indebted-member pairs, four triples, omitted sole-member pair,
and zero grand label have exactly the reported target values. This is
a target conflict countertest, not evidence of a positive-gap table.
The independent-profile mixing falsifier is not evaded by the proof:
all local laws change independently relative to one old source, and
the deterministic repair is a literal profile with proved equal full
caps.

No unresolved mathematical objection remains after the ordered-cut
clarification. The section is a genuine fresh-table strict source
reduction, not a conditional domination interface. Its surviving random
atomic first-collision, multiple-cap geometry remains unconsumed; sure
root owners and outcome-equivalent later cap points are not excluded.

## Complete independent BA1–BA10 review: absorbing carrier and finite penalty

Reviewer: CODEX_NOETHER. Status: PASS as an ORDINARY TWO-DOMAIN SOURCE
PRODUCER, not a Fin4 UE proof or a strict exclusion of the original
full-carrier minimum class. No other BA review verdict or author's
assessment was used. I read the entire section headed
“Forward global attempt: an absorbing carrier and a terminal-row penalty”
in the owned notebook; the reviewed heading-through-before-Section50
bytes have SHA256
`b3729a8482a429a2035e66ca2d11bf3d55a92b91042a8ea25d1040a041c4ae59`.
I also checked its transfer against the canonical frozen
[`RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md`](../exports/RANDOM_EARLIEST_COLLISION_PAYOFF_KERNEL_BRIDGE.md),
especially the original finite-chart, signed head/root and sole-supplier
proofs. The earlier PD contribution in that canonical input is my own;
this review independently checks the NEW absorbing-domain transfer,
penalty limit and simultaneous final-table selection, and relies on the
independently reviewed canonical input rather than self-certifying PD.

### Exact accepted quantifiers and the finite-C boundary

From a hypothetical positive unrestricted terminal gap, and for EACH
requested relative tolerance ε>0, BA produces ONE finite table with
positive singleton, positive full and absorbing gaps, two separately
rigid minimum debt vectors, both canonical geometries, and relative gap
and debt-vector distances below ε times the absorbing gap. Every
absorbing-source marked law has at least one zero-Never owner. That
owner is not asserted paid, first-root sure, a maximizer, or the same
owner in different families. The TWO minimum sets need not intersect.

The table is selected before sources and the two objective minima are
compared at that SAME table. No exact equality of gaps/vectors, no
finite-penalty absorption, no common minimizing law and no tail Nash or
minimum-tail assertion is a conclusion. I found no illicit limit of
reward tables being substituted for this finite selection. Common
normalization may make the absolute gap small; the statement correctly
retains relative, not uniform absolute, estimates.

### Full-cap translation, coupling and ALL moving minima

For s_m≥0, the finite deadline supremum dominates Never because delayed
finite replies tend to Never plus c_−m s_m. Adding C to every FINITE
coalition coordinate in that row increases EVERY finite reply by C,
whereas Never increases by C(1−c_−m). Thus the new ENTIRE cap is exactly
B_m+C, even when neither supremum is attained. The prescribed shift
is C(1−c), giving d_m^C=d_m+Cc. Response mixtures introduce no larger
value. The joint-Never atom-moving inequality d_m≥s_m c is valid for
arbitrary independent laws and gives preservation of zero/positive
full gap when s_m>0.

The absorbing-class approximation changes a selected owner's complete
law on mass η≤c^(1/4); it does not presume any fixed owner's Never mass
is small. The payoff cost is at most8Mη in total and the three changed
observer caps at most6Mη; the moved owner's cap is unchanged. This
derives the coefficient14 with ALL finite and Never responses uniformly
controlled. For C→∞ one uses this coupling at the OLD bounded rewards,
not at the growing translated bound. Near-minimizers of D_old+Cc have
c→0, their old pairs approach K_abs and D_old→d; hence Cc→0 as well.
Every contradictory moving selection would give the same compact
argument. At finite C, actual approximating sequences plus the extra
scalar c provide the required lift of carrier minima; no uniqueness of
that lift is needed. The square-root graph correctly falsifies finite-C
attainment and is explicitly not an actual positive-gap game.

### Absorbing anchor, signed transport, tails and fillers

The class is the UNION of the four zero-Never owner classes. A finite
subsequence chooses one common anchor. For finite approximation, move
that anchor's sufficiently small late FINITE mass to a NEW finite date,
not Never; all menus still converge by coupling. In the quantile chart
the anchor density is identically zero on the Never interval. Its
weak-* limit is zero on (c,1), so q_j(Never)=0. Escaping finite dates
remain finite ordered points, possibly accumulating at finite c; c is
not Never. This proves the asserted MARKED anchor, not realization of
the whole marked pair by one integer-clock law.

Existing-own-atom resets and the bounded old head/late conditionals
preserve zero Never mass of this anchor at EACH actual approximant,
including negative legal parameters. If the anchor has no Never mass,
it cannot acquire a supported Never target. Thus every transported
small-box pair lies in K_abs, and the same full moving-test convergence
retains all active branches and c⁺. No new nonsupported clock is inserted.
Any finite root prefix of an absorbing actual suffix stays absorbing.
Conversely, at a sole nonsure root supplier each owner's continuation
probability is positive in the limit, so the original anchor survives
literal conditioning and the suffix belongs to K_abs. The root-sure
case does not require any anchor in its filler: the sure prefix already
absorbs, so arbitrary K_all fillers are legal. The draft correctly does
NOT extend a nonsure prefix's floor to all w∈K_all.

### Margins without borrowing full-carrier minimality

I reread `minimumTerminalSemantic_singletonMargin` and the underlying
auxiliary Nash budget in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticAuxiliaryNashBudget.lean`,
`quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect` in
`UniformEquilibrium/Quitting/Terminal/AuxiliaryNashDefectBudget.lean`,
`exists_first_solo_capThreshold_hit` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticSoloCapThreshold.lean`,
and `positive_minimum_preemptedOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.

The DECLARED minimum theorems require the original full carrier.
BA6 does not apply them to an absorbing minimum. Instead, its weak
margin proof uses an algebraic exact-Nash prefix budget and the floor
only at a prefix in its own compact invariant C. The solo threshold
construction has no minimum hypothesis: it consists of finite prefixes
and an upper debt bound max(D(source),B_i−s_i). At a C minimum the weak
margin makes that upper bound B_i−s_i. Compactness of C supplies the
threshold limit. A below-singleton exact Nash root at that limit is
again a legal prefix in C; its debt budget gives the stated quadratic
margin. Every use of the minimum floor is thereby internal to C.
For the absorbing C, BA3 plus s_m>0 gives actual no-UE, and
`exists_singletonColumnBlockerCertificate_of_fourPlayer_noUniform` in
`UniformEquilibrium/Quitting/Classification/LCP/FourPlayerSingletonColumnBlockers.lean`
then supplies the preemptor for EVERY owner, without own-singleton signs.
No full-minimum conclusion is smuggled into the margin generalization.

### Same final-table canonical inputs and simultaneous rigidity

The compact positive-singleton fiber maximizer is legitimate since
Δ_abs is8-Lipschitz. The cap bound and weak margin at THAT absorbing
minimum give Ω_abs≤1−a<1; AllNever is not used as an absorbing competitor.
The sign-adaptive target owns1, stays in the fiber, and pushes every
old positive contact to at least1>Ω_abs. The same finite comparison
therefore gives actual new absorbing-gap separation. Small generic
perturbation and recipient regularization preserve strict signs/gaps
and positive singleton. No minimizing law is carried across that step.

The canonical deterministic repairs remain absorbing: a singleton
sure root permits every punishment filler, and a release of one member
of a nonsingleton leaves a retained sure supplier. Signed head/root
boxes preserve the old anchor. The sole-supplier tail floor is the
absorbing floor justified above. The rest of SA/BG uses no arbitrary
nonsure K_all graft. Thus all-active and nonisolated later cap sets,
first-root collisions and genuine kernel bridges transfer with the
correct δ_abs and absorbing rigidity.

Row translation leaves ALL homogeneous coalitional difference labels
unchanged except F_(m,∅)=s_m, which diverges. Therefore eventual full-gap
closeness to d preserves ALL contact separations in BOTH objectives.
For each C_n the two concave recipient scalarizations have coordinate
regular sets of full measure; their intersection allows θ_n→1 with
boxes as small as needed for the growing row bound. For arbitrary
weighted new minimizing laws, the OLD nonnegative weighted debt plus
weighted penalty are bounded by absorbing competitors. OLD coupling
forces old D→d and C_n c→0. Compactness and original absorbing rigidity
then give a_n→b. The fixed old absorbing carrier separately gives b_n→b.
This checks ALL moving minima, not just one old branch or selected law.

### Exact attempted falsifiers and strategic value

I independently enumerated the complete sixty-coordinate modified
fixture at the half-root/half-Never law. The old debts are exactly
(7/16,19/32,19/32,7/8); row3's root/later/Never menu is
(7/8,−3/4,−7/8). Adding7 gives the menu
(63/8,25/4,21/4) and debt21/16 in that row, total increase7/16.
The sign countertest also works on the ENTIRE absorbing class:
participant−1/passive0 gives B_i≥0 by Never and
D≥E|first coalition|≥1, attained by pure singleton, whereas full
AllNever has debt0. Its row translation falsifier pinpoints exactly
why s_m≥0 is necessary. These are solved-table and abstract-graph tests,
not positive full-gap evidence.

The checked `exists_uniformEquilibriumPayoff_iff_finiteMenuEarlyAbsorption_of_singleton_pos`
in `UniformEquilibrium/Quitting/Terminal/FiniteMenuEarlyAbsorptionNecessity.lean`
already supplies the zero-gap strategy-class completeness. BA does not
claim that as new. The new ordinary content is the two-domain finite
producer and the prefix-invariant-margin/canonical-source transfer.
It supplies an ADDITIONAL anchored minimizing source at the same table,
while retaining the original full source; it does not narrow the class
of original full-carrier minima or identify the two minima. Its finite
anchor is automatic from the selected absorbing DOMAIN, not a proved
supported best response or renewable paid clock. In a sure-root arm,
arbitrary-tail floor strength is retained; in a nonsure arm only
absorbing tails are covered. Consequently this is a legitimate global
alternative source, but an asserted strict counterexample exclusion or
stronger all-tail consumer would still require new mathematics. No UE
contradiction, export placement, or Lean certification is given here.

No unresolved mathematical objection was found in the reviewed scope.

### Separate BA export-value decision

Verdict: NOTES-ONLY at present. This does not retract the mathematical
PASS. I read the current `exports/README.md` gate separately: a sound
new arbitrary-domain producer is insufficient without a demonstrable
stronger counterexample restriction or a strict narrowing of a live
consumer. BA has not yet supplied that strategic increment.

The exact EXTRA necessary condition produced is: for every requested
relative ε, one may select a new finite positive-gap table having an
absorbing-domain canonical minimum with a zero-Never anchor, alongside
the full-domain canonical source, and make the two minimum sums and
rigid debt vectors relatively ε-close. It does not assert an anchored
FULL minimum, a common semantic pair, or even that the anchored pair
lies in an ε-neighborhood of a full minimum. Zero Never mass is
tautological for one owner of every actual approximating law in that
domain. The finite table and its normalized absolute gap vary with ε;
letting ε→0 supplies no one fixed positive-gap table with common minima.
Thus no previously surviving FULL-minimum configuration is excluded.

Concrete potential leverage is that finite prefixes, supported resets
and old conditional laws preserve the anchor; a nonsure sole-root
suffix remains in K_abs and a sure-root prefix permits arbitrary K_all
punishments. The latter all-tail capability already holds for sure
roots of the full source. The former does not derive a paid or optimal
anchor, a root-sure supplier, renewed absorption, a matching continuation,
or an ALL-tail upper-cap comparison. At a nonsure root the original
unrestricted K_all floor is lost rather than strengthened. Relative
debt closeness alone cannot repair that loss: all-tail competitors may
have caps/payoffs far from both minimum sets and the two minima need
not coincide.

I therefore would not export this as an eliminated branch, a strengthened
canonical full source, or a completed consumer. A next proof genuinely
using the anchor—e.g. producing an actual same-table strict debt descent
on this COMPLETE absorbing domain, proving its anchored minimum is also
full-minimal, or forcing a paid renewable anchor without losing the
needed tail floor—could change the gate decision. None is proved by
BA1–BA10, and no auxiliary condition supplying it should be appended
and then counted as coverage. The present new mathematics is worth
retaining in the owned notebook and the existing review record.

## Independent FC1–FC6 full-clock source review

Reviewed the ENTIRE section `Forward full-source consumer: zero debt and
complete finite clocks` in `notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`,
ending before `Forward normal form: counterexamples arbitrarily near one
constant table`. Exact section SHA256:
`d5ba4cc57104b3ccce875e435200432eeb2c7af5462d924d9340dfdb38b1541d`.
No other FC verdict was consulted. This is ordinary mathematics, not a Lean
check or final standalone-artifact certification.

Verdict: MATHEMATICAL PASS. The stronger necessary counterexample condition
also has affirmative export-level value, subject to standalone assembly and
the usual independent gate. This differs from the BA value verdict because
FC identifies ORIGINAL full minima at the SAME table and exact numerical gap;
the increment is not merely a finite-a.s. anchor in another domain.

### Source selection and exact minimum alignment

FC produces a counterexample table with ALL own singletons strictly positive
and the canonical full-source inputs. Every full minimum pair has one common
nonnegative debt vector a. Either all entries are positive, or EVERY full
minimum pair admits realization by profiles whose FOUR clocks are finite a.s.
The latter arm retains the original gap, original minimum-pair set, rigidity,
and floor over ALL original carrier tails. New clocks and collision ancestry
are allowed; old ones are not claimed unchanged.

I read BAP1–BAP2, rather than assume a positive-singleton adapter. The actual
reverse transport is `isUniformEquilibriumPayoff_original_of_singlePivotNormalized`
in `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`.
Its positive pivot and original punishment-normality premises are supplied.
`quittingSoloReward_singlePivotNormalized` in
`UniformEquilibrium/Quitting/Root/SinglePivotNormalization.lean` gives own
vector e_m. Translating each zero-own row uses BA2's actual full-cap identity
and cannot lower the positive full gap. This is not assumed inverse affine
invariance with Never fixed. Common positive rescaling is legitimate.

The ORIGINAL gap is continuous on the compact positive-singleton fiber. Its
maximum Ω is positive; the weak full-minimum margin and unit cap bound give
Ω≤1−a_i<1. The sign-adaptive endpoint stays in that fiber and pushes positive
contacts to at least1. Thus the contact proof needs only Ω<1 here. Generic
perturbation and regular positive recipient scaling preserve strict own signs
and contact separations. Minima are selected afresh; no later argument needs
continued fiber optimality.

The exact joint-Never debt inequality in
`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean` gives
c_n≤d_k(p_n)/s_k→0 for ANY realizing sequence of ANY full minimum when a_k=0.
Moving a smallest Never atom to a finite date has a vanishing uniform coupling
bound for every payoff and every pure response, hence also every full cap.
The resulting profiles absorb a.s. at the SAME table. Common debt rigidity
applies this to ALL full minima. Since K_abs⊆K_all, both gaps and both complete
minimum-pair sets coincide exactly. No penalty limit or relative error enters.

### All-response completion and actual ROW witnesses

For an actual absorbing independent profile, choose a finite-a.s. owner m.
If it has no second anchor, choose j≠m with r_m({j})≤s_m and replace ONLY j's
old Never atom by a delayed all-finite law of maximal atom η. Its old finite
part stays fixed. Multiplying the new law by the old Never mass only reduces
coincidence. Prescribed payoffs and all caps except m's and j's are uniformly
screened by m's old clock; j's full cap is exactly unchanged.

The deleted-own-clock issue for m is handled separately, not hidden in that
screen. Outside OLD opponent finite-tail events, old exits are before T or
all opponents were Never. On the latter cylinder the new test pays a mixture
of s_m, r_m({j})≤s_m and a tie reward, whose probability is at mostη for ANY
finite test date. The old delayed finite-reply limit is
V_m(Never)+c_{−m}s_m≤B_m. Thus FC3 uniformly bounds ALL new finite responses
and the literal Never response by the old full cap plus an error tending0.
Moving near-best tests cannot bypass this bound.

Conversely s_m≥0 makes the OLD full cap its finite-test supremum. Fix one old
near-best finite test first, then put T beyond it; that test is unchanged.
This gives convergence of the entire cap, not just an upper estimate. The
geometric clock can have arbitrarily long duration; no uniform time bound was
used. Once TWO anchors are fixed, every responder has an unchanged anchor
among its opponents. All remaining Never atoms may therefore be moved to
sufficiently late finite dates with uniformly vanishing payoff/cap errors.
Those final dates are chosen AFTER the first delayed law is fixed. The stated
diagonal choice has the correct order. Closure gives K_fin=K_abs, not just
equality of gaps or zero-gap completeness.

I independently read `exists_core_blocker_of_mem_normalCore` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCore.lean`: it is a ROW
witness M(m,j)≤0 with j≠m. The actual no-UE declaration is
`normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/AmbientCarrierElimination.lean`.
`normalizedSoloMatrix_eq_soloReward_sub` in
`UniformEquilibrium/Quitting/Classification/PreemptionGateDictionary.lean`
literally identifies M(m,j)=r_m({j})−r_m({m}). This is NOT a transposed
COLUMN preemption condition. `IsQuittingNormalPlayer` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean` is true
P_m≤s_m; FC does not assume that punishment is attained.

### Source regeneration, falsifiers, and significant increment

Every zero-debt-branch minimum pair now has all-four-finite actual
approximants. For the finite-profile marked producer, truncate small late
FINITE masses to another FINITE deadline, not Never. Total-variation pair
control justifies this preliminary step. The separate Never indicator is
continuous in the marked topology, so its exactly0 mass stays0 in the limit.
Both literal Never and the zero-mass finite endpoint remain full responses.
Raw integer dates can escape: these are newly produced finite-a.s. COMPACT
calendar clocks, not raw-time tightness or old-calendar preservation.

The canonical source theorem applies afresh because the table, pair, true
full numerical minimum, contact exclusions and debt vector are unchanged.
Absorbing-domain minimality is never substituted for full minimality. Random
first collision and a genuine root/later kernel bridge are produced anew.

FC6's COMPLETE raw table checks exactly. A pure singleton, all other owners
Never, is unrestricted Nash. At EVERY all-four-finite profile every Never
response pays10, while prescribed total reward is at most31; D≥9, attained
by distinct deterministic dates. This falsifies arbitrary all-finite
completeness and isolates the missing ROW condition. Positive own signs alone
are insufficient. Infinite test dates, long geometric tails, simultaneous
completion, and arbitrary original realizing sequences yielded no falsifier
under FC's actual hypotheses.

The inspected `FiniteMenuEarlyAbsorptionNecessity.lean` equivalence at gap0
does not prove whole positive-gap carrier equality or original minimum-set
identity. The nearby finite-menu punishment and early-absorption sources do
not give this ROW-witness completion. This is a bounded overlap check, not an
exhaustive producer census.

My unreviewed RM18 sure-owner graft produces at most TWO finite-a.s. clocks
under a strict punishment-versus-AllNever-ceiling premise. FC subsumes that
clock simplification in the produced zero-debt branch: EVERY original minimum
pair admits FOUR finite-a.s. clocks, without a sure root, a sole bridge,
punishment attainment, or strict P_m<s_m. RM18's stationary attainment and
solved equality-boundary tests are distinct mathematics, not FC exceptions.

The actual excluded source mode is a zero-common-debt original minimum pair
having NO all-four-finite realization at its own exact semantic value. The
remaining consumer may take an ORIGINAL all-four-finite minimum retaining the
arbitrary K_all tail floor, or a branch whose EVERY bridging owner is paid.
This is a genuine stronger necessary counterexample condition, unlike BA's
separate relatively close companion. It supplies no paid reset, raw-time
renewal, finite expected duration, equilibrium or strict debt descent. Those
remain open; none is silently supplied as a conditional field. No unresolved
mathematical objection was found in the exact frozen FC scope.

## Final whole-artifact FC assembly and falsification review

Artifact: `FOUR_FINITE_CLOCKS_AT_ORIGINAL_MINIMA.md`; canonical lifecycle
target `exports/FOUR_FINITE_CLOCKS_AT_ORIGINAL_MINIMA.md`.
Exact SHA256:
`0452b5cdebd2cc3186634b98df67ea841c15cba1794e8749931199bfb4c3766b`.
I read the ENTIRE frozen artifact, Sections1–18, including the rebuilt
positive-own source and all boundary tests; the file has1786 newline
characters and1787 logical lines. This verdict concerns these exact bytes,
not an inferred certification from the shorter FC review. No other final
artifact verdict was read. The packet was not edited.

Verdict: WHOLE-ARTIFACT ordinary mathematical PASS; no unresolved objection.
Separate export-value verdict: AFFIRMATIVE. Final placement, review-count and
repository tracking checks remain the coordinator's gate, not this review's
authority. No Lean certification or full Fin4 UE completion is asserted.

Contribution disclosure: the retained sole-indebted deterministic-coalition
release incorporates my earlier PD contribution, already independently
reviewed by MORSE and BROUWER. I do not count this review as an independent
origin audit of that contribution. I checked its literal date-zero use and
integration here, and independently checked the rebuilt normalization,
positive-own fiber, whole-carrier completion and complete source quantifiers.
The other canonical inputs have prior independent ordinary reviews, but the
entire source→final-clock chain was read and stress-tested afresh here.

### Complete input-to-source chain

Sections1–2 keep the original information structure literal: independent
complete clocks, all finite/Never responses, and original zero Never payoff.
The correspondence declarations named in
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean` were
located and reread under their imports. They identify actual laws with
behavioral payoffs and unrestricted replacement caps. The declared no-UE/gap
equivalence in `UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean`
has the stated all-profile quantifier. Section2's ordinary SUM conversion
does not require a best-response supremum to be attained.

The positive pivot is produced, not assumed. Original full normal core and
true punishment normality satisfy precisely the hypotheses of
`isUniformEquilibriumPayoff_original_of_singlePivotNormalized` in
`UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`.
The transport creates new profiles and a fixed affine target; it is not
unchanged-law affine invariance. The own vector becomes e_m. Section14's
FULL-cap shift then raises all three zero owns while preserving the positive
gap. A common normalization gives the positive floors used in Section7.

The worst positive-singleton fiber is compact and the TRUE SUM infimum is
8-Lipschitz. Its own floors plus the actual full-minimum margin imply Ω<1.
Every relevant contact target is at least1 and the entire convex segment
stays in that fiber. The proof correctly uses fiber maximality only in this
ONE comparison. All93 cohorts include old zeros in their correct future
positive branches. The60 assignments are disjoint; their signs, label
coefficients, Ω−16α interval and32α<σ arithmetic are consistent.

Afterwards contraction, row-distinct genericization and positive recipient
scales may leave the fiber. The later proofs require only retained signs,
contact gaps, fresh positive unweighted gap and debt rigidity. The concave
fixed-carrier scalarization produces coordinate-regular weights, not a
maximizer of that scalarization. At such weights the two supporting
inequalities fix EVERY minimizing debt vector. This supplies ONE final table
BEFORE its actual minimizing sequences, while preserving positive own signs.
No old minimum, cap point or debt vector is carried through genericization.

### Marked full caps, all-active boxes and genuine kernel bridge

Sections3–5 give the actual finite-law approximation, chronological atom
charts, bounded marginal weak-* limits, separate endpoint/test-set limits,
product rectangle-density argument and AE/L¹ outcome-kernel transport.
Positive mixture atoms are retained isolated midpoints; other finite points
have zero mass. All moving finite responses and Never are transported, not
only a favorable fixed tester. The finite endpoint c has zero mass and is
distinct from the separate Never label; c⁺ is only a finite-kernel duplicate.

Both kinds of signed target have explicit ORIGINAL legal likelihood bounds.
Whole retained dates are conditioned using their raw LEFT/RIGHT boundaries;
ordered clock coordinates are not confused with those quantile boundaries.
The old density and kernel maps remain bounded and unchanged. Every fixed
small signed parameter pair belongs to the ORIGINAL carrier and retains the
true global floor. Nonisolated upper caps are stabilized by the SAME positive
affine transformation on the WHOLE upper test family, not by false isolation.

I reread the exact declaration
`positive_minimum_fourPlayer_allOwner_quadraticMargins` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`.
Its full-carrier membership/minimum, Fin4, reward bound and positive debt
premises are supplied at every use. No absorbing or old weighted minimum
substitutes for that premise. The deterministic case's literal date-zero
pair equality removes unsupported-calendar insertion; its retained supplier
uniformly screens the unilateral release. The all-active head polynomial
then uses rigidity only on ACTUAL small-box minima, with fixed-cut transport
even when cutoff masses later degenerate. Far endpoints remain selected
regrets, not full-cap or minimum claims.

The no-preactive-mass conclusion precedes the earliest active atom argument.
The sole-root supplier's conditional suffix is an actual carrier limit,
possibly above δ, and the ledger gives the strict contradiction with the
quadratic cap margin. Under no root/later bridge, the entire supported root
box is cap-stable; individual regret constancy forces ORIGINAL suppliers
pure, not just a pure algebraic endpoint. Randomness rules that out. Fresh
row distinctness and a positive original opponent-root coalition event make
the final bridge's payoff kernels genuinely different. Moving finite tests
witness the distinction exactly; only their values become co-maximal in the
limit. No finite-index exact co-maximality or paid bridge is asserted.

### Whole-carrier completion and exact original-minimum regeneration

Section15 reapplies actual no-UE normal-core production to the FINAL table.
I reread `exists_core_blocker_of_mem_normalCore` and
`normalizedSoloMatrix_eq_soloReward_sub`: their ROW witness is precisely
r_m({j})≤s_m, j≠m. It is neither a COLUMN preemptor nor inherited normality
after a table perturbation.

The independent delayed geometric replacement preserves old finite atoms.
Its maximal atom controls ALL simultaneous tests of the deleted anchor. The
old finite-tail exceptional event is distinguished from old Never masses;
the latter yield the explicit s_m/passive/tie payoff comparison. The resulting
upper bound is uniform in every finite response and Never. Nonnegative own
reward supplies an unchanged near-best FINITE test for the lower bound. Two
unchanged anchors then screen simultaneous completion of the other clocks,
with the final dates chosen after the first delayed law. Thus K_fin=K_abs
holds for ENTIRE pairs, under exactly the stated weak ROW/nonnegative-own
hypotheses, including equality cases.

A common zero debt and a strictly positive singleton force c_n→0 for ANY
realizing sequence of ANY original minimum. Moving a smallest Never atom
therefore preserves its full pair and supplies absorption. This proves BOTH
directions of exact minimum-set alignment at the SAME table/gap. The original
arbitrary K_all-tail floor remains unchanged. Section17 then truncates finite
tails to FINITE dates at EACH index, never to Never. Its new minimizing chart
has c_n=c=1, empty Never interval, and zero mass at the finite endpoint c.
All four prescribed marked clocks are finite a.s.; the complete response menu
is not shortened. Earlier chronology and raw tightness are expressly not
claimed. Reapplication of the canonical producer is legitimate at that same
true original minimum.

### Exact falsification attempts and strict value verdict

All added Section18 tests check. The passive10/participant0 table has exact
whole P_fin debt floor9 while a pure singleton gives full/absorbing debt0;
it removes the ROW hypothesis and nothing else. The equality witness1 with
tie reward100 gives cap1+99 sup H({t}), so delayed deterministic replacement
fails and diffuse maximal-atom control is essential. The all−1 table has the
deleted anchor's Never cap0 but every all-four-finite cap−1, isolating the
nonnegative-own lower-cap premise. The participation-indicator table separates
K_all from K_abs even though the claimed minimum sets agree. These are entire
class or exact semantic countertests, not positive full-gap examples.

My RM19 equality wall survives intact and is NOT a missing hypothesis here:
generic positive-own P_i=s_i may be attained only by all-Never opponents.
FC supplies a closure realization, not an actual absorbing punishment,
stationary optimizer, or actual minimizing profile. No strict P_i<s_i is used
in the theorem, and neither the packet's four clocks nor its handoff silently
upgrades this to attainment. RM18's two-clock closure is superseded in the
produced zero-coordinate arm; its stationary attainment remains separate.

The significant increment over the frozen random-collision bridge source is
EXACT original-minimum alignment PLUS FOUR finite-a.s. marked clocks, without
losing its arbitrary all-law tail floor. Previously allowed zero-debt minima
with no such same-pair realization are excluded at the produced table. This
is stronger than BA's approximately close absorbing companion and stronger
than implemented zero-gap finite-menu early-absorption equivalence. The
counterexample producer supplies all strategic hypotheses: positive owns,
ROW witnesses, rigidity, table separations and realizing sequences. No
conditional punisher, controller, cap selector or tail Nash is unproduced.

I found no deferred ordinary proof, dependency on a conference note, or
untracked declaration in the artifact. Every named strategic declaration was
located in its cited project file; the nearby MAX/weighted-source citations
are clearly overlap distinctions, not proof inputs. Repository tracking and
hash promotion remain mechanical coordinator checks. Affirmative export value
does NOT imply a consumer of the residual: chronological paid renewal,
off-minimum cap leakage control, actual minimizing-law attainment and uniform
equilibrium remain open exactly as Section18 states.

## Independent NP1–NP9 full-section review: strict absorbing-gap separation

Verdict: ORDINARY MATHEMATICS PASS; AFFIRMATIVE SIGNIFICANT SOURCE-REDUCTION
VALUE. This is not a Lean certification or a full-conjecture proof.

Reviewed surface: the entire section headed “Forward global source: strict
absorbing-gap separation forces a fully paid finite bridge” in
`notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, excluding the following
heading and section. Its exact SHA256 is

    a2cf862fb5006c6b8acc513a5bfa5bd897e61522bd426498727ebf239600b5ed

I read the complete section, independently reconstructed the global source
and all-response comparisons, and attempted the falsifiers below. I did not
read another NP review or verdict, edit the author, export, edit/build Lean,
or run Git. My earlier RM20 contains the zero-sum instance of the signed-row
identity; my RM18–RM21 investigate sure-owner punishment. Those are disclosed
related contributions, not certification of the author's new global
full/absorbing separation or completion argument.

### Exact accepted quantifiers and global selection

From ANY Fin4 no-uniform-payoff game, the section produces ONE FRESH
unit-bounded, within-row-generic table with positive own singletons, a true
ORIGINAL full-carrier minimum δ>0, a strictly larger absorbing-carrier gap
δ+g, and one common debt vector at ALL full minima. No old table, minimum,
normalization, chronology or canonical93 contact exclusion is carried to
this final table. Every sufficiently near-minimal actual profile, not just
one selected realizing sequence, has a uniform positive joint Never mass
and uniformly positive debt in EVERY coordinate. Every marked full-minimum
producer has the stated nonsure paid finite-to-finite bridge. Literal Never
is retained among complete tests and proved strictly suboptimal, not removed
by a response restriction.

NP2's negative row translation is valid exactly because BOTH old and new
own singletons are nonnegative. Delayed finite replies converge to
V(Never)+h·s, so the complete cap equals the finite-response supremum on
BOTH tables. Every finite response then translates by C even when C<0;
the prescribed shift is C(1−ν), and debt shifts by Cν. The absorbing
ENTIRE-pair map and absorbing-gap invariance follow. This does not assert
arbitrary negative-own affine invariance.

For NP3 I reread
`isUniformEquilibriumPayoff_original_of_singlePivotNormalized` under its
imports in `UniformEquilibrium/Quitting/Punishment/SinglePivotUniformPayoff.lean`
and `all_punishmentNormal_of_normalCore_eq_univ` in
`UniformEquilibrium/Quitting/Classification/LCP/NormalCorePunishmentNormal.lean`.
The reverse transport genuinely requires original normality and a positive
pivot. The no-UE normal-core source supplies those before this operation.
The normalized own vector is e_m; subtracting its one pivot row gives a
zero-own table with positive ABSORBING gap A, not a positive full gap.
AllNever correctly has full debt0 there.

Adding t to all four rows leaves absorbing debt unchanged and makes every
full-profile debt D_z+4tν. The smallest-Never-atom coupling uses only a
bounded reward and changes all payoffs/caps, hence D, by at most
14Mν^(1/4). Together with tν≤d_i≤D it proves a UNIFORM positive full gap,
not merely positive debt at AllNever. The bound
min(A/2,t(A/(28M))⁴) is valid. Choosing t<A/8 simultaneously puts that gap
strictly BELOW A. The proof therefore retains a genuine counterexample
with the full original all-tail floor.

Both gap functions are 8-Lipschitz on their FIXED respective actual law
classes. Consequently inward scaling, generic perturbation, then a positive
coordinate-regular recipient scaling sufficiently close to1 preserve the
strict separation and own positivity. The full debt carrier scales exactly;
the DR supporting inequalities apply to ALL its weighted minimizers and
give one common unweighted debt vector at the final table. Genericity is
selected before scaling, survives row scaling, and no subsequent selection
silently drops separation. The absorbing minimum need not itself be rigid.

### Actual near-minima, marked completion and all-active branches

The uniform inequalities in NP6 apply to every actual near-minimizer.
Taking limits along ANY actual realizing sequence gives the stronger minimum
floor (g/(14M))⁴. The marked Never interval records those limiting marginal
masses, so the floor survives without raw clock tightness. The complete
finite endpoint has value R_i+h_i s_i>R_i; all n_i and s_i are positive.
Thus Never is strictly below every cap, but a moving finite deadline may
still be needed to realize a compact finite maximizer. No actual raw cap
attainment is asserted.

The NP7–NP8 signed-box arguments control ENTIRE active response families.
For a strict chronological head, all upper responses undergo the SAME
positive affine map; all lower responses occupy a compact strict-gap set.
For an isolated supported root atom, root-only caps have complement gaps
and later families again share the affine map. Old whole-atom right-prefix
transport handles both signs and every moving response, including the last
finite tester and Never. Full minimum plus multiaffine constancy first fixes
the SUM; common debt then fixes each row polynomial. Far algebraic endpoint
evaluations are not claimed to retain actual caps.

Every positive head mass e_i is<1 because that owner's Never mass is positive.
For two or more head owners the selected-polynomial endpoint identity
d*_i=e_i d*_i therefore contradicts d*_i>0 directly: no deterministic-outcome
exclusion, contact spectrum or extra genericity is needed. A sole head
instead forces original U_h=s_h and violates the strict quadratic full-minimum
prescribed margin. The null-earliest alternative similarly violates the
cap-minus-own margin. Thus the earliest active clock is a retained isolated
atom and there is no earlier prescribed mass.

At the literal first collision all rates are<1. One supplier is excluded
by its exact original suffix ledger and D_tail≥δ, not by declaring the
tail minimizing or Nash. At least two suppliers are strictly mixed. Under
the hypothetical absence of a root/later bridge, root-only and wholly later
cap families are stable under the full signed root box. A root-only supplier
would change its positive debt by the factor1−λ; a wholly later supplier
would satisfy d*=a_h d* with a_h<1. Both contradict rigidity. The resulting
bridge owner is paid, and its later compact test is FINITE because Never
is strictly suboptimal for every owner.

The kernel distinction uses a positive ORIGINAL nonempty opponent-root
event. Root Quit pays r_i(S+i), while a later response pays r_i(S). Distinct
within-row entries give a genuine payoff difference. Co-maximality is at
the limiting marked source; retained/moving finite original witnesses only
approach both cap values. The positive paid root gain survives eventually.

### Whole-block renewal and independent falsifiers

NP9's profile is an honest independent periodic hazard profile. The block
ends after every original finite atom and includes an empty finite tester;
one-block finite tests therefore attain the original complete finite cap.
Waiting k blocks gives R_i∑_(r<k)h_i^r+h_i^k V_i(t), and periodic Never gives
R_i/(1−h_i). Their full supremum is exactly
max(B_i,R_i/(1−h_i)). All unrestricted behavioral replies are mixtures of
these pure tests. At least two original suppliers imply h_i<1 for EVERY
owner, including a nonsupplier, so the denominators remain positive along
the finite approximants. Prescribed renewal payoff is U_i/(1−ν).

These actual competitors are absorbing, hence their debt is≥δ+g. Subtracting
the source debt δ yields exactly NP12, including the positive payoff term;
U_i>s_i>0 comes from the same true full minimum. Consequently at least one
new upper renewal cap must grow. The section does not mistake payoff
conditioning for complete-cap preservation or claim replay descends.

I inspected the ordinary overlap against the exact declarations
`tendsto_quittingTerminalPayoff_periodizedTailWindow_conditionedValue` in
`UniformEquilibrium/Quitting/Cycles/ConditionedPeriodicRenewal.lean` and
`quittingTerminalPayoff_capNashRootStack_eq_conditionedSplit` plus
`debtDrop_div_terminalDebt_le_capNashStackAbsorptionSum` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalCapNashRenewalObstruction.lean`.
Those conditioned-delivery and tradeoff results do not already supply the
strict full/absorbing gap or this all-near-minimizer floor. The existing
`lawTightStrictSaturation_fullDebt_or_resetRigid_or_singletonNeverCycle`
in `UniformEquilibrium/Diagnostics/Quitting/LawTightCapNashStrictMinimum.lean`
has surviving alternative arms and is not an unconditional all-paid producer.

Attempted falsifiers: negative-old-own translation; a zero absorbing gap
with positive shifted AllNever debt; a finite endpoint co-maximizing with
Never; an owner with no root atom; just one root supplier; all-algebraic
endpoints mistaken for actual minima; and renewal deadlines just after a
block boundary. The explicit own−1 translation test correctly fails outside
NP2. The padded cyclic zero-own geometric example has the stated debt
3q³/[1−(1−q)⁴]→0, so it correctly refutes production without A>0, not NP4.
For a future standalone packet, that regression's complete table should be
spelled out instead of the abbreviated “three-cycle pair±1/grand−1” name;
the main NP theorem does not depend on it. I found no unresolved mathematical
objection to the frozen section.

### Separate strict value decision and precise remaining consumer

AFFIRMATIVE: this is a substantial counterexample-class restriction, not
BA's approximately close absorbing companion or FC's alternative zero-debt
realization. It produces a fresh true FULL positive-gap table where ALL
near-minimizers retain Never and ALL full-minimum debts are positive. In
particular no sure first root, zero-debt bridge or literalNever maximizing
branch survives at THAT produced table. The paid finite-to-finite bridge and
quantitative forced renewal leakage are genuine same-table outputs, not
supplied verifier fields. It does not retroactively exclude those branches
at the old canonical table or preserve its93 contact spectrum.

The new restriction makes a whole-law conditional-Never/renewal consumer
strategically credible: every old minimum has an unscreened positive survival
branch, yet any absorbing completion must pay the born-cap leakage. NP12
identifies the specific complete-cap obstruction to naive replay. Constructing
a different absorbing law below δ, or proving the zero-own absorbing gap A
cannot be positive, remains OPEN. No uniform equilibrium, positive-gap
example, finite raw cap attainment or export placement is certified here.

## Whole standalone NP artifact: independent byte-bound mathematical gate

Verdict: ORDINARY MATHEMATICS PASS; AFFIRMATIVE STRICT SOURCE-REDUCTION
VALUE. No unresolved mathematical objection. This verdict is for the ENTIRE
standalone assembly, not inferred from my earlier NP section review.

Artifact: `exports/FULLY_PAID_NONSURE_FINITE_BRIDGE_SOURCE.md`,1016 lines,
SHA256

    21e596e53595811ad4f83b657d97b3942d53e313d69bb2e9e243c2ee2af11953

I read ALL Sections1–13 in these exact bytes, independently checked the
inlined source compiler, signed transport, common-debt selection, first-root
and whole-cap renewal arguments, and recomputed ALL boundary tables. I did
not read BROUWER's final review or another final-artifact verdict. I did not
edit the artifact, exports, Lean or shared indexes, compile, stage, commit
or push. Related contribution disclosure: my RM20 has the zero-sum signed
row identity; my earlier section review requested the complete cyclic test;
my own notebook has the independent whole-Never graft and solved-table
countertests. None certifies the new global separation or the assembly.

### Exact source chain and same-table quantifiers

The initial no-UE hypothesis is converted to an ORIGINAL positive full gap.
The full normal-core theorem supplies punishment normality before applying
the tracked reverse single-pivot normalization. Both old and new own signs
justify subtracting the pivot row. The resulting zero-own table has positive
ABSORBING gap, while its full gap correctly vanishes. Adding small positive
row constants gives a UNIFORM positive full gap strictly below that absorbing
gap. No finite penalty attainment or restricted minimum is substituted.

The whole-pair completion cost14Mν^(1/4) controls ALL observers' full caps.
Both value functions have the fixed-class8-Lipschitz modulus, so inward
scaling, generic perturbation and positive regular recipient scaling preserve
all strict properties at ONE final table. Section5 proves coordinate
regularity by one-variable concavity/Fubini and pins EVERY minimizing debt
vector through the two signed supporting inequalities. It is not a false
convexity assertion about independent profile mixtures. Genericity survives
positive scaling; full and absorbing gap separation is checked after scaling.

Every sufficiently near-minimal actual law then has a uniform joint Never
floor. EVERY full minimum and ANY realizing sequence inherit it. The minimum
common vector is strictly positive in every coordinate. This immediately
separates the entire full minimum set from K_abs at the same final table.
No old table's minimum, cap selector, chronology or93 contact exclusion is
carried. All later globality and quadratic-margin invocations use this
CURRENT true unweighted FULL minimum and original carrier.

### Inlined marked compiler and legal negative variations

Sections6–7 supply the previously external chart arguments in sufficient
ordinary detail. Finite truncation uses uniform deleted-opponent coupling,
not a claim of raw tightness. Marginal weak-* convergence plus uniformly
bounded product densities gives convergence on rectangle tests, then all
L¹ kernels. Prescribed and moving-response kernels converge strongly off
null raw boundaries; their errors are split before applying the fixed-kernel
weak-* test. No product of uncontrolled weak limits is used.

Endpoint-set convergence identifies retained positive mixture atoms with
single interval gaps. Each such midpoint is isolated; null cuts, the last
finite test c and the separate Never label remain distinct. The exceptional
uncollapsed endpoint set is null by the countable complement-gap argument.
Thus compact response continuity, every moving finite witness, cap upper
and lower limits and original FULL-carrier membership all hold.

The signed atom resets use positive old OWN atom mass. The signed chronological
conditionals use positive fixed old cut mass and unions of whole original
date intervals. LEFT/RIGHT raw boundaries distinguish strict before/after
a retained atom, and their indicators converge strongly. Formula(2) keeps
the old-chart densities uniformly bounded on a two-sided legal box. Product
and moving-kernel convergence realizes the entire modified full pair there.
No insertion at an unsupported clock is silently licensed. All these law
changes keep mass at c zero, so the extra c⁺ tester duplicates c but is not
confused with Never.

The all-upper-family affine identity controls nonisolated and multiple late
maxima without assuming a uniform complement gap. Only the compact LOWER
inactive set uses its strict gap. Root-only isolated caps use their genuine
complement gaps. The multiaffine interior-minimum step is applied after full
cap stability, and common debt pins each row polynomial. Distant polynomial
endpoints are explicitly not certified as actual minimizing cap pairs.

Positive Never masses make every strict head probability<1. Two or more
heads then contradict positive-debt rigidity by d*=e_i d*. A single head
contradicts the strict prescribed singleton margin. The earliest zero-mixture
alternative contradicts the cap margin. The isolated first root is therefore
literal, and all its positive rates are<1. The sole-supplier argument includes
the entire original conditioned suffix and its true K_all floor; it neither
declares a Nash tail nor drops deleted-observer caps. The positive continue
product permits its actual rebased conditional realization.

Section10's hypothetical root-only/later partition is exhaustive only under
absence of a bridge. Its signed box preserves every active family, and the
two individual regret contradictions apply to root suppliers. This forces
a paid root/later bridge. Never is already strictly below EVERY cap, so the
later point is FINITE. The two literal reward kernels differ on a positive
original opponent-root coalition event by within-row genericity. Moving
finite witnesses approach both cap values; exact raw co-maximality or raw
attainment is not asserted.

### Exact renewal overlap and all boundary calculations

I read `UniformEquilibrium/Quitting/Cycles/PeriodicFiniteReplyPrefix.lean`
under its imports. Its
`quittingPureTimeValue_periodizedPrefix_block_interpolation`,
`quittingPeriodicWindowRefusalValue_periodizedPrefix_eq_div`, and
`quittingBestReplyValue_periodizedPrefix_le_max` have exactly the opponent
contraction and first-block finiteBound premises quoted in Section11.
The unrestricted cap reduction is indeed supplied by
`sSup_range_quittingTerminalPayoff_update_eq_periodicWindow`. The artifact
honestly claims no new generic interpolation formula. Its extra EMPTY final
phase makes the old full finite supremum a first-block value. A first-block
maximizing phase and literal Never provide the two matching lower bounds,
yielding exact max(B,R/(1−h)), not merely the tracked upper bound.

At least two nonsure suppliers give h_i<1 for EVERY owner, even a nonsupplier,
so the original finite approximants have positive limiting denominators.
Their periodic competitors absorb almost surely and obey the same-table
absorbing floorδ+g. Subtraction of the original debt gives(P17), with the
strict positive payoff term supplied by(QM). No born cap is omitted.

ALL four Section12 tests verify. The all−1 table isolates the OLD-own sign
premise. The fully specified padded three-cycle has pure finite cap candidates
−q²(1−q)^(3t), Never cap0, U=−q³/[1−(1−q)⁴] for each core recipient and
the stated vanishing absorbing debt. It now includes all60 coordinates.
The passive2/participant0 half-root table has U15/16,B15/8,R7/4 and repeats
to U1,cap2, raising total debt by1/4. The participant−1/passive0 table loses
the empty finite response if period1 is used: repeated cap0 rather than1/8.
Its specified period2 retains cap1/8. Each is correctly a solved game or
hypothesis/menu countertest, not a positive-gap example.

All strategic named declarations were located in their cited project files;
the exact reverse normalization, original gap bridge and true-minimum
quadratic-margin hypotheses were checked under their imports. The artifact
has no borrowed conference-proof dependency or deferred ordinary lemma.
Repository tracking/promotion remains the coordinator's mechanical check.

### Separate final strict-value decision

AFFIRMATIVE, unchanged but independently checked for the final assembly.
The new necessary source has a STRICT full/absorbing gap, a uniform Never
and debt floor at EVERY near-minimizer, no sure first root, and a PAID
FINITE-to-FINITE bridge. This removes the prior source's zero-debt and sure
branches at ONE produced table without surrendering original all-tail
globality. It is stronger than an equivalent zero-gap domain or a companion
absorbing minimum. The complete forced renewal leakage adds an actual
whole-law restriction, while its generic cap formula overlap is acknowledged.

The theorem remains a necessary source restriction. It does not prove
admissible return, cap-compatible descent, raw minimum attainment, a no-UE
example or uniform equilibrium. SG/NF9 is absent and is not imported into
this verdict. Those exact open boundaries are part of the accepted scope.

## Independent CL1–CL10 circuit-input and raw-chamber review

Verdict: PASS, with no unresolved mathematical objection. This checks the
complete section headed “Dual follow-through: a closed singular full-Nash
circuit retires the rational shell”, through BEFORE “Negative dual attempt:”,
in `notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`. Section SHA256:

    0a7b002181838a65118b65adb6c8fe51c5cfb7de024f7707f62cafc2e6858ae2

The base CL1–CL8 subrange through BEFORE CL9 has SHA256:

    191fc80086228218ba9f41905be6f4e22e695ca3bfa6b160bcbdf9c1aafc647a

I read the entire section and independently reconstructed its actual
table/root calculations. This is not a verdict on the whole notebook or a
future standalone artifact. No other CL review was read. I authored the
separately saved ZU compiler which CL8 explicitly reconstructs; that
contribution is disclosed rather than described as blind certification.
The new actual circuit inputs, closure certificate and raw-table extension
were independently tested here. No Lean edit/build, export, staging, commit
or push was performed.

### Actual ports, complete roots and exact closure

The full fifteen-row table is retained. The forward predecessor order is
solo0 ladder, solo3 ladder, literal solo1, literal triple123, pair02 ladder.
Both solo favorite recurrences, telescoping survival products and ALL
spectator inequalities check. Solo3's quiet2 test uses both endpoint
annotations, not an above-own passive target. The solo1 rate is exactly
2N/T; its head and quiet3's negative joining gap check.

I formed forced-Quit/Continue expectations directly from all sixty table
entries with independent opponent subset probabilities. The active triple
differences are exactly f₁,f₂/T,f₃/T. Quiet0's numerator is exactly G₀.
The printed W is consequently justified by ACTUAL indifference. No fourth
owner, grand payoff or response branch is omitted.

Independent rational symbolic arithmetic confirms both pair active
differences vanish identically and both quiet normalized differences equal
CL4, including97/60 and13/15. The displayed bounds follow for B,D≥1,a≤1
although W₁,W₃<1. Requiring all quiet annotations≥own would incorrectly
reject this circuit. The pair survival product telescopes through
(1+t′/C₀)/(1+t/C₀)=1−q₂ and
(1+a′/C₂)/(1+a/C₂)=1−q₀. I checked the general terminal weights against
both active endpoint equations and total-mass normalization. CL16 is thus
a return to the SAME b,d, not independently selected favorable ports.

I executed the entire CL6 verifier in exact SymPy rational arithmetic;
every assertion passed. Its polynomials were first checked against the
independently reconstructed actual gaps. Rational J⁻¹ exists. The monomial
magnitude bounds dominate every Hessian value throughout the box, so the
center displacement, derivative variation and self-map bounds prove a
contraction, not acceptance of a rounded root. Box-wide inequalities retain
interior rates, positive t,a∈(0,1), strict quiet0 gap and every solo endpoint
condition. The closed circuit is an actual algebraic conclusion.

### Chronology, ALL caps and the fixed target

Reverse the ENTIRE finite predecessor list, not just each ladder. Every
finite block then has the correct continuation/head incidence. No infinite
endpoint is installed at a finite date. Full-root Nash identifies each
scalar companion value at the reference annotation. Its Lipschitz constant
is DELETED-opponent survival, whereas prescribed payoff uses joint survival.
The resulting seam bound is the SUM of endpoint errors, with no length
factor. Fixed positive first solo0/solo3 rates supply two DISTINCT owners,
so every deleted-opponent period contraction is uniformly below1.

Censoring after m periods changes rewards only when all opponents survive
to that cut. For EVERY response, including Never and later deadlines, the
change is≤5κᵢᵐ. Hence the scalar period-map fixed point is the ACTUAL
unrestricted cap, not a selected fixed point or merely a finite-test bound.
Joint contraction alone would not suffice. The printed debt bound follows
and every approximant approaches the ONE fixed port V. For each chosen
finite period, geometric opponent absorption gives finite mean stopping
time uniformly against deviations; this bounds finite-average/terminal
differences and supplies the terminal-to-uniform step. Choose accuracy and
the truncated period first, then a horizon threshold, never a new target.

I inspected `quittingRootCompanionMap_eq_max_endpoints` in
`UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`,
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`,
and the literal definition in
`UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean` under
their imports. Exact roots have residual/regret0 on that floor-free relation;
all ports lie in rewardBound+2. Normality follows from
`isQuittingNormalPlayer_of_singleton_nonneg` in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`, without
any premium-sign assumption. Therefore summing finite ladder inequalities,
taking limits by continuity, and canceling ALL common ports contradicts
EVERY continuous charged potential as CL7 claims. This independently gives
UE through the named characterization, apart from the ordinary compiler.
These are static declaration checks, not new Lean-check/integration seals.

### Full raw-coordinate neighborhood and finite criterion

CL21–25 adapt all rates/ports to the NEW raw table. Favorite inequalities
give geometric contraction; nonfavorite start/endpoint tests cover the
entire solo interval. The structural initial quiet threshold equality is
retained by construction, not falsely called a strict inequality. All
remaining needed comparisons have uniform strict slack on the closure box.

For generic raw pair entries the exact normalized quiet gap is
sᵢ−vᵢ+(a/E₂)δᵢ,₀+(t/D₀)δᵢ,₂+
(ta/(D₀E₂))δᵢ,₀₂. Substitution of the endpoint expression for vᵢ gives
CL26. CL27 suffices uniformly for ALL t≥0,0≤a≤1 because
L_t+aL_ta≤L_t+max(L_ta,0), with L₀,L_a<0. The stated dependence on Bᵢ
is monotone. Base b≥3/2,d≥13/10 supplies strictly negative margins for
infinitely many rows approaching a binding active endpoint. Pointwise
strictness/continuity was NOT used to infer this uniform conclusion.

The denominator-cleared polynomial map is the actual-gap/return-residual
map multiplied by nonzero positive scalars at its zero. Its nonsingular
Jacobian therefore yields the same implicit-function continuation. Compact
box margins and the factored quiet inequalities persist under independent
perturbations of ALL60 entries. A qualitative open UE chamber is proved;
no numerical reward radius is asserted. At rational input tables the
reusable box conditions are finite rational tests that PRODUCE the exact
closure by contraction, not an externally supplied exact-cycle field.

### Bounded overlap and mathematical value

The named paired RawRegion, BelowSingleton RawFamily, strict/weak crossed
RawSource and InverseRawSource definitions were inspected in their printed
files. Their COMPLETE matching/relabeling choices fail for the table reasons
stated. The cyclic-child pivot fails for every pivot. The criterion in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`
requires both child inverse and literal outside weights nonnegative;
independent arithmetic finds only child023 has nonnegative inverse, with
outside weights(−3/5,6/5,2/5). Negative pair13 fails projective Q-bar.
These failures persist on a smaller raw subchamber. They do not exclude
arbitrary supplied cycles or separately selected quiet-child equilibria.

Independent ALL16 support enumeration at offset(−1,−2,−3,−4) gives only
z=(14/5,0,34/5,13/5), outside slack13/5, active determinant5. Principal
determinants and negative columns give R₀; the degree count is1. The printed
positive simplex image also checks. Elementary no-UE necessary matrix
screens remain compatible but are not mistaken for sufficient no-UE data.

This is genuine constructive progress: actual finite periodic approximate
Nash laws consume a previously unresolved rational trial, and a raw-table
return-map mechanism produces an open full-coordinate UE class beyond the
compared sources. ZU alone was only a supplied supporting compiler; CL
supplies its missing actual charged closure. Neither this review nor CL
claims arbitrary Fin4 UE, universally obligatory circuits, a positive-gap
example or noncoverage by ALL existing producers. An export needs its own
self-contained final artifact/gate; this review does not place a packet.

## Focused SC1–SC6 scalar-producer and free-coordinate delta check

Verdict: PASS, with no unresolved mathematical objection. I read the
complete section “Scalar raw producer: one-variable closure and fourteen
genuinely free reward coordinates” through BEFORE “Dual follow-through:”
in `notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md`, section SHA256

    4eb42752d24e980aa464ce8c78d40fd5baee316b8a8d8937fe52473e55492cd2

This is a targeted delta verdict, not a new compiler audit or certification
of a future standalone. The preceding CL verdict remains byte-bound to its
own hash. My ZU contribution remains disclosed. No other SC review was
read; no author/export/Lean edits or git operations were performed.

### Actual algebra produces the strategic closure

For an active triple owner, the forced-Quit-minus-Continue gap divided by
opponent survival is own-minus-continuation plus the three actual membership
gains times the two opponent odds and their product. I independently formed
these equations with generic symbols. Substitution of SC1 makes ALL three
active gaps vanish identically: Z solves owner1, p solves owner3, and the
stated D_X and X solve the remaining owner2 equation. The signs of the
original divisors are explicit interval hypotheses; no hidden zero is
cancelled away. Positive X,Y,Z gives interior rates, and0<p<1 is separately
retained.

The pair quiet return coordinates are linear-fractional in t. Direct
substitution shows D_s is the positive-denominator-cleared solo3 favorite
denominator and N_s is the corresponding solo2-coordinate numerator.
Consequently V₂,₂=r₂,3+L₁₃N_s/D_s. Setting E(t)=0 actually enforces
V₂,₂=s₂+J₂₁p/(1−p). Since E is affine and e₁>0, t=−e₀/e₁ solves it
exactly. Thus the literal solo1 root is Nash by the derived favorite
indifference, not by a supplied compatibility field. Its resulting head
has precisely the three coordinates used to derive the triple equations.

The remaining Ψ=0 sets W₀=s₀+t. The pair map then returns the SAME b,d
chosen by its fractional formulas. Every port in the five-piece itinerary
matches. The fixed interval denominator conditions make Ψ continuous;
the two strict endpoint signs produce an interior zero by IVT. Any one
such zero may be fixed before the accuracy choice. Neither uniqueness,
contractivity of this scalar return nor a numerical root is required.

### Interval certificate and ALL active/quiet inequalities

I executed the entire SC5 exact rational verifier; every assertion passed.
Independently checked generic elimination specializes to its printed X,Z,p.
The raw favorite equation equals E*/(1−p), so its t-coefficient is indeed
coef/(1−p), positive on the interval. All original denominators have
positive factors proved separately: D_X,1−p,d−r₃,0, D_s, the pair factors,
and the positive constants. The factored denominator of Ψ may be negative;
its sign is explicitly checked, not falsely declared an original positive
divisor. The interval-ratio routine reverses signs consistently and uses
all four endpoint ratios. Coefficient magnitudes bound the ENTIRE interval,
not finitely many samples.

The whole-interval bounds give b>s₁,d>s₃,t>0,a∈(0,1) and a strict quiet0
triple gap. The constants in SC7 and the endpoint comparisons cover all
three solo pieces, including structural quiet coordinates initially at
their own thresholds. Positive λ₀,λ₃<1 follow from those conditions.
The pair coefficient tests ℓ_t<0 and ℓ_t+ℓ_ta<0 are equivalent to the
uniform condition needed for every aₙ∈(0,1); with ℓ₀,ℓ_a<0 they cover
every pair root, however close to the limiting threshold port. No quiet
player is automatically declared Nash because its INITIAL price is above
own; in particular the below-own triple outputs retain the endpoint-based
pair test.

The explicit coefficient criterion consists of finite reward-derived
inequalities. It produces, rather than assumes, the actual closed-circuit
inputs already consumed by the unchanged complete-cap compiler. Signed own
levels are harmless because deleted-opponent contraction, supplied by two
distinct positive-rate owners, controls Never; no appeal to positive-own
normalization is used for the direct strategic construction.

### Exact unrestricted-response support mask

I independently enumerated every itinerary support A and every recipient i,
all subsets T⊆A\{i}, and both possible terminal coalitions T and T∪{i}.
The resulting set has EXACTLY46 recipient-coalition coordinates. Its
complement is exactly the fourteen coordinates listed in SC6; all36 entries
of the nine prescribed rows are included. This checks the individual
recipient coordinates, not merely whether the coalition itself is reachable.

At an unabsorbed date every public live history still consists only of
Continue actions. Replacing an owner's ENTIRE behavioral clock can choose
any later date/phase, but cannot make unchanged opponents outside that
date's support quit. Distinct dates cannot accumulate into one terminal
coalition. The mask therefore covers every finite deadline, Never, clock
mixture and history-dependent unilateral deviation, not only on-path
expectations. A listed free entry might matter in a DIFFERENT deviator's
terminal vector, but that deviator's payoff uses a different recipient
coordinate; it does not enter its cap. This distinction is respected.

Arbitrary finite changes of the fourteen entries leave each constructed
profile's entire payoff vector and every owner's full unilateral cap
unchanged. They also leave all raw scalar/quiet criteria unchanged. The
strict finite inequalities persist on an open set of the46 used coordinates;
the other14 range independently over ALL real numbers. The resulting
unbounded raw cylinder is stronger than the small60-coordinate CL chamber.
It is a concrete reward-only sufficient class, not arbitrary-game coverage,
not an assertion that this itinerary is obligatory, and not absence of every
other known producer. Final standalone assembly still needs its own gate.
