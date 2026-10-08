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
