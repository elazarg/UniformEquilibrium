# Signed inverse columns: independent falsification

Reviewer: CODEX_NOETHER. Ordinary mathematics and bounded read-only source
checks; no Lean build or verification claim. No counterpart feedback was read.

## Tested claim and verdict

I read the author manuscript from “A nonbijective favorable graph survives
the complete matrix source” through EOF, bound to whole-file SHA256
`1dd1b15c6e963cb6c4d21f5eaba0fdd8884c40df0b4ecda15613888e09b52a52`:
`notes/CODEX_BROUWER__QUITTING_TABLE_COVERAGE.md`.

**PASS for the raw theorem and substantive class narrowing.** The cone and
radial construction really produces the four proper hazards; the negative
inverse column is handled algebraically, not by reversing a player's payoff.
The complete repaired table genuinely fails the compared actual raw source
tests, including all fourteen nonnegative quiet F/J children. There is one
harmless strictness sentence to correct in a final assembly, specified below;
its weak replacement proves the same exhaustive sure-owner census. A later
standalone artifact requires its own byte-bound assembly check.

Corrected-byte delta verdict: the same review surface also **PASSes** at
whole-file SHA256
`3c98194d8adbb5bfcbcd8ad26e5fdfd7c1e98ce91b5c62b3fbba99fb93d8103f`.
Reversing only “forces x,y≤1/11” back to “forces x,y<1/11” in a
read-only stream reproduces the original tested SHA256 exactly. Thus the
sole delta is the harmless strictness correction proved below. No remaining
repair is required. The all-fourteen raw-J proof later in this review is
a separately proved coverage strengthening, not an extra hypothesis or
a claim that those paragraphs are already in the frozen author manuscript.

The game has independent private Continue/Quit actions, public histories,
signed finite absorbing rewards, zero live reward including selection date,
and zero Never payoff. Every unilateral replacement is behavioral and may
use Never or arbitrarily late random stopping. The theorem quantifies over
raw Γ, a scheduled-pair partition, inverse-column signs, participant and
passive increments, and the stated finite buffers. No root, strategy or
continuation witness is an input. Its conclusion is exact terminal Nash and
one fixed original-game UE target, with the same profile at every accuracy
and every sufficiently large horizon.

## Matrix source and inverse calculation

For the displayed matrix I independently obtained determinant13 and inverse

    [[2/13,5/13,−7/13,1],
     [5/13,6/13,−11/13,1],
     [1/13,9/13,−10/13,1],
     [1/13,9/13,−23/13,2]].

The triple determinants are26,−10,6,2. Every principal support of size≥2
is nonsingular; a singleton homogeneous LCP support fails on a negative
entry in its column. This proves R₀. At offset−1 the sole positive entry
in each row forces coordinates0,1,2 positive. The child012 solution with
coordinate3 zero is(1/2,1/2,1/2), with fourth residual−1/2, so it is
infeasible. The only root is the full positive vector1. Its active
determinant is13 and there are no inactive coordinates.

Thus the regular test-offset degree formula has exactly its required
strict-inactive and nonsingular-active hypotheses, yields degree+1, and
the nonzero-degree theorem gives standard Q at every offset. The exact
declarations inspected are `exists_finset_r0Degree_eq_sum_sign_det` in
`MathUE/LinearProgramming/R0DegreeSum.lean` and
`isStandardQ_of_r0Degree_ne_zero` in `MathUE/LinearProgramming/R0Degree.lean`.
This falsifies the claimed simplification “Q and degree+1 force the
unique-positive graph to be a permutation.” It does not itself produce UE.

The child012 inverse is strictly positive; its actual outside inverse row
is(−1,−9,23)/26. Every other triple inverse has negative entries. These
calculations retain the actual row direction and agree with
`PassiveRowInverseCriterion.inverseWeight` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.

## Cone, radial equation, and below-floor buffer

With G=Γ⁻¹diag(σ)>0, m=min G, L=max G and κ=m/(4L), each normalized
image of G times a positive vector has coordinates≥κ. The three terms of
diag(σ)N are all nonnegative under SC1 and the cubic coefficient is
strictly positive. For X=tx on Δκ, I obtain exactly

    ∑F(tx)≥4mκ³t³∑σ_i c_i=A t³.

For 0<t≤1 the three contributions are bounded by3σ_i c_i t²,
σ_iΠ_i t², and−σ_iK_i t²; hence the displayed C t² bound is valid.
Choosing r<min(R,1,1/C) and AR²>1 gives the two strict radial signs.
The normalized-simplex/clamped-radius map is continuous on a compact
convex product. At r its unclamped radius is strictly larger than r; at R
it is strictly smaller than R. Neither boundary can be fixed. An interior
fixed point has ∑F(tx)=t and then F(tx)=tx. This is an actual original
odds root, not a scaled eigenpoint with an unproved multiplier.

The full odds identity remains valid when b_i=−Γ_i,a(i) is negative:

    c_i X_a(i)(1+X_j)(1+X_k)
       =Γ_ijX_j+Γ_ikX_k+K_iX_jX_k+Π_iX_a(i)/(1+X_a(i)).

It is equivalent to ΓX=N(X). Multiplying this equation by signs changes
no original action payoff or ordering. Active Quit and Continue equal U_i;
passive Continue is W_i by this identity.

The buffer proof is noncircular. The produced X obeys X_a≤t<R and
X_j,X_k≥κt. Therefore H_i≥2κt/(1+R)². For c_i<0 the chosen
B_i makes B_iH_i≥|c_i|t≥|c_i|X_a; for c_i>0 the zero buffer gives
Quit≤s_i<W_i. These are all actual passive outcomes, including the
unilateral simultaneous triple. Signed own levels and below-own W_i
require no additional premise. The SC1 signs exclude c_i=0.

## Original behavior and uniform horizons

All four produced hazards are proper. Policy iteration realizes the bounded
phase values as actual almost-sure terminal payoffs. For each deviator,
the three opponents' period survival product is strictly below1 regardless
of the replacement. Iterating the two endpoint inequalities leaves a
bounded remainder times its n-th power, uniformly over every behavioral
replacement. This covers Never and arbitrarily late or unbounded stopping;
it does not condition away a legal deviation.

The opponent geometric tail gives the stated expected-time bound. The
conservative2M[1+2/(1−ρ)]/N target error and twice that regret bound
include the initial live-zero and selection-zero dates. The phase-A target
and profile are selected before accuracy; every larger horizon uses those
same objects. There is no changing-target compactness shortcut.

The actual consumers inspected are
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`. All their
policy, root-Nash and deleted-cycle hypotheses have been produced.

## Exact fixture and exhaustive sure-owner census

I recomputed G>0 with m=1/13,L=2,κ=1/104; A=5/3655808;
R=1000; and B₂=52104052. Substituting all four stated X and K values
gives zero residual in each original equation. Exact enumeration of all
sixteen endpoints gives the stated U,W. Passive Continue-minus-Quit gaps
are15467/330225,3694177318073/1320900,126179/1313250,
5789/131325 for players1,2,0,3 in their passive phases, all positive.
All cap coordinates have the claimed strict slack.

I independently reconstructed the twelve induced-game endpoint rows for
each designated sure owner and obtained exactly the author's table. The
four case classifications are exhaustive, including the mixed j=2 edge
and all-proper three-variable alternatives. All remaining sure-owner
profiles fail an actual immediate-Quit versus Never comparison. For j=0
I recomputed the negative difference
−724795040468913623231/692156460057385664250. For the mixed j=2 row
the upper bound(−100D+1002)/101<0 and the strictly positive Never payoff
have the required signs. The other rows are literal reward comparisons.
Hence EVERY stationary profile with a sure quitter is excluded, not just
pure coalitions or the first retired candidate profile.

Editorial correction: in the j=0 proof, nonnegative
1−11x−11y−83xy implies x,y≤1/11, not strictly<1/11. Equality occurs
at(x,y)=(1/11,0). The needed strict player2 inequality still follows:

    difference₂≤−D(1−x)+1002x≤(−10D+1002)/11<0.

Thus y=0 and player1 forces x=1, the same contradiction. Replace that
one strict symbol by≤ in a final handoff; no theorem or census change
is needed. This is not an unresolved mathematical obstruction.

The census excludes sure-owner STATIONARY raw producers. It is not a
claim that a transient one-shot anchored profile can be replaced by its
stationary first row. The independent one-shot join-monotone anchor
criterion also fails here: each player has a negative literal joining
gain, for example0 at1,1 at02,2 at0,3 at01.

## Stronger direct quiet-source comparison

The universal child debt counterprofiles check, but one can additionally
exclude every actual nonnegative F/J raw child already at J. For a child S,
background T⊆S and outsider k, its required inequality is

    r_k(T∪{k})−r_k(T)
      ≤∑_{i∈S}λ_ki[r_i(T∪{i})−r_i(T)],       λ_ki≥0.

Here are fourteen literal witnesses. Every omitted gain is positive and
all child joining gains in that row are nonpositive:

| S | T | k | omitted gain |
|---|---|---|---|
| 0 | 0 | 1 | 1/2 |
| 1 | 1 | 3 | 1/2 |
| 2 | 2 | 0 | 1/2 |
| 3 | 3 | 0 | 2 |
| 01 | 1 | 3 | 1/2 |
| 02 | 0 | 1 | 1/2 |
| 12 | 1 | 3 | 1/2 |
| 23 | 3 | 0 | 2 |
| 03 | 03 | 1 | d₁ |
| 13 | 13 | 2 | 100 |
| 012 | 1 | 3 | 1/2 |
| 013 | 13 | 2 | 100 |
| 023 | 03 | 1 | d₁ |
| 123 | 123 | 0 | 1000 |

Thus no child and no nonnegative weights satisfy the raw J family; no
supplied-strategy absence inference is needed. The actual five-kind bound
`withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean`
is separately contradicted by the exact zero-debt, zero-Never child
profiles with positive omitted debt. A specially selected safe child
profile is not ruled out by either universal statement.

## Actual-source overlap and nonclaims

The negative inverse column survives positive affine row scaling and
relabeling, so it cannot meet a nonnegative full-inverse criterion. The
favorable graph is not a matching or four-cycle, excluding both strongest
crossed/opposite-sign matching raw classes. The three pair-word comparisons
also intrinsically exclude EVERY proper all-below-singleton two-phase
output:03/12 has positive active premiums,01/23 has c₁=1/2>0,02/13
has c₀=1/2>0. No unspecified local radius was guessed.

For cyclic-child sources,012 is the only possible directed positive
three-cycle. The passive inverse row(−1,−9,23)/26 fails the nonnegative
weights; resonance and degree exits fail at the exact Q/R₀ degree+1
matrix. For the actual joint-pivot source only pair03 has both positive
participant premiums. Its child2 joint passive increment is K₂>0,
violating the retained nonpositive outsider input; pairs13 and23 have
negative pivot premiums. None has zero participant premium. The two-high-
passive raw family requires two nonnegative pivot comparisons but pivot3
has only one. The precise definitions inspected are `RawRows` and
`exists_uniformPayoff_of_resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`,
`outsideInverseWeight_eq` and `exists_uniformPayoff_of_passiveNumerators` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildPassiveInverseExit.lean`,
`CyclicChildJointPhase.RawTable` in
`UniformEquilibrium/Quitting/Cycles/CyclicChildJointPhaseSource.lean`, and
`JointPhaseData.q₂_nonpos`, `JointPhaseData.q₃_nonpos` in
`MathUE/CyclicChildJointPhasePivot.lean`.

All twelve ordered weak-unit guard counterfaces recompute as stated, and
each singleton has a profitable join, excluding the instant-no-join fork.
I inspected `QuittingOneSidedWeakUnitGuards`,
`stationaryTerminalNash_or_instantNoJoin_of_oneSidedWeakUnitGuards`, and
`exists_uniformPayoff_of_oneSidedWeakUnitGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean`.
Recipient2 also fails every conditional-range blocker by ContinueUpper≥4,
QuitWithoutLower≤1 and QuitWithLower≤−1. The source predicate is
`IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`.
Influence1→0 changes sign from−9/2 to−1−K₀>0, falsifying
`SignConsistentQuittingInfluence` and `IsAffineQuittingMembershipGain` in
`UniformEquilibrium/Quitting/Stationary/SignedInfluenceCycleBalance.lean`
and `UniformEquilibrium/Quitting/Stationary/ComponentwiseWeightedPotential.lean`.

The trap, floor and quotient tests are correct: traps03,I; no protected
player; full-trap P=88 and L=90 at13; no global nonnegative forced-Quit
floor weight after the two stated background rows; and the product-low
violation on03. Row sums1 exclude terminal upper weights and force equal
positive scales inside a response block, whose all-sure displacements
1000,1001,1002,−104 are distinct. The finite paired/tournament/visible-
matching-cylinder patterns also fail their literal signs or equalities.

No exclusion of every proper-three or full-support stationary equilibrium
is established or needed. The floating-point roots are not proofs. In
particular `PairedCubicStationaryExample.exists_local_stationary_branch`
in `UniformEquilibrium/Quitting/Examples/BlockPair/PairedCubicLocalPersistenceStrategic.lean`
supplies an existential neighborhood of a different center, not a radius
or universal root producer for every table with that architecture. Neither
blanket membership nor blanket exclusion from all such neighborhoods may
be inferred. An arbitrary supplied-root verifier is not coverage from the
raw table. The theorem genuinely adds the signed-column completion family
with explicit original-game strategies; it does not claim unrestricted
Fin4 coverage or any new Lean seal.

## Final standalone assembly verdict

PASS for the complete675-line
`exports/SIGNED_INVERSE_COLUMN_UNIFORM_EQUILIBRIUM.md`,
SHA256`72c207a851995fec7452a76c9f9c9a4545d41fe154d1330d98d33238f1e986e0`.
I read the entire artifact without reading counterpart feedback. This is
a final-artifact/assembly check against the substantive independent audit
above, not acceptance of a different untested theorem.

The raw hypotheses, signed positive-inverse cone, explicit inner/outer
radii, outsider buffers and original-utility root equations are unchanged.
The two-phase proof supplies actual endpoint inequalities, payoff
realization, arbitrary behavioral/Never and late-stopping control, and one
fixed profile and uniform target before the accuracy and horizon
quantifiers. No utility sign is normalized away. The quantitative horizon
bound is conservative and retains zero live payoff.

The sure-owner census now correctly uses x,y≤1/11. Its contradiction
remains strict, so no missing boundary equilibrium is introduced. The
stronger all-fourteen-child J table is fully included: I recomputed every
child gain vector and omitted gain using exact fractions. I separately
recomputed the exceptional child123 equilibrium, its two zero differences
and omitted gain5210405575/136773399. The standalone distinguishes these
raw nonnegative-row exclusions from the broader universal withdrawal
bounds; the latter use genuine zero-debt, zero-Never child profiles.

The complete fixture, singleton degree/source argument, all-three-word
below-singleton exclusion, weak-unit faces, conditional-range and
influence tests remain as reviewed. All nineteen cited Lean files are
tracked. The implementation handoff names the actual behavioral and
fixed-target consumers in `PeriodicCompiler.lean`, rather than presenting
a supplied certificate as the new raw producer.

Scope is preserved: this excludes an additional possible counterexample
class with the stated signed-column and reward-buffer hypotheses. It does
not assert absence of every proper-three stationary root, membership or
nonmembership in unspecified local neighborhoods, unrestricted Fin4
coverage, or a new Lean seal. No unresolved mathematical objection remains
for these exact standalone bytes.
