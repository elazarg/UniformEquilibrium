# Independent review: negative-premium three-phase producer

Reviewer: CODEX_BROUWER. Ordinary mathematics, not a Lean check.

## Reviewed surface and verdict

The surface is the final section “A negative-premium three-phase producer
for a no-good cyclic child” through EOF in
[the author notebook](../notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md),
whole-file SHA256
`5540f0d1b6843507b1859cc123566a380f24d74d96b543720c4c423eb88bdd01`.
No counterpart review was read.

The claim is an unconditional finite raw-table producer: the five vectors
(N1), twelve caps (N2), 0<ε≤1, arbitrary remaining reward coordinates,
and arbitrary positive playerwise scales and signed own levels produce an
exact terminal Nash profile and one fixed original-game uniform payoff.
The same three-row profile works for every accuracy. It is not a claim
that arbitrary Fin4 games have this form.

**Literal frozen-surface verdict: repair required.** The child-only value
vector (N15) contains one wrong coordinate. It must read

    V_A=(8/13,3,1,1),
    V_B=(24/13,1,3,1),
    V_C=(20/13,1,1,3).

The printed V_B,3=3 is false. At phase A, player3's Continue endpoint
is V_B,3 while its Quit endpoint is1. At phase B the actual recursion
gives V_B,3=(2/3)u₃(1)+(1/3)V_C,3=1, not3.

**Mathematical verdict after this explicit one-coordinate repair: PASS.**
The raw theorem, selected profiles, parameter interval, and fixed-target
conclusion do not change. The corrected B passive comparison for player3
is Quit≤1=Continue, using u₃(13)≤1. The child123 quiet-lift counterprofile
also remains exact, with the same positive pivot gain. I found no further
unresolved strategic input. Final admission must bind corrected bytes,
not silently treat the displayed frozen vector as correct.

## Scalar selection: independently checked identities and signs

For the low branch put d=1+3y−p and use the displayed rational z,w.
I recomputed, from the two Bellman equations rather than from the printed
quadratic, the exact identities

    3(1−p)(1−y)d f = F,
    3(1−p)(1−y)d g = G.

The multiplier is positive on the entire chosen rectangle. The cap
p̄=(3−4y)/(4−3y) is at most1/2, gives z=1, and satisfies
3y−p≥7/10. Thus the w denominator never vanishes and w is proper.

For y<2/3, F(0)<0<F(p̄). Since F is strictly concave, its first
crossing is unique in the cap interval and has positive derivative.
At y=2/3, its chosen root is0 with derivative (55−8ε)/3>0;
the other root is beyond the cap. Consequently the square-root formula
in (N8) is continuous even at this endpoint, with a positive denominator.
This produces a branch; continuity is not an extra selection assumption.

At y=2/5 the test F(1/5)<0 places the selected p above1/5.
The constant part of G is at most−3/25 there, while its ε coefficient
is strictly negative for p≤1/2. At the other endpoint the exact value
is g=(30−52ε)/27. Hence the intermediate root exists throughout
0<ε<15/26, has all four rates proper, and is chosen independently
of the accuracy. No uniqueness of the final scalar root is needed.

At ε=15/26 the separate child-only profile is checked directly.
Its pivot A gain is exactly (15−26ε)/39, so this threshold is not
an unexplained continuation of the proper-profile assertion.

## All actions, arbitrary completions, and signed rewards

I expanded both pure endpoints for each of the four players at all
three rows. For the low branch the only Continue-minus-value residuals
not identically zero before imposing the two equations are

    phase B, player0: −g,
    phase B, player3: −f.

All four active Quit endpoints equal the stated values. At phase A
the two passive centered Quit-minus-value bounds are

    player1: ε(y−p)−(3y−p),
    player2: −εp.

For H=(3−ε)y−p, I independently recovered

    V_C,0−1=H/d,
    V_C,3−εw=3H/d.

Here H>3/10. The B pivot bound follows from its actual policy recursion:
V_B,0=2z+(1−z)V_C,0≥1+z≥1+εz. The other B passive caps are
εz≤3z and 0≤p(1−ε)/(1−p). These are comparisons to the actual
phase values; they do not replace the negative joint-phase value by
an unavailable singleton floor.

With corrected (N15), every high-branch endpoint passes for
15/26≤ε≤1. In particular B3 has equality at its tighter actual value1.
No grand coalition, or any of the twenty-eight unrestricted coordinates,
can occur on path or under one unilateral deviation. At the joint row
only the two specified outsider triples can additionally occur; their
relevant coordinates are explicitly capped in (N2).

An exact signed boundary stress uses ε=1, all twelve caps at equality,
every unrestricted canonical coordinate equal to37, and

    s=(−5,2,−7,0),   k=(2,1/3,5,7/2).

The actual phase values are

    A=(−75/13,8/3,−7,0),
    B=(−43/13,2,3,0),
    C=(−51/13,2,−7,7).

The Continue-minus-Quit vectors are respectively

    (22/39,4/9,0,0),
    (14/39,0,20/3,0),
    (14/13,0,0,14/3).

Every Continue endpoint equals the actual prescribed value; every active
entry is indifferent. Thus negative actual values and arbitrarily large
unused collisions are genuinely permitted, not just asserted.

## Full behavioral and uniform-horizon consumer

Each deleted-player period has the stated survival factor ρ_i<1, even
when p=0. A deviator cannot change the opponents' private live coins;
the unique unabsorbed public history fixes their calendar. Opponent-only
survival therefore bounds survival under every behavioral replacement,
including Never and arbitrarily delayed stopping.

Whole-period contraction first identifies the annotations with actual
terminal values. Iterating the endpoint inequalities then gives the full
terminal cap, with a remainder bounded by 2Mρ_iⁿ. This order is important:
the terminal Nash claim is not merely a supplied Bellman verifier.

The signed transformation preserves each finite one-step equality and
inequality because all reward and continuation masses sum to1. Under
every deviation absorption occurs almost surely, so the row translation
also contributes its full constant to the terminal expectation. No false
general affine invariance with a variable Never mass is used.

For the initial live-zero convention the N-date average is
(N−T−1)⁺r/N. The opponent-only tail gives E[T+1]≤3/(1−ρ_i), uniformly
over every deviation, so the stated C/N delivery and 2C/N Nash errors
follow for all positive N. The target and strategy do not depend on N
or accuracy. This is not exact finite-horizon Nash.

I inspected the exact declarations
`isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate` and
`isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate`
in `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean`.
Their inputs are exactly policy recursion, zero root Nash, and playerwise
opponent contraction. `quittingRootExpectedPayoff_update_eq_endpointMix`
in `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` reduces
the arbitrary mixed root response to the two checked endpoints.
`IsεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/FirstBranch.lean` quantifies over all
replaced Boolean marginals. The periodic compiler then explicitly passes
from arbitrary behavior to the deviator's actual live hazard. No supplied
favorable strategy or unproved completeness assertion remains.

## Bounded coverage and significance check

The ε=100/729 table satisfies every prescribed entry and cap. I recomputed
the printed principal determinants, inverse, and all four literal gaps at
continuation P=629/729. The proof excluding quiet and sure child hazards
is valid. The common increasing map has no nonconstant three-cycle;
its fixed point r(h) is strictly increasing, and the pivot gap
ε(1−r(h))³−r(h) vanishes only at h=1/10. Thus the complete cube root is
uniquely (1/10,1/10,1/10,1/10), with no sure coordinate.

I checked the actual floor-priced singleton definition and both alternatives
`exists_uniformPayoff_or_singletonBase_pos_gap` and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
Here punishment really equals P: immediate Quit guarantees P and a sure
adverse opponent bounds the full response by P. An accepted concrete base,
including a partial free carrier, would extend to a full root at that
punishment with a sure coordinate. The unique-root calculation excludes
the entire source carrier, not merely one selected induced Nash law.

All fourteen listed child profiles are exact and have zero joint Never
mass, with corrected child123 phase value as above. Each outside gain is
positive; for the cyclic child it is (15−26ε)/39. I inspected
`quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin`
in `UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean`.
Its universal supplied-profile inequality directly contradicts each
zero-debt/zero-Never witness, so this is a genuine exclusion of the five
withdrawal certificate kinds, not a finite test on one favored profile.

The singleton matrix's mixed inverse column excludes the signed-column
cone. Row0's two positive singleton comparisons exclude the matching
sign hypothesis read in `PairedCycle.CrossedMatching.RawSource` in
`UniformEquilibrium/Quitting/Cycles/CrossedMatchingPhaseSource.lean`.
The only mutually nonnegative joining pair is03, while no pair is mutually
negative. Hence the two-pair, below-floor and opposite-sign pair criteria
cannot be relabeled into this table. No triple has all six positive pair
joins, as required by the triple–singleton collision-box raw criterion.
The greatest premium core is all four players, not cardinality three.
Negative participant premiums occur in every row, preventing a nonempty
protected set. The proper trap123 has positive singleton charge and
negative global weighted-floor coefficients at background0.

I also inspected `CyclicChildSingleton.RawRows`, `resonance`, and
`exists_uniformPayoff_of_resonance` in
`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/CyclicChildSingletonAdapter.lean`:
the printed nonresonance calculation is on the actual singleton matrix.
The all-negative pivot column is uniquely0, and every possible pivot
partner has negative child premium, outside the nonnegative-premium
one-/two-joint cyclic-child inputs.

**Significance verdict:** after the explicit value repair, this is actual
original-table UE production on a completion family with a concrete source
increment, not an improved supplied-root interface. The exact persistent-
base and universal-child exclusions remove the major whole-class overlap
pitfalls of earlier anchor constructions. This bounded review does not
claim to exclude every stationary strategy or every unspecified local
neighborhood theorem. It also does not claim every completion is new.

No further hypothesis weakening is needed for acceptance. In particular,
replacing the raw caps by selected-rate inequalities would change a useful
finite table producer into an assumed-root interface unless those rates
were simultaneously produced; I make no such extension here.

## Final repaired standalone: exact-artifact PASS

I read all 795 lines of
[the standalone packet](../exports/NEGATIVE_PREMIUM_CYCLIC_CHILD_UNIFORM_EQUILIBRIUM.md),
SHA256
`d914edc619e9d28d64131dc734cd31f9f6d8c87f00a323693911d68794d82421`.
This is a bounded assembly/delta check against the preceding independent
proof review. No counterpart review was read.

**Final-artifact verdict: PASS on these exact bytes, with no unresolved
mathematical objection.** The old frozen-value objection is repaired, not
waived: (N15) now has V_B,3=1, A3's active equality and B3's passive
equality are explicit, and the nine high-branch passive comparisons all
use the corrected actual values. The child123 witness and its positive
outside gain are unchanged and valid. The main raw assumptions, whole
ε interval, arbitrary twenty-eight unused coordinates, signed utility
extension, produced low-branch root and same-profile uniform quantifiers
are preserved without weakening.

The added signed low-branch test has four strictly negative target
coordinates, as claimed. The ε=1 stress agrees with the independent
twenty-four-endpoint calculation recorded above. The actual-data and
handoff sections retain all three policy equalities, three exact root
Nash statements and four opponent contractions; none is silently assumed
as raw input. The handoff's endpoint bridge
`isεQuittingRootEndpointNash_iff_isεQuittingRootNash` in
`UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean` is the
literal all-marginal consumer. The paired/solo source suggestions do not
substitute for the already supplied scalar production proof.

I checked the new response-quotient exclusion independently. Every row
of Γ sums to1, so the necessary singleton block-sum identities force
positive row scales to agree within each recipient block. The fifteen
partitions leave only the discrete, {0}|{1,2,3}, and indiscrete candidate
partitions. Their matrices are Γ, [[0,1],[−1,2]], and [1], respectively.
The middle matrix is R₀, has sole offset−1 root(1,1) and determinant1;
its inverse is [[2,−1],[1,0]]. Each remaining candidate has degree1 and
positive determinant, also after positive row scaling. Thus the two
specific quotient producers printed in the packet are indeed excluded,
without claiming failure of all possible quotient invariance.

For this delta I inspected
`quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`,
`exists_uniformEquilibriumPayoff_of_responseInvariant_singletonSign` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotientStrategic.lean`,
and
`finFour_exists_uniformEquilibriumPayoff_of_responseQuotient_nonnegative_inverse`
in `UniformEquilibrium/Diagnostics/Quitting/FinFourResponseQuotientCriterion.lean`.
The latter literally requires a negative determinant and nonnegative
inverse. The four-clock predecessor condition and paired-cycle
`RawRegion.eq_partner_of_singleton_lt` comparisons are also correctly
bounded source failures, not blanket stationary exclusions.

The entire packet is self-contained ordinary mathematics with named
production-source references. It has no dependency on another conference
note, counterpart review, untracked mathematical helper, or process
history. Its significant-class claim is the demonstrated original-table
producer and explicit failure of the compared raw sources, not a claim
to settle arbitrary Fin4, all stationary strategies, or unspecified
existential neighborhoods. The strategic witness is fully produced.
