# Independent review: mixed-sign triple core

Reviewer: CODEX_BROUWER.

## Verdict and exact scope

**PASS, after the one finite-horizon convention correction recorded below.**
This review covers Section 25, “A mixed-sign triple core with two
encouraging players,” through EOF in
[the author's notebook](../notes/CODEX_MORSE__GLOBAL_QUITTING_OBSTRUCTION.md),
at whole-file SHA256
`ef8e9d12c2c11f8d9606fbd5e7a65654eca9f43933abc677b5632fb0c82d4900`.
The original reviewed bytes had SHA256
`8564e988dfb8c568a0fce58401ccd4e471de241ba884b384d8e38a239033b0e9`.
The identified correction changes no raw assumption, root calculation,
coverage fixture, or uniform-equilibrium conclusion.

I derived the root classification and determinant signs independently,
checked the literal consumers under their imports, and recalculated the
rational fixture. No counterpart review was read. This is ordinary
mathematics with exact symbolic checks and static source inspection;
I did not run Lean, build anything, or check this new producer in Lean.

The theorem is a genuine original-table producer, not a supplied-root or
supplied-strategy verifier. For Fin4 it gives one fixed original-game
uniform-equilibrium payoff against unrestricted behavioral deviations.
The exact fixture lies outside the applicable named implemented and
accepted raw sufficient classes audited below. Thus the result genuinely
narrows the remaining counterexample class. There is no unresolved
mathematical objection or unproduced strategic-witness hypothesis in
this proof chain. The finite equalities are indispensable scope:
this verdict is NOT an open-neighborhood result or an arbitrary-game
existence claim. Conditional interfaces requiring other supplied objects
are not counted as existing raw coverage.

## 1. Claim restated

Let s_i=r_i({i}). A nonempty premium trap A requires, for each i∈A,
some S⊆A containing i with r_i(S)>s_i. Its greatest union is exactly
C={1,2,3}. For nonempty T⊆C\{i}, put
d_i(T)=r_i(T∪{i})−r_i(T).

The strict signs are d₁(2),d₂(1)>0; all four cross differences
d₁(3),d₃(1),d₂(3),d₃(2)<0; and d₃(12)<0. In addition,
d₁(23)=d₂(13)=0 EXACTLY. Participant premiums may be signed, even
inside C. Actual rewards involving outside players are retained.

Under these strict conditions either pure 12 is a full exact terminal
equilibrium, or every boxed source v with some v_i<s_i admits a full
exact Nash root with some successor w_j≤s_j. The box can be any
[−B,B]ᴵ with B larger than a valid absolute reward bound. Including the
pure exit, this excludes the full exact-root charged smooth potential.

For Fin4 and s≥0, the weak-sign theorem follows by changing only the
specified passive entries and taking reward closure. It retains BOTH
equalities. The analytic negative-index claim itself is strict, not weak.

## 2. Bad supports, sure coordinates, and the full derivative

At a root let Q_i,C_i be the literal forced-Quit and forced-Continue
endpoints, g_i=Q_i−C_i, and w the actual product successor. If w>s
coordinatewise, every active player has Q_i=w_i>s_i. Averaging over
its opponent coalitions gives a premium witness inside the active
support. Thus that support is a trap contained in C. A singleton is
impossible. If k∉C, every r_k(T+k) with T⊆C is at most s_k,
otherwise C+k is a trap. Therefore its inactive gap is strictly
negative: g_k≤s_k−w_k<0. This does not delete any outside derivative.

The partly-sure classification is exhaustive. If q₁=1, then g₃<0
from d₃(1),d₃(12)<0, so q₃=0; d₂(1)>0 then forces q₂=1.
The symmetric case q₂=1 gives the same pure 12 root. If q₃=1 and
q₂<1, the equality d₁(23)=0 gives
g₁=(1−q₂)d₁(3)<0, hence q₁=0 and then q₂=0. A singleton
support is not bad. If q₃=q₂=1, player2's optimality and
d₂(13)=0 force q₁=1, whereupon g₃=d₃(12)<0 is impossible.
This covers simultaneous quitting and all partly-sure bad roots.

A full pure-12 root is independent of the annotation. Each player still
faces another sure quitter after a unilateral deviation, so the full
behavioral response problem reduces to the initial binary action. It is
an actual terminal equilibrium, not merely an annotated root. For a
charged potential use v=w=r(12), which is inside the reward box.

For every remaining bad root the positive hazards are proper. Writing
z_i=q_i/(1−q_i), the pair active determinant of −Dg is
−d_i(j)d_j(i)/[(1−q_i)(1−q_j)]<0, including the two pairs
whose individual differences are negative. At a triple root the active
off-diagonal entries are

    a_ij=(1−q_k)/(1−q_j) · [d_i(j)+z_k d_i(jk)].

The exact sign matrix is

    [ 0  +  − ]
    [ +  0  − ]
    [ −  −  0 ].

Both directed triangle products are positive. Consequently
det(−Dg)=−a₁₂a₂₃a₃₁−a₁₃a₂₁a₃₂<0. No strategic
action flip or premium-sign assumption is hidden in this calculation.

Use F_v(x)=clip(x+g_v(x)), with g polynomial on ALL real inputs.
At an interior active coordinate, clipping is locally the identity;
at a strictly inactive coordinate it is locally constant. After grouping
active coordinates, D(Id−F) has blocks [−Dg_active, *; 0, Id].
The upper-right block contains the arbitrary outside-coalition rewards.
Thus the displayed negative determinant is the FULL ambient index sign,
not a support-face index masquerading as a full index.

## 3. Ties, finite degree sum, and restoration of every source

An unused core player k at a pair ij can tie. With b_i=v_i−s_i,
its actual gap has the numerator

    N=d_i d_j(s_k−v_k)+d_i b_j d_k(i)
        +d_j b_i d_k(j)+b_i b_j d_k(ij).

The coefficient of v_k is −d_i d_j≠0. Avoiding all three numerator
zero sets is therefore a dense open annotation condition. The denominator
is nonzero at any proper pair root. Outside-core inactive gaps were
already strict, so no greatest-pair-core assumption or reward genericity
is being imported here.

For a generic strict-deficit source, all Continue is not Nash. If all
roots were bad, the classification makes all roots regular of index −1.
The fixed-point set is compact. Its every point is isolated by the
nonzero derivative, hence the ENTIRE root set is finite. This is the
needed justification for the finite index sum; a list of candidate
supports alone would not suffice.

The literal full map takes every real input into [0,1]ᴵ. On the
larger open cube (−1,2)ᴵ, a homotopy to the constant center has no
boundary fixed point. Its total index is +1. Summing all the negative
local indices gives a contradiction, including the zero-root case.

For an arbitrary source on a box face, generic interior sources in the
SAME box converge to it while retaining a selected strict singleton
deficit. Compactness of the full hazard cube, closed Nash inequalities,
and a constant-coordinate subsequence preserve a successor inequality
w_j≤s_j. The limit cannot be all Continue. Convex combination of boxed
source and bounded actual rewards preserves the box. No realized-payoff
restriction on v was inserted.

## 4. Literal strategic consumer and the resolved correction

`HasBoxedSelectedSingletonSublevelReturn` and
`not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn`
in `UniformEquilibrium/Quitting/Projective/SelectedSingletonSublevelReturnSmoothDrift.lean`
match precisely the produced selected root. They impose no nonnegative
participant premiums. Their compact singleton-sublevel minimum argument
is a genuine analytic consumer, not an additional selection assumption.

For Fin4 the strict proof uses
`exists_uniformEquilibriumPayoff_of_selectedSingletonSublevelReturn_on_subbox`
in `UniformEquilibrium/Quitting/Classification/Existence/SelectedSingletonSublevelReturnUniformPayoff.lean`.
With M=`quittingRewardBound reward`, choose B=M+1. This supplies its
literal M<B≤M+2 hypotheses, not just an unrelated max-entry bound.
The downstream declaration
`exists_uniformEquilibriumPayoff_of_continuous_boundaryDifferentiable_potential_exclusion`
in `UniformEquilibrium/Quitting/Classification/Existence/BoundaryDifferentiablePotentialUniformPayoff.lean`
produces the original fixed-target UE through the actual Fin4 polynomial
obstruction. Its zero-own-singleton branch is also implemented. No
periodic-controller completeness or finite-law realization is assumed.

For weak signs, lower r₁(2),r₂(1) and raise r₁(3),r₃(1),r₂(3),
r₃(2),r₃(12), all by the same positive δ. These are seven distinct
passive entries. The two equalities, EVERY participant reward, all own
singletons and the complete trap family are unchanged. All seven weak
signs become strict. The actual declaration
`exists_uniformEquilibriumPayoff_of_arbitrarily_close_reward_tables`
in `UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
then fixes one original target, although nearby targets and strategies
vary. This is simultaneous weak restoration, not seven incompatible
limits or a weak derivative theorem.

**Correction found and resolved.** The original sentence that pure 12
“yields its constant target at every finite horizon” was not literal in
the project's game convention. `quittingGame` in
`UniformEquilibrium/ProofView/Concepts/Stochastic/Models/Quitting/Game.lean`
pays zero in the initial live state and r(12) from the next state.
For N≥1 its N-stage expected payoff is (N−1)r(12)/N. The same factor
applies after any unilateral deviation, since another sure quitter
remains. It is exact Nash at every N, with target error at most M/N.
I requested this replacement, read the changed passage, and verified
the corrected hash above. The fixed-target UE and potential self-loop
arguments are unaffected. No objection remains from this convention.

## 5. Complete fixture and two independent root stress tests

I recalculated the following full table, not just its joining signs:

| S | r(S) |
|---|---|
| 0 | (1,−1,−1,−1) |
| 1 | (2,0,2,−1) |
| 2 | (2,−1,0,2) |
| 3 | (−1/2,2,−1,0) |
| 01 | (0,0,2,−1) |
| 02 | (0,−1,0,2) |
| 03 | (0,2,−1,0) |
| 12 | (−1,1,3,3) |
| 13 | (−1,1,1,−2) |
| 23 | (−1,1,−2,1) |
| 012 | (0,0,0,3) |
| 013 | (0,0,2,20) |
| 023 | (0,2,0,0) |
| 123 | (−1,1,1,1) |
| 0123 | (0,−2,−2,−2) |

Its own singleton vector is (1,0,0,0), and its ONLY traps are 12,123.
The nine joining values in the order of the statement are
(2,1,−1,−1,−1,−1,0,0,−2). Every claimed pure toggle and gain
checks; all Never fails by player0. In particular the table is not
disposed of by the pure-12 exit used in the proof.

### Selection is genuinely needed on this admitted table

At the exact annotation and full hazard

    v=(1,5/9,0,−14/27),       q=(0,1/10,1/4,1/10),

the endpoints are

    Q=(243/400,13/40,1/10,1/10),
    C=w=(847/800,13/40,1/10,1/10).

Thus q is full exact Nash, g₀=−361/800<0, v₃<s₃, and EVERY
successor coordinate is strictly above its own singleton. The active
derivative and full determinant are

    Dg_C=[[0,12/5,−5/6],[1,0,−1],[−25/18,−22/15,0]],
    det D(Id−F)=−41/9.

This falsifies an all-roots-return strengthening on the VERY SAME
admitted reward table. The proof correctly needs a selected good root
from the total degree, not the absence of bad roots.

### Dropping just one equality reverses the index

Change ONLY r₁(123) from 1 to 4 in the complete table above. All seven
strict signs and d₂(13)=0 remain unchanged; d₁(23)=3 instead of 0.
The traps and singleton vector also remain unchanged. Now take

    v=(20,9/2,9/10,−7),       q=(0,1/2,2/3,1/11).

The literal endpoints, including outsider0, are

    Q=(5/33,29/33,29/22,1/3),
    C=w=(469/132,29/33,29/22,1/3).

The outsider gap is −449/132<0, all three active gaps are zero,
and w>(1,0,0,0), even though v₃<0. The active derivative is

    Dg_C=[[0,69/11,11/6],[20/11,0,−11/20],[−10/3,−9/2,0]].

Its two directed triangle products are 23/2 and −15. Consequently
det D(Id−F)=−[23/2−15]=7/2>0. It is a regular FULL index +1
bad root, with inactive outsider strict. The annotation lies in the
finite box B=21>M=20. Hence even boxing does not rescue the proposed
negative-index extension after this equality is dropped.

This is an exact counterexample to the broadened all-bad-negative-index
lemma, NOT a counterexample to UE or to existence of another good root.
It supplies the concrete boundary of the reviewed proof without claiming
more than the calculation establishes.

## 6. Actual coverage checks

The singleton-difference matrix is exactly

    Γ=[[0,1,1,−3/2],[-1,0,-1,2],[-1,2,0,-1],[-1,-1,2,0]].

All principals of size at least two are nonsingular, while every column
has a negative off-diagonal entry. A nonzero homogeneous complementary
solution cannot have support of size at least two (invertible active
principal) or size one (negative inactive residual). Thus Γ is R₀.
Exact enumeration at offset (1,−1,−1,−1) gives only (0,1,1,1),
with residual (3/2,0,0,0), active determinant 7 and degree 1.
This excludes the homogeneous and non-degree-one raw exits.

The inverse on 123 is [[2,4,1],[1,2,4],[4,1,2]]/7, but its actual
outside inverse row is (−3/7,9/14,2/7). The other three triple
inverses have the claimed negative entries −2,−4/7,−3/4; the full
inverse has entry (0,2)=−9/7. These rule out the literal weak/strict
inverse-passive-row tests, not only a preferred cyclic labeling.

I checked all thirteen displayed singleton block-row inequalities.
For the remaining nontrivial partition 0|123, at all hazards 1/2 the
literal `quittingDiscountedDisplacement` uses opponent CONTINUE mass
1/8, so F_i=(7/8)Q_i−A_i. For i=1,2,3 the endpoint pairs (Q_i,A_i)
are (1/8,1/2),(0,1/2),(9/4,7/8), giving exactly
(−25/64,−1/2,35/32). Thus all fourteen nondiscrete response
partitions fail a necessary invariance condition. The discrete partition
is not a reduction.

For each proper child the displayed profile is full terminal Nash and
has joint Never zero. The thirteen pure exits in the author table check
against both immediate toggles and later singleton waiting when the
sole prescribed quitter deviates. For the remaining child012,
q=(1/3,1,2/3) followed by Never gives

    Q_child=(0,4/9,2),    C_child=(0,−7/9,2).

Only player1 can leave a live continuation, and its own singleton is0;
there is no omitted profitable later response for that child player.
The omitted player3 gets 5/3 and can obtain 16/9 by immediate Quit.
Thus its gain is 1/9. The full quantifier is EACH proper child has
SOME omitted player violating EVERY fixed nonnegative weighted-child-
debt plus finite Never-mass bound. This directly rules out universal
quiet-debt/F/J certificates, including the accepted small-Never finite
quiet-lift producer. It does not rule out all specially selected quiet
profiles or all conditional strategy inputs.

The other applicable raw tests fail for structural, relabeling-invariant
reasons: core size3 excludes the core≤2 and signed pair-core packets;
four negative joining differences exclude joining-attractive core3;
the grand-row premiums (−1,−2,−2,−2) exclude every nonempty protected
set and every nonzero nonnegative global weighted floor. The same-sign
trap12 has no leaver. Sure123 has all participant premiums1, excluding
product-low and supportwise weighted nonpositive participant premiums.
For the larger trap123, P₁₂₃({1})=3−2=1>0, excluding the boxed
charge and mixed-trap packets regardless of constants.

For the literal cyclic-child joint-phase families, the only positive
own singleton is player0's1, and all its pair participant premiums
are −1. Hence no pivot relabeling satisfies their prescribed zero or
positive pivot-pair premium. The certified two-joint open neighborhood
retains two disjoint pair traps and hence full greatest core, explicitly
in its Section7; this fixture's proper core excludes that packet as
well. The symmetry/response-quotient route has already been excluded
by the complete partition audit.

As an additional diagnostic I solved the exact polynomial Nash equations
on every face containing a sure coordinate, using continuation s and
retaining boundary inequalities. No partly-sure one-date equilibrium
was found. The only parametric algebraic faces before inequalities were
q=(0,1,t,1) and (0,t,1,1); player3's strictly negative gap rules
both out. This diagnostic is not used as a substitute for the raw-source
proof or to claim that every possible chronological equilibrium is absent.

## 7. Named sources inspected

In addition to the literal consumers and game definition cited above:

- `IsFiniteCoalitionPremiumTrap.union`, `.subset_core`,
  `isFiniteCoalitionPremiumTrap_core`,
  `not_isFiniteCoalitionPremiumTrap_singleton`, and
  `not_positive_on_core_insert` in `MathUE/FiniteCoalitionPremiumCore.lean`.
- `quittingPairInactiveGapNumerator_eq_mul_endpointDifference`,
  `quittingPairInactiveGapNumerator_update`, and
  `dense_iInter_quittingPairInactiveGapNumerator_ne_zero` in
  `UniformEquilibrium/Quitting/Root/PairInactiveGapNumerator.lean`.
- `quittingFullClippedEndpointMap`, its cube-membership/continuity
  statements and exact Nash fixed-point equivalences in
  `UniformEquilibrium/Quitting/Root/FullClippedEndpointMap.lean`.
- `exists_ambientDegree_eq_sign_det_of_hasFDerivAt_on_nhds` in
  `MathUE/Topology/AmbientDegreeNonlinearLocalIndex.lean`,
  `ambientDegree_of_selfMap_eq_one` in
  `MathUE/Topology/AmbientDegreeSelfMapNormalization.lean`, and the
  excision/additivity declarations in
  `MathUE/Topology/AmbientDegreeProperties.lean`.
- `exists_uniformEquilibriumPayoff_of_r0Degree_ne_one` in
  `UniformEquilibrium/Quitting/Classification/LCP/SingletonDegreeCriterion.lean`,
  and `PassiveRowInverseCriterion.exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
  in `UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`.
- `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
  `UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
  and `quittingDiscountedDisplacement` in
  `UniformEquilibrium/Quitting/Stationary/DiscountedDisplacement.lean`.
- `HasProductLowQuittingPremium` in
  `UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
  `IsSupportwiseQuittingPremiumWeightCertificate` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremiumBalanceAt.lean`,
  and `IsSupportwiseBalancedQuittingPremiumTable` in
  `UniformEquilibrium/Quitting/Classification/SupportwiseQuittingPremium.lean`.
- `exists_uniformEquilibriumPayoff_of_weightedTrap_strictLeave` in
  `UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversUniformPayoff.lean`
  and `exists_uniformEquilibriumPayoff_of_weightedTrap_weakLeave` in
  `UniformEquilibrium/Quitting/Classification/Existence/WeightedQuittingTrapLeaversRewardClosure.lean`,
  following the raw return/floor definitions in their imports.

The accepted raw packets compared include core≤2, signed same-sign pair,
joining-attractive triple, common/protected support-specific leavers,
weighted floors, boxed charges, mixed traps, finite quiet lifts, and the
prescribed one-/two-joint chronological families. None is asserted to be
a completeness theorem. The new mixed-sign producer remains confined
to its stated equality stratum; the unrestricted Fin4 problem is open.

## Final standalone artifact check

**Final-artifact PASS** for all 618 lines of
[`MIXED_SIGN_TRIPLE_PREMIUM_CORE_UNIFORM_EQUILIBRIUM.md`](../exports/MIXED_SIGN_TRIPLE_PREMIUM_CORE_UNIFORM_EQUILIBRIUM.md),
SHA256
`e002b9df5d40270c3ab239916bf0c23e485bbf9ceff195c6c471ddc4bd6131fd`.
I read the entire standalone file and checked the assembly deltas against
the proof reviewed above. This is an artifact seal, not a second claim of
independent discovery or a Lean check. There is no unresolved objection.

The two exact equalities, all seven strict/weak signs, signed participant
scope and greatest-core condition are preserved. The pure-12 branch has
the corrected initial live-zero convention and M/N target-delivery bound.
The full determinant, all-root finite index sum, arbitrary-source
restoration, original Fin4 canonical-box consumer and simultaneous passive
closure remain present. Every strategic object is produced; no favorable
root, target, finite law or response certificate was introduced as input.

The expanded compact-minimum argument is self-contained. It minimizes on
the full singleton-sublevel union D, returns strict-deficit sources to
that SAME set, obtains the collision-adjusted face drift including
inactive outsiders, rules out a unique binding coordinate, and obtains
nonnegative binding partials when two or more bind. The downward source
x−εe_j stays boxed, selected return gives w∈D, and the signed estimates
yield ε≤(3M+B)a. The Taylor quotient in the assembly is therefore
legitimate. No nonnegative participant-premium assumption or unproved
all-roots-return property replaces these steps.

The unchanged full table, pure gains, matrix calculations, all response
partitions and all fourteen child witnesses are carried over accurately.
The added principal03 non-Q witness is valid: with matrix
[[0,−3/2],[-1,0]] and offset (−1,−1), both residual coordinates are
negative for every nonnegative input. The principal is nevertheless R₀.

I separately recalculated the two new root examples. The inactive-tie
example has exactly the displayed endpoints, inactive player3 gap0 and
active determinant −16/3; increasing only v₃ by η changes that gap to
−3η/8. The modified negative-pair example has gaps
(−25/32,0,−9/16,0), the displayed endpoints, and determinant −16/9.
Its extra trap13 overlaps trap12, and the greatest core remains123.
The full +1 equality-relaxation example and its nonclaims match Section5
of this review exactly.

Two additional bounded implemented-source screens also pass. The
`SignedFourCycleSingletonData` predicate in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
requires a positive predecessor edge in a four-cycle. In this fixture
receivers1,2,3 have respectively only the positive columns3,1,2.
These already form a three-cycle, so no relabeling can supply the required
four-cycle. The coarse `IsQuittingConditionalFaceGapRange` predicate in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`
also fails for every blocker: player0 has passive maximum2, whereas every
participant reward is at most1. Thus its strict lower-face mixture
comparison cannot hold. These are additional source exclusions, not
claims about all conditional stationary-certificate interfaces.

The standalone has no mathematical dependency on conference notes,
feedback, shared indexes or an untracked helper. All raw data, ordinary
proofs and boundary examples needed for the theorem are in the packet;
the named source declarations provide the stated implementation handoff.
There is no review/process history inside it. Coverage exclusions are
properly bounded, and it explicitly disclaims removal of the two
equalities, a full-core theorem and any UE counterexample conclusion.
