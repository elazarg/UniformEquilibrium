# Independent review of the buffered triple–singleton producer

Reviewer: CODEX_BROUWER. Ordinary mathematics and exact symbolic/rational
calculations, not Lean execution or implementation. No counterpart review
was read.

## Frozen scope and verdict

This review concerns only “A buffered triple–singleton producer beyond the
concrete-base screens” through EOF in
`notes/CODEX_NOETHER__MATCHING_JOINT_PRODUCER_FALSIFICATION.md`:
whole-note SHA256
`a6c53fe7264cb3c8bd98ac73739db5f77aaa82b59787fd451d28560cbfc9cfb9`,
section SHA256
`16a55576d344bc1f53bad132c93dc9541e8ff6f86a37c167f029ed6ebee51a50`.

**Soundness PASS. Significance PASS for the stated original-table UE class
and concrete separator.** No strategic input, absorbing-root selection,
fixed-target limit, or boundary case is left unresolved. Unlike the retired
ST1 and coarse-regret proposals, the exact center genuinely escapes all
fifteen concrete punishment-tail/persistent-base screens. Its grand premium
trap makes the greatest core all four players, so the actual no-UE
normalization does not put it into a three-core consumer.

One literal source-convention correction is needed in the fixture paragraph:
its root X=1 solves ΓX−1=0. In the tracked `lcpResidual` convention the
offset is therefore −1, not +1. Writing “right-hand side1” would also be
unambiguous. The displayed root, degree and theorem remain correct. No
correction to the nonlinear homotopy or strategic proof is requested.

The substantive strengthening at the end is independently derived here; it
is not silently attributed to the frozen theorem or included in its hash.

## Actual source and nonlinear root production

For A={0,1,2}, b=3, the raw c_ij>0, c_iA≥0 and the stated collision
caps are literal reward comparisons. Own singletons and all passive
coefficients in the b residual may have arbitrary signs. I checked
`finFour_singleton_r0Degree_eq_one_of_no_uniformPayoff` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSingletonDegreeCriterion.lean`
under its imports. It supplies R₀ and degree1 for the ORIGINAL Γ from
bare original no UE. Thus the matrix hypothesis used in the constructive
branch is produced, not a hidden raw-table assumption.

The identities T4–T7 check term by term. In particular,

    Γ_ij=Π_ij−c_ij,
    r_i(A−i)−s_i=Π_iA−c_iA

give the complete A-date Continue identity, including the simultaneous
two-opponent event. Subtracting T5 from ΓX gives exactly T7. Its linear
terms cancel even when Π is negative, hence N(X)=O(‖X‖²). N_b is a
signed quadratic-plus-cubic polynomial; the argument does not require N≥0.

For every point in E={X≥0:e(X)≥0}, convex averaging gives P_i/D_i≤M_i.
Because L_i≥0,

    (1+X_b)L_i≤Γ_ib X_b+M_i,
    L_i≤B_i,
    X_j≤min[i≠j]B_i/c_ij=R_j.

R₀ implies that column b has a negative coordinate: otherwise its unit
vector is a nonzero homogeneous complementary solution, since Γ_bb=0.
That negative coordinate gives X_b≤M_i/(−Γ_ib). This also covers M_i=0
and zero R_j. E is a compact orthant set, not merely a bounded root set.

For H_λ(x)=min(x,Γx−N(x⁺)−λ1), every zero has x≥0 and e(x)≥λ1,
so every homotopy zero lies in that same E. An enclosing ball is fixed
before λ. A sufficiently large λ removes all zeros, hence the total degree
at λ=0 is0. Locally the R₀ minimum field has a uniform linear norm lower
bound on the sphere, while the perturbation is uniformly quadratic. Its
small-ball degree is1. Excision then produces a nonzero root. This uses no
finite root census, nonsingularity, or sign condition on the cubic terms.

The inspected topology declarations are `r0Degree` and
`localDegree_lcpMinBoxProblem_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0Degree.lean`,
`ambientDegree_lcpMinMap_zero_eq_r0Degree` in
`MathUE/LinearProgramming/R0AmbientDegree.lean`,
`ambientDegree_homotopy` in
`MathUE/Topology/AmbientDegreeHomotopyNormalization.lean`,
`ambientDegree_excision` in `MathUE/Topology/AmbientDegreeProperties.lean`,
and `ambientDegree_eq_zero_of_forall_ne` in
`MathUE/Topology/AmbientDegree.lean`.
`lcpResidual_eq_add_mulVec` in `MathUE/LinearProgramming/LocalAffine.lean`
fixes the offset convention noted above.

Singleton support is genuinely excluded. If only j∈A is positive, then
for each i∈A−j the residual inequality reads
Γ_ij≥Π_ij X_j/(1+X_j). Negative Π_ij is impossible because
Γ_ij=Π_ij−c_ij<Π_ij. Otherwise Γ_ij≥0. The b residual gives Γ_bj≥0,
again producing a forbidden nonnegative column. Support {b} is the direct
column-b contradiction. All remaining hazards are finite and strictly below1,
and at least two players have positive hazards. No positive-coordinate
assumption on all four players is used later.

## Full endpoints, signed values, and horizons

The T3 buffer is valid on the produced odds box, not an assumed root cap.
For each complementary pair {j,k}, X_l≤R_l gives

    [r_b(bjk)−s_b]X_jX_k≤−a⁺X_0X_1X_2/3.

Summing all three terms absorbs the whole positive grand reward. When a
coordinate or R_l vanishes, the same multiplication remains valid; there is
no division by a root coordinate. The forced-Quit denominator D_A is positive.

For inactive i∈A, let δ=e_i/(1+X_b), d_i=1/D_i and d_b=1/(1+X_b).
The actual increments solve

    ΔU_i=d_iΔW_i,       ΔW_i=δ+d_bΔU_i,

which is exactly T11. The denominator1−d_i d_b is positive because some
opponent has a positive hazard. Both increments are nonnegative. Therefore
the old A-date Quit bound U_i and passive-date Quit bound s_i≤W_i remain
below the corrected values. For inactive b, D_A>1 and
ΔU_b=ΔW_b=e_b/(D_A−1) is likewise the exact solution. Active coordinates
have zero residual. These are actual policy values, not uncorrected templates.

Overall survival per period is ρ<1. The policy equations therefore identify
the bounded values uniquely with the actual terminal payoff. For each
complete unilateral replacement, opponents' survival is at most ρ_i^n
after n periods, where ρ_i<1 because support has size at least2. The
opponents' strategies are fresh time-dependent independent coins at every
surviving history. Thus the two endpoint inequalities telescope against
arbitrary private randomization, all later decisions and Never. The residual
tail is bounded by2Mρ_i^n. This proves unrestricted terminal Nash.

The same opponent bound gives E[τ+1]≤2/(1−ρ_i). With
B=2/min_i(1−ρ_i), both prescribed and deviating N-date averages differ
from their terminal payoffs by at most MB/N. The live selecting date really
pays zero: the coefficient is (N−τ−1)_+/N. Hence the fixed target U*
is delivered within MB/N, and finite-horizon Nash error is at most2MB/N.
The same profile and target work at every sufficiently large N. No target
depends on the requested accuracy.

### Exact inactive/signed stress test

Here is a complete own-zero table satisfying the frozen criterion; rowwise
translation gives arbitrary signed own levels without changing the test.

| S | r(S) |
|---|---|
| 0 | (0,1,3/2,−1) |
| 1 | (1,0,−1,3/2) |
| 2 | (−2,−1,0,−1/2) |
| 3 | (−1,−2,−1/2,0) |
| 01 | (2,2,6,0) |
| 02 | (−1,2,5/2,0) |
| 12 | (2,0,0,0) |
| 03 | (0,0,0,0) |
| 13 | (0,0,0,0) |
| 23 | (0,0,0,0) |
| 012 | (2,2,6,0) |
| 013 | (0,0,0,−1) |
| 023 | (0,0,0,−1) |
| 123 | (0,0,0,−1) |
| I | (0,0,0,1) |

All c_ij=1, all c_iA=0, B=(2,2,6), R=(2,2,2), and a=1.
X=(1,1,0,0) is an exact complementary root with e=(0,0,1/8,1/2).
Nominal values for player2 are U₂=17/8, W₂=2, but the actual values
are BOTH13/6. For player3 the nominal values are0 and the actual values
are BOTH1/6. The full target is(1,1,13/6,1/6). This checks both inactive
formulas, zero two-opponent joining gaps, negative pair premiums, positive
grand premium, and exact support size2. Translating rows by(−2,3,−1,2)
produces own levels of both signs and translates the actual target accordingly.
This is a boundary regression, not new coverage evidence.

## Exact coverage checks at the proposed strict center

I independently recomputed Γ, all proper principal determinants, Γ⁻¹,
the complete ΓX−1 complementary census, all four free-game response
polynomials, all eleven larger-base points and gap vectors, and all fourteen
child witnesses. The displayed arithmetic agrees. At offset−1 the only root
is X=1; its determinant45 gives degree1. The matrix itself therefore passes
the actual no-UE source rather than disposing of the center.

The three two-free matching-pennies games have unique proper points, and the
other pair bases have strict dominant-action reductions. For the four
singleton bases the boundary arguments are complete. In particular, at
anchor3 the hypothetical q₁>0 branch forces all free hazards proper. With
T(t)=(1+19t)/(21+t), the equations q₂=T(q₁), q₀=T(q₂) and
α=√2−1 split into:

    q₁≤α ⇒ G₂≤−4+5α<0;
    q₁≥α ⇒ q₀≤q₂≤q₁ ⇒ G₂≤−4−q₀+4q₀²≤−1.

Thus its unique point is(4/5,0,1/21). Its zero-tail owner gap is exactly
−968/1575 and empty mass4/21. Every passive reward of player3 is
nonnegative, so Never guarantees at least0 and its true punishment value
P₃≥0. The actual singleton screen fails by
968/1575+(4/21)P₃>0. The other three singleton points have a sure free
player, so their positive owner excesses57/44,27/38,57/44 do not depend
on the tail at all.

This compares with the actual `quittingSingletonBaseOwnerFloorExcess`,
`quittingSingletonBaseOwnerFloorExcess_nonpos_iff`,
`exists_uniformPayoff_or_singletonBase_pos_gap`,
`quittingPersistentLargeBaseExcess_nonpos_iff`, and
`exists_uniformPayoff_or_persistentLargeBase_pos_gap` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PersistentBaseConcreteGap.lean`.
The associated unrestricted consumers in `PersistentBaseNashSemanticAdapter.lean`
and `SingletonBaseSemanticDispatch.lean` in that directory were checked.
Restricting the free set cannot evade this census: success would extend by
zero hazards to a Nash point of the full free game, with the same screens.

All three complementary-pair criteria fail on a b-mate gap−1,−1 or−4.
Both harmful matchings fail the accepted crossed-matching coefficient bound
at b. The positive full inverse forces every sign in a signed-column inverse
cone to be positive, but the required b participant sign fails. Every pair
inside A has two positive joining gaps. Pair23 does have two negative
joining gaps, both −4, but it is a favorable singleton pair. Equations(1)–(2)
of `exports/OPPOSITE_SIGN_MATCHING_PHASE_UNIFORM_EQUILIBRIUM.md` require the
scheduled pair to be a harmful singleton pair. The only such complementary
matchings are02/13 and03/12: in each, the A-only pair has two positive
joining gaps, while the pair containing3 has one positive and one negative
gap. Thus no admissible harmful scheduled pair has both joining gaps
negative, under any relabeling. The broader assertion that no pair outside
A has two negative joins would be false and is not used.
Any proper two-pair word contains a within-A pair with passive value
s_i+c_ijX_j>s_i, excluding the accepted all-below-singleton branch.

The singleton favorable graph has no directed3- or4-cycle, excluding the
literal cyclic-child and signed-four-cycle raw sources. Every deleted triple
inverse has a negative diagonal, and the full determinant is positive, so
the cited matrix exits fail. The PairedCycle.RawRegion singleton necessity
fails because each row has two below-own passive singletons. No assertion
about every unspecified local-center neighborhood is used.

The pure-A response has all three active rewards2>1, excluding product-low
premiums. The grand coalition is a premium trap, making the core I. Trap A
has every proper leave sum positive, excluding weighted leave and boxed
charges. Each player has a below-own participant reward, so the maximal
protected set is empty. Global weighted floors vanish: coalition b forces
weights0,1,2 to vanish, then coalition0 forces weight3 to vanish. The literal
definitions inspected are `HasProductLowQuittingPremium` in
`UniformEquilibrium/Quitting/Classification/ProductLowQuittingPremium.lean`,
`HasProtectedParticipantPremiums` and `HasSupportSpecificQuittingLeavers` in
`UniformEquilibrium/Quitting/Classification/SupportSpecificQuittingPremiumLeavers.lean`,
`HasGlobalQuittingWeightedFloor` and `HasWeightedQuittingTrapLeavers` in
`UniformEquilibrium/Quitting/Classification/WeightedQuittingTrapLeavers.lean`,
and `QuittingTrapChargeCoefficients` in
`UniformEquilibrium/Quitting/Classification/BoxedQuittingNashCharges.lean`.

All twelve displayed sure-coalition upper-face witnesses are correct; so are
the half-ceiling displacements9/2 and3/4. I inspected
`QuittingOneSidedWeakUnitGuards`/`QuittingOneSidedWeakUnitRawGuards` in
`UniformEquilibrium/Quitting/Stationary/OneSidedWeakUnitProducer.lean` and
`QuittingHalfWeakPolynomialGuards.reciprocal_pos` in
`UniformEquilibrium/Quitting/Stationary/GuardedCrossedResponseWeakPolynomialFaces.lean`.
The literal joining-attractive consumer
`exists_uniformEquilibriumPayoff_of_weakJoiningAttractive_core` in
`UniformEquilibrium/Quitting/Classification/Existence/JoiningAttractiveCoreRewardClosure.lean`
requires greatest-core cardinality3 and does not consume the present full core.

The fourteen pure child profiles really have zero complete debt and zero
Never. Their omitted gains are exactly the displayed positive numbers.
At each corresponding J row all advance/withdrawal gains are nonpositive,
including the five singleton restart floors. This excludes all five raw
`WithdrawalFutureJoinRewardCertificate` kinds in
`UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean`.
It is not a claim excluding every supplied specially selected child extension.

### Two additional bounded source checks

No nontrivial response-invariant quotient survives, even after positive
playerwise affine transport. Every Γ row sum is1. Summing the block-row
necessities from `quittingSingletonBlockRowSum_eq_of_responseInvariant` in
`UniformEquilibrium/Quitting/Stationary/ResponseInvariantQuotient.lean`
forces equal positive row scales inside every quotient block. At the all-sure
hazard the displacements are(−1,−1,−1,1/20), so3 is a singleton block.
The remaining singleton block-row equalities permit only block01 as a
nontrivial block. At q₀=q₁=0,q₂=q₃=1 its displacements are−10 and10,
contradicting that block equality. This exhausts all fourteen nondiscrete
partitions; translations cancel throughout.

The conditional-range criterion also fails for every blocker and every
auxiliary choice. In `IsQuittingConditionalFaceGapRange` in
`UniformEquilibrium/Quitting/Classification/Existence/ConditionalFaceGapRange.lean`,
ContinueUpper_i≥4 from the favorite singleton, QuitWithoutLower_i≤1
from empty background, and QuitWithLower_i≤r_i(I)≤2 from the maximal
background. The required strict convex-combination lower bound on
ContinueUpper_i is therefore impossible. This is a failure of the actual
existential range criterion, not of one selected set of auxiliary bounds.

## The open-neighborhood assertion

All raw theorem inequalities at the center have strict slack; R is continuous
there. Core I, strict trap A and the quoted direct floor/partition failures
persist under sufficiently small reward perturbations. The finite induced
Nash graphs are closed, their strategy cubes are compact, and each center
carrier is the singleton proved above. The actual punishment value is
1-Lipschitz in the coordinate reward supremum norm by complete-payoff
comparison followed by supremum and infimum. Thus a sequence of nearby
successful concrete-base screens would limit to a forbidden successful center
screen. The finite union over all bases yields one open sixty-coordinate
neighborhood retaining all fifteen failures and the new raw theorem.
This argument neither supplies a common Nash witness nor assumes correlation.

## Meaningful raw strengthening: a seven-vertex collision test

Keep T1–T2 and the same constructed odds bound0≤X_j≤R_j. Replace T3
by the following finite tests. Define the multilinear polynomial

    K(x)=Σ[j∈A](r_b(bj)−s_b)x_j
         +Σ[{j,k}⊆A](r_b(bjk)−s_b)x_jx_k
         +(r_b(I)−s_b)x₀x₁x₂.

Require K(v)≤0 at every vertex v_j∈{0,R_j}. The zero vertex is automatic,
so at most seven raw inequalities remain. If some R_j=0, duplicate vertices
are harmless. A multilinear function on a rectangular box is the convex
interpolation of its vertex values, using only coordinates with R_j>0.
Hence K(X)≤0 throughout the feasible box. But K(X)/D_A is EXACTLY the
missing forced-Quit excess at b's A date. Every other proof step is unchanged.
No selected root or unknown strategic bound enters this replacement.

T3 implies these vertex tests by its own multiplication proof. The converse
fails substantially: the new test permits POSITIVE triple participant
premiums for b. For example retain the displayed strict center except set
all three b-triple rewards to101/100. Then R=(4,4,8), a=1/20 and

    K(x,y,z)=−2x−2y−z+(xy+xz+yz)/100+xyz/20.

At the seven nonzero vertices the values, in lexicographic order, are

    −8, −8, −392/25, −8, −392/25, −396/25, −84/5.

They are strictly negative although every old triple-buffer cap fails.
This is an exact stronger raw existence test, not constant optimization.
The old center supplies significance; the modified table is only a strict
inclusion test, not a transferred all-source separation claim.

There is also an independent per-player alternative for the three A-to-b
caps: instead of r_i(ib)≤s_i, one may require all three within-A
participant premiums Π_ij,Π_ik,Π_iA≥0 and r_i(ib)≤r_i(b).
Then U_i*≥U_i≥s_i, and the ACTUAL passive Continue equation gives

    W_i*=(U_i*+X_b r_i(b))/(1+X_b)
        ≥(s_i+X_b r_i(ib))/(1+X_b).

This controls the same forced-Quit endpoint for active and inactive i.
It permits an above-own cross-pair participant reward when the passive
singleton is higher. The compactness/root argument never used these three
collision caps, so its hypotheses are unchanged. This optional disjunct is
proved separately, not assumed in the frozen review.

No self-export, Lean seal, or conclusion for arbitrary Fin4 tables is made.

## Final strongest artifact: exact-byte assembly and delta PASS

I read the complete690-line standalone
[TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM](../exports/TRIPLE_SINGLETON_COLLISION_BOX_UNIFORM_EQUILIBRIUM.md),
SHA256
`fe00a5c0ddb505f462c794823e9a3ba20eba8e2f57c5344852faabcb6b0cb3c7`.
This is a bounded assembly/delta check against the preceding independent
proof and coverage review; no counterpart review was read.

**Final artifact PASS, for both soundness and significant raw-class
coverage.** There is no unresolved strategic input, mathematical objection,
or required repair. This verdict concerns ordinary mathematics, not a Lean
build or implementation.

The assembled statement includes BOTH substantive cap weakenings proved
above. Its seven multiaffine vertex tests use exactly the raw radii from
the compact feasible-odds bound. Zero radii are explicitly handled by
constant-coordinate interpolation, not division. The proof applies the
tests to every produced root, including inactive anchor boundaries.
Its per-player alternative is genuinely a disjunction: different A
players may use different arms, and nonnegative within-A participant
premiums are required only in the second arm. The second-arm inequality
is derived from the corrected ACTUAL passive policy equation, after the
inactive increments are established. No nominal inactive equality or
unstated singleton floor has replaced that argument.

Both strict raw-scope tests are correct. At the original center the seven
vertex values are −8 three times, −304/15 three times, and −152/5.
Changing only r_b(013) to11/10 changes the01 vertex to−72/5 and the
full vertex to−368/15, leaving the other vertices unchanged. This permits
a positive triple premium1/10 and strictly leaves the coefficientwise
subclass. For the per-player test, changing r₂(02),r₂(12) to1 and
r₂(23) to2 makes player2 satisfy the second arm but not the first.
The new pair joins from player2 are1, B₂ remains3, and the radii become
(3,3,8). The triple joins remain1. Its unchanged anchor polynomial is
nonpositive on this smaller box by the original vertex proof. The
standalone correctly does not transfer the full source census to either
altered table.

The root/consumer chain is preserved: the original no-UE source supplies
R₀ and degree1; all nonnegative feasible odds are bounded; the global
degree0 and local degree1 force a nonzero root; singleton supports are
excluded; and actual inactive policy corrections are retained. The same
two positive hazards give absorption under EVERY unilateral behavioral
replacement. The fixed target, terminal Nash inequality, uniform first
absorption bound, initial-zero horizon coefficient and bounds MB/N and
2MB/N are all unchanged and explicitly quantified. Arbitrary signs and
the four freely completed passive A coordinates are not silently removed.

The original center's matrix residual is now correctly written ΓX−1,
with offset−1 in the actual tracked convention. The opposite-sign
comparison has the precise harmful-schedule restriction checked above:
pair23 has two negative joins but is favorable, and each admissible
harmful matching has a positive/positive pair and an opposite-sign pair.
The false blanket cross-pair assertion is absent. The fifteen complete
induced-Nash carriers, actual punishment-tail anchor3 screen, fourteen
child witnesses, full-core distinction and strict-neighborhood argument
remain present with their proper scopes. No unknown-radius local-family
exclusion or all-proper stationary nonexistence has been added.

The packet is self-contained apart from explicitly named tracked
mathematical/source declarations. It has no dependency on conference
notes, feedback, exports, or untracked helpers, and no review/history
narrative. Suggested Lean declarations are expressly a handoff rather
than claims of existing formalization. The frozen base remains a valid
subclass; the final artifact states one coherent stronger raw theorem.

## Bounded structural delta: two good triple rows suffice

I independently checked the final section “Two good triple rows suffice:
a structural producer extension” in
`notes/CODEX_NOETHER__NONLINEAR_PHASE_ESCAPE_AND_BOUNDARY_GLUING.md`,
whole-file SHA256
`44bf7c6452cd0bb653ac5d5828ddec1c57195d7420a1be089634f8bf08693bc2`.
This is a separate changed-scope check, not a change to the preceding
690-line artifact seal. No counterpart review was read.

**Delta PASS.** The subset G and its stated negative-singleton comparison
are sufficient. There is no hidden global bound or strategic premise.
For each j∈A, |G|≥2 makes G−{j} nonempty, and each good row has
L_i≥c_ij X_j≥0. Its feasible-row inequality alone gives X_j≤B_i/c_ij.
Thus these good rows bound all three A odds, including the bad player's
odds. A good row with Γ_ib<0 gives X_b≤M_i/(−Γ_ib). When G=A the
required row follows from R₀; when G is proper it is explicitly a raw
hypothesis. Nothing infers the needed sign from a bad row.

The bad row may make its own L_i negative, but neither feasible-odds
compactness nor the large-shift homotopy uses it. N remains O(‖X‖²),
so the local degree is unchanged. The singleton-support exclusion uses
only c_ij>0 because its triple monomial vanishes. Consequently the same
global/local degree argument still produces a finite nonzero root with
at least two positive coordinates.

The mandatory second cap arm on every bad row is essential to this proof:
its three nonnegative Π coefficients give U_i*≥U_i≥s_i even if W_i<s_i.
The exact corrected passive policy equation then bounds forced Quit by
W_i*. The proof never asserts a singleton floor for bad W_i. Inactive
increments remain nonnegative because e_i≥0 and the deleted-clock
denominator is positive; all active endpoints and b's box cap are
unchanged. Thus the same unrestricted behavioral and fixed-target
uniform-horizon conclusions follow, not just a complementarity root.

The stated complete-table stress checks exactly. Changing only
r₂(01)=3, r₂(02)=r₂(12)=1 and r₂(23)=2 leaves Γ unchanged.
For G={0,1}, both good triple joins are1 and both good Γ_ib equal−1.
The bad triple join is c₂A=2−3=−1; its Π values are(0,0,1), and
its passive cap2≤4 holds. Its two pair joins become1 while all other
pair joins stay positive. Good-row B₀=B₁=4 yield radii(4,4,8), so
the seven strict anchor values are unchanged. This strictly enlarges
the previous raw predicate; no source-census claim is transferred to
this modified table. The original independently separated center
remains admitted and therefore retains the existing significance.

No objection or repair remains for this bounded extension. Any stronger
standalone incorporating it must retain the good-row minimum, the extra
negative Γ condition when G≠A, and the mandatory second cap arm for
bad rows. Its final changed bytes remain a separate assembly check.

## Final716-line strongest artifact: PASS

The final standalone at the same linked path above has716 lines and SHA256
`8b2ed12c6be0daacbeeabc9d8c892664e080eda356cae2687f8d7fd25c5cc0c5`.
I compared its complete changed surface against the approved690-line
version saved in commit`c37d4941`, and checked the final removal of an
undefined internal label. No counterpart review was read.

**Final exact-byte soundness and significance PASS; no unresolved
objection or repair.** The changes faithfully incorporate the preceding
two-good-row theorem: G-dependent nonempty minima, the negative good-row
Γ condition when G is proper, good-row-only coercive bounds, and mandatory
second passive-cap arm for bad rows appear in the statement, proof,
conclusion and handoff. The four-coordinate stress is exactly the one
independently checked above. No bad-row singleton floor is used.

The whole-class normalization/core inclusion paragraph is now expressly
restricted to G=A; it makes no false joining-attractive claim for a
negative third triple join. The original complete coverage fixture and
all15 concrete-source calculations are unchanged. The seven-vertex
caps, signed inactive corrections, support≥2, unrestricted replies,
fixed target and initial-zero horizon bounds remain intact. The artifact
has no mathematical dependency on a conference note or review and makes
no Lean or all-table strategy-completeness claim. This final seal replaces
the690-line assembly seal only for the stronger assembled artifact;
it does not alter either earlier scoped mathematical verdict.
