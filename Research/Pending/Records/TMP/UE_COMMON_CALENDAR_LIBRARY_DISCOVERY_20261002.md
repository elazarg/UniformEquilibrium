Historical design record. Frozen source/review artifact; see Research/Pending/README.md.

# Common-calendar prerequisite library discovery

Static discovery verdict: substantial canonical infrastructure exists, but no
ready-made finite log-sum-exp package, compact Danskin derivative theorem, or
all-minimizer box-normal tuple producer was found in the searched checkout.
These are known-source formalization obligations, not new mathematical
assumptions. The common-calendar producer is NOT complete.

No Lean, Lake, compiler, Git, shared edit, worktree, snapshot, duplicate cache,
or child agent was used. This report is the only write, under `/tmp`. Every
declaration observation is static, not checked here. No new mathematical
research was performed. Formulas use terminal-readable Unicode.

## Scope

Read the four source exports listed in the hash inventory, including all 709
lines of `SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE.md`; retained the prior
complete reading of the three screened-source packets and dependency audit.
Searched MathUE, UniformEquilibrium, GameTheory (including its generic
`GameTheory/GameTheory/Math` tree), pinned Mathlib and Maths, relevant Research,
and `math/fable/lean`. Read exact declarations/imports of the proposed owners.
Search absence is scoped discovery evidence, not a theorem of global absence.

Pinned versions, from `lake-manifest.json`, without Git inspection:

- Mathlib: `5ed2965256430c3649e86755f9576b54eca72435`, input v4.34.0.
- Maths: `26622cefd5329d5b5545ad09e3678151bd61ba52`, input v4.34.0.
- GameTheory is the path dependency `GameTheory`.

The G1–G4/A1–A10 identifiers below are the dependency audit's specifications,
not existing declaration names. Proposed interfaces below are specifications,
not tested Lean syntax or proof seals.

## 1. G1: finite log-sum-exp and entropy

No existing `softmax`, `logSumExp`, `log_sum_exp`, or equivalent common-calendar
package was located in the searched generic/production trees. Do not introduce
a new abstract weight certificate in place of the literal exponential weights.

Useful exact library owners:

- `Real.hasDerivAt_exp`, `HasDerivAt.exp`, `HasFDerivAt.exp`, and
  `Real.contDiff_exp` in Mathlib `Analysis/SpecialFunctions/ExpDeriv.lean`.
- `Real.hasDerivAt_log`, `HasDerivAt.log`, `HasFDerivAt.log` in Mathlib
  `Analysis/SpecialFunctions/Log/Deriv.lean`; the composition rule requires
  nonzero input. Here positivity of the finite exponential partition discharges it.
- `HasDerivAt.sum` in Mathlib `Analysis/Calculus/Deriv/Add.lean`.
- `Real.negMulLog_nonneg`, `Real.concaveOn_negMulLog`, and
  `Real.hasDerivAt_negMulLog` in Mathlib
  `Analysis/SpecialFunctions/Log/NegMulLog.lean`. This imports Log.Deriv,
  Pow.Asymptotics and Convex.Deriv; it is a scalar entropy primitive, not a
  finite Shannon-entropy theorem.
- `ConcaveOn.le_map_sum` in Mathlib `Analysis/Convex/Jensen.lean`, importing
  Convex.Combination and Convex.Function. Nonnegative weights summing to one
  are explicit; use uniform weights to obtain entropy ≤ log cardinality.

Minimal generic interface: nonempty finite J, τ > 0, g : J → ℝ, literal
Z = ∑[a ∈ J] exp(g(a)/τ), λ(a) = exp(g(a)/τ)/Z, F = τ log Z.
Conclude Z > 0, λ > 0, ∑ λ = 1, max g ≤ F ≤ max g + τ log |J|,
and F = ∑ λg + τ∑ negMulLog(λ). For differentiable literal gain functions,
prove derivative F = ∑ λ Dg, and the second derivative identity
F″ = ∑ λg″ + (∑ λ(g′)² − (∑ λg′)²)/τ. Zero tester is an actual application
label, not necessary for the generic theorem; it gives nonnegative max gain.

The reward-linear corollary must use actual rows g(a,r) = ⟨r,v(a)⟩:
F − τ log |J| ≤ ⟨r,∑ λv⟩ ≤ F. This is reward work, NOT an l1 norm equality,
NOT normality of the selected source, and NOT a 60-coordinate optimization.

## 2. G2: compact envelope and all-minimizer selection

Already available:

- `IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`, and
  `IsCompact.continuous_sInf` in Mathlib `Topology/Order/Compact.lean`.
  The latter says that jointly continuous F on parameter × point has continuous
  parameterized sInf over a fixed compact point set. It does NOT give a derivative.
  The module imports Topology.Algebra.Support, Order.IntermediateValue,
  and Order.LocalExtr. Use a compact subtype to accommodate continuous-on domains.
- `Math.Topology.isCompact_convexHull_of_finiteDimensional` in
  `MathUE/Topology/CompactConvexHull.lean`. It applies to an arbitrary compact
  set in finite dimension, not just a finite set. Its proof already uses
  Carathéodory; do not reprove compactness of the gradient hull.
- `geometric_hahn_banach_compact_closed` in Mathlib
  `Analysis/LocallyConvex/Separation.lean`: a compact convex set disjoint from
  a closed convex set admits a continuous linear functional with a strict gap.
- `mem_convexHull_iff_exists_fintype` in Mathlib
  `Analysis/Convex/Combination.lean`: membership supplies a finite index type,
  nonnegative weights summing to one, points in the ORIGINAL set, and their
  weighted sum. This is exactly the finite tuple extraction after intersection.
- `IsLocalMaxOn.hasFDerivWithinAt_nonpos` in Mathlib
  `Analysis/Calculus/LocalExtr/Basic.lean` is a smooth local-extremum tool.
  It is NOT applicable directly to a nonsmooth minimum envelope before Danskin.

Do not misuse the related existing owners:

- `Math.LinearAlgebra.exists_euclideanUnit_strictConvexSeparator_fintype`
  (`MathUE/LinearAlgebra/FiniteConvexStrictSeparation.lean`, importing
  OccupationFlowAlternative) separates a FINITE column hull from zero.
  Old-minimizer gradients may form an infinite compact set; no finite list has
  been supplied before the theorem constructs it. Use compact-hull separation
  above, not an assumed finite discretization of all minima.
- `MathUE/LinearAlgebra/ConeSeparation.lean` handles finite-generated cones;
  its closedness/separation infrastructure does not itself prove the envelope
  normal intersection.
- `Math.BoxComplementarityProblem.IsSolution` in
  `MathUE/Topology/BoxComplementarityProblem.lean` describes coordinate normal
  signs for a GIVEN continuous field. It does not construct the required
  convex combination of gradients. LowerBoxBoundaryMinimum concerns a smooth
  potential on a different boundary, not this minimum envelope.

Missing minimal generic Danskin interface:

Let E be finite-dimensional real parameter space, X a nonempty compact metric
space, O an open parameter neighborhood, F jointly continuous on O × X, and
A(r,p) the actual parameter derivative with HasFDerivAt (F(·,p)) A(r,p) r
for every (r,p) ∈ O × X. Require joint continuity of A there. Define
f(r) = min[p ∈ X] F(r,p), and M(r) = {p ∈ X | F(r,p) = f(r)}.
For each r ∈ O and v, conclude the right-direction difference quotient tends to
min[p ∈ M(r)] A(r,p)(v), together with attainment of that derivative minimum.
The set M(r) is the set of ALL old minimizers. Neither uniqueness nor a
favorable selected minimizer's gradient is a hypothesis.

Finite-calendar tuple extension: finitely many nonempty compact X_N and smooth
F_N on the SAME parameter domain. Product tuples select one p_N ∈ M_N(r)
at EVERY index. The averaged value is the minimum over the product of the
averaged functions. At a maximum r of this average on a closed box K, output
finite tuples t_j, weights w_j ≥ 0, ∑ w_j = 1, each component a genuine old
minimum, and z = ∑[j] w_j average[N] A_N(r,t_j(N)) such that
∀ y ∈ K, ⟨z,y−r⟩ ≤ 0. Use coordinates or the dual consistently.
The source requires no quantitative bound on the number of tuples.

Missing box glue: closed convex outward-normal cone, coordinate sign formula,
and separation-to-feasible-direction contradiction with the Danskin formula.
On a nondegenerate interval, z_i ≤ 0 at the lower endpoint, z_i = 0 in the
interior, and z_i ≥ 0 at the upper endpoint. After A5 rules out upper endpoints,
all coordinates of this AVERAGED normal are ≤ 0. No such assertion follows for
every tuple or the eventually selected actual profile. Do not put any of these
desired normal statements into a game-facing input certificate.

These additions formalize the exported proof; compactness, continuous derivative
and global box-maximization are necessary stated hypotheses, not hidden glue.

## 3. G3: same-weight chord curvature

Canonical scalar analysis: `taylor_mean_remainder_lagrange_iteratedDeriv` in
Mathlib `Analysis/Calculus/Taylor.lean` gives the order-one Taylor remainder
from ContDiffOn of order two on the unordered closed interval. It handles the
endpoint by within-Taylor coefficients; isolate an elementary real corollary
F(t) ≤ F(0) + t F′(0) + H t²/2 for 0 ≤ t ≤ 1 and F″ ≤ H.
Do not reprove Taylor's theorem. An upper second-derivative bound suffices;
an absolute bound is harmless but stronger than needed.

`Math.norm_increment_sub_increment_le_of_hasFDerivWithinAt` in
`MathUE/Analysis/DerivativeDifferenceMeanValue.lean` (importing Calculus.MeanValue)
is a useful first-derivative error tool, not the second-order descent lemma.

Existing finite-product Fubini, bind, and total-variation owners in
`MathUE/PMFProduct` can support exact product expansions. In particular the
finite raw payoff polynomial already has degree ≤ number of players. Neither
that degree bound alone nor existing small-hazard expectation bounds prove
the required sharp uniform derivative constants for arbitrary marginal chords.
No ready-made chord derivative bounds 16/96 were found.

Minimal game-independent addition: for a bounded payoff on the product of four
finite action sets and independent probability marginals μ_i(t) = (1−t)p_i+tq_i,
prove its first and second derivative formulas by expanding the finite product.
Apply to response payoff minus source payoff (the response owner's marginal
is fixed in the response term). With unit reward bound obtain |g′| ≤ 16 and
|g″| ≤ 96 uniformly in source, competitor, tester and t ∈ [0,1]. Combining
G1 gives H = 96 + 256/τ for the same literal softmax.

Minimal descent interface: H > 0, h twice continuously differentiable along
[0,1], h″ ≤ H, −h′(0) ≤ H, h(0) = a, and b ≤ h(t) for EVERY t ∈ [0,1].
Conclude h′(0) ≥ −√(2H(a−b)). In the negative-derivative case the legal
step is −h′(0)/H; the source's |h′| ≤ 16 and H ≥ 96 discharge its upper bound.
This cannot be omitted from a curvature-only argument.

Actual output should fix p ∈ argmin_XN F and its literal λ(p) FIRST, then state
∀ q ∈ X_(N+1), ∑[a] λ(p,a) Dg_a(p)[q−p] ≥ −√(2H(f_N−f_(N+1))).
Do not choose weights after q. The shifted version uses the SAME recomputed
λ-hat against EVERY q ∈ X_(N+3), not merely against the solo-Quit competitors.

## 4. G4: weighted discarding and actual entry selection

Existing owners:

- `GameTheory.Math.Probability.FinDist.probOf_le_expect_div` and
  `.markov_inequality` in `GameTheory/GameTheory/Math/Probability/Bounds.lean`,
  importing only generic FinDist. Nonnegativity is needed only on support.
  This is a permitted generic dependency for MathUE.
- `Math.ProbabilityMassFunction.exists_mem_support_le_expect` in
  `MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean`, importing the
  generic ProbabilityMassFunction umbrella. It selects a real support atom of
  a bounded observable. Its sibling `exists_mem_support_expect_le` is the
  opposite inequality; avoid swapping them.
- Finset strict sum comparisons / the additive generated
  `Finset.exists_le_of_sum_le` can give a direct finite-weight proof without
  converting representations. Mathlib finite uniform `expect` lemmas alone
  are not arbitrary tuple-weight selection.

Missing small glue interface: finite weights w ≥ 0 summing to one, pressure P_i
with |P_i| ≤ M, bad set B of exact mass d < 1, and weighted pressure sum ≤ A.
Output an i outside B with w_i > 0 and
P_i ≤ (A + Md)/(1−d). Keep d and denominator positivity explicit. Add a
nonnegative residual observable R with mean ≤ b to bound threshold-discard
mass by b/t. The calendar endpoints contribute their actual mass separately.
Use actual selected tuple/calendar entries, never play a mixture of tuples.
No new probability theorem is needed beyond this finite packaging.

## 5. Existing actual owners substantially reducing A1–A10

### A1/A2: polynomial laws and full tester completeness

`UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean` imports
FiniteCalendarPayoffClosure, generic Simplex, ProfileNeverMass and
StageCoalitionStoppingLaw. It owns `quittingFiniteCalendarDecodedLaws`, exact
finite/Never coordinates, `quittingTerminalOutcomeMass_finiteCalendar_eq`,
`quittingTerminalOutcomeMass_finiteCalendar_none_eq`, and
`quittingFiniteCalendarRawPayoff_eq_terminalPayoff`.
`FiniteCalendarRawPolynomial.lean` imports the raw owner and parameters plus
MvPolynomial.Degrees. Its `eval_quittingFiniteCalendarRawPayoffPolynomial`
identifies the literal polynomial with the same payoff; degree bounds also exist.
Reuse these, with updates/reindexing for tester responses.

Generic finite simplices already have convexity/compactness and coordinate/PMF
bridges in `GameTheory/GameTheory/Math/Probability/Simplex.lean`, including
`convex_simplexWeights`, `isCompact_simplexWeights`, `mem_simplexWeights`.

Important additional production discovery:
`UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean` imports
FiniteDeadlineReplyCap, CompactStoppingLawCapUpperBound, TerminalExploitability,
and BoundedSupportAverage. It proves
`quittingContinuationBestResponseValue_finiteDeadlineTimingProfile_eq_max`:
the UNRESTRICTED behavioral cap equals max(finite menu cap, exact late row),
including deadline zero. The exact late-row owner is
`quittingFiniteDeadlineTimingProfile_pureTime_eq_never_add_of_le`:
for every t ≥ N its value is Never payoff plus opponent-Never product times
the owner's singleton reward. Thus later finite times coincide with each
other, but need NOT coincide with Never.

A2 needs only common-pool embeddings and a max-gain adapter from this owner:
X_N has finite dates 0..N−1 and Never; J has zero plus all owners times dates
0..L and Never, with at least one date ≥ N. Keep this SAME J when enlarging
the competitor calendar. For N ≤ 2k−2, X_(N+3) still has last date ≤ 2k and
the common pool through L = 2k+1 still contains a late representative. Equality
of duplicate labels must hold as functions on this whole competitor domain,
not just at the selected profile. Never remains distinct.

A1 still needs the literal reward derivative row:
v_a(S,i) = 0 unless i is a's owner; in that row it is response terminal mass
minus source terminal mass. Own-singleton projection gives the four pressure
coordinates. Neither smooth payoff existence nor the polynomial degree bound
already supplies this joined declaration.

### A3: precise finite-clock promotion boundary

The coherent existing Research slice is:

`FiniteClockTerminalSemantics` → `EscapeAwareQuantileClockTransport` →
`EscapeAwareQuantileClockHierarchy`.

The first defines `quittingFiniteClockSemanticReachable` using actual independent
PMFs on Option ℕ with finite support bound; its second pair coordinate remains
the literal unrestricted cap. It proves compactness via its finite-clock fold.
The transport module imports the first, MathUE.Probability.QuantileClockCollision
and ProbabilityMassFunction.Coupling. Its
`hasEscapeAwareQuantileClockCompression_of_normalized` constructs compression
internally from |reward| ≤ 1; no favorable compression premise is needed in
the normalized public consumer. The hierarchy imports this transport plus
MathUE.Topology.NestedOuterApproximation.

The exact final owners are
`quantileClockSupport_fin4` (8j+1),
`escapeAwareQuantileClock_fin4_normalized_quantitative_bracket` (gap ≤ 24/j),
and `exists_finiteClockSemanticPair_exploitability_eq_upper` (attained upper
value in the actual finite-clock reachable set). Combined they yield an
actual independent finite-clock profile with E ≤ η+24/j, not just payoff
approximation. Monotonic support embedding already exists as
`isFiniteClockStoppingLaw_mono` / `quittingFiniteClockSemanticReachable_mono`.

Promote the needed coherent slice into production (or extract the above
definitions and their full proof dependency closure), without copying a
Research interface and then importing Research. Existing MathUE quantile and
collision kernels need no second owner. Full outer-hierarchy results not used
by the source can remain Research after their shared foundations are promoted.
Promotion requires root-owned build/axiom/import checks; none was done here.

Remaining A3 glue: j = floor((k−1)/8) is eventually positive, 8j+1 ≤ k,
24/j → 0; convert the finite-clock law to the actual coordinate simplex.
Then FOR EVERY old softmax minimizer on EVERY N ∈ [k,2k], at the SAME maximizing
reward table, E ≤ η+24/j+τ log |J|. The quantile theorem is already reward
uniform under the common unit bound; do not fix one table before claiming
uniformity over the selected table sequence.

### A4/A5: same-table minima, moat and normal signs

The compact minimum and compact box maximum library tools handle existence
and continuity. Telescoping Δ_N = f_N−f_(N+1) must keep one reward table fixed.
There is no need for a new minimax interchange theorem. Calendar embeddings,
nonnegativity of Δ_N, telescoping, and error limits are still missing glue.

`minimumTerminalSemantic_exploitabilitySingletonMargin` in
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPlateauDynamicCostate.lean`
says at every positive global MAX carrier minimum: η ≤ B_i−s_i for every i.
It imports the plateau defect/costate infrastructure and PunishmentFloorViolation.
It is not a DebtSum theorem. Near-minimum uniformity over varying tables still
requires the closed-graph/same-profile reward-transport compactness join.
Do not assert it from separate fixed-table compactness alone.

`Math.Topology.exists_eventually_uniform_pos_on_closed_of_compactSpace`
in `MathUE/Topology/CompactRobustMoat.lean` is useful once there is a FIXED closed
compact bad/near-minimum fiber with joint continuity. It does not manufacture
the varying carrier graph. It also permits an empty closed subset, so preserve
nonemptiness separately when selecting actual minima.

### A6: silent shift and softmax transport

Already in production `UniformEquilibrium/Diagnostics/Quitting/AllContinuePrefixSemantics.lean`:

- `quittingTerminalSemanticPair_allContinuePrefix_eq` preserves the same full
  pair provided every singleton ≤ its cap.
- `quittingTerminalOutcomeMass_allContinuePrefix_eq` preserves the entire
  terminal law without that cap premise.
- `quittingPureTimeDeviationPayoff_allContinuePrefix_shift` shifts finite
  tester labels by one and fixes Never.
- `quittingPureTimeDeviationPayoff_allContinuePrefix_zero` is exactly the
  owner's singleton reward.

The leaner semantic-pair kernel is
`quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap` in
`UniformEquilibrium/Quitting/Root/TerminalSemanticPair.lean`.
Do not copy the parallel fable prefix argument. A finite-calendar decoded-law
adapter identifying literal finite-date shifting with prefix semantics remains.
A5 supplies its cap premise; a public producer must derive it, not assume it.

Still missing: SAME common pool normalizer ratio Z-hat/Z = 1−ell+a,
ell ≤ 1/(L−N+1), a ≤ 4 exp(−σ/τ), and bounded-observable transport.
Recompute λ-hat from shifted gains. Newly introduced date-zero labels are
small-weight labels, not deleted labels. Old λ cannot silently be reused.

### A7–A10: quantitative joins remain

A7 joins G3 with Δ_N+Δ_(N+1)+Δ_(N+2)+τa and preserves EVERY competitor in
X_(N+3). A8 must derive the exact solo-Quit0 identity for the SAME λ-hat, then
θ_i(B_i−s_i) ≥ E−ε−R−4a and every θ_i ≥ Ω_b/4 eventually. Owner masses are
outputs, not favorable witness fields.

A9 averages residuals, discards last two calendars and high residuals, and
uses G4 to select one actual tuple entry carrying all simultaneous conclusions.
Only the SUMMED four-coordinate pressure remains controlled after selection.

A10 can directly reuse
`abs_quittingTerminalExploitability_sub_le_of_reward_close` and
`abs_quittingTerminalExploitabilityInf_sub_le_of_reward_close` in
`UniformEquilibrium/Quitting/Terminal/TerminalExploitabilityRewardRobustness.lean`
for the 2δ full-regret/infimum errors. This module imports TailStepSelector,
UniformPayoffExistenceClosure and TerminalDebtPrefixDescent. The same-law
inactivity error 4δ and weighted chord derivative error 16δ require new finite
sum/chord adapters. Keep the SAME laws and SAME weights when moving to the
fixed limiting table. Laws/owner masses/pressure do not change with rewards.

## 6. Single-pivot packet: a smaller source-faithful specialization

This packet does not assume the generic polynomial fiber gap or the new
MAX total-singleton collar. Its collar comes from the exact secant inequality.
For fixed b, only own singleton of player 0 changes x, and the other three
own singletons are zero. Source hypotheses include rational b,t,α, unit bounds,
and e(t)>2α. These are not produced by the calendar lemmas themselves.

Required missing actual secant adapter, for every profile and y<x:
E_y(p)−(x−y)z(p) ≤ E_x(p) ≤ E_y(p)+(x−y)(1−z(p)). It comes from the SAME
actual law coefficients in A1 and complete caps, and yields 1-Lipschitz e.
The existing general 2-Lipschitz reward theorem is weaker and does not establish
this secant collar. At selected ξ≥t the universal bound
E_ξ(p)+(ξ−t)z(p) ≥ e(t)>2α yields z≥3α/4 for EVERY required near minimum.
This is not the DebtSum cap≈singleton slab collar.

Use compact level-set maximum to select largest α-level a to the right of t,
then maximize the average smoothed objective plus cx on [a,1], c=α/4.
The exported endpoint/max-moat argument gives x_k<1 eventually. At x_k=a,
the RIGHT direction is still feasible; do not assume an interior critical point.

The scalar Danskin corollary chooses, at EACH N, an old minimizer minimizing
∂xF_N. One tuple then has average pivot pressure ≤ −c. No convex mixture of
tuples is needed in this scalar specialization. This simplification is already
explicit in the export, not a new discovery/generalization. All subsequent
uniform collar/moat/near-minimum estimates must have held for every minimum
before this tuple is chosen.

Reuse A1–A4 and A6–A10 with this scalar selection. Discarding gives an actual
entry with pivot pressure ≤ −c+o(1), and the same fixed ξ receives the same-law
transport. The remaining finite pivot reply and strategic-delay claims in the
packet are separate consumers: do not claim them from the common-calendar
source. The production exact after-support-vs-Never formula above is a useful
owner for the finite-Never conversion, not permission to identify those actions.

## 7. Minimal implementation sequence and nonclaims

1. Promote finite-clock semantics/transport/needed quantitative consequence.
2. Add generic finite log-sum-exp identities and compact Danskin derivative.
3. Add box-normal tuple extraction using existing compact hull/separation;
   scalar tilted corollary may be implemented independently as the smaller case.
4. Add finite-product chord derivatives, Taylor descent and finite discarding glue.
5. Adapt existing actual polynomial/full-cap/prefix owners to the common pool.
6. Prove all-minimizer uniform estimates, same-table telescoping, shift-weight
   comparison, same-weight all-competitor residual, owner masses, selection,
   and fixed-table transport in that order.

The source construction may be conditional on the stated positive fiber/tilted
source hypotheses. It must NOT be conditional on a supplied favorable inner
minimizer, profile normal, positive owner tester masses, same-weight competitor
inequalities, or the selected collar that it is supposed to construct.

Packet 1 additionally needs its independent MAX singleton-mass collar/closed
carrier graph C1–C5 before selection. Packet 2 retains its membership-stretch
ancestry and pure-coalition gap instead. The scalar packet has its own secant
collar. None of these should be conflated with CompleteCapSingletonSlabCollar
or CompleteCapSingletonLimitCollar, whose objective is DebtSum.

The final fixed game/parameter/collar must precede every requested accuracy
and depth. One actual independent silent profile and ONE tester law must
simultaneously satisfy the claimed errors, pressure and every-competitor bound.
No uniform runtime, denominator bound, equilibrium, new descent theorem, or
frontier contradiction has been discovered here.

The fable search supplied no needed common-calendar tool. The inspected
FableDebtMinimaSeparation has a different certified-floor/sum-debt purpose;
its carrier passage is explicitly not formalized. Fable silent-prefix material
has production counterparts listed above. No fable file is cited as production
authority. No genuine beyond-export mathematical generalization was developed
or relied on, so there is no new research claim to hand off to math agents.

## Hash inventory

Hashes identify the bytes inspected, not Lean/build seals. Paths below are
relative to `/home/elazarg/UniformEquilibrium` unless absolute.

```text
d91cf597df1f45d4287b53244d4f91463ed7f9313d75748a3f0fbcb87dbdfe0c  math/exports/SINGLE_PIVOT_SECANT_COLLAR_AND_STRICT_PRESSURE.md
c3004d986acc316a20b7c29a7cdc9c764235f843e4b006a7fc99e0cbe0e0f5d7  math/exports/GENERIC_SCREENED_ROOT_EXCLUSION_AND_SINGLETON_MASS_COLLAR.md
24537ca80ba0c3ac610c73259ca44977acda1d985527fedba524de98589ac2b6  math/exports/MEMBERSHIP_STRETCH_AND_SINGLETON_FIBER_SOURCE_REDUCTION.md
83ee0a42c89aa0f37a29b74bee059fc6dca8cbda309f9e6806f84bf410bb8297  math/exports/THREE_SURE_MINIMA_REQUIRE_OPPOSED_MEMBERSHIP_REVERSALS.md
0f4412a92546f7036c1d850e96141275526cf18e9aa000bc48c1c079d8509a59  /tmp/three-source-packets-dependency-audit.xEpZYgxQ/DEPENDENCY_AND_THEOREM_SPECS.txt
9ad0bd4a3c7810cec92850b57325740f849f5df698ca975dc148a60e4b41a086  lake-manifest.json
c25921f8cb5d16c31baa21933bf3ddd9d6f02a22b1b81cd189933ee4291bad2b  MathUE/Topology/CompactConvexHull.lean
21fe6de76c6092485e5c7cf24651786eaf4e05b4e31e3b523f2eeee6604ce4cc  MathUE/LinearAlgebra/FiniteConvexStrictSeparation.lean
5c33ee1001ed389cf8577ce6d24bdc714fc3fc26eb8e320dcd0872c68e2e2082  MathUE/Topology/CompactRobustMoat.lean
6424f152010d6299e808fae428244435c5a6720263df6b338e89b9d8d70b9c2c  MathUE/ProbabilityMassFunction/BoundedSupportAverage.lean
c91f72c4dd4e886159dea3e2f14a1b258294180d8bc482d3d9ae94e158016fb3  GameTheory/GameTheory/Math/Probability/Bounds.lean
31d145e5c97d8889e95426df292ad7c29400e6ecabfd601e8b84c1ea16c4897f  UniformEquilibrium/Quitting/Terminal/FiniteDeadlineFullReplyCap.lean
ca59914671dade34de350d99fa077d28dbbdf9bbe05c4698eee74494bb3be029  UniformEquilibrium/Diagnostics/Quitting/AllContinuePrefixSemantics.lean
0bf0ba12e59e857d11d19393d777b40e64c28894a6bf33b3a780c03bd465b318  UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPolynomial.lean
f2a33a6f50ee0532df59c4d64a019f5b942966affd786441408f98c6d64d2202  UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPayoff.lean
50dece401bcdc2d7676e46e07778dc9b2e1a51008de30bf87722845d0f1176bc  Research/Quitting/FiniteClockTerminalSemantics.lean
b7c7d43cff024ddaaecb144ea849db993c4665121d9ec91b322c8a8c0ae563bd  Research/Quitting/EscapeAwareQuantileClockTransport.lean
3554a83750b5deddfcd09b4ccaae1ad45142992520b50615dd7b9055d61087ab  Research/Quitting/EscapeAwareQuantileClockHierarchy.lean
7c02670f2e88f16acd11d69ddd6afb8d8118adca50279e1abb2a3c7761feb044  .lake/packages/mathlib/Mathlib/Topology/Order/Compact.lean
649cfe33fdb3999dfe168ee52cdfba11c45856e3fc34f7be4f971c80c772166e  .lake/packages/mathlib/Mathlib/Analysis/LocallyConvex/Separation.lean
fb6529ffb0c5734dc0412ae2f6b80c48c921e5aa863355ac56f1e1db37f9b408  .lake/packages/mathlib/Mathlib/Analysis/Convex/Combination.lean
e249365f3eff509bfd9774e8e5f380c7e0290d76847871daee3616fb15b6b643  .lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean
fba037b49e06e1fe416f04f9682bfe924601cfaf0aa137ec54331a288c995160  .lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean
```
