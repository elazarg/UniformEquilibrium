# Reflection potential audit

Identity: CODEX_RADON_REFLECTION.

Current status: the reviewed packet's quadratic, multi-affine, radial,
third-derivative, monotone-transform, and rational-rejection arguments are
valid under its standing assumptions. No Lean verification or export is
claimed. The semantic corollary should explicitly retain nonnegative own
singletons; punishment normality does not imply that hypothesis.
The [independent feedback](../feedback/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_RADON_REFLECTION.md)
contains the claim-by-claim verdict.

## Self-contained question

For n≥2, let a finite quitting table give r(S)∈[−1,1]ⁿ for every nonempty
coalition S, and write s_i=r_i({i})≥0. All live and Never rewards are zero.
A product root q∈[0,1]ⁿ draws each player's Quit independently, with coalition
probabilities π_q(S), absorption A(q)=1−π_q(∅), and successor

    F(v,q)=π_q(∅)v+∑_{S≠∅}π_q(S)r(S).

At fixed continuation annotation v, exact root Nash means both pure endpoint
payoffs of player i are at most F_i(v,q), for every i. The source v may be
any point in K=[−3,3]ⁿ and need not be a behavioral payoff. Does the
universal inequality P(v)−P(F(v,q))≥A(q) exclude every quadratic and every
multi-affine polynomial, and force the packet's radial/derivative behavior
at each global minimum of a regular P? Does it yield rational rejection in
the actual robust relation at every supplied positive rational tolerance?

This is a supplied-function impossibility question with arbitrary finite
expectations. Players control only their own root distributions in these
local inequalities. No correlated signal, observation extension, stopping
rule, or full-strategy deviation estimate is introduced. The sole semantic
use is to restrict the polynomial already produced by the existing
four-player characterization.

## Source route and declarations inspected

Read root/math `AGENTS.md`, `SOURCES.md`, `GOAL.md`, both research methods,
`exports/README.md`, and the conference filename inventory. Relative method
links in the math instructions resolved one directory too high; the actual
files read were `docs/methods/MATH_RESEARCH_METHOD.md` and
`docs/methods/PARALLEL_RESEARCH_METHOD.md` within the repository.

The bounded route was the full robust relation and polynomial characterization
in `docs/TOOLKIT.md`. Declarations were read in their source files with imports:

- `ChargedRelation.IsPotential` in `MathUE/ChargedPathBudget.lean` fixes
  orientation as P(target)+charge≤P(source).
- `IsQuittingFloorFreeRobustEdge`, `quittingRobustChargedEdgeResidual`,
  `quittingRobustChargedEdgeRegret`, and
  `quittingFloorFreeRobustChargedRelation` in
  `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean` allow
  every boxed source/root/target satisfying coordinate residual and regret
  bounds ≤τA. Regret is computed at the source. There is no floor or selector.
- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`,
  `quittingRootContinuePayoff`, and
  `quittingRootSuccessorPayoff_eq_endpointMix` in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`, and
  `quittingRootCoordinateNashDefect`,
  `quittingRootCoordinateNashDefect_nonneg`, and
  `isεQuittingRootNash_iff_coordinateNashDefect_le` in
  `UniformEquilibrium/Quitting/Root/NashDefect.lean` verify the endpoint
  convention and the continuous max-of-endpoints defect.
- `exists_isZeroQuittingRootNash` in
  `UniformEquilibrium/Quitting/Root/NashExistence.lean` supplies a root for
  every real tail annotation; its import is the existing finite endpoint
  Nash bridge through `Boundary/Repair/ComplementarityClosed.lean`.
- `continuous_quittingRootAbsorptionMass_simplex` and
  `continuous_quittingRootCoordinateNashDefect_simplex` in
  `UniformEquilibrium/Quitting/Root/NashDefectContinuity.lean` support the
  rational approximation argument. The nearby
  `exists_rational_quittingRootTotalNashDefect_lt` in
  `UniformEquilibrium/Quitting/Root/RationalApproximateQuittingRoot.lean`
  already gives approximate rational roots at fixed annotations, but does
  not include this packet's strict rejecting edge or relative charge bound.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`
  has Fin 4, all-terminal reward bound, all-player punishment normality,
  and one positive singleton as hypotheses. Its fixed box radius is
  rewardBound+2, and its existential polynomial is constructed, not assumed.
- `quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential`
  in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateConsumer.lean`
  is the reverse semantic consumer, with unchanged game hypotheses.
- `IsQuittingNormalPlayer` and
  `isQuittingNormalPlayer_of_singleton_nonneg` in
  `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`, and
  `quittingBestReplyValue`, `quittingPunishmentValue`, and
  `quittingPunishmentValue_le_max_solo` in
  `UniformEquilibrium/Quitting/Stationary/MinMax.lean` show why normality
  cannot be substituted for the sign assumption. The hostile two-coordinate
  example there explicitly has negative punishment values.

A narrow search of the selected Projective/Root and MathUE interval subtrees
for reflection, multi-affinity, quadratic potentials, radial reversal, and
third derivatives found no implementing counterpart. This is an overlap
check restricted to that route. `Literature/README.md` was read; no paper
theorem or unbuilt Literature claim is needed as a proof input.

The entire source packet, companion, and credited
[shape-exclusion export](../formalized/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md)
were inspected. The old probe and global-minimum facts are credited prior
mathematics. The adaptive reflection and corner comparison supply the new
function-class exclusions; no assertion of publication novelty is made.

## Independent calculations and attempted falsifiers

The reflection bound fails if its upper rectangle is replaced by K's top:
a_j=1/2 and x_j=3 give 2x_j−a_j=11/2. The packet's choice b_j=max(a_j,1)
instead yields the needed bound. For s_j=0, a_j=3, and x_j=0, the reflected
coordinate equals −3 exactly, so a strict-interior assumption would lose a
valid boundary case.

Removing nonnegative own singletons breaks two specific steps: s=−1,
a=3, x=−1 gives reflection −5; and θ=2/3 with corner costs
c_i=c_j=1, c_{ij}=1/10 gives nonowner derivative 2/45>0. These are
counterexamples to unstated extensions of the proof steps, not to A or B.
The table r(S)=(1,−1,0,0) for every nonempty S has punishment vector equal
to its singleton vector: an immediate Quit attains each constant coordinate,
and an opponent's immediate Quit forces it. Thus all players are normal and
one singleton is positive, while another is negative. The narrower
nonnegative-singleton subclass must be explicit in the corollary.

Direct integration by parts on [0,1] and [1,2] verifies the midpoint
identity. Its constant is sharp for the one-dimensional constraints:
f(t)=δt(t−2)²/2 has f≥f(0)=0
on [0,2], f′(1)=−δ/2, and f‴=3δ. This does not assert that this cubic is
a full quitting potential.

Using the exact two-player table r¹=(0,−1), r²=(−1,0), r^{1,2}=(1,1),
with owner 1 quitting with h=1/4, the collision-repaired source (0,2/3)
has successor (0,1/4) and zero defects. The upper-frozen source (0,3)
has successor (0,2) and nonowner Continue-minus-Quit 7/4. Both are boxed
exact roots. These cases were independently evaluated with rational
arithmetic after inspecting the companion's payoff evaluator.

The entire companion passed `python -B gpt/VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py`:
160 reflection identities, 201 box cases, 36 corner derivatives, 120 exact
Nash probes, 11 kernel monomials, and the four face identities with Hessian
spectrum 96,32,−64,−64 and corner values 1408 and −1136. These checks are
finite evidence; the proof audit supplies the universal conclusions.

## Normalization and remaining scope

Common scaling by λ>0 scales every finite-horizon payoff, terminal payoff,
unilateral gain, and punishment value, because it leaves Never=0 and scales
all terminal rewards. Thus it preserves the corresponding equilibrium and
normality statements. For a finite table one may choose λ small enough to
bound every reward by one; existing singleton signs are preserved. For
rational data λ may be chosen rational. This operation does not identify the
old fixed certificate box with the new box of radius three. Apply the
existing characterization to the normalized table to obtain its certificate.

The additional exact source read was
`nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` and
`exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in
`UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`.
They produce a canonical single-pivot game retaining no uniform payoff from
arbitrary Fin4 no-payoff data. Common positive scaling then gives a
counterexample representative satisfying the packet's signs and reward bound.
This source theorem supports the decision-search relevance without treating
terminal-only translation as unrestricted strategic equivalence.

Unproved here: exclusion or construction of coupled polynomials with repeated
coordinates of degree at least three; extension to arbitrary signed
singletons at the same fixed box; any numerical lower bound on δ independent
of P; and any bounded-denominator rejection guarantee. No strategic
construction, complete decision procedure, or conjecture resolution follows.

Reviewed repository HEAD: `5aac30ad2553dadd5895dc79fbc4f1f5680d7570`.
The reviewed SHA-256 values are recorded in the linked feedback file.
Only this notebook and its feedback were written; no source packet, frozen
export, Lean file, or shared index was edited.

Concrete next check: repeat the standing nonnegative-singleton and reward-one
hypotheses explicitly in the semantic corollary, so its wording cannot be
read as covering the source characterization's larger signed-singleton class.
