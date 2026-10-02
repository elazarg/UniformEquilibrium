# Crossed stationary-response degree escape: independent mathematical review

## Verdict

PASS for the stated strict, weak, and guarded-degree theorems in
`gpt/CROSSED_STATIONARY_RESPONSE_DEGREE_ESCAPE.md`. No mathematical correction
is required before an export-gate request. Export assembly must replace the
temporary manuscript/checker references with the actual proof and finite
certificates; the original is ordinary mathematics, not a checked Lean result.

The genuine increment is a raw-table, collision-sensitive stationary
producer in a full-degree-+1 region with no usable response-invariant
quotient. The original individual incentives are recovered from the guarded
crossed map; no desired root, punishment plan, or strategic witness is an
input. The result does not cover arbitrary completions of the singleton
matrix and does not show that every Q matrix admits UE.

## Claim and mathematical checks

The model is finite four-player quitting with zero live and Never reward,
arbitrary signed terminal rewards, independent private clocks, and complete
unilateral behavioral replacements. The weak theorem assumes det Γ > 0,
Γ⁻¹ ≥ 0, twenty-four lower-ranking comparisons, and eighteen nonpositive
half-ceiling Bernstein coefficients. It produces stationary profiles with
full terminal regret tending to zero and one fixed uniform payoff target.
The strict theorem produces an exact stationary behavioral equilibrium with
0 < q₀,q₁ < 1/2 and q₂+q₃ > 0. The more general theorem instead assumes
the two strict polynomial face guards, positive reciprocal comparisons, and
PΓ being R0 of integer degree different from +1.

1. The residual is Δᵢ = (1−αᵢ)Qᵢ−Hᵢ, independent of qᵢ, with ambient
   derivative −Γ. The displayed payoff/displacement identity has the correct
   factor 1−C and sign. Hᵢ is the unnormalized one-stage Continue absorption
   contribution, not the stationary Never payoff Hᵢ/(1−αᵢ).
2. A fixed point with a nonzero outsider hazard cannot lie on either crossed
   coordinate's lower or artificial upper face: its partner's guard forbids
   that face. Thus both original selected residuals vanish. The outsider
   coordinates retain their own endpoint signs. At outsider zero, Δᵢ(t)/t
   is affine, negative at zero by reciprocity and at 1/2 by the upper guard;
   it is negative throughout the relevant interval. Only the origin remains
   on that face. This establishes original individual Nash, not coalition
   Nash or an equilibrium restricted to half-rate deviations.
3. Global degree is +1 on the expanded ambient box. The small-origin
   displacement is min(q,PΓq+O(‖q‖²)); lower clipping cannot be dropped.
   R0 supplies a positive homogeneous sphere margin, so the quadratic
   perturbation preserves local degree κ(PΓ). No nonzero-root regularity or
   finiteness is used. Excision retains all strategy-face roots.
4. Strict inverse positivity gives R0 directly, before right-hand-side
   invariance is invoked. LCP(PΓ,−1) then has the unique positive solution
   (PΓ)⁻¹1; its Jacobian determinant is negative. Hence κ(PΓ)=−1 and the
   nonzero fixed-point set has total degree +2. This is not exactly two roots.
5. At least three positive hazards make every αᵢ < 1. Each complete response
   is a mixture of finite deadlines and Never, whose values lie between Qᵢ
   and Hᵢ/(1−αᵢ). The endpoint equations therefore give Bᵢ=Uᵢ even for
   negative singleton rewards. The geometric first-opponent time yields the
   stated uniform-in-response horizon bound. No normality or punishment
   completion is needed.
6. Censoring private tails independently preserves the actual terminal
   payoff formula and changes any deviated payoff only on the event that
   every opponent survives the censoring date. The bound 3Mρᴷ therefore
   includes after-support responses and Never.

## Weak boundary

The nonnegative-inverse strictification is valid for n ≥ 3. If Bᵢⱼ and
(BKB)ᵢⱼ vanish, the nonempty row and column supports collapse to one common
index. Invertibility forces a positive entry outside its row and column,
giving a positive second-order contribution. Thus Γ−eK has strictly positive
inverse for all sufficiently small positive e, with determinant sign intact.

The literal reward modification has distance at most 3e. Its lower gap gains
e. At the half ceiling, direct recomputation gives δQᵢ=−3e/2,
δHᵢ=−e/2, and δΔᵢ=−e+(3e/4)β. The Bernstein coefficients of β are in
[0,1], so every weak upper coefficient becomes strictly negative. No empty
terminal reward is shifted. The direct weak-polynomial-guard variant also
works: at partner zero the residual change is e(1−β), strictly positive off
the origin.

Reward distance δ changes complete exploitability by at most 2δ. A payoff
subsequence gives one fixed target. The horizon is chosen after choosing a
single approximant; its possibly deteriorating contraction denominators do
not change the quantifier order. There is no claim that the limit strategy
exists, that the cap is continuous there, or that weak hypotheses give exact
stationary attainment.

## Explicit falsification attempts and arithmetic

Removing the guards really breaks the transfer. If the only nonzero reward
is r₀({0,1})=2, then at q=(0,1,0,0), Δ=(2,0,0,0). The row-swapped unit-cube
map fixes q, although original player 0 gains two by joining. The degree
calculation alone would not make that root strategically usable.

The displayed half-ceiling table defeats the stronger sure-partner shortcut:
both selected players gain one by joining a pure partner. Thus replacing its
half-ceiling guard by a full-ceiling guard is not harmless. Conversely, the
proved interiority allows all actual deviations to certain Quit.

The complete 257-line supplied checker `gpt/VERIFY_CROSSED_RESPONSE.py` was
inspected before execution; it only performs exact Fraction computations
and prints results. Its run passed. It verifies the table, inverse and
determinants, both Bernstein arrays and coefficient sensitivity norms,
rational root, actual full caps, all fourteen partition exclusions, all
fourteen proper-child LP certificates, and every pure-coalition toggle.
This is arithmetic evidence, not a mechanical check of degree theory.

The inequalities separating the fixture from the quotient criterion are
exact polynomial witnesses. Eight partitions fail the first-order block
row-sum condition; the six survivors fail the displayed nonlinear identities.
The discrete partition retains full degree +1. All-child LP failure concerns
the stated universal raw tests, not every possible extension of one actual
child equilibrium. The known root itself has player 3 Never.

The 1/100 reward neighborhood is valid: inverse error is bounded by
6δ/(1−6δ), the lower margins lose at most 2δ, and each Bernstein coefficient
has reward-coordinate coefficient norm at most two. With Γ fixed, the 22
outsider nonsingleton entries are wholly unrestricted, while the other 22
lie in a nonempty open polyhedron. Arbitrary signed singleton levels are
allowed by applying the theorem anew to row-translated tables, not by
asserting strategic invariance of Never-fixed translations.

## Sources and overlap

The bounded source route used `docs/TOOLKIT.md`, then the following tracked
files and declarations (paths are repository-root relative):

- `UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`:
  `IsQuittingStationaryBoundaryAdmissible`,
  `quittingTerminalPayoff_stationary_eq_of_fixedPoint`,
  `quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash`,
  `isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts`, and
  `isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts`.
- `UniformEquilibrium/Quitting/Classification/LCP/PositiveInverse.lean`:
  `isStandardQMatrix_of_positive_rightInverse` and
  `noHomogeneousSimplexSolution_of_positive_leftInverse`.
- `UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`:
  `isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`, whose
  explicit original-table normality premise must not be silently discarded.

The original author-hosted Gowda paper, *Applications of Degree Theory to
Linear Complementarity Problems*, MOR 18(4), 1993, Section 2, pp. 869–870,
matches the whole-space minimum convention, orientation, bounded-RHS R0
degree invariance, and basic degree properties:
<https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf>.

The already reviewed stationary-response quotient theorem supplies a
comparison, not a proof dependency of this crossed construction. Ambient
degree escape itself is not the new increment; guarded row permutation and
the collision-sensitive raw class are. No Lean build or new axiom audit is
claimed.

## Safe consolidation

The strict argument works for finite n ≥ 3 and any one common ceiling
h ∈ (0,1]: replace the upper face 1/2 by h and clip the selected pair to
[0,h]. The zero-outsider affine bracket is negative at zero and h. The
half-ceiling Bernstein and full-ceiling joining tests can therefore be
corollaries of one theorem, while their stated weak-boundary hypotheses
remain explicit. This is a direct parameterization of the same proof,
not a reason to omit any artificial-face guard.
