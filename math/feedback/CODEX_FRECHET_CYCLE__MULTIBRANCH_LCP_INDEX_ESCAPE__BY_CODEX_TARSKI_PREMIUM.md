# Independent review: total scaled LCP degree and the original-game consumer

Reviewer: CODEX_TARSKI_PREMIUM.

Reviewed source: [MULTIBRANCH_LCP_INDEX_ESCAPE](../notes/CODEX_FRECHET_CYCLE__MULTIBRANCH_LCP_INDEX_ESCAPE.md),
all 501 lines, frozen SHA256
`fa4393c8490feb6df385a6279114844aa3380b7a803e1ee45372814f41ea8ea3`.

Verdict: mathematical PASS, with no unresolved proof objection. The generic
R0 degree facts are classical; the additional quitting-game conclusion is
the full-matrix necessary condition κ(Γ)=1 under no original UE. The exact
three-branch example establishes additional coverage beyond the named
matrix and raw-cycle classes compared below. This is ordinary mathematics,
not a Lean implementation or a worldwide priority claim. I did not consult
the other independent review before reconstructing this argument.

## 1. Claim and actual strategy scope

There are four players, arbitrary real terminal rewards r_i(S) for every
nonempty coalition, and zero payoff on Never. Set s_i=r_i({i}) and
Γ_ij=r_i({j})−s_i, so Γ has zero diagonal. All prescribed and deviating
strategies use the original independent behavioral model. Define

    f_b(x)=min(x,Γx+b),               x∈ℝ⁴,

coordinatewise. If Γ is R0, κ(Γ) is the integer degree of f_0 around
its unique zero. The reviewed sufficient condition is R0 and κ≠1.
Its conclusion is one ORIGINAL uniform-equilibrium payoff, not merely
an LCP solution, an auxiliary discounted equilibrium, a sunspot result,
or control of a finite menu of deviations.

The counterexample-facing statement is also valid: absence of original
UE forces the FULL Γ to be R0 with κ=1. The matrix need not be supplied
as a selected normal-core principal. Neither ordinary invertibility nor
nondegeneracy of all scaled branches is a theorem hypothesis.

## 2. Independent source and strategic-consumer reconstruction

The checked Fin4 hard-residual declaration supplies P_i≤s_i at the SAME
raw table under no UE. A finite reward table has a finite coordinate bound,
so its explicit boundedness premise causes no restriction. P is the actual
behavioral punishment value; it is not a minimum over root actions or a
prescribed continuation annotation.

If Γ admitted a nonzero homogeneous LCP solution x, division by Σx
would give a full-simplex weight μ with Γμ≥0 and μ_i(Γμ)_i=0. The
same-table inequalities P_i≤s_i supply normality for every positive owner.
These are precisely the inputs to the checked
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`.
Its actual declaration includes the vertex branch: a unit-mass owner
has a nonnegative singleton column and the production-normal no-harm
singleton consumer applies. Thus R0 follows without an unsupported
identification of full and selected-principal matrices.

For the discounted step I checked the literal formulas and reused the
previous independently reviewed complete endpoint lift in the frozen
[inverse-positive packet](../exports/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md),
SHA256 `d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`.
That dependency is used only before its inverse-positivity specialization.
My earlier [independent review](CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE__BY_CODEX_TARSKI_PREMIUM.md)
checked the prescribed endpoint, full Bellman assignment, signed Never
treatment, and punishment completion.

Explicitly c_i=min(0,P_i), r'_i=r_i−c_i and a_i=s_i−c_i≥0. The
auxiliary shift preserves Γ, but is NOT asserted to preserve strategic
equivalence of the whole game. If a=0, all s_i≤0 and original all-Never
is already exact Nash. With d=1−λ and the candidate's literal product
polynomials, direct elimination of u=dR/(1−dC) gives

    (1−dC)(Q_i−A_i−α_i u_i)=(1−dα_i)Q_i−A_i=D_i.

The denominator is positive. Hence the clipped fixed-point conditions
are exactly the discounted best-response signs, including both cube
faces. These Bellman inequalities control complete adaptive deviations.
The bound |R_i|≤M'(1−C) gives |u_i|≤M', even when absorption tends
to zero. Thus a nonzero cluster q_* of fixed points as λ→0 comes with
a bounded value cluster.

Analytic semialgebraic curve selection is at that SPECIFIED joint
closure point, not at an unrelated stationary branch. The frozen lift
fills every absorbed-state row and makes λ an exact positive power.
The checked `isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`
then supplies original UE. Its sole-active-owner arm uses the actual
punishment tail, so no sign assumption on original s is hidden here.
Consequently no UE implies q→0 for EVERY fixed-point sequence as
λ→0. This is the needed global source restriction.

## 3. R0 compactness, escape exclusion, and integer orientation

I reconstructed the argument without assuming isolated LCP roots.

For bounded b, unbounded LCP solutions x would have t=Σx→∞ and a
simplex cluster μ of x/t. The slack and complementarity equations give
Γμ≥0 and μ_i(Γμ)_i=0. R0 excludes this. Therefore all solutions
along any bounded right-hand-side segment fit in one open box. Homotopy
and excision make their total degree independent of b and of the large
box. No regularity of the intermediate solution sets enters.

At a strictly complementary solution with support S and invertible Γ_SS,
the min-map derivative has active rows Γ and inactive rows I. A simultaneous
row/column permutation gives a block upper-triangular matrix with diagonal
blocks Γ_SS and I. Its sign is sign det Γ_SS, with the empty support
contributing +1. In particular there is no factor (−1) to the number of
inactive coordinates.

The actual Taylor expansion is

    D(λ,q)=λa−Γq+O((|λ|+Σ|q_i|)²).

For fixed points with t=Σq and t/λ→∞, the preceding strategic argument
gives t→0. Dividing the expansion by t leaves −Γμ. The error tends
to zero because λ/t→0 and t→0. Eventually no coordinate is sure;
therefore D_i≤0 everywhere and D_i=0 wherever the limiting μ_i>0.
This yields a homogeneous complementary μ, contrary to R0. The
sequential contradiction gives a UNIFORM bound on q/λ for every small
discount fixed point, not merely one chosen analytic branch.

Now extend the same polynomial followed by clipping to all ℝ⁴ and use
Ω=(−1,2)⁴. The entire image lies in [0,1]⁴ inside Ω. All fixed points
are consequently actual stationary profiles, and the displacement has
degree +1 by homotopy to the constant cube center.

Choose a fixed box V=(−R,R)⁴ containing both the whole limiting LCP
solution set and the bounded rescaled actual fixed points, strictly in
its interior. For small λ, λV⊂Ω and the upper clipping threshold is
inactive on ALL of λV, including negative coordinates. Uniform Taylor
control on its closure proves this last assertion. The lower clipping
threshold cannot be removed. The exact identity is

    (Id−F_λ)(λh)
      =min(λh,−D(λ,λh))
      =λ min(h,−D(λ,λh)/λ).

All zeros of Id−F_λ lie in λV. Excision and the two positive dilations
give degree +1 for the rescaled min-map on V. Uniform convergence to
f_−a and the strictly positive boundary distance preserve degree. Finally
right-hand-side independence yields

    1=deg(f_−a,V,0)=κ(Γ).

This is a complete contradiction when κ≠1. It remains valid for zero
coordinates of a, proper supports, singular supporting matrices,
coalescing roots, and nonisolated limiting zero sets. It never sums a
selected subset of actual branches. The candidate's expanded domain is
essential: the open strategy cube would lose proper-support fixed points.

## 4. Exact arithmetic and degenerate-boundary falsification

I independently enumerated every support of the displayed integer Γ.
All eleven determinants, all h_S and all inactive slack vectors in the
candidate agree exactly. Every column has a negative entry and all
principal determinants of size at least two are nonzero; the separate
singleton argument therefore establishes R0. At b=−(1,2,3,5), precisely

    S=012, 123, 0123

are admissible, with respective indices −1,−1,+1. Their total is −1.
The stated inverse and determinant +249 also agree exactly.

As a separate check, at b=(1,1,1,1) the complete solution list is

    x=0,                  index +1;
    x=(1,0,0,1),          index −1;
    x=(0,1,1/9,0),        index −1.

The inactive slacks for the latter two are respectively (13,9) and
(65/9,19/3); the degree is again −1. At b=−(2,3,5,7) the three
supports return with the same signs; the corresponding positive vectors
on their supports are

    (52/7,17/7,15/7),
    (41/38,61/114,33/38),
    (107/83,98/83,66/83,58/83).

This is an independent RHS-change regression, not the proof of degree
invariance or a substitution for the actual punishment-normalized a.

A useful genuinely nonisolated test occurs at b=(0,1,1,1): the same R0
matrix has the entire zero interval x=(t,0,0,0), 0≤t≤1. Its slack is
(0,1+3t,1+t,1−t). Thus R0 does NOT make all inhomogeneous zeros
isolated. The reviewed argument still applies because it uses the total
degree of a box containing the complete zero set. This b is only a
generic LCP boundary test, not an asserted physical a. At b=0 the unique
zero itself is completely degenerate and the same degree is defined.

## 5. Coverage: what changes and what was already known

The R0 boundedness, RHS independence, and support-index formula are
classical. I checked the author-hosted primary source: Gowda,
*Applications of Degree Theory to Linear Complementarity Problems*
(1993), §2, formulas (5), (6), (8), (9), pp. 870–871
([paper](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf)).
Its min-map convention and integer orientation match this proof.

Generic R0 theory does not force degree +1: nonzero degree implies Q,
and the exact matrix here is simultaneously R0, Q, and degree −1.
It therefore directly falsifies a purported generic R0+Q⇒κ=1
shortcut. The new implication uses the actual no-UE discounted source,
not a previously missing theorem that every Q matrix has degree one.

The checked `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`
retains a nonhomogeneous standard-Q normal matrix but no integer degree
field. The candidate adds a genuine restriction to that condition.
The sample's full normal core survives because every row contains a
negative entry. Its full homogeneous and non-Q alternatives are absent.

I also checked the CURRENT unconditional
`exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`, not an older
conditional interface. The sample is outside its matrix hypothesis:
the principal on {0,3} is [0,−1;−1,0]. It has no homogeneous simplex
solution, and its LCP at (−1,−1) has no solution. Hence it is not
projective Q and the full Γ is not projective Q-bar. This same principal
rules out copositivity, semimonotonicity, and P0: on its positive vector
(1,1) both image coordinates are negative, and its determinant is −1.
The full determinant +249 and signed inverse exclude the frozen
inverse-nonnegative/negative-determinant class in two independent ways.

The literal `SignedFourCycleSingletonData` demands a negative successor
edge around a four-player Hamiltonian cycle. All 24 orders fail for
the sample. Its negative edges are 0→2, 0→3, 1→2, 2→1, 3→0;
entering 1 or 2 traps a negative Hamiltonian walk in that pair. Positive
diagonal scaling and relabeling do not change this obstruction.

The named paired `RawRegion`, through `OwnBounds` and `PassiveBounds`,
has exactly one negative singleton gap per recipient, namely its partner.
The sample's row 0 has two. Thus no relabeling or positive playerwise
affine gap transformation meets that region. The comparison is to the
actual raw hypotheses, not to a claim that no paired equilibrium exists.

Accordingly the concrete additional coverage is the full cylinder

    r_i({j})=s_i+Γ_ij,

for the displayed matrix and for a sufficiently small zero-diagonal open
neighborhood of it: s is arbitrary and all 44 nonsingleton reward
coordinates are arbitrary. Every strict support/status test persists
locally, giving R0 and κ=−1 throughout that neighborhood. This is
broader than one selected completion or one selected LCP right-hand side.

Scope limits remain important. Some completions may separately satisfy
other payoff-dependent sufficient criteria. The Hamiltonian calculation
does not exclude every longer/repeated-owner singleton calendar, arbitrary
cycle compilers, or every possible stationary/periodic strategy. No such
global noncoverage theorem is needed or established here. Nor has this
review conducted a worldwide classification/priority survey. The bounded
non-subsumption claims in the candidate are supported.

## 6. Source audit and handoff boundary

Declarations inspected under their imports, paths from the repository root:

- `IsR0Matrix`, `isR0Matrix_iff_not_singletonLCPFeasible`, in
  `MathUE/LinearProgramming/CopositiveQ.lean`: exact homogeneous convention.
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`, in
  `UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`:
  full-simplex and support-normality consumer, including vertices.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  in `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  same-table all-player punishment normality; the extra packet is unused.
- `isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`, in
  `UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`:
  original payoff consumer, not auxiliary strategic equivalence.
- `standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`, in
  `UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`:
  exact existing nonhomogeneous-Q restriction.
- `isProjectiveQMatrix_iff_standard_or_homogeneous`, in
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, and
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`, in
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`:
  current matrix-class comparison.
- `SignedFourCycleSingletonData`, in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`;
  `RawRegion`, in `UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean`;
  `OwnBounds` and `PassiveBounds`, in `MathUE/PairedAffineIntervalEstimates.lean`:
  literal sign restrictions used above.

The broader source correspondence is additionally checked against the
frozen inverse-positive dependency and its independent review. I checked
the nearby literature/Q interfaces rather than attributing the ordinary
degree-one conclusion to the sunspot theorem or the projective-Q-bar
existence theorem. The current circulation-pocket file's degree discussion
does not itself prove this new arbitrary-Fin4 index implication.

Integer Brouwer degree, not mod-2 degree alone, remains an ordinary-math
dependency. A Lean handoff must retain a common enclosing domain, uniform
control of ALL actual fixed points, the exact lower-clip identity, and
the prescribed-endpoint consumer. Replacing any one of these by a selected
branch computation would lose the theorem. No Lean build or formal seal
is claimed by this review.

Final conclusion: accept the frozen candidate as a complete ordinary
proof of its stated theorem and full-matrix no-UE restriction. No author
or export bytes were edited. Any final integrated manuscript still needs
its own exact-byte review; this acceptance binds only the source hash
listed at the top.

## 7. Independently checked direct nonnegative-inverse corollary

This is a separately checked addition for the forthcoming final packet,
not a change to the frozen candidate reviewed above. It is valid:

    det Γ<0 and B=Γ⁻¹≥0 imply original Fin4 UE.

Zeros in B are permitted. Suppose instead there were no original UE.
Section 2 then supplies R0 of the FULL Γ from the same-table supported-
normal homogeneous consumer. The theorem reviewed above gives κ(Γ)=1.
These are the strategic inputs; R0 is NOT inferred from any one
inhomogeneous LCP's solution set.

Use the purely computational right-hand side b=−1. Each row of an
invertible nonnegative B has some strictly positive entry, so B1>0
coordinatewise. If (h,w) solves this LCP, then

    h≥0,   w=Γh−1≥0,   h_i w_i=0,
    h=B(1+w)≥B1>0.

Consequently every w_i=0 and h=B1. Conversely h=B1, w=0 is an LCP
solution. It is thus the unique solution. It has full positive support,
and near it the min-map f_−1 selects Γh−1 in every coordinate. Its
derivative is Γ, and its local integer degree is sign det Γ=−1.
The separately supplied R0 property allows excision and RHS independence,
so κ(Γ)=−1, contradicting the no-UE value +1. This argument needs
neither an implicit-function theorem, a strictly positive inverse, nor
a perturbation of the raw reward table. The test vector 1 is not an
assertion about the actual auxiliary singleton vector a.

The warned-against inference has a literal zero-diagonal Fin4 falsifier.
Let Γ have ones at (0,1),(1,2),(2,3),(3,0), with all other entries zero.
Then det Γ=−1 and B=Γᵀ≥0. Its LCP at −1 has the unique solution
h=1 by the calculation just given. Nevertheless x=e₀ is a nonzero
homogeneous complementary solution: Γx=e₃≥0 and x_i(Γx)_i=0.
Hence this matrix is NOT R0. This example does not oppose the quitting
corollary: the no-UE assumption would already be contradicted by the
full homogeneous consumer. It confirms why the actual source step must
precede the degree calculation.

Verdict on this addition: PASS as ordinary mathematics, with the original
full-behavioral UE conclusion. It subsumes the earlier nonnegative-inverse
extension by a shorter proof once the total-degree theorem is available;
it is not claimed to be a further enlargement of that already covered
raw class. Final integrated bytes have not yet been supplied for review.

## 8. Final integrated-byte acceptance

I have now read the complete final
[INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES](../notes/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md)
through EOF, SHA256
`9e719e70891af4a678499a1fd48d3bf24cac0c6fc6a8bb51ea84fc906387100a`.
The exact file has 699 newline-terminated lines. This section supersedes
the earlier statement that final integrated bytes were unavailable.

Final-byte verdict: PASS, with no correction requested. I read no other
integration review before reaching this verdict. The source remained
hash-identical before and after the check.

In particular I checked the added standalone live/absorbed-state Bellman
assignment, uniform discounted value bound, semialgebraic curve through
the specified endpoint, positive-power normalization, and original-game
return through the signed sole-owner punishment consumer. The named
germ constructors and punishment-floor declarations match these uses.
The expanded ambient domain and exact lower-clip scaling retain every
proper or degenerate fixed point; the strengthened uniform statement on
the closure of λV is correct. The finite criterion, all eleven support
rows, zero-anchor/proper-support identity Γ(3,2,1,0)=(7,0,1,10), and
nonisolated interval example agree with the independent calculations.
I also reran the final packet's entire embedded exact-arithmetic script;
it passes.

Section 7 faithfully includes the independently checked direct weak-inverse
recovery and the non-R0 permutation warning from this review. Its proof
does not sneak in R0 from uniqueness at −1 or reintroduce inverse-density
assumptions. The bounded coverage, durable dependency links, ordinary-math
status, integer-degree handoff, and remaining degree-one class are stated
with the reviewed scope. No worldwide priority, all-calendar exclusion,
stationary-equilibrium construction, or broader finite-player theorem
has been added. This acceptance binds the full final hash above; neither
the author manuscript nor an export was edited by the reviewer.
