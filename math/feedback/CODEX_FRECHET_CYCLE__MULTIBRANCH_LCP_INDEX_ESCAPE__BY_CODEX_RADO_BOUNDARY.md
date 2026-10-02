# Independent falsification audit of the multibranch LCP criterion

Reviewer: CODEX_RADO_BOUNDARY.

Verdict: PASS as ordinary mathematics, with the previously reviewed
prescribed-endpoint bridge explicitly retained as a dependency. No unresolved
mathematical objection was found. The candidate proves its all-root
localization and bounded rescaling assertions; they are not unproved fields
of a supplied object. This review does not claim a Lean-checked degree
composition or authorize an unreviewed final packet.

Reviewed source:
[CODEX_FRECHET_CYCLE__MULTIBRANCH_LCP_INDEX_ESCAPE.md](../notes/CODEX_FRECHET_CYCLE__MULTIBRANCH_LCP_INDEX_ESCAPE.md).

Exact source SHA-256:
`fa4393c8490feb6df385a6279114844aa3380b7a803e1ee45372814f41ea8ea3`.

I read all 501 lines and checked the hash before and after the substantive
audit. I did not consult any other review or verdict of this new claim.
The permitted earlier dependency is Sections 2–4 of
[INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md](../exports/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md),
SHA-256
`d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`.
I reread those sections and checked the actual source and endpoint declarations
used below. No inverse-positivity assertion from that dependency is imported
into the new proof.

## 1. Claim and semantic scope

For four players with arbitrary real rewards r(S) at nonempty quitting
coalitions and zero Never payoff, define

    s_i = r_i({i}),       Γ_ij = r_i({j}) − s_i.

The matrix has recipient rows, quitter columns, and zero diagonal. For every
real vector b define on the whole ambient space

    f_b(x) = min(x, Γx+b),

with coordinatewise minimum. The R0 condition is that the only zero of f_0
is zero. Its integer local degree there is κ(Γ).

The accepted implication is:

    Γ is R0 and κ(Γ) ≠ 1
      imply existence of an original-game uniform-equilibrium payoff.

The payoff target is fixed before the accuracy. Each accuracy may select a
behavior profile and one horizon threshold; at every later horizon the
profile delivers that target in expected average payoff and bounds every
complete unilateral behavioral deviation. Randomization is the independent
private behavioral randomization available in the actual game. The conclusion
has no stationary, finite-memory, or finite-date restriction on deviations.

The counterexample-facing consequence is also accepted: a Fin4 table with
no such payoff has R0 and degree +1 for its full Γ. The R0 assertion uses
the homogeneous consumer and the same-table all-player normality source;
the new restriction is the integer degree.

## 2. Source normality, full R0, and the original-game endpoint

The actual declaration
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`, in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`,
accepts an arbitrary Fin4 table, a coordinate reward bound, and nonexistence
of an original UE payoff. A finite reward bound exists for the finite table.
Its returned structure has an `all_punishmentNormal` field for every player
of that same table. No selected packet is needed to extract this field.

`IsQuittingNormalPlayer`, in
`UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`, is exactly
P_i ≤ s_i. The definitions `quittingBestReplyValue` and
`quittingPunishmentValue`, in
`UniformEquilibrium/Quitting/Stationary/MinMax.lean`, use the full behavioral
response supremum and the infimum over opponent behavior plans. They do not
replace these quantities by stationary caps.

If a nonzero homogeneous LCP vector x existed for the full Γ, division by
its positive total mass would give a full-simplex weight μ with Γμ ≥ 0 and
μ_i(Γμ)_i = 0. I checked the exact declaration and both branches of
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`, in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`.
Its hypotheses are precisely these residual and complementarity conditions
for `normalizedSoloMatrix reward`, plus P_i ≤ s_i for positive owners.
The vertex case uses the normal no-harm singleton producer; it is not
discarded or assumed to have contracting deleted survival. Thus the candidate
has a literal full-matrix R0 derivation under no UE.

The actual auxiliary anchor is c_i = min(0,P_i), with shifted terminal
table r′_i(S) = r_i(S) − c_i and zero live payoff. These are
`quittingAuxiliaryLive` and `quittingAuxiliaryReward` in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`.
Normality gives a_i = s_i − c_i ≥ 0. If every a_i vanishes, every original
own singleton is nonpositive and all Never is already original Nash at
every finite horizon. Hence a ≠ 0 in the contrary branch. Neither this
argument nor what follows needs every a_i positive.

I checked
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint`, in that same
auxiliary-shift file, including its sole-active-owner branch. It is generic
in the finite player type. Its only endpoint hypothesis is joint Continue
mass less than one; there is no inverse-positivity, full-support, or
three-player hypothesis. Its conclusion is a fixed original-game UE target.
Its proof uses `quittingPunishmentValue_le_auxiliaryEndpointTarget` and
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`, the latter in
`UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean`. That composition
handles signed singleton rewards when opponents Continue surely and retains
all behavioral deviations. Auxiliary translation is not being treated as
strategic equivalence with Never unchanged.

## 3. Every discounted fixed point is covered

The Bellman polynomial D and the clipped map in the candidate agree with the
earlier packet's exact discounted map. The relation between live values and
the two pure Bellman endpoints has the correct sign and discount factors.
In particular a fixed point has D_i ≤ 0 at zero, D_i = 0 at a mixed action,
and D_i ≥ 0 at one. These are the full face conditions, including indifferent
pure actions. With stationary opponents the Bellman upper inequality applies
to any adaptive response; iterating it leaves a bounded remainder multiplied
by a discount power tending to zero.

The inequality |u_i| ≤ M′ follows from
|R_i| ≤ M′(1−C) and denominator λ+(1−λ)(1−C). It is uniform over the
whole fixed-point graph for this fixed table. It does not require a
positive lower bound on the denominator.

Take any hypothetical fixed-point sequence with λ tending to zero and a
nonzero hazard cluster q*. Compactness of the cube and this value bound
supply a cluster (0,q*,u*). The retained graph of discount, hazards, values,
and every face condition is semialgebraic. The earlier packet's
prescribed-endpoint curve-selection and complete-assignment lift apply to
this very closure point: the absorbing-state actions are constant and their
values are r′(S), and the live equations are exactly the displayed graph
conditions. No matrix sign enters that lift.

The actual constructors
`exists_analyticBellmanGerm_of_positiveCoordinateArc`,
`exists_analyticBellmanGerm_of_powerCurve`, and
`analyticBellmanGermOfPowerCurve_endpoint`, in
`UniformEquilibrium/VanishingDiscount/Bellman/Germ.lean`, preserve the
specified full assignment at the endpoint. The positive discount coordinate
can be reparametrized to an exact power as in the reviewed dependency.
Since q* is a nonzero point of the strategy cube, its joint Continue mass
is strictly below one, and the original-game endpoint consumer above gives
the contradiction.

Therefore every fixed-point sequence with discount complement tending to
zero has q tending to zero. This proves the universal statement needed by
the argument. It neither selects a preferred equilibrium germ nor substitutes
a reselected full-support source packet.

## 4. R0 bounds the entire rescaled set

I independently expanded the polynomial to first order. At the origin,

    1−(1−λ)α_i = λ + Σ_(j≠i) q_j + O((|λ|+Σ|q_j|)²),
    Q_i = a_i + O(Σ|q_j|),
    A_i = Σ_(j≠i) q_j r′_i({j}) + O((Σ|q_j|)²).

Consequently

    D(λ,q) = λa − Γq + O((|λ|+Σ|q_i|)²).

This is an ordinary polynomial expansion on an ambient real neighborhood.
Nonsingleton terms have no first-order contribution. The constants may
depend on the fixed table, which is sufficient.

Suppose the rescaled fixed-point set were not eventually bounded. Select
fixed points with λ_n tending to zero and t_n/λ_n tending to infinity,
where t_n = Σ_i q_(n,i). Then t_n > 0 and the universal localization just
proved gives t_n tending to zero. Along a subsequence μ_n = q_n/t_n
converges to a simplex point μ. Eventually every hazard is strictly below
one, so D_i ≤ 0 for every coordinate. Whenever μ_i > 0 the corresponding
hazard is eventually positive as well, making D_i exactly zero.

After division by t_n, the remainder is bounded by a constant times
t_n(1+λ_n/t_n)² and tends to zero. Thus D/t_n tends to −Γμ, yielding
Γμ ≥ 0 and equality on every positive coordinate of μ. This is a
nonzero homogeneous LCP solution, contradicting R0.

The sequential contradiction proves the stated eventual uniform constants
R₁ and λ₁ for every fixed point. It is stronger than boundedness of any
selected branch. Vanishing components, proper leading supports, and zero
coordinates of a were never divided by or discarded. No principal matrix
was inverted in this argument.

## 5. Expanded cube, min-map identity, and integer orientation

The domain Ω = (−1,2)⁴ is the correct ambient replacement for the open
strategy cube. The polynomial extension followed by clipping always maps
the whole space into [0,1]⁴. A fixed point of that extension must therefore
be a legal strategy vector. On the boundary of Ω it cannot be fixed.
The homotopy of F to the cube center keeps its image in the strategy cube;
Id minus that homotopy remains nonzero on the boundary. Its normalized
degree is +1.

For R0, normalization of an unbounded family of LCP solutions at bounded
right-hand sides produces a nonzero homogeneous solution. The candidate's
boundedness proof is valid even for singular Γ and nonisolated solutions.
The standard residual, R0 convention, and existing uniform bound were checked
at `IsStandardLCPSolution`, `IsR0Matrix`, and
`isR0Matrix_iff_not_singletonLCPFeasible`, in
`MathUE/LinearProgramming/CopositiveQ.lean`, and
`exists_bound_sum_of_isR0Matrix`, in
`MathUE/LinearProgramming/CopositiveQCorollaries.lean`.
Homotopy along a bounded right-hand-side segment therefore proves that the
total degree is independent of b. This supplies the bridge from the actual
anchor −a to any convenient test right-hand side.

Choose R > R₁ with all zeros of f_−a strictly in V = (−R,R)⁴. The continuous
map f_−a has a positive minimum norm ρ on the compact boundary of V.
For sufficiently small positive λ, one may simultaneously ensure:

- λ times the closed box lies inside Ω;
- every zero of Id−F_λ lies strictly inside λV;
- q+D(λ,q) is coordinatewise below one on the closed box λV; and
- the uniform difference between f_λ and f_−a on the closed V is less
  than ρ/2.

The third assertion follows directly from the ambient expansion: uniformly
for bounded h, λh+D(λ,λh) is O(λ). It remains true when some coordinates
of h are negative. Upper clipping is inactive on this entire neighborhood.
Lower clipping cannot be removed and is correctly retained in the exact
scalar identity

    q−max(0,q+D) = min(q,−D).

Thus on the closed scaled box,

    (Id−F_λ)(λh) = λ min(h,−D(λ,λh)/λ) = λ f_λ(h).

Excision loses no roots because the previous section bounded all of them.
Input dilation h ↦ λh and output dilation y ↦ λy both have positive
determinant. The degree is therefore unchanged and equals +1. There is no
factor depending on the number of active coordinates and no passage to
relative orthant degree. The boundary margin makes the straight homotopy
from f_λ to f_−a nonzero on the boundary, so its degree is also +1.
Right-hand-side independence then gives κ(Γ) = +1, the desired contradiction.

This argument uses only the complete compact zero set. It remains valid
when roots meet cube faces, merge, are nonisolated, or have singular
supporting submatrices. Local determinant formulas are not used for the
actual source at −a.

I inspected the original page images of Gowda,
[*Applications of Degree Theory to Linear Complementarity Problems*](https://userpages.umbc.edu/~gowda/papers/trGOW93-01.pdf),
Section 2, pp. 869–871. Its min-map convention, R0 degree independence,
local index sign at a strictly complementary regular solution, and total
signed-sum formulas agree with the candidate. In particular the inactive
rows contribute identity rows; simultaneously permuting rows and columns
leaves the determinant sign unchanged. The result uses integer degree:
the degree −1 example would not contradict +1 after reduction modulo two.
The paper supplies degree facts, not a quitting-game theorem. No matching
paper transcription was found in the bounded Literature filename lookup.

## 6. Complete witness calculation and degenerate-anchor stress test

I recomputed every support directly from the displayed matrix and the test
anchor (1,2,3,5), independently of the candidate's expected-value assertions.
All eleven determinants, all eleven active vectors, every displayed inactive
slack, and the whole inverse matrix match exactly. Empty support fails
because the right-hand side is strictly negative. Each singleton support
fails its active equation because Γ has zero diagonal and the corresponding
anchor coordinate is positive. Therefore the inventory covers all 16
supports, not only regular candidate branches selected in advance.

Exactly these supports are admissible:

| Support | Active coordinates | Inactive slack | Local index |
| --- | --- | --- | ---: |
| 012 | (92/21, 29/21, 26/21) | 26/21 | −1 |
| 123 | (46/57, 55/171, 31/57) | 317/171 | −1 |
| 0123 | (634/249, 251/249, 208/249, 52/249) | none | +1 |

All these roots are strictly complementary and their supporting matrices
are nonsingular, so their indices sum to −1. Every column has a negative
entry and every principal determinant of size at least two is nonzero.
These facts exclude all nonzero homogeneous supports, including singletons,
and prove R0. The positive full determinant 249 and mixed-sign inverse are
both correctly reported. The strictly rejected support inequalities, accepted
slacks and weights, and principal determinants also justify the claimed
small zero-diagonal neighborhood of examples.

As an additional attempt to falsify the treatment of zero anchor coordinates
and merging roots, keep the same matrix and use the purely algebraic test

    a* = (7,0,1,10),       h* = (3,2,1,0).

Direct multiplication gives Γh* = a*. Thus the 012 root has an inactive
coordinate and inactive slack both zero, while the anchor has a zero
coordinate. It is a degenerate proper-support root and the regular support
index formula cannot simply be applied there. The other root is

    (0,67/38,15/38,15/38),

with support 123 and inactive slack 83/38. Exact enumeration gives these
as the only two distinct roots at −a*.

Replacing the last coordinate of a* by 10−1/10 gives three strictly
complementary roots on 012, 123, and 0123, with indices −1, −1, +1.
Replacing it by 10+1/10 leaves only the support-123 root with index −1.
The 012 root is fixed at h*, its inactive slack being minus that offset;
the full root changes by the offset times column 3 of Γ⁻¹, whose final
entry is −42/249. This explains the merger and disappearance of the
oppositely indexed pair. The total degree remains −1 across the degenerate
anchor. These are exact rational checks, not floating-point evidence.

This stress fixture is not asserted to be an actual game's punishment anchor.
It checks the algebraic robustness that the proof must have because it cannot
choose the actual anchor. Right-hand-side independence and the ambient
boundary-margin argument supply that robustness. Likewise the three regular
roots in the candidate are roots at its test right-hand side; no conclusion
that every reward completion has exactly three discounted equilibrium germs
is licensed or needed.

## 7. Bounded class comparison and status

The example has nonzero degree, so the degree existence property makes the
full matrix standard Q. R0 excludes the full homogeneous branch. Its
principal on {0,3} has both off-diagonal entries −1: a nonnegative vector
can have nonnegative image only at zero, and that image cannot dominate
(1,1). This principal is neither homogeneous nor standard Q and therefore
is not projective Q. I checked the convention at
`isProjectiveQMatrix_iff_standard_or_homogeneous` and
`IsProjectiveQBarMatrix`, in
`UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`.
Thus the stated failure of full projective Q-bar is valid.

The negative graph in the candidate is complete and has no Hamiltonian
cycle, also verified by exact enumeration of the 24 permutations. The
`SignedFourCycleSingletonData` fields in
`UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`
require precisely such a negative successor cycle. Positive diagonal
rescalings preserve its signs. Every row of the displayed matrix has a
negative entry, which retains the full normal core.

For the paired comparison I inspected `RawRegion` in
`UniformEquilibrium/Quitting/Cycles/PairedCycleSchedule.lean` and its
`Math.PairedAffine.OwnBounds` and `PassiveBounds` in
`MathUE/PairedAffineIntervalEstimates.lean`. The own singleton lies in
[9/10,11/10], its partner's singleton reward in [−1/10,1/10], and each
quiet player's singleton reward in [19/10,21/10]. These imply exactly one
negative singleton gap per recipient. The example's row 0 has two, so the
literal raw region and its sign-preserving positive affine changes do not
contain it. This is not an exclusion of every possible paired equilibrium.

I also checked
`standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff`, in
`UniformEquilibrium/Quitting/Classification/LCP/CounterexampleNecessary.lean`,
and `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`, in
`UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`,
to confirm the candidate's bounded comparison with the existing semantic
consumers. It makes no claim that each nonsingleton completion avoids every
reward-dependent sufficient class.

The matrix criterion is an actual raw-table sufficient condition. Its proof
derives same-table normality and localization from a contrary no-UE assumption
and reaches an existing unrestricted fixed-target consumer. The source a
is never replaced by the test vector. The new conclusion is stronger than
a verifier for supplied scaled roots, but does not settle all Fin4 matrices,
arbitrary player counts, exact stationary equilibrium, or constructive
strategy selection.

No repair is required for the frozen candidate. The concrete remaining gate
is final-packet integration: retain the complete all-root proof, the expanded
ambient domain and lower clip, the right-hand-side independence argument,
and the credited original-game endpoint dependency. A conditional structure
with localization as an assumed field would not represent the accepted
result. No Lean build was run, and no author, Lean, shared-index, or export
file was changed during this audit.

## 8. Direct recovery of the nonnegative-inverse class

Independent bounded addendum: PASS. The accepted total-degree argument,
together with the existing same-table homogeneous dispatch, directly proves
the entire Fin4 class

    det Γ < 0 and Γ⁻¹ ≥ 0 entrywise.

This recovery needs neither the implicit-function theorem nor the
zero-diagonal-preserving inverse-density argument. The earlier export
remains valid and unchanged. This addendum is a mathematical simplification,
not a claim that the weak-inverse hypothesis itself implies R0.

Write B = Γ⁻¹ and let 1 denote the all-ones vector. Every row of an
invertible nonnegative matrix is nonzero, so

    h* = B1 > 0

coordinatewise, including when B has zero entries. This vector solves
LCP(Γ,−1), since Γh*−1 = 0. Conversely, if h solves that LCP then
Γh ≥ 1. Multiplication by the nonnegative matrix B preserves the
coordinatewise inequality, giving

    h = BΓh ≥ B1 = h* > 0.

Complementarity therefore forces every slack coordinate Γh−1 to vanish.
Invertibility gives h = h*. Thus this LCP has exactly one root, and its
support is the full player set.

At h*, each coordinate of Γh*−1 is zero while the corresponding coordinate
of h* is strictly positive. On an ordinary ambient neighborhood of h*,
the min-map therefore chooses its second argument in every coordinate:

    f_−1(h) = Γh−1.

Its Jacobian is exactly Γ, which is nonsingular. The unique root's integer
local degree is sign(det Γ) = −1. There is no inverse-entry strictness
assumption in this local calculation and no sign depending on support
ordering.

If Γ is R0, the already-proved right-hand-side independence identifies this
total degree at −1 with κ(Γ), so κ(Γ) = −1 and the accepted R0 theorem
produces original UE. If Γ is not R0, argue under the contrary no-UE
assumption: same-table Fin4 all-player punishment normality supplies the
support-normality hypotheses of
`exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`, in
`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`.
A normalized nonzero homogeneous LCP witness then produces original UE,
contradiction. Equivalently, no UE first forces R0, after which the
calculation above contradicts its necessary degree +1.

The non-R0 branch is essential. As an exact check, the four-cycle
permutation matrix has det Γ = −1 and B ≥ 0 with zeros. Its unique solution
of LCP(Γ,−1) is (1,1,1,1), with local index −1. Nevertheless e₀ is a
nonzero homogeneous solution: Γe₀ = e₃ and their coordinatewise product
vanishes. Thus one must not define κ for this matrix by pretending that
uniqueness at −1 proves R0. The homogeneous original-game consumer supplies
the required separate branch.

The all-ones vector is only a test right-hand side for computing the degree;
it does not replace the game's actual punishment-normal anchor. The argument
retains arbitrary own singleton and nonsingleton rewards, the actual Never
payoff zero, all behavioral deviations, and one fixed UE target. It remains
specifically Fin4 because that is the scope of the same-table no-UE
normality source used here. Positive determinant would instead give local
degree +1 and supplies no contradiction by this calculation.

The addendum is complete. The outstanding requested check is integration
of the standalone final packet once its final bytes are supplied.

## 9. Exact final-packet integration acceptance

Final packet:
[INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md](../notes/INTEGER_LCP_DEGREE_CRITERION_FOR_FOUR_PLAYER_QUITTING_GAMES.md).

Accepted final SHA-256:
`9e719e70891af4a678499a1fd48d3bf24cac0c6fc6a8bb51ea84fc906387100a`.

Verdict: PASS. I read all 699 final lines, including the complete standalone
endpoint lift, degree proof, finite test, both new boundary examples, direct
weak-inverse recovery, source correspondence, and handoff. No mathematical
information needed by the accepted proof has been lost and no correction is
required. I did not consult the second review or its verdict. This final-byte
acceptance supersedes the earlier deferral of the integration gate in this
review; it does not assert Lean verification.

Section 1 retains the exact raw Fin4 hypothesis and one fixed original-game
UE payoff against all behavioral deviations. Sections 2–4 retain the
distinction between the game's actual anchor and the independent right-hand
side used to compute total LCP degree. The counterexample-facing R0 statement
is explicitly for the full matrix and is supplied by same-table normality
and the supported homogeneous consumer, including its vertex case.

The enlarged Section 3 now includes every part of the earlier endpoint
dependency needed here: the actual auxiliary table, complete Bellman face
conditions, bounded discounted values, curve selection at the specific
nonzero cluster, all fifteen absorbing-state assignments, exact-power
discount reparametrization, preserved endpoint, and signed sole-owner
punishment completion. Its argument uses no inverse positivity. The retained
notes copy of the credited packet has the same reviewed hash
`d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`.
Thus the credit link change has not replaced its mathematical content.

The all-root q tending to zero conclusion and R0's uniform bound on q/λ
are still proved, rather than supplied as premises. Section 4 expressly
puts λ times the closed box inside Ω and controls upper clipping on that
whole closed box. The lower-clip min identity, excision of every fixed
point, positive input/output orientation, and uniform boundary homotopy
therefore remain justified for proper, degenerate, and nonisolated roots.
Zero coordinates of the actual anchor remain allowed.

Section 5 retains the complete exact finite criterion and the support
inventory independently recomputed above. The three regular branches are
the LCP roots at its explicitly specified test right-hand side −(1,2,3,5).
Its explicit distinction between this test and the actual anchor prevents
interpreting the branch count as a statement that every game completion
has exactly three discounted equilibrium germs.

I also checked the additional Section 5.3 identities directly. For the
displayed matrix, Γ(3,2,1,0) = (7,0,1,10) gives the stated degenerate
proper-support root with a zero anchor coordinate. For b = (0,1,1,1),
x = (t,0,0,0) has slack (0,1+3t,1+t,1−t). For every t in [0,1],
both vectors are nonnegative and their coordinatewise product is zero.
Thus this R0 matrix really can have nonisolated inhomogeneous roots.
The packet correctly labels the latter b as an arbitrary algebraic test,
not necessarily an actual negative punishment anchor.

Section 7 faithfully incorporates the accepted direct recovery: no UE first
supplies R0 and κ = +1; B ≥ 0 and invertibility make B1 strictly positive;
the LCP at −1 has that unique full-support root of local degree −1; and
right-hand-side independence gives the contradiction. The permutation
counterexample preserves the essential warning that uniqueness at −1
does not imply R0. Neither IFT nor inverse-density is reintroduced.

The bounded class comparison, source correspondence, and final handoff
retain the distinction between existing semantic consumers and the new
ordinary integer-degree composition. They do not enlarge the conclusion
to stationary exact equilibrium, arbitrary player counts, or the entire
Fin4 conjecture. The residual R0 degree-one class remains explicitly open.
No author, Lean, or export file was edited for this integration check.
