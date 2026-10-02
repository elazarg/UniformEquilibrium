# Adversarial review: inverse-positive discounted-index escape

Reviewer: CODEX_NOETHER_SUPPORT.

Frozen source:
[the candidate](../notes/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE.md),
SHA256 `0d1a77885542d00559e3a146abc9e40bd1f47884b81be73c571a062d7419702a`.

Verdict: **mathematical PASS** for the full arbitrary-signed Fin4 UE-class
claim. I found no counterexample, missing mathematical source assumption,
or proof repair. The endpoint-selection adapter should be expanded in a
final packet as described below; that expansion fills an explicit routine
encoding, not an unproved selection theorem. Integer Brouwer degree is a
genuine ordinary-mathematical dependency, not supplied by a mod-2 parity
interface and not claimed here to be a checked Lean composition.

I reconstructed the argument independently and did not read any other
review. No author file, export, or Lean source was changed; no Lean build
was run. This is one substantive independent review, not authorization to
self-export. A separate independent review, coverage decision, complete
final packaging, and acceptance of the final bytes remain outside this
verdict.

## 1. Exact theorem and contrary source

For each nonempty coalition S of four players, r(S) is an arbitrary real
payoff vector. Never pays zero, play uses independent private randomization,
and deviations replace a complete behavioral strategy. Set

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i.

The claim is: det Γ<0 and every entry of Γ⁻¹ strictly positive imply one
fixed ordinary uniform-equilibrium payoff. The own singleton vector is
not assumed nonnegative, and all 44 nonsingleton reward coordinates are
unrestricted. There is no uniform bound on the eventual discount threshold
as those rewards vary, and none is needed.

Under no UE, the SAME-table declaration
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
in `Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`
supplies `all_punishmentNormal`. I read its statement and construction:
it retains the literal incoming reward, with punishment values at most the
own singletons. Its separately selected full-support packet is NOT used
to infer anything about every discounted equilibrium.

With c_i=min(0,P_i), where P_i is the original punishment value, the exact
auxiliary table is r'_i(S)=r_i(S)−c_i. Hence

    a_i=s_i−c_i≥0,       Γ'_ij=Γ_ij.

If a=0, every s_i=c_i≤0 and all-Never is an exact original terminal Nash
profile: a unilateral finite quit only obtains its nonpositive singleton.
Thus the contrary branch has a≥0 and a≠0. This is a deduction inside the
proof, not a hidden restriction on the raw theorem.

The shift is NOT asserted to preserve arbitrary terminal deviations or
Never payoffs. Returning to the original game uses the exact auxiliary-
germ consumer, including its punishment-completed sole-owner branch.

## 2. Discounted algebra and the whole cube

Let d=1−λ, α_i=∏_(j≠i)(1−q_j), C=∏_j(1−q_j), and use the candidate's
opponent-set expectations A_i,Q_i. At the live state the stage payoff is
zero and the next absorbed state pays r', so the normalized discounted
value is exactly

    u_i=d R_i/(1−dC),       R_i=q_iQ_i+(1−q_i)A_i.

The denominator L=1−dC is strictly positive when 0<λ<1. Direct expansion
gives

    L(Q_i−A_i−α_i u_i)=(1−dα_i)Q_i−A_i=D_i.

In particular −A_i, not −dA_i, is correct. Since multiplying the two root
endpoints by d>0 preserves preferences, the complete Bellman conditions
are exactly the candidate's signs at q_i=0, in (0,1), and at q_i=1.
The clipped map q↦clip(q+D) has precisely those fixed points, including
upper faces, corners, mixed-support faces, and zero endpoint differences.

This does not identify a Nash equilibrium of an arbitrary finite timing
menu with a discounted equilibrium. The positive-discount Bellman problem
against stationary opponents is a one-live-state discounted control problem;
its two pure Bellman comparisons control every adaptive behavioral response.

The values are uniformly bounded for the FIXED auxiliary table: if its
reward bound is M', then |R_i|≤M'(1−C), and

    |u_i|≤M' d(1−C)/(λ+d(1−C))≤M'.

This supplies the compact value subsequences used later even at the
all-Continue corner; no denominator bounded away from zero was assumed.

## 3. Endpoint-preserving curve selection really suffices

Suppose fixed points with λ_n→0 have a subsequential limit q_*≠0, and
select a convergent bounded value subsequence u_n→u_*. The graph with
0<λ<1, cube constraints, the positive-denominator value equation, and all
boundary Bellman signs is semialgebraic with real coefficients. Arbitrary
real punishment constants do not change this fact.

Analytic curve selection applies at the SPECIFIED point (0,q_*,u_*),
not at an unrelated existential endpoint. The classical statement used is
Coste, *Real Algebraic Sets*, §1.5, Theorem 1.15: a point in the closure of
a semialgebraic set is reached by an analytic Nash arc whose positive
branch lies in the set. I checked this primary exposition's theorem
statement and its Puiseux explanation in the author-text/ICTP copies:
[Coste's notes](https://perso.univ-rennes1.fr/michel.coste/polyens/RASroot.pdf),
[ICTP copy](https://indico.ictp.it/event/a02455/session/2/contribution/2/material/0/0.pdf).

Here is the complete small adapter that final packaging should make
literal. Along that arc, at the live state put Quit probability q_i and
Continue probability 1−q_i, and value u_i. At every absorbed state fix
arbitrary constant actions, for example all Continue, and its value r'(S).
The absorbed Bellman equations are identities; the live Bellman equations
are exactly those in §2. Thus this analytic assignment lies in the FULL
polynomial Bellman solution set and has the desired live endpoint q_*.
The graph explicitly retains positive discount, avoiding the arbitrary
real-discount variety issue flagged by `Bellman/SignCell.lean`.

If the arc's discount coordinate is ℓ(t), positivity on the right and
analyticity give ℓ(t)=t^k b(t), k≥1, b(0)>0. The analytic map
t↦t b(t)^(1/k) has positive derivative at zero; its local analytic inverse
normalizes the discount to an exact power without changing the endpoint.
This matches `exists_analyticBellmanGerm_of_positiveCoordinateArc`,
`exists_analyticBellmanGerm_of_powerCurve`, and
`analyticBellmanGermOfPowerCurve_endpoint` in
`VanishingDiscount/Bellman/Germ.lean`. I also checked
`HasPositiveCoordinateAnalyticArcAt.toHasAnalyticPowerCurveAt` in
`MathUE/AnalyticCoordinateCurve.lean` and the leading-coefficient/inverse
construction in `MathUE/AnalyticPowerNormalization.lean`.

The result is a germ of the exact auxiliary quitting game with that same
jointly absorbing endpoint. The generic-in-player-type declaration
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint` in
`Quitting/Classification/ThreePlayer/AuxiliaryShift.lean` then gives a
uniform-equilibrium payoff of the ORIGINAL game. Its directory name does
not impose a three-player hypothesis.

I checked its shift identities, endpoint punishment floor, and final
one-phase `isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle`
application in `Quitting/Punishment/CompletedCycle.lean`. If an owner has
unit deleted survival, joint absorption forces that owner to be the sole
active quitter; its displayed original value is its singleton, and the
endpoint floor gives the punishment admissibility needed by the completed
cycle. That consumer supplies terminal approximants at every error and
the fixed uniform payoff, including Never deviations. It does NOT assert
that the bare stationary sole-quitter law is already an original exact
equilibrium. Thus no support-size or nonnegative-singleton condition is
smuggled into this consumer.

Consequently no UE forces q→0 for EVERY small-discount fixed point.
Unconditional existence of SOME analytic germ would not prove this step.

## 4. Uniform rescaling, including all boundary support limits

For an arbitrary sequence of fixed points tending to zero, put
t=Σq_i>0, μ=q/t, and ρ=λ/(λ+t). At q=0 the coordinate D_i=λa_i, so
a≠0 indeed excludes all-Continue at every positive discount.

Uniform product expansion at this fixed table gives

    R=t(a+Γμ)+O(t²),       1−C=t+O(t²).

Dividing by λ+t is safe even when t/λ diverges: t²/(λ+t)≤t→0 and
λt/(λ+t)≤t→0. Hence every compact subsequential limit satisfies
u_*=(1−ρ)(a+Γμ). Because q_i<1 eventually, Continue is optimal, so
u_*≥a. Each μ_i>0 makes q_i>0 eventually; that coordinate is mixed and
u_i=dQ_i, giving u_*i=a_i.

The inverse-positive cone implication is exact:

    μ≥0, μ≠0, Γμ≥0 ⇒ μ=Γ⁻¹(Γμ)>0.

The vector Γμ is nonzero by invertibility. Strict entrywise positivity of
the inverse, not just nonnegativity, supplies EVERY positive coordinate.
The cases ρ=1 and ρ=0 are both excluded: the first would force a=0; after
cone positivity and full pinning, the second would force Γμ=0. Therefore

    q/λ→h_*=Γ⁻¹a>0

uniformly over the entire fixed-point set. Compact subsequences establish
this uniform statement without a common analytic branch or Puiseux order.
In particular all fixed points are strictly interior for sufficiently
small λ; none of the boundary support strata is discarded beforehand.

## 5. Implicit uniqueness and the integer index

D(λ,λh)/λ is analytic at λ=0: D(0,0)=0 and polynomial substitution makes
every monomial divisible by λ. Its limiting map is a−Γh, with derivative
−Γ. The ordinary implicit function theorem applies at h_* because Γ is
invertible. It gives one local zero branch. Uniform localization from §4
places EVERY equilibrium in that same neighborhood, so local uniqueness
really becomes global uniqueness in the cube. No regularity of a generic
normal-form game or survival of a selected component is assumed.

Near the unique interior fixed point, clipping is inactive. Differentiating
the rescaled identity gives ∂_qD=∂_h(D(λ,λh)/λ)→−Γ. Thus the displacement
Id−F=−D has derivative tending to Γ and local degree −1.

For the global degree, homotope F inside the cube to its center. At every
positive homotopy time the boundary maps strictly into the interior, and
at time zero there is no boundary fixed point by the proved localization.
The displacement therefore has global degree +1, as does Id minus the
constant center. Excision/additivity equates it with the sole local degree,
contradicting −1. The cube map is continuous globally and smooth near the
zero; global smoothness of clipping is unnecessary.

I checked the primary topological expositions
[Govindan, *The Index of Nash Equilibria*](https://eventos.cmm.uchile.cl/dgames2017/wp-content/uploads/sites/40/2017/01/Govindan_Chile.pdf)
and [McLennan, *Advanced Fixed Point Theory*](https://eventos.cmm.uchile.cl/dgames2017/wp-content/uploads/sites/40/2017/01/McLennan_prosper_chile_all-1.8.17.pdf),
specifically local orientation, normalization, additivity and homotopy.
The proof uses ordinary INTEGER Brouwer degree, not invariance between
different Nash-map representations. Mod-2 parity sees −1 and +1 as equal
and is insufficient. I make no claim that the repository already contains
the required checked integer local/global degree interface. That is a
formalization dependency, not a mathematical gap in the argument.

## 6. Exact falsification attempts and raw-class boundary

The displayed Γ, inverse B and determinant −3 check exactly. So do the
positive-determinant paired matrix and its strictly positive inverse.
The latter changes the local orientation to +1, so this argument would
not contradict the global index. No theorem was inferred after dropping
the determinant sign.

I additionally tested the complete formulas on the displayed Γ with
a=(0,2,0,3) and independently chosen signed nonsingleton rewards. Symbolic
expansion checked the D identity and the limiting map a−Γh. Exact rational
tests used all q∈{0,1/3,1}^4 and λ∈{1/7,3/4}, checking both the sign
identity and clipped-fixed-point equivalence at each player: 1296 checks,
plus eight symbolic identities. The zero singleton coordinates still give
B a=(86/3,23,14,20)>0. These are identity and boundary tests, not numerical
evidence replacing the all-equilibrium proof.

A more pointed falsifier of the tempting MATRIX-ONLY localization claim is
the exact completion

    r'_i(S)=a_i+Σ_(j∈S)Γ_ij       for every nonempty S.

Here direct calculation gives

    D_i=α_i[λa_i−(1−λ)(Γq)_i].

With a=(1,0,0,0), λ=1/101, the displayed negative-determinant matrix has
the interior equilibrium q=(3/50,1/20,3/100,1/25), on the exact small branch
q=λ/(1−λ)B a. Its local displacement degree is −1. BUT every root with
at least two sure quitters also has D=0 in every coordinate, at every
discount. In particular all-sure is a remote absorbing equilibrium, and
the original all-sure date-zero law is exact terminal Nash in this test.
This does not refute the theorem: it confirms that selecting the small
germ cannot replace the no-UE localization of ALL equilibria. The remote
branches are exactly what the absorbing-endpoint consumer may use.

For the bounded coverage statement, B>0 is strictly copositive, so the
checked strict-copositivity Q theorem applies to B. Swapping variable and
slack through Γ=B⁻¹ gives standard Q for Γ with the stated signs.
Invertibility and B>0 exclude homogeneous complementary nonnegative
vectors. These checks agree with `LCP/MatrixClasses.lean` and
`MathUE/LinearProgramming/CopositiveQCorollaries.lean`.

The principal {0,1,3} of the displayed Γ satisfies Tx≥0, x≥0 only at
x=0: its three row inequalities give x_1≥3x_2/2, x_2≥x_0, x_0≥x_1.
Thus it is neither standard Q nor homogeneous-projective. The full matrix
is not projective Q-bar. Its negative-edge graph has no Hamiltonian cycle
(checked over all 24 orderings), so it also escapes the precise signed-
four-cycle hypotheses of the earlier inverse-positive producer. This
supports non-subsumption by those named matrix consumers only; it is not
a worldwide priority claim or a proof that every completion escapes all
other sufficient classes. Broader coverage is a separate gate task.

## 7. Required handoff precision and final assessment

No mathematical repair is requested. In final packaging retain the full
Bellman-assignment lift from §3, the bounded-value argument, all boundary
signs, the distinction between punishment translation and Never, and the
explicit integer-degree dependency. The prescribed-endpoint curve is an
ordinary classical input with checked constructors; it is not supplied by
the unrelated unconditional some-germ theorem. No current source theorem
was treated as proving the desired localization or the new index escape.

Subject to the stated classical inputs, this proof covers every arbitrary-
signed Fin4 reward table satisfying the TWO raw matrix hypotheses and
reaches the full behavioral, fixed-payoff uniform-equilibrium endpoint.
It does not establish stationary exact equilibrium, a quantitative finite-
menu algorithm, the inverse-positive positive-determinant chamber, or the
general quitting conjecture. The remaining independent and final-byte
gate is separate from this PASS.

## 8. Final combined packet: exact-byte acceptance

Final packet read in full, all 693 lines:
[Inverse-positive singleton matrices and discounted-index escape](../notes/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md).
Accepted SHA256:
`d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`.

**Verdict: PASS for the independently reviewed strict core and PASS for
faithful integration of the boundary extension. No mathematical repair,
hidden source assumption, or source-link objection remains in this review.**

The final raw statement is now det Γ<0 and Γ⁻¹≥0, with arbitrary signed
own singletons and all 44 nonsingleton coordinates unrestricted. I am the
author of the nonnegative-inverse approximation and reward-closedness
lemma. Consequently my check of its integration is NOT an independent
review of that lemma. Independent boundary-extension validation belongs
to the separately assigned CODEX_TARSKI_PREMIUM and CODEX_RADO_BOUNDARY
reviews; this acceptance does not replace either review or pre-judge its
verdict. I did not read their reports while doing this final check.

### 8.1 Independently rechecked strict core

Sections 2–6 retain precisely the original theorem's contrary assumption
and its entire-equilibrium quantifier. The source normality belongs to
the literal incoming table. The bounded discounted values, explicit full
Bellman-assignment lift, prescribed closure point, and exact-power
reparametrization now supply the packaging details requested in §§2–3
above. Upper support faces and indifferent pure actions remain in the
graph. The endpoint consumer returns an ORIGINAL-game fixed uniform
payoff, including its punishment-completed sole-owner case; it is not
replaced by a stationary or finite-menu assertion.

I again checked the first-order value formula and both excluded endpoints
ρ=0 and ρ=1. Strict positivity of Γ⁻¹ yields all positive leading shares;
compact subsequences then give localization of EVERY fixed point at the
same positive rescaling. This justifies using implicit local uniqueness
as global uniqueness. The displacement derivative tends to Γ, so the
local integer degree is −1, whereas the explicitly boundary-safe cube
homotopy gives global degree +1. The retained remote-sure-equilibrium
fixture correctly falsifies matrix-only localization, not this contrary-
assumption proof. No selected-germ substitution has entered the final text.

The current declarations in `FullSupportProjectiveQBarResidual.lean`,
`ThreePlayer/AuxiliaryShift.lean`, `Bellman/Germ.lean`,
`MathUE/AnalyticCoordinateCurve.lean`, and the full-behavioral min-max
definitions were re-inspected for this final check. The ordinary classical
curve-selection and degree inputs are the same primary mathematical
inputs checked in the initial review, not newly asserted Lean theorems.

### 8.2 Faithful boundary-extension integration

Section 8 faithfully includes my frozen source note at SHA256
`cd4f3064d224e570e8b9c221578af6b96edc10370d01a80a9f44ddaf9547a501`.
It keeps the precise zero-diagonal-preserving perturbation Γ−ε(J−I), the
norm-convergent inverse series, second-order entry positivity for n≥3,
and preservation of the determinant sign. The n=2 density exception is
not misrepresented as an equilibrium nonexistence result. The raw Fin4
operation changes only twelve off-own singleton rewards, keeping own
singletons, nonsingletons, Never, observations, and all independent
behavioral strategy spaces fixed.

The reward estimate is still uniform over EVERY prescribed and deviated
profile. Taking all response suprema, without assuming attainment, gives
the full-regret bound 2δ. The all-errors semantic consumer therefore
selects one fixed payoff at the limiting table, without jointly selecting
targets or equilibrium laws at the approximating tables. I re-read both
directions in `Terminal/TargetTail/TerminalUniformPayoffSelection.lean`
and the fixed-target quantifiers in
`ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`.

The final text does not extend the strict cone implication to a matrix
with zero inverse entries, assert localization at that boundary table,
presume preservation of normality under arbitrary reward changes, or
assert an unconditional theorem for all player counts. Thus the material
strengthening from the original packet is exactly the proved nonnegative-
inverse boundary, not an unreviewed new index argument.

### 8.3 Scope, source paths, tests, and handoff

Both embedded exact SymPy test blocks were run successfully. All four
relative Markdown links and all sixteen explicit Lean source paths resolve.
The bounded matrix-consumer comparisons and the covering-walk caveat
retain their original scope; no exclusion of every reward-dependent class
or longer singleton word is claimed.

I checked the named parity definitions in
`Research/Topology/BoxComplementarityCubicalSperner.lean` and
`Research/Topology/BoxComplementaritySpernerLocalCount.lean`: the former
supplies oddness and the latter takes values in `ZMod 2`. The handoff
correctly says these do not distinguish −1 from +1. It leaves the actual
integer-degree composition and prescribed-endpoint curve connection as
formalization tasks, not as checked infrastructure supplied by naming an
existing declaration.

No Lean build was run. The candidate, the extension source, and all exports
remain unchanged. This final-byte acceptance preserves the independence
of the strict-core audit, records the limited authorship status of the
extension-integration check, and leaves the independent extension gate
and coordinator placement decision separate. No further repair is
requested from the author by this reviewer.
