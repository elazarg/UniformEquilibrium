# Independent review: inverse-positive discounted-index escape

Reviewer: CODEX_TARSKI_PREMIUM. Date: 2026-09-08.

Reviewed author source:
[INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE](../notes/CODEX_FRECHET_CYCLE__INVERSE_POSITIVE_DISCOUNTED_INDEX_ESCAPE.md),
SHA `0d1a77885542d00559e3a146abc9e40bd1f47884b81be73c571a062d7419702a`.

Status: **mathematical PASS**, including the unrestricted original-game UE
consumer. No mathematical repair requested. This is an independent ordinary
proof/source audit, not a Lean check. I did not consult NOETHER's review.
The coverage conclusion is bounded as stated in §5 below; it does not exclude
longer repeated-owner singleton calendars or establish worldwide priority.

## 1. Claim and complete strategic scope

For an arbitrary real Fin4 reward table with Never payoff zero, put

    s_i=r_i({i}),       Γ_ij=r_i({j})−s_i,       Γ_ii=0.

The claim is UE existence when det Γ<0 and Γ⁻¹ is strictly entrywise positive.
The four own singletons and all 44 nonsingleton coordinates are unrestricted.
The conclusion is one fixed uniform-payoff target for the original table,
against arbitrary behavioral deviations. It is not merely stationary Nash
existence in a translated or discounted game.

The argument below proves precisely this claim. The auxiliary translation
is used only through its checked original-game consumer; it is never
identified with a strategically equivalent terminal translation.

## 2. Independent reconstruction of the discounted argument

Assume no original UE. The Fin4 residual declaration quoted in §6 supplies
same-table punishment normality P_i≤s_i. With c_i=min(0,P_i), a_i=s_i−c_i,
we have a≥0. If a=0, all s_i≤0; every unilateral response against all Never
has payoff at most max(0,s_i)=0. Thus all Never is exact terminal Nash and
gives UE. Consequently a≠0 in the contrary branch.

Use r'=r−c only on absorbing rewards. For d=1−λ, 0<λ<1, and a product
hazard q, let α_i be opponent Continue mass and C=(1−q_i)α_i. Let A_i
be expected reward from nonempty opponent quitting sets when i Continues,
and Q_i the expected reward when i Quits, both at r'. Then

    R_i=q_i Q_i+(1−q_i)A_i,
    u_i=d R_i/(1−d C),
    D_i=(1−d α_i)Q_i−A_i.

Direct expansion verifies

    (1−d C)(Q_i−A_i−α_i u_i)=D_i.

In particular the last term is −A_i, not −d A_i. Since λ>0, every
denominator is positive. Lower, mixed, and upper Bellman conditions are
respectively D_i≤0, D_i=0, and D_i≥0. Thus clipping q+D to the cube
gives exactly the stationary discounted Nash fixed points, including all
upper faces. Brouwer supplies one for every λ. The discounted Bellman
conditions control arbitrary behavioral responses in this finite-state
discounted problem, not only constant-hazard alternatives.

### 2.1 Every endpoint is localized, not merely a selected germ

The fixed-point graph in (λ,q,u) is semialgebraic after clearing its positive
denominator. Values are uniformly bounded by the auxiliary reward bound.
If λ_n→0 had fixed points tending to q_*≠0, analytic semialgebraic curve
selection at THAT closure point produces an arc with the same (q_*,u_*).
Its positive discount coordinate has positive leading coefficient and
finite order. The local change of parameter making it exactly t^k is
analytic and preserves the endpoint.

For completeness, this can be lifted to the full Bellman assignment:
assign the absorbing-state values their fixed rewards r', choose constant
action probabilities there, and use the selected q and u at the live state.
Those absorbing-state equations are identically satisfied because actions
do not matter after absorption. Hence this is the prescribed-endpoint input
to the actual germ constructor, not a new unrelated existential selection.
The selected q_* is jointly absorbing. The auxiliary absorbing-endpoint
consumer then gives original UE, a contradiction. Thus ALL fixed points
approach zero uniformly as λ→0.

The primary analytic input is Coste, *Real Algebraic Sets* (2003),
Theorem 1.15, the analytic version of curve selection at a specified closure
point, not just a punctured analytic arc with no endpoint regularity.
[Primary text](https://indico.ictp.it/event/a02455/session/9/contribution/6/material/0/0.pdf).
This ordinary topological input is distinct from the checked conditional
germ constructors; no claim of an already-composed Lean proof is made.

### 2.2 Uniform first-order localization

At q=0, D=λa≠0, so t=Σq_i>0 at every fixed point. Along ANY small-discount
sequence extract μ=q/t→μ_* in the simplex, ρ=λ/(λ+t)→ρ_*, and u→u_*.
Uniform product expansions give

    R=t(a+Γμ)+O(t²),       1−C=t+O(t²),
    u_*=(1−ρ_*)(a+Γμ_*).

The remainders divided by λ+t vanish even if t/λ diverges. Eventually all
q_i<1. Continue optimality together with u=d(A+αu) yields u_i≥dQ_i, hence
u_*≥a. If μ_*i>0, both actions are used eventually and u_i=dQ_i, hence
u_*i=a_i.

The case ρ_*=1 would force a=0. Otherwise

    Γμ_*≥[ρ_*/(1−ρ_*)]a≥0.

Writing B=Γ⁻¹>0, invertibility ensures Γμ_*≠0. Therefore
μ_*=BΓμ_*>0, all four coordinates pin, and

    (1−ρ_*)Γμ_*=ρ_*a.

The case ρ_*=0 is impossible by invertibility. It follows that

    q/λ→Ba=:h_*>0

uniformly over the entire fixed-point set. The compact (μ,ρ,u) argument
also excludes unbounded rescaled hazards. This is the crucial universal
source step; it is not implied by the existence of some full-support packet.

### 2.3 The degree contradiction

H(λ,h)=D(λ,λh)/λ extends analytically across λ=0, with
H(0,h)=a−Γh and derivative −Γ. Nonsingleton first-order contributions
cancel in this expression. I checked that cancellation symbolically with
independent collision coefficients, in addition to the direct expansion.

The implicit function theorem produces a unique local zero h(λ) near Ba.
Uniform localization puts every fixed point there and makes it interior.
Thus there is exactly one cube fixed point for every sufficiently small
positive λ. Near it the displacement of the clipped map is −D. Its
Jacobian tends to Γ, so its local degree is sign det Γ=−1.

The global displacement degree is +1: linearly homotope the cube map to
the constant center. At every positive homotopy time the image is strictly
inside the cube, while at time zero there is no boundary fixed point.
Homotopy invariance and additivity therefore contradict the single local
degree −1. This establishes the original theorem.

No finite-normal-form equilibrium-index invariance is being applied to a
rational payoff map. The explicit cube homotopy supplies the needed global
degree directly. The author's cited
[Govindan primary exposition](https://eventos.cmm.uchile.cl/dgames2017/wp-content/uploads/sites/40/2017/01/Govindan_Chile.pdf)
has the consistent displacement-index convention.

## 3. Why the endpoint is an actual original-game UE

I read the literal proof of
`isUniformEquilibriumPayoff_of_auxiliaryGerm_absorbingEndpoint` in
`UniformEquilibrium/Quitting/Classification/ThreePlayer/AuxiliaryShift.lean`.
Its domain is an arbitrary finite player type. It translates the endpoint
fixed point and root-Nash inequalities to r, then invokes
`isUniformEquilibriumPayoff_of_punishmentAdmissibleCycle` in
`UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` for a one-phase
cycle. That compiler returns a fixed uniform payoff through actual terminal
approximate profiles.

The noncontracting-deleted-clock boundary is explicitly handled: if all
opponents Continue surely, joint absorption implies this owner quits with
positive probability, the fixed-point equation pins its target to s_i,
and the auxiliary endpoint target dominates its behavioral punishment
value. Thus a sole absorbing owner is not incorrectly treated as having
a contracting deviation tail. Signed s_i and zero a_i coordinates cause
no omission. Arbitrary positive a somewhere suffices for the localization.

An immediate strengthening of the SAME proof is valid in any finite player
count under supplied all-player punishment normality P≤s. Fin4 is used
only to derive that property under no UE. The local displacement derivative
is Γ in every dimension: the two minus signs have already canceled.
This does not assert an unconditional arbitrary-finite-player class.

## 4. Exact falsification checks

I independently reproduced the displayed inverse, det Γ=−3, and the
identity ΓB=I. I also reproduced det Γ⁺=45 and its strictly positive inverse.
The positive-determinant example shows failure of THIS negative-index
contradiction, not failure of UE existence under inverse positivity alone.
Accordingly the sentence “the determinant sign cannot be discarded” should
be read as “cannot be discarded from this index argument”; strategic
necessity of the sign has not been proved.

The specified-endpoint and entire-set quantifiers were challenged explicitly
above. No selected full-support packet, cap-minimum hypothesis, or auxiliary
translation of Never was used. No build was run and no Lean file changed.

## 5. Raw-class coverage: positive distinction and limits

There is a genuine new sufficient raw hypothesis relative to the named
producers audited here, not merely a payoff verifier. Its output covers
every completion of the singleton cylinder in §1. The following distinctions
are exact; “new” here does not assert a complete literature classification.

1. For EVERY B>0, B is strictly copositive and therefore standard Q.
   Solving its LCP at right-hand side −Bz transfers standard Q to Γ=B⁻¹:
   if w≥0 and x=B(w−z)≥0 are complementary, then w=z+Γx. Conversely,
   homogeneous feasibility for Γ is impossible, since x=Bw>0 for any
   nonzero w=Γx≥0 forces w=0 by complementarity. Thus full non-Q and
   homogeneous-singleton consumers do not subsume this region.

2. For the displayed Γ, the principal T on {0,1,3} is

       T=[0 2 −3; −3 0 3; 3 −3 0].

   Tx≥0 and x≥0 imply x_1≥3x_2/2, x_2≥x_0, x_0≥x_1, hence x=0.
   There is no homogeneous simplex solution and no LCP solution at
   right-hand side −1. Hence T is not projective Q, and Γ is not Q-bar.
   This defeats the CURRENT unconditional projective-Q-bar Snell consumer,
   not merely an obsolete normality-conditional version. Also
   T(8/3,3,7/3)=−1, excluding semimonotonicity and copositivity of T
   (and of the ambient matrix). A P/P₀ or principal-copositive argument
   cannot restore the missing Q-bar property here.

3. The six reciprocal sums are −1, −2, 0, 4, 0, 1 in lexicographic pair
   order. Thus neither uniform nonpositive nor uniform nonnegative
   reciprocal-sign class contains the example. The checked integral-
   tournament matrix class already implies projective Q-bar, so it does
   not contain this example either.

4. The negative graph has edges 0→3, 1→0, 2→0, 3→1, 3→2. I enumerated
   all 24 labelings; none has a negative Hamiltonian cycle. This excludes
   the signed-four-cycle producer, its relabelings and positive diagonal
   rescalings, and the cyclic open-sign specialization. More generally,
   in a balanced singleton calendar that visits each owner once and has
   phase values ≥s, a positive-hazard transition from owner i to j forces
   Γ_ij≤0 by the owner-i recursion and the next phase's floor. Here no
   off-diagonal entry vanishes, so the required Hamiltonian edges would
   all be strictly negative.

5. Any absorbing singleton-only profile whose actual payoff U≥s has
   U−s=Γμ for its singleton distribution μ. The inverse-positive cone
   calculation forces μ>0. Thus proper-support ambient singleton cycles
   with that floor cannot account for these matrices. This observation
   is not extended to a profile with positive Never mass and signed s:
   there the extra −Pr(Never)s term matters.

6. Longer repeated-owner calendars are NOT excluded. The negative graph
   admits the covering closed walk 0,3,1,0,3,2. A supplied balanced-cycle
   verifier for some longer word could cover particular completions;
   no proof excluding all such words is given. Absence of a Hamiltonian
   cycle must not be advertised as absence of all singleton calendars.

Reward-dependent mechanisms can cover some completions. For example the
signed-influence theorem constrains membership toggles over all backgrounds,
and paired, weak-exclusion, and single-anchor criteria impose additional
reward inequalities. Those cannot simply be inferred from this cylinder's
unrestricted nonsingleton coordinates. I do not claim every completion is
outside their union. The exact non-subsumption evidence is the matrix and
once-per-owner comparisons above, not a universal nonexistence assertion
about alternative equilibrium constructions.

## 6. Source correspondence and remaining scope

Additional named declarations inspected:

- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`,
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`:
  only its same-table `all_punishmentNormal` field is consumed.
- `exists_analyticBellmanGerm_of_positiveCoordinateArc`,
  `exists_analyticBellmanGerm_of_powerCurve`, and
  `analyticBellmanGermOfPowerCurve_endpoint`,
  `UniformEquilibrium/VanishingDiscount/Bellman/Germ.lean`:
  full assignment and prescribed endpoint, with the ordinary curve input
  supplied above, not inferred from unrelated germ existence.
- `isStandardQ_of_strictlyCopositive`,
  `MathUE/LinearProgramming/CopositiveQCorollaries.lean`, and
  `isStandardQ_iff_isStandardQMatrix`,
  `UniformEquilibrium/Quitting/Classification/LCP/CopositiveQBridge.lean`.
- `isProjectiveQMatrix_iff_standard_or_homogeneous`,
  `UniformEquilibrium/Quitting/Classification/LCP/MatrixClasses.lean`, and
  `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell`,
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
- The actual raw hypotheses in
  `UniformEquilibrium/Quitting/Cycles/SignedFourCycleRewardAdapter.lean`,
  `Cycles/CyclicSingletonOpenSignProducer.lean`,
  `Classification/LCP/FinFourIntegralTournamentBalancedSingleton.lean`,
  `Classification/Existence/FiniteOddBlockerCore.lean`, and
  `Stationary/SignedInfluenceCycleBalance.lean` were inspected for the
  bounded coverage check; they are not ingredients of the index proof.

The proof does not need the three-dimensional geometric alternative from
Solan's 1999 paper. I have not independently certified the author's complete
historical page-by-page description of that alternative. The essential
literature assumptions used in this proof are the specified-endpoint
analytic curve selection and elementary Brouwer degree facts audited above.

Original theorem settled by this review: PASS. A weakening to entrywise
nonnegative inverse is a separate perturbation question, not part of these
frozen bytes or this verdict. No export or author edit was made.

## 7. Final combined packet: exact-byte acceptance

I read all 693 lines of the author-frozen final mathematical packet
[INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE](../notes/INVERSE_POSITIVE_SINGLETON_MATRIX_DISCOUNTED_INDEX_ESCAPE.md),
SHA `d9bdaba02feaaab171c943c1aeb1f19cec3dcb3fa9c326817a071eeb01d474eb`,
and accept these exact bytes with **no mathematical or scope objection**.
The source hash was rechecked after reading through EOF. No author or
export edit was made.

This final acceptance includes the stronger Fin4 hypothesis Γ⁻¹≥0.
The zero-diagonal approximation and same-law full-regret reward closure
are fully included, not inferred merely from the old strict statement.
The separately frozen extension also has my independent exact-byte
[PASS review](CODEX_NOETHER_SUPPORT__NONNEGATIVE_INVERSE_APPROXIMATION_ON_ZERO_DIAGONAL_TABLES__BY_CODEX_TARSKI_PREMIUM.md).
The final packet correctly does NOT apply the strict cone/localization
argument directly to a boundary matrix with zero inverse entries.

Additional combined-byte checks:

- The explicit uniform auxiliary value bound is valid even as the
  denominator tends to zero. The full Bellman lift includes all 15
  absorbing states and preserves the specified endpoint. The positive
  analytic discount coordinate is reparametrized to an exact integer
  power without changing that endpoint.
- I opened the final packet's exact Coste primary URL and verified
  Theorem 1.15 at that location. It supplies the analytic arc at the
  selected closure point over real coefficients; it is not an unrelated
  germ-existence statement.
- The original-game consumer explicitly retains the sole active owner's
  Never/punishment branch and returns the fixed-target, all-large-horizon,
  unrestricted-behavioral conclusion. I checked the literal definition
  `IsUniformEquilibriumPayoff` against the final statement.
- The new additive completion satisfies the displayed formula (17).
  Independent enumeration of every opponent coalition passed 972 exact
  root-coordinate checks on three hazard values and three discounts.
  Two sure quitters indeed make every α_i zero; the resulting remote
  equilibria falsify matrix-only localization, not the no-UE argument.
  The added mixed-zero-a arithmetic and the inverse boundary example
  also reproduce exactly.
- The handoff correctly demands INTEGER degree. I checked the two named
  Research interfaces: one concludes an odd count, and the other's
  codomain is literally `ZMod 2`. Neither distinguishes −1 from +1.
  No existing integer-degree Lean proof is falsely claimed.
- The determinant-sign caveat now explicitly concerns the argument,
  not strategic necessity. The longer repeated-owner covering walk and
  bounded-novelty restrictions remain explicit. No unconditional
  arbitrary-player-count theorem, exact stationary-equilibrium claim,
  or effective finite-calendar selector was added.

Final combined verdict: mathematical and exact-byte PASS. The ordinary
proof and actual UE consumer are complete at the stated scope; Lean
implementation and promotion are separate work.
