# Reflection and multi-affine exclusions for full quitting potentials

Authors: the supplied [reflection and multi-affine packet](../gpt/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS.md); mathematical assembly and semantic source audit by CODEX_ALEXANDROV_GATE. The singleton-face and minimum-localization dependencies come from the earlier [shape-exclusion packet](../formalized/QUITTING_POTENTIAL_SHAPE_EXCLUSIONS.md), not from this addendum.

Independent reviews: [Radon reflection review](../feedback/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_RADON_REFLECTION.md), [Bernstein scope review](../feedback/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_BERNSTEIN_REFLECTION.md), [final Radon packet audit](../feedback/REFLECTION_MULTIAFFINE_EXPORT__BY_CODEX_RADON_REFLECTION.md), [final Bernstein packet audit](../feedback/REFLECTION_MULTIAFFINE_EXPORT__BY_CODEX_BERNSTEIN_REFLECTION.md). The [coordinator synthesis](../feedback/REFLECTION_AND_MULTIAFFINE_POTENTIAL_EXCLUSIONS__BY_CODEX_COORDINATOR.md) records the precise normalization and scope repairs.

## Exact statement

Fix a finite player set I of cardinality n ≥ 2. For every nonempty coalition S ⊆ I let r(S) ∈ ℝᴵ satisfy |r_j(S)| ≤ 1 for every j. Put rⁱ = r({i}) and s_i = r_i({i}); assume every s_i ≥ 0. Live and Never rewards are zero. Set

    K = [−3,3]ᴵ,        C = ∏ᵢ [s_i,3].

For v ∈ K and a product root q ∈ [0,1]ᴵ, define its independent coalition probabilities, absorption charge, and successor by

    π_q(S) = ∏ᵢ∈S q_i ∏ᵢ∉S (1−q_i),
    A(q) = 1−π_q(∅),
    F(v,q) = π_q(∅)v + ∑_{S≠∅} π_q(S)r(S).

An exact Nash root against v is an independent one-stage mixed Nash equilibrium with continuation v if everybody continues; its endpoint formulas are given below. The full exact-root inequality is

    P(v) − P(F(v,q)) ≥ A(q)                         (E)

for every v ∈ K and every exact Nash root q against v. In particular it is not an inequality only on chosen roots, a selected orbit, realizable continuation payoffs, or the part of the box above s.

The following ordinary mathematical results hold.

1. No real polynomial of total degree at most two satisfies (E), regardless of the signs or degeneracy of its Hessian.
2. No real multi-affine polynomial satisfies (E). Here multi-affine means affine separately in each coordinate, equivalently a linear combination of the square-free monomials ∏ᵢ∈B v_i for B ⊆ I. For n = 4 this excludes all sixteen such monomials with arbitrary coefficients, including triple and four-coordinate interactions.
3. Suppose P is continuous on K, differentiable on an open neighborhood of C, and satisfies (E). For every global minimum a of P on K, define δ = minᵢ(a_i−s_i). Then δ > 0, and there are x ∈ C with at least one x_i = s_i and d = x−a such that

       2x−a ∈ K,       ∇P(x)·d ≤ −δ/2 < 0.         (RR)

   The segment a+td, 0 ≤ t ≤ 2, lies in K. Along that segment P rises and subsequently falls. If P is C³ on an open neighborhood of K, then

       max_{0≤t≤2} D³P(a+td)[d,d,d] ≥ 3δ.           (T3)

   The derivative is directional, not a prescribed mixed partial; its location need not be above s.
4. Let Q be quadratic or multi-affine. If Φ is C¹ on an open interval containing Q(K) and is either nondecreasing or nonincreasing on Q(K), then Φ∘Q does not satisfy (E). Flat parts are allowed.
5. If the rewards and the coefficients of an excluded quadratic or multi-affine polynomial P are rational, then, for every supplied rational 0 < τ ≤ 1/4, there are rational v ∈ K and q ∈ [0,1]ᴵ whose rational exact successor u = F(v,q) lies in K, with A(q) > 0, root regrets at most τA(q), and

       P(v)−P(u) < A(q).

   Thus exact rational enumeration eventually rejects this candidate at that tolerance. The rational root need only be approximately Nash; no denominator bound is asserted.

No standard-Q, R₀, punishment-normality, or strategic realization assumption is needed for these analytic statements. The sign, reward bound, box, and full-root quantifiers above are retained throughout.

## Conjecture-facing change

The named open obligation is the polynomial alternative in
`quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential`.
For a Fin4 table satisfying |r_j(S)| ≤ 1, every s_i ≥ 0, and some s_i > 0, its fixed box is exactly K. Every robust polynomial certificate satisfies (E). Consequently its existing equivalence can be strengthened, without changing the table or tolerance, to

    no uniform-equilibrium payoff
      ↔ no punishment-vector exact Nash root with a sure quitter
         and ∃ rational τ ∈ (0,1/4], ∃ rational polynomial P,
           P is a full robust unit-charge potential on K at τ,
           totalDegree(P) ≥ 3, and P is not multi-affine.          (PC)

Every polynomial in this existential clause also has (RR) and (T3) at every global minimum. Polynomial degree and multi-affinity concern the polynomial after coefficient cancellation, not a syntactic expression with redundant terms.

This is a strict restriction of the actual certificate language: all quadratics, including indefinite ones, and every square-free higher-degree ansatz are removed. These classes are not all quasiconvex, so the earlier quasiconvex exclusion does not establish this restriction. Higher-degree polynomials with repeated-coordinate powers remain unexcluded.

Moreover, existing actual single-pivot normalization and common positive reward scaling send every hypothetical Fin4 counterexample to a table in the stated bounded, nonnegative-singleton class. One then invokes the existing polynomial producer afresh on that scaled table. Thus the restriction loses no hypothetical Fin4 counterexample at the decision level. It does not assert that arbitrary signed-singleton tables satisfy the analytic hypotheses, or transport a previously produced polynomial between fixed boxes.

## Strategic inputs and admission

The analytic theorems quantify over all exact roots; finite Nash existence supplies one wherever the proof needs it. Their annotated values need not be actual continuation payoffs. They assume no strategy, rate, survival schedule, punishment plan, or chronological certificate.

For the decision reduction, the only initial datum is an arbitrary finite Fin4 reward table together with the proposition that it has no uniform-equilibrium payoff. The existing normalization theorem produces a literal single-pivot counterexample. Common scaling uses only its finite reward table. The existing characterization produces the rational tolerance and polynomial from no-UE, and already contains the converse semantic consumer. No additional unproduced strategic input is present.

The missing project capability is therefore an explicit strengthened equivalent polynomial obstruction and its decision-preserving normalization adapter, not a new supplied-object existence class or an exceptional conditional result. The remaining obligation is to settle the surviving higher-degree, non-multi-affine polynomial alternative (or another route to the conjecture).

## Definitions and probability semantics

At each live stage every player privately randomizes between Quit and Continue, independently conditional on the public history. A nonempty quitting coalition is absorbing. The live-stage reward, including the stage whose actions first cause absorption, is zero; subsequent absorbed stages receive r(S). If absorption never occurs, the terminal and live rewards are zero. There is no correlation device or restriction to bounded controllers.

For a player j, write π_{−j,q}(T) for the product probability of T ⊆ I\{j}. The one-stage endpoint values are

    Quit_j(v,q) = ∑_{T⊆I\{j}} π_{−j,q}(T) r_j(T∪{j}),
    Continue_j(v,q) = π_{−j,q}(∅)v_j
                       + ∑_{∅≠T⊆I\{j}} π_{−j,q}(T)r_j(T),
    F_j(v,q) = q_j Quit_j(v,q) + (1−q_j) Continue_j(v,q),
    e_j(v,q) = max(Quit_j(v,q),Continue_j(v,q)) − F_j(v,q) ≥ 0.

Exact Nash means all e_j = 0. Since a mixed deviation is a convex combination of these two endpoints, these are precisely the ordinary one-stage Nash conditions. They are not, by themselves, bounds on an unrestricted behavioral deviation in the infinite game.

A robust edge at tolerance τ ≥ 0 is any triple (v,q,u) with v,u ∈ K, q ∈ [0,1]ᴵ, and, for every j,

    |u_j−F_j(v,q)| ≤ τA(q),       e_j(v,q) ≤ τA(q).

Its charge is A(q). A full robust potential satisfies P(v)−P(u) ≥ A(q) for every such triple. There is no punishment floor or support restriction. An exact root with u = F(v,q) is a robust edge for every τ ≥ 0: the two errors vanish, and u ∈ K by convexity because all rewards lie in [−1,1]ᴵ. This proves the robust-to-(E) implication.

For the semantic corollary, UE(r) means that there exists one fixed target payoff z such that for every ε > 0 there are a behavioral profile σ and H₀ with, for every H ≥ H₀, expected H-stage average payoff γ_H satisfying

    |γ_H(σ)_j−z_j| ≤ ε,
    γ_H(σ_{−j},σ′_j)_j ≤ γ_H(σ)_j+ε

for every player j and every history-dependent behavioral deviation σ′_j. The profile and H₀ may depend on ε; z does not. All assertions use expected payoffs, not pathwise payoff guarantees.

The punishment value μ_j is the infimum over opponent behavioral plans of the supremum of j's terminal expected payoff over all behavioral replies. A player is normal when μ_j ≤ s_j. Every nonnegative s_j implies normality: the plan in which all opponents always Continue caps the best reply at max(s_j,0) = s_j. Conversely, normality does not imply s_j ≥ 0. The finite sure-root alternative is the existence of an exact Nash root against v = μ with some q_i = 1.

## Source correspondence and attribution

The supplied reflection packet is the source of the new reflection, unrestricted-quadratic, multi-affine, directional third-derivative, monotone-transform, and rational-rejection arguments. The earlier stable shape-exclusion packet supplies the older face probe and minimum-localization method; both are proved again below to make this packet self-contained. No external paper theorem is an additional premise, and no publication-novelty claim is made.

The bounded source route was selected through `docs/TOOLKIT.md` and `docs/FRONTIER.md`. The inspected declarations and their uses are:

- `quittingRootSuccessorPayoff`, `quittingRootQuitPayoff`, `quittingRootContinuePayoff`, and `quittingRootSuccessorPayoff_eq_endpointMix` in `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`: the coalition successor and endpoint formulas above.
- `quittingRootCoordinateNashDefect`, its nonnegativity, and `isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero` in `UniformEquilibrium/Quitting/Root/NashDefect.lean`: ordinary nonnegative Nash regret, not absorption-normalized regret.
- `exists_isZeroQuittingRootNash` in `UniformEquilibrium/Quitting/Root/NashExistence.lean`: finite root existence for every annotated tail. No tail-realization assumption occurs in its statement.
- `IsQuittingFloorFreeRobustEdge` and `quittingFloorFreeRobustChargedRelation` in `UniformEquilibrium/Quitting/Projective/RobustChargedRelation.lean`, with `ChargedRelation.IsPotential` in `MathUE/ChargedPathBudget.lean`: all boxed source/root/target triples, absolute Bellman error, ordinary regret, and target potential plus charge at most source potential.
- `quittingBestReplyValue` and `quittingPunishmentValue` in `UniformEquilibrium/Quitting/Stationary/MinMax.lean`; `IsQuittingNormalPlayer` and `isQuittingNormalPlayer_of_singleton_nonneg` in `UniformEquilibrium/Quitting/Classification/AbnormalPlayers.lean`; `HasQuittingPunishmentVectorNashRootWithSureQuitter` in `UniformEquilibrium/Quitting/Classification/InstantPunishmentSureQuitterCharacterization.lean`: the literal punishment, normality, and sure-root definitions used here.
- `quittingGame_not_exists_uniformEquilibriumPayoff_iff_noSureRoot_and_rationalPotential` in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateCharacterization.lean`: the existing producer and equivalence, for Fin4, bound M, all-player normality, and a positive singleton, with certificate box M+2. Its imports are `RobustChargedRelationPolynomialSeparator`, `RobustCapacityFromPacketFailure`, and `PolynomialForwardCertificateConsumer`.
- `quittingGame_not_exists_uniformEquilibriumPayoff_of_noSureRoot_of_rationalPotential` in `UniformEquilibrium/Quitting/Projective/PolynomialForwardCertificateConsumer.lean`: the unrestricted semantic converse, on the identical box M+2.
- `IsSinglePivotSingletonTable` in `UniformEquilibrium/Quitting/Terminal/SinglePivotFiniteMenuSource.lean`: own singleton values are one at the pivot and zero elsewhere. `FinFourSinglePivotNormalization`, `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff`, and `exists_finFour_no_uniformPayoff_iff_exists_singlePivot` in `UniformEquilibrium/Diagnostics/Quitting/FinFourSinglePivotNormalization.lean`: actual no-UE on that literal normalized table is an output, not a premise disguised as a field. The normalization file imports `FinFourSinglePivotActualSource` and `SinglePivotCanonicalConsequences`.
- `IsUniformEquilibriumPayoff` in `UniformEquilibrium/ProofView/Concepts/Stochastic/Equilibrium/Uniform.lean`: a fixed payoff target, expected finite-horizon delivery, and all behavioral deviations.

A narrow quadratic/multi-affine/reflection/third-derivative search in the Projective certificate subtree found no declaration implementing these new exclusions. The implemented source equivalence is reused, not re-exported as new mathematics. The independently reviewed older shape results are a mathematical dependency, not a claim of new Lean coverage. No source file or Lean declaration is changed by this packet.

## Proof

### 1. Collision-adjusted singleton probe

Fix x ∈ C with x_i = s_i. For j ≠ i put Δ_j = r_j({i,j})−r_j({i}). Define d_i = 0 and

    d_j = max(Δ_j,0) if x_j < 3,
    d_j = 0          if x_j = 3.

For sufficiently small 0 < h < 1, take the root with q_i = h and all other q_j = 0, and set

    vʰ = x + h d/(1−h),
    uʰ = (1−h)vʰ + h rⁱ.

The source is boxed: the nonzero corrections are nonnegative and occur only at coordinates strictly below 3, so finiteness gives a common sufficiently small range of h. The successor is boxed by convexity. Player i is indifferent because vʰ_i = s_i. For j ≠ i with x_j < 3, Continue minus Quit is

    (1−h)(x_j−s_j) + h(max(Δ_j,0)−Δ_j) ≥ 0.

For a frozen coordinate x_j = 3 it is

    (1−h)(3−s_j)−hΔ_j > 0

for all sufficiently small h, since 3−s_j ≥ 2 and |Δ_j| ≤ 2. Thus this is an exact Nash root and A(q) = h. The upper-coordinate freeze is essential for keeping vʰ in K.

Since vʰ = x+hd+O(h²) and uʰ = x+h(d+rⁱ−x), differentiability at x and (E), divided by h and followed by h ↓ 0, give

    ∇P(x)·(x−rⁱ) ≥ 1.                              (F)

Continuity of the gradient is not used. This is the older face inequality, now obtained from the full exact-root relation including upper-coordinate boundary points.

### 2. Location of every global minimum

Continuity and compactness give a minimum a ∈ K. Finite Nash existence gives an exact root against a. Its successor is in K, so minimality and (E) imply A(q) = 0. Therefore every q_i = 0. The Nash conditions for all Continue are a_i ≥ s_i for every i; hence a ∈ C.

If some a_i = s_i, (F) gives ∇P(a)·(rⁱ−a) ≤ −1. But a+t(rⁱ−a) lies in K for 0 ≤ t ≤ 1, and global minimality makes its right derivative at t = 0 nonnegative. This is a contradiction. Consequently

    a_i > s_i for every i,       δ = minᵢ(a_i−s_i) > 0.   (M)

This applies to every global minimum. It does not assert a_i < 3 or ∇P(a) = 0.

### 3. Adaptive lower-face minimum and reflection

Fix such a minimum a and let b_j = max(a_j,1). Define

    D_a = ∏ⱼ[s_j,b_j],
    B_a = {x ∈ D_a : x_i = s_i for at least one i}.

All coordinate intervals have positive length by (M), a ∈ D_a, and B_a is nonempty and compact. Choose x minimizing P on B_a. Write g = ∇P(x) and J = {j : x_j = s_j}.

If J = {i}, variation of any other coordinate stays in B_a. Hence g_j = 0 when s_j < x_j < b_j and g_j ≤ 0 when x_j = b_j. In (F) for i the i-coordinate coefficient is zero; every upper-coordinate coefficient is b_j−r_j({i}) ≥ 0, because b_j ≥ 1. Thus g·(x−rⁱ) ≤ 0, contradicting (F). We have |J| ≥ 2.

Now a one-coordinate variation in either available direction remains in B_a: if a lower coordinate is moved upward, another lower coordinate remains. The necessary one-sided derivative signs are therefore

    g_j ≥ 0 at x_j = s_j,
    g_j = 0 at s_j < x_j < b_j,
    g_j ≤ 0 at x_j = b_j.

For any i ∈ J, the upper contributions to (F) are nonpositive and the interior contributions vanish. Since s_j−r_j({i}) ≤ 2 and lower g_j ≥ 0,

    1 ≤ g·(x−rⁱ) ≤ ∑ⱼ∈J g_j(s_j−r_j({i})) ≤ 2∑ⱼ∈J g_j.

On a lower coordinate a_j−x_j ≥ δ. On an upper coordinate a_j−x_j = a_j−b_j ≤ 0 and g_j ≤ 0. Thus

    g·(a−x) ≥ δ∑ⱼ∈J g_j ≥ δ/2.

This proves the derivative assertion in (RR). For y = 2x−a, use s_j ≥ 0, a_j ≤ 3, and 0 < a_j ≤ 3 to obtain

    y_j ≥ 2s_j−a_j ≥ −a_j ≥ −3,
    y_j ≤ 2b_j−a_j = max(a_j,2−a_j) ≤ 3.

So y ∈ K, and the full segment from a to y lies in the convex box K.

Let f(t) = P(a+t(x−a)). Then f(t) ≥ f(0) on [0,2], while f′(1) < 0. For sufficiently small ε > 0, f(1−ε) > f(1) ≥ f(0). Hence f attains on [0,1] a maximum strictly larger than both endpoint values. This proves the asserted rise and subsequent fall without assuming quasiconvexity.

### 4. Quadratic exclusion and quantitative third derivative

For a quadratic P(z) = c+ℓ·z+(1/2)zᵀHz with symmetric H, direct expansion about x gives

    P(2x−a)−P(a) = 2∇P(x)·(x−a).

The quadratic terms in x−a cancel. If P satisfied (E), the left side would be nonnegative by minimality of a, whereas (RR) makes the right side at most −δ. This contradiction proves the degree-at-most-two exclusion, with no Hessian-sign hypothesis.

For any C³ function f on [0,2], integration by parts twice on each half gives

    ∫₀¹ t²f‴(t)dt = f″(1)−2f′(1)+2f(1)−2f(0),
    ∫₁² (2−t)²f‴(t)dt = −f″(1)−2f′(1)+2f(2)−2f(1).

Adding and dividing by four yields the midpoint identity

    [f(2)−f(0)]/2 − f′(1)
      = (1/4)∫₀² (1−|t−1|)² f‴(t)dt.

For the reflected segment from Section 3, the left side is at least δ/2. The nonnegative kernel on the right has total mass 1/6. Therefore max f‴ ≥ 3δ. The chain rule gives f‴(t) = D³P(a+td)[d,d,d], proving (T3).

### 5. Multi-affine exclusion

A multi-affine polynomial has a global minimum at a vertex of K: start at any minimum and successively replace each coordinate by an endpoint where the affine one-coordinate restriction is no larger. The replacements preserve minimality. By (M), the only possible minimizing vertex is the top vertex t = (3,…,3). Every other vertex therefore has strictly larger value.

For B ⊆ I, let tᴮ be t with the coordinates in B changed to −3, and set c_B = P(tᴮ)−P(t). Thus c_∅ = 0 and every nonempty c_B > 0. Choose i with c_{ {i} } minimal among the singleton gaps, abbreviating it as c_i. Set x_i = s_i and x_j = 3 for j ≠ i, and put θ = (3−s_i)/6. The standing assumptions give 0 < θ ≤ 1/2.

Affine interpolation in coordinate i gives P(x)−P(t) = θc_i. If x^{−j} denotes x with coordinate j changed from 3 to −3, then for j ≠ i the two-coordinate interpolation gives

    P(x^{−j})−P(t) = (1−θ)c_j+θc_{ {i,j} },
    ∂ⱼP(x) = [θc_i−(1−θ)c_j−θc_{ {i,j} }]/6 < 0.

Indeed c_i ≤ c_j, 2θ−1 ≤ 0, and θc_{ {i,j} } > 0. In (F) for i the own coefficient is zero, and every other coefficient is 3−r_j({i}) ≥ 2. Since n ≥ 2, this makes ∇P(x)·(x−rⁱ) < 0, a contradiction. This proves the multi-affine theorem without a total-degree restriction.

### 6. Monotone scalar transforms

The continuous image Q(K) is a compact interval. Let H = max_{z∈Q(K)} |Φ′(z)|. If H = 0, the mean value theorem makes Φ constant there, and the face inequality rules out P = Φ∘Q.

Suppose Φ is nondecreasing and H > 0. On every exact edge with A(q) > 0, (E) forces Φ(Q(v)) > Φ(Q(F(v,q))), hence Q(v) > Q(F(v,q)). The mean value theorem gives

    A(q) ≤ Φ(Q(v))−Φ(Q(F(v,q)))
         ≤ H[Q(v)−Q(F(v,q))].

If A(q) = 0, q is all Continue and F(v,q) = v, so the same inequality holds. Thus HQ itself satisfies (E), contradicting Section 4 or 5. For nonincreasing Φ, replace Q by −Q and Φ(z) by Φ(−z). Both excluded polynomial classes are preserved by multiplication by a scalar and by sign reversal. This proves the transform theorem under the stated componentwise C¹ hypothesis.

### 7. Rational robust rejecting edges

By Section 4 or 5 there is a real exact root (v,q) violating (E). It has A(q) > 0, since a zero-charge root gives F(v,q) = v. The functions A, F, every e_j, and P are continuous in (v,q); A and F are polynomial, and e_j is a maximum of two polynomial endpoint expressions minus F_j.

Fix the supplied τ > 0. At this violating exact root the inequalities

    A(q) > 0,     P(v)−P(F(v,q)) < A(q),
    e_j(v,q) < τA(q) for every j

are all strict. They persist in a relative neighborhood in K×[0,1]ᴵ. Rational points are dense in this product of rational closed intervals, including near its boundary. Choose a rational pair in that neighborhood. Rational rewards make u = F(v,q) rational, and convexity keeps u in K. The Bellman residual is exactly zero. All displayed inequalities therefore give the required rational rejecting robust edge.

Enumerate rational v and q in the two boxes, compute the rational successor, and test the finitely many rational inequalities. An enumeration covering every pair must find such a witness. This is candidate rejection at a supplied tolerance, not a denominator bound, a uniform finite search cutoff, or an exact-rational-Nash assertion.

## Adapter and semantic consumer

For the bounded nonnegative-singleton Fin4 class in (PC), all players are normal by the argument in the definitions section, and some singleton is positive by hypothesis. Apply the existing characterization with rewardBound = 1. Its right-hand side is exactly the no-sure-root clause and rational robust potential clause written here, because 1+2 = 3. Its forward direction produces τ and P; neither is an extra assumption. The robust-to-exact implication and Sections 4–5 add degree at least three and failure of multi-affinity to that very same P. Its smoothness also permits (RR) and (T3). Conversely, forget the new restrictions and invoke the existing converse. This proves (PC).

To obtain the decision-level reduction from an arbitrary hypothetical Fin4 counterexample r, choose any finite bound on its finitely many reward coordinates. The existing theorem `nonempty_finFourSinglePivotNormalization_of_no_uniformPayoff` produces a literal normalized table r̂, a pivot p, and no-UE for r̂, with own singleton values one at p and zero elsewhere. This is an actual semantic output of the theorem, not merely an affine chart identity or an assumed normalized counterexample.

Choose an integer N ≥ 1 at least as large as every |r̂_j(S)|, set λ = 1/N > 0, and define r̄ = λr̂. Then |r̄_j(S)| ≤ 1 and its singleton vector is λ at p and zero elsewhere. The positive entry need not stay numerically one.

Here is the required scaling argument in the literal strategy semantics. The active/absorbing states, observations, actions, and transitions of r̂ and r̄ are identical, so the same behavioral profiles and deviations give the same distributions of histories, absorption coalitions, and Never. Every realized finite-horizon average and terminal reward under r̄ is λ times the corresponding reward under r̂, hence so are their expectations and all unilateral gains. If z is a uniform-equilibrium payoff of r̂, then for accuracy ε in r̄ choose the profile and horizon threshold for accuracy ε/λ in r̂; it delivers λz and satisfies the unrestricted deviation inequalities. The converse uses multiplication by 1/λ. Thus UE(r̄) is equivalent to UE(r̂), so r̄ remains a counterexample. For the bounded terminal rewards, positive scaling also commutes with each supremum over replies and infimum over opponent plans; its punishment vector is λ times that of r̂. Alternatively, normality of r̄ follows directly from its nonnegative singletons.

Apply the polynomial characterization afresh to r̄ with bound 1. This produces a fresh rational polynomial and rational tolerance on [−3,3]⁴ to which all the exclusions apply. No previous fixed-box polynomial is transported, and no terminal-only translation is treated as a strategic equivalence. The input rewards may be real; positive rational scaling does not assert they become rational. Rationality of the newly produced polynomial comes from the characterization itself. Rational rewards are needed only for the separate explicit rational-rejection corollary.

Together with the trivial direction that forgets extra table and certificate restrictions, this proves that the existence of a Fin4 counterexample is equivalent to the existence of a bounded table with singleton vector λe_p for some p and λ > 0, satisfying the right-hand side of (PC). This is a narrowed obstruction, not a constructed counterexample or an existence theorem for UE.

## Exact boundary tests and attempted falsifiers

The [companion exact-arithmetic checker](../gpt/VERIFY_REFLECTION_AND_MULTIAFFINE_EXCLUSIONS.py) verifies 160 quadratic identities, 201 reflected-box cases, 36 multi-affine derivative identities, 120 collision-adjusted exact-root probes, and 11 third-derivative kernel monomials. These finite regressions supplement the proofs; none is a universal proof or a new Lean check.

1. Collision and upper-bound repair. With two players, r({1}) = (0,−1), r({2}) = (−1,0), r({1,2}) = (1,1), take h = 1/4. At x = (0,0), the correction gives v = (0,2/3), u = (0,1/4); both players are indifferent at the root (1/4,0). At x = (0,3), freezing the upper coordinate instead gives v = (0,3), u = (0,2), and player 2's Continue-minus-Quit value is 7/4. Applying the interior correction there would leave the box.
2. Reflection boundaries. With a_j = 3 and s_j = x_j = 0, the reflected coordinate is exactly −3, which is allowed. Using the fixed upper cap 3 instead of b_j = max(a_j,1) can fail: a_j = 1/2 and x_j = 3 would reflect to 11/2. If the sign condition is removed, s_j = x_j = −1 and a_j = 3 reflect to −5. These are failures of unsigned or nonadaptive extensions, not counterexamples to the stated theorem.
3. Multi-affine sign boundary. If an unsigned extension permits θ = 2/3, with c_i = c_j = 1 and c_{ {i,j} } = 1/10, the displayed derivative becomes 2/45 > 0. The upper bound θ ≤ 1/2 is a substantive use of s_i ≥ 0.
4. Normality does not imply singleton signs. For four players let every nonempty coalition pay the constant vector (1,−1,0,0). Each player can guarantee her coordinate by quitting immediately, and an opponent can force that same coordinate by quitting immediately. Therefore μ = s = (1,−1,0,0): all players are normal and one singleton is positive, but a singleton is negative. Common positive scaling does not repair its sign. This is why actual single-pivot normalization precedes scaling.
5. Face inequalities alone are insufficient. Let s = (1/4,1/4,1/4,1/4), let the centered singleton columns be those of

       Γ = (1/4) [ 0   3  −1  −1
                    3   0  −1  −1
                   −1  −1   0   3
                   −1  −1   3   0 ],

   and put y = v−s and

       Q(y) = −4∑ⱼ y_j + 64(y₀y₁+y₂y₃)
                + 16(y₀+y₁)(y₂+y₃),       P(v) = Q(v−s).

   The singleton rewards rⁱ = s+Γ_i lie in [−1,1]⁴; nonsingleton rewards can be any bounded completion. On the face y_i = 0, write t for its paired coordinate and u,w for the other two. Direct differentiation gives

       ∇Q(y)·(y−Γ_i) = 1+4t+32t(u+w)+128uw ≥ 1

   for all t,u,w ≥ 0. Nevertheless the Hessian eigenvalues are 96,32,−64,−64, and

       P(3,3,3,3) = 1408,
       P(3,−3,3,−3) = −1136.

   A multi-affine polynomial has a minimizing vertex, so here some minimizing vertex is not the top vertex and violates (M). It cannot satisfy the full-root inequality, despite satisfying every nonnegative singleton-face inequality. The companion verifies all four face identities and these exact values. This also demonstrates why neither convex/quasiconvex tests nor a face-only search subsume the present full quadratic exclusion.
6. Quantifier boundaries. A zero absorption charge gives the identity edge, not a contradiction. Replacing the required unit drift by zero allows constant potentials. Any fixed positive drift coefficient κ is covered by applying the exclusion to P/κ. The proof assumes at least two players; it makes no claim for an empty player set. Rational rejection uses τ > 0 and does not promise rational exact Nash points. In (T3), δ depends on the potential and its chosen minimum; no potential-independent lower bound or prescribed mixed partial follows.

## Lean handoff

The new targets are ordinary mathematics; no new Lean theorem, trust seal, strategy implementation, or source-level adapter is claimed here. Suggested declarations should take explicit finite reward, sign, box, regularity, and full-edge hypotheses, not package the desired conclusion as a structure field.

1. Establish the full-exact-edge restriction of `IsQuittingFloorFreeRobustEdge` using the endpoint mixture and successor box bound. Reuse the stable shape-exclusion face/minimum lemmas if they have been implemented; otherwise formalize the complete probes in Sections 1–2, including the frozen upper coordinates.
2. Formalize the adaptive rectangle, lower-face minimizer signs, and reflected point in K, then `fullRootPotential_radialReversal`. No interior assumption on a or gradient-continuity assumption is needed for this part.
3. Prove the quadratic midpoint identity and `not_fullRootPotential_totalDegree_le_two`; separately use vertex interpolation for `not_fullRootPotential_multiaffine`. The multi-affine target may first use a finite square-free coefficient function B ↦ c_B, then connect to `RationalPolynomial 4` and its real evaluation.
4. Formalize the one-dimensional midpoint integral identity for C³ functions, the directional chain rule, and the monotone C¹ composition argument. Keep the outer function's neighborhood regularity explicit.
5. Obtain rational approximate rejecting edges from continuity and rational density in the boxed source/root product, with exact successor and ordinary regret. Keep the rational root's approximate Nash status in the statement.
6. Add the strengthened equivalence by applying the existing characterization at rewardBound = 1, and add the decision reduction using the actual single-pivot normalization theorem, common positive scaling in the literal payoff semantics, and a fresh characterization call. Do not import conference Markdown, assume a polynomial producer, or infer an unproved fixed-box certificate transport.

The narrow validation targets are these declarations and the existing root/robust-relation/normalization consumers named above. The exact boundary fixtures isolate upper-box, sign, degree, and full-relation mistakes without requiring a repository-wide refactor.

## Scope and nonclaims

This packet neither proves nor refutes the finite-quitting uniform-equilibrium conjecture. Its semantic reduction is for Fin4; it does not reduce arbitrary player counts to four. It produces no UE strategy or terminal-exploitability gap and rules out no actual reward table by itself. It excludes neither all polynomials nor every smooth potential, and supplies no degree bound, denominator bound, tolerance lower bound, or complete decision procedure.

The analytic claims require |r_j(S)| ≤ 1, all s_i ≥ 0, the exact box [−3,3]ᴵ, and all exact roots at every boxed annotation. Punishment normality alone does not replace the signs. A selected branch, a punishment-floored relation, or the face inequalities alone is not the full relation. The radial third-derivative conclusion is exactly the directional statement proved above. All strategic conclusions rely on the named existing unrestricted semantic theorems, not on treating a one-stage Nash inequality as a behavioral equilibrium proof.
