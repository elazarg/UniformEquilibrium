# Review of repair dual obstruction and deleted-law reconstruction

Reviewer: CODEX_LARCH_GEOMETRY. Date: 2026-09-07.

Reviewed [the theory sketch](../notes/CODEX_LARCH_DUAL__REPAIR_EXCLUSION_THEORY.md)
against the exact VANISH trap formulas and the displayed finite repair LP
definitions. This is independent ordinary-math review, with no Lean build.
Both central deductions pass the review below. No conjecture-facing producer
or claim of new general compression is inferred from them.

## 1. All optimal duals fail payoff exclusion at the stated source

The claim is stronger than failure of one proposed dual selection: every
optimal dual, aggregated to player weights, has strictly positive weighted
payoff surplus above singleton rewards.

I checked the complete pivot-replacement debt formulas in
[HILBERT's trap](../notes/CODEX_HILBERT__FULL_EXPLOITABILITY_COORDINATE_REPAIR_TRAP.md).
Splitting its nonpivot maximum gives exactly g_Q and g_C in the reviewed
note. The pivot row gives exactly g_0. At X=x and L=1−x all three equal m.

The endpoint definitions `responderNeverEndpoint`, `responderFirstEndpoint`,
`responderLimitEndpoint`, and `constraintGain`
(`UniformEquilibrium/Quitting/Terminal/PivotRepairFiniteLP.lean`) support the
claimed active-row reduction for deadline one. Here a nonpivot's own
singleton and pivot-tie rewards are both zero, while its reward when the
pivot quits first is −1. Thus the first endpoint has no first-atom
dependence, and the Never/limit endpoints are strictly below the active
first endpoint at this source. The zero row is also strictly slack.

For any optimal dual, the source must minimize its weighted affine
objective. Decreasing L, decreasing the first atom together with it, and
increasing Never mass is a feasible direction from this source. Therefore
the coefficient x(1−2w₀) must be nonpositive. This checks the sign in the
crucial conclusion w₀≥1/2. Complementary slackness then gives the weighted
surplus w₀(1−x)−m≥(1−x)(1/2−x)>0.

I also checked the displayed explicit dual: its X and L coefficients
vanish; α<1 reduces to the stated cubic factorization, whose sign is
negative on 1/3<t<3/8. This confirms attainment and positive value without
depending on an unspecified dual selection theorem.

The equal weight on the three nonpivots has weighted surplus −m, so it is
indeed an available exclusion weight at the same source. The repair dual's
failure does not exclude existence of exclusion weights and does not
identify maximum-debt and total-debt objectives. The note preserves these
distinctions correctly.

## 2. Reconstruction bound and its singularity

The identity μ(t,S)=aᵢ(t)μ⁻ⁱ(t,S), for i outside S, is correct with strict
survival aᵢ(t)=Pr(Tᵢ>t). Using survival at t−1 would incorrectly retain
ties containing i. The Never identity also holds literally.

Under the lower bound aᵢ≥ν, write full-law restrictions b=ac and b'=a'c'.
Then a(c−c')=(b−b')−(a−a')c' gives precisely the displayed sum bound,
including the factor δᵢ/2 in total variation. The restriction b need not
be a probability law; c' is a probability law, which is the normalization
actually used. A lower bound on a alone is sufficient for this asymmetric
proof, so the two-sided assumption is conservative and valid.

Every deterministic quitting-time response is a bounded measurable test
of the opponent dated event. Averaging over complete independent responder
laws cannot exceed the pure-response supremum. The TV estimate therefore
controls unrestricted caps without an attainment assumption. The two-player
example has dated TV exactly ν and cap difference exactly one, correctly
showing order-1/ν deterioration and complete failure at ν=0.

The future consumer genuinely needs the dated outcome law and survival
functions on the same independent source. Unmarked coalition observables
alone do not provide these data. The note identifies this gap explicitly.

## 3. Connection to the parallel geometry sketch

The [quantitative collapse sketch](../notes/CODEX_LARCH_GEOMETRY__OBSERVATION_STABILITY_THEORY.md)
handles a complementary singular regime. Individual Never probabilities can
be zero there, but every unilateral deletion leaves an almost-sure
opponent quitter at a common root. That caps the counterfactual tail
directly, without dividing by the deleted player's survival.

This suggests a useful division of the prospective theory: inverse-survival
reconstruction where the censoring probability stays positive, and direct
counterfactual-tail coupling where the remaining opponents absorb with high
probability. Neither regime alone covers arbitrary laws. A proposed global
compactification should retain the residual deleted mass where both controls
fail, rather than treating either adapter as a complete solution.

## Disposition

The two central elementary deductions pass this independent mathematical
review. The all-duals obstruction is a concrete reason to retire the direct
repair-dual-to-exclusion implication. The deletion estimate is a sound
conditional adapter whose conjecture-facing actual-data consumer remains
open. No unresolved mathematical objection was found in these claims.
