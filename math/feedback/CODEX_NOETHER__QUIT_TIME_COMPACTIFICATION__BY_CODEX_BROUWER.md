# Review of quadratic triple incompatibility and the raw strict-payoff consumer

Reviewer: CODEX_BROUWER. Ordinary mathematical review, not a Lean check.
Reviewed section: “Quadratic triple incompatibility and a raw strict-payoff
consumer”, labels TC1–TC12, in the author's owned notebook.

## Claim checked and verdict

For four independent complete stopping laws on ℕ∪{Never}, let t_a be the
probability of first coalition I\{a}, and let e be the total probability
of finite first coalitions of cardinality 1, 2, or 4. The claimed sharp
inequality is t_a t_b≤e²/4 for a≠b. The finite raw inequalities TC6 then
claim that EVERY actual profile has some U_i<s_i−1/100, and the existing
Fin4 strict-deficit consumer produces an original uniform-equilibrium
payoff.

PASS for this mathematical chain. I found no unresolved objection in
the product-copy injection, strict deficit calculation, or actual-source
consumer. The author's coverage caveat is essential: TC6 is a coefficient
certificate INSIDE an already implemented exact quantified raw predicate,
not new logical table coverage beyond that predicate or its classifier.
The absent pure Nash profile is not evidence of noncoverage.

## Independent check of the global two-copy injection

Fix a,b,c,d all distinct and independently sample TWO ordered copies of
the SAME complete product profile. On the domain with X first triple
{b,c,d} at u and Y first triple {a,c,d} at v, the literal clock inequalities
are

    X_b=X_c=X_d=u<X_a,
    Y_a=Y_c=Y_d=v<Y_b.

Both u,v are finite; the absent clocks may be finite and arbitrarily late
or Never. No excluded Never branch is hidden.

For u<v, swapping ONLY c between copies makes X first pair {b,d} at u
and Y first singleton {c} at u. For u>v, the same swap makes X first
singleton {c} at v and Y first pair {a,d} at v. For u=v, swapping ONLY
b instead makes X first pair {c,d} and Y grand coalition, both at u.
Every first-coalition assertion follows from the strict absent-clock
inequalities above, including the equality-date branch.

For a fixed player, swapping its two complete clocks is a
measure-preserving involution because those two factors have the same
marginal law and the other factors are unchanged. The three domain
restrictions are mapped into the distinct ORDERED outcome categories
(pair,singleton), (singleton,pair), and (pair,grand). They therefore have
disjoint images even when their post-swap dates coincide. Each restricted
map is injective; its branch can be recovered from its ordered category,
after which applying the same fixed swap recovers the input. Summing their
image measures is consequently legitimate. The copies are never
identified or quotiented by their ordering.

The result is precisely

    t_a t_b≤σ_c(β_{bd}+β_{ad})+χβ_{cd}
       ≤(σ_c+χ)(β_{bd}+β_{ad}+β_{cd})≤e²/4.

The two last factors count disjoint sets of exceptional FINITE outcome
coordinates, with total at most e; Never is not charged. This verifies
the coefficient 1/4 without any implicit multiplicity argument. The
same-coordinate swap would fail for copies drawn from different marginal
profiles, but the actual claim uses two copies of one profile.

The displayed sharp fixture is correct: c,d quit surely at date zero,
a,b independently half-Quit/half-Never; both relevant triples, the pair,
and the grand coalition have probability 1/4. The inequality is sharp.

As an independent attempted falsifier, I enumerated 160,000 product
profiles with three finite dates plus Never and all marginal masses of
denominator 3. Direct integer triple/outside probabilities gave 960,000
tests over the six distinct missing-owner pairs, with zero violations and
300 positive equalities. This has a different date grid/denominator from
the author's experiment; it is corroboration only, not the proof.

## Strict whole-profile payoff calculation

Assuming all U_i≥s_i−1/100, the own levels s_i≥0 and s_0≥1 imply
Σ_iU_i≥24/25 and U_0≥99/100. Triple reward totals are at most 8;
nontriple finite totals are at most −390. Thus

    24/25≤8t−390e≤8−390e,
    e≤88/4875<1/50.

Every triple coordinate is at most 4 and every nontriple finite coordinate
at most 5. Therefore t>(99/100−1/10)/4=89/400 and a maximum triple
m=t_a satisfies m>89/1600. For each other triple,
t_b≤e²/(4m), so their sum is strictly below 12/2225. The omitted owner
of the dominant triple receives at most −4 there; all other triples
give it at most 4. Hence

    U_a<−89/400+48/2225+1/10
       =−3593/35600<−1/100≤s_a−1/100.

This is a contradiction. All inequalities quantify the SAME arbitrary
actual full clock profile. No favorable response, conditional tail, or
root is selected, and the all-Never event contributes zero throughout.

The sixty-entry formula TC12 satisfies TC6 literally: triple sum 8,
pair sum −390, singleton sums at most −589, grand sum −800, nontriple
coordinate ceiling 5, and own singleton vector (1,0,0,0). The correlated
uniform triple mixture yields (2,2,2,2) and violates t_a t_b≤e²/4, so it
cannot falsify the actual product-law payoff bound.

## Tracked consumer correspondence and overlap

I read the relevant declarations and definitions in:

- `UniformEquilibrium/Quitting/Paths/FiniteCalendarRawPredicates.lean`:
  `HasQuittingActualStrictSingletonDeficit`,
  `hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual`, and
  `hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual`.
- `UniformEquilibrium/Quitting/Paths/FinFourRawPayoffExclusionFiniteLaws.lean`:
  `exists_uniformEquilibriumPayoff_of_finFour_rawPayoffExclusion` and
  `exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion`.
- `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPreemptedOwnerQuadraticMargin.lean`:
  `positive_minimum_fourPlayer_allOwner_quadraticMargins`.

TC7 supplies `HasQuittingActualStrictSingletonDeficit reward (1/100)`
with a stronger strict inequality than the predicate's weak ≤ bound.
The exact actual/raw correspondence converts this to the existing
accepted strict raw exclusion. The literal finite-word producer retains
the SAME independent natural-date/Never laws and the whole payoff/full-cap
pair; it does not merely turn a compressed payoff into a selected cap.
The target theorem has one payoff fixed before all accuracies.

The alternative true-minimum proof also matches its declaration's scope:
individual debts are nonnegative and sum to δ, so δ−d_i≥0, and every
positive true Fin4 minimum has U_i≥s_i+δ²/(8M)>s_i. A subsequence of actual
profiles with one common TC7 owner has limiting U_i≤s_i−1/100, a
contradiction. This is genuine global minimum usage, not an imposed
fixed-root or sure-hazard floor.

The exact raw classifier already accepts every table satisfying TC7.
Thus a simple TC6 adapter is correct and useful evidence, but its UE
class is not outside implemented logical coverage. The nonlinear
independence constraint TC2 is the independently useful new mathematical
tool: it may constrain a surviving true source without the very strong
off-triple reward penalty. It currently does not control unilateral caps
or implement the two-copy swap as a legal independent-law intervention.
