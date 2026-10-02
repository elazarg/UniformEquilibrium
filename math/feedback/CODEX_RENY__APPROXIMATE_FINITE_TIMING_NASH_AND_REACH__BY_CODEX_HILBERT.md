# Independent review of finite-Nash support pruning and punishment floors

Reviewer: `CODEX_HILBERT`.

Reviewed note:
[`CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md`](../notes/CODEX_RENY__APPROXIMATE_FINITE_TIMING_NASH_AND_REACH.md),
frozen Sections 1–11, with the detailed adversarial check focused on Sections
8–11 and their compact-limit dependencies in Sections 3–5.

Status: **ordinary mathematical review passes; no unresolved mathematical
objection found**. The whole-prefix one-sided budget, simultaneous literal
pruning, endpoint/cap stability, retained boundary suffix, and the noncircular
punishment-floor deduction are valid under their stated hypotheses. This is
not a Lean build, export, approximate-block-capacity theorem, or complete
finite-forward packet producer.

## 1. Exact statement checked

Fix m finite players, rewards bounded by M > 0, zero Never payoff, and an
independent finite timing ε-Nash profile with allowed dates 0,…,N−1 and
Never. The Nash condition controls every complete unilateral replacement
within that finite menu, with coordinate error at most ε ≥ 0.

At each literal root, let Qᵢ and Cᵢ be Quit and Continue followed by the
actual prescribed continuation. Suppose on 0 ≤ t < K ≤ N the *original*
profile satisfies joint reach R(t) ≥ ρ > 0 and all Continue probabilities
1−qᵢ(t) ≥ η > 0. Deleting exactly the original hazards with Qᵢ−Cᵢ < −δ,
δ > 0, gives total deleted hazard μ and support error Δ satisfying

    μ ≤ mε/(ρδ),
    Δ = max(δ,ε/(ρη)) + 4Mμ.

The inequalities are against the recomputed actual continuation values.
The construction retains every root from K onward, increases joint reach,
loses exactly μ total marginal hazard and at most μ total unweighted root
absorption charge, and perturbs prescribed suffix payoffs and unilateral
caps by at most 2Mμ each. Thus full terminal exploitability changes by at
most 4Mμ. These statements have no hidden deadline factor.

## 2. Why the whole-prefix budget is valid

Fix one player and its opponents. The finite menu gives a single pure-action
cap c, with slack c−f(a) ≥ 0 for every permitted date or Never. Its own
prescribed stopping law supplies the disjoint budget

    Σₐ pᵢ(a)(c−f(a)) = c−Uᵢ ≤ ε.

At date t with positive own atom, the alternative that always continues
through t and then uses the prescribed conditional own tail is a permitted
mixture of later dates and Never. Therefore its unconditional payoff
f_later(t) is at most c. If original own continuation has zero mass, the
finite timing realization's fallback is still supported on this same menu;
the statement needs that finite-menu fallback, as the note explicitly says.

Before t, this plan and Quit at t share the same opponent absorption payoff.
On opponent survival through t, their difference is Cᵢ(t)−Qᵢ(t). Thus

    f_later(t)−f(t) = S₋ᵢ(t)(Cᵢ(t)−Qᵢ(t)).

The factor R(t)qᵢ(t) is pᵢ(t)S₋ᵢ(t), giving the exact identity

    R(t)qᵢ(t)(Cᵢ(t)−Qᵢ(t))₊
       = pᵢ(t)(f_later(t)−f(t))₊
       ≤ pᵢ(t)(c−f(t)).

Summing uses each own atom's slack once. It does not add mutually exclusive
Quit opportunities, nor assume one deviation can collect all local gains.
Zero own atoms and zero opponent reach contribute zero. The opposite
orientation in the root residual is correctly excluded: the positive-solo
example of Section 7 has weighted accumulated residual Kε despite total
finite and unrestricted debt ε.

On each deleted hazard Cᵢ−Qᵢ > δ, the source reach bound gives
ρδ Σ_deleted qᵢ ≤ ε. Summing over m players proves the claimed μ bound.
There is no repeated application of the ex ante ε estimate per date.

## 3. Simultaneous pruning and suffix recomputation

The rule is evaluated once at the original profile. It need not remain the
same sign test after other players or later roots have been changed; the
uniform perturbation estimate pays for that change.

Couple old and new Bernoulli actions using independent private uniforms
for every player-date pair. The probability of a disagreement at a specified
pair is exactly qᵢ(t)−q'ᵢ(t). A single union bound over *all* changed pairs
is at most μ. No sum of successive payoff perturbations is needed. Before
the first disagreement both terminal histories and payoffs agree, so bounded
payoffs differ in expectation by at most 2Mμ.

For a suffix value at cut t, reset both literal root sequences at t and use
the same argument on future uniforms. Fresh behavioral randomness after the
cut is independent of the earlier survival event, so this compares the
actual conditional suffix laws directly. It does not compare two global
conditional measures through an estimate that would require division by
their different reach probabilities. This is why no extra factor 1/ρ
appears in the payoff-stability bound.

The argument covers roots changed for several players and at several dates.
When a player is forced to Quit at the current root, its own current random
bit is simply omitted. When forced to Continue and then follow its respective
prescribed tail, that bit is again omitted while future changes remain in
the same μ budget. Each endpoint therefore moves by at most 2Mμ and its
difference by at most 4Mμ.

For a fixed arbitrary complete behavioral deviation, use the same deviator
in both worlds. Until an opponent disagreement, the deviator sees identical
public histories and can be coupled identically. Only changed opponent
hazards enter the bound. The estimate is uniform over that entire deviation
class, so taking suprema preserves the 2Mμ cap bound. This includes deviations
using dates outside the finite menu; the proof is not a finite-menu cap test.

Every pruned hazard lies in [0,1], and from K onward the displayed hazards
coincide exactly. Recomputing values from these actual roots gives Bellman
identities automatically. The conditional suffix from K is identical in law
and payoff; its *unconditional* terminal mass may increase because entry
reach increases. The note claims the correct literal-root retention and
does not assert preservation of unconditional tail atom weights.

## 4. Support inequalities, charge, and boundary indexing

If q'ᵢ(t) > 0, the original gap was at least −δ, and hence the new gap is
at least −δ−4Mμ. Continue remains positive because pruning only increases
its probability. On the original source, conditional finite ε/R(t)-Nash
implies

    (1−qᵢ(t))(Qᵢ(t)−Cᵢ(t)) ≤ ε/R(t).

Dividing by the supplied Continue floor and source reach gives the upper
gap bound ε/(ρη), then ε/(ρη)+4Mμ after modification. These are precisely
the two conditions in `IsQuittingRootSupportApproxNash`; they are stronger
than the mixed-root weighted endpoint conditions. The rare negative-solo
Quit example of Section 9 correctly demonstrates why pruning was needed.

Root absorption is 1−∏ᵢ(1−qᵢ). It is monotone and its change is at most the
sum of marginal changes at the same date. Summing proves the charge loss
bound. The claim concerns unweighted root absorption charge; no alternative
survival-weighted charge is silently substituted.

One endpoint distinction matters when Section 11 is used: the hypotheses
R(t) ≥ ρ for t < K do not assert R(K) ≥ ρ. They do give

    R(K) ≥ ρ ηᵐ

when K > 0, by applying the Continue floor at K−1. A punishment-floor claim
for the final displayed value must therefore separately ensure
N−K ≥ H_τ and ε/R(K) ≤ e_τ, as Section 11 explicitly requires. Sufficient
uniform error control uses ε ≤ e_τ ρηᵐ. Larger *modified* reach cannot be
used to certify an unverified source condition retroactively.

## 5. The punishment-floor producer is not circular

Section 11 specializes to Fin4 and assumes no uniform-equilibrium payoff.
The checked source supplies both a fixed positive terminal gap and all-player
punishment normality. For a proposed violating sequence of finite εₙ-Nash
profiles with εₙ → 0 and Nₙ → ∞, Sections 3–4 give limiting Never masses
aᵢ ≥ Γ/M. At every fixed date t, original joint reach has a strictly
positive limit. Thus εₙ/Rₙ(t) → 0 at that fixed date, and finite Bellman
equations and conditional root inequalities converge to an exact annotated
spine with initial value u.

The annotations are limits of actual conditional payoff vectors, so they
lie in the canonical reward cube. The actual limiting hazard sequence has
positive limiting marginal survival; hence its marginal hazard sums, and
therefore joint absorption sum, are finite. These verify the hypotheses of
`IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`.

I inspected that theorem's proof and its two used ingredients. Summable
absorption produces an annotation limit above the singleton vector. A
punishment-floor violation on an exact edge propagates forward without an
increase in that value. Normality puts the punishment floor below the own
singleton reward, contradicting such a violation at the boundary. Neither
the theorem nor these used proof steps invokes a terminal approximate-Nash
producer, the persistent-spine equilibrium consumer, or execution of the
escaped annotation as a terminal continuation.

Therefore the contradiction compactness argument giving

    ∀τ>0 ∃H_τ≥1 ∃e_τ>0 ∀N≥H_τ ∀ finite e_τ-Nash p,
      Uᵢ(p) ≥ χᵢ−τ for every i

is valid. It is a uniform statement about finite approximate equilibria,
not a claim that those finite profiles are unrestricted approximate equilibria.
Applying it to reached conditional tails requires the explicit source
error/reach and remaining-deadline conditions, including the final value.
Pruning then gives the floor χᵢ−τ−2Mμ.

## 6. What remains supplied and what is actually produced

The fixed compact carrier is automatic: take the common reward cube for
all actual recomputed conditional values. The author incorporated this
clarification while freezing the later statement.

The following source hypotheses remain necessary at the reviewed boundary:

- one actual finite ε-Nash source and a particular prefix;
- positive source joint-reach and Continue floors on that prefix;
- for the punishment field, sufficiently small source conditional errors
  and sufficiently long remaining deadlines at all displayed cuts;
- the Fin4 no-uniform-payoff hypothesis used for the uniform punishment
  statement, or the corresponding independently supplied normality/gap data;
- enough original absorption charge to meet the requested target after
  losing at most μ.

For fixed positive ρ and η, choosing δ = √ε makes μ and the support error
vanish without any bound on the deadline. This does not produce ρ, and does
not itself prove that a high-charge source exists under those floors.
For the finite-forward consumer, the source choices must be available in
the consumer's error/charge quantifier order. A reach bound depending on the
requested charge is permitted only if the earlier source error can be chosen
small enough for that bound. Those production steps are outside frozen
Sections 1–11. The reviewed construction itself has no circular reach use.

## 7. Exact checks and bounded source audit

An additional exact arithmetic test used two players, three dates, each
hazard 1/100, and reward −1 to a player precisely when that player belongs
to the terminal coalition, zero otherwise. Both players' best finite and
unrestricted response is Never. Their finite Nash error is
294069601/10¹⁰; each one-sided cumulative budget is 291139003/10¹⁰. With
δ=1/2 all six hazards are pruned, μ=3/50, and the resulting profile is
all-Never. Original prefix reach is at least (99/100)⁴ and Continue floor
is 99/100. Python `Fraction` enumeration verified those values. This checks
simultaneous multi-date/multi-player pruning; the general guarantee above
comes from the proof, not the experiment.

Declarations inspected under their imports:

- `IsQuittingRootSupportApproxNash` in
  `UniformEquilibrium/Quitting/Boundary/Repair/SupportEnlargementAlternative.lean`.
- `IsεQuittingRootEndpointNash`, `isεQuittingRootEndpointNash_iff_purePayoff_le`,
  and the two endpoint-minus-prescribed identities in
  `UniformEquilibrium/Quitting/Root/SuccessorCertificate.lean`.
- `QuittingFiniteForwardPacket` and
  `exists_singleSeamProjectiveLasso_of_finiteForwardPackets` in
  `UniformEquilibrium/Quitting/Projective/FiniteForwardProjectiveLasso.lean`.
- `pmfTV_pmfPi_le_sum` and
  `abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV` in
  `MathUE/PMFProduct/TotalVariation.lean`.
- `abs_quittingFiniteDeadlineTiming_mixedEU_sub_le` and
  `abs_quittingFiniteDeadlineTiming_mixedGain_sub_le` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`.
- `quittingTerminalPayoff_update_eq_expect_behaviorStoppingLaws` and
  `quittingBehaviorDeviationPayoffCap_eq_pureTime` in
  `UniformEquilibrium/Quitting/Paths/CounterfactualStoppingLaw.lean`.
- `IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
  and its playerwise proof in
  `UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`.
- `successorValue_le_current_of_punishmentValue_violation` and its
  stationary-cap amplification proof in
  `UniformEquilibrium/Quitting/Debt/Dynamic/PunishmentFloorViolation.lean`.
- `exists_quittingAnnotationBoundary_of_summableAbsorption` and
  `quittingSingletonReward_le_annotationBoundary` in
  `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryLimitGeometry.lean`.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  and the resulting normality field in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

The finite timing Bellman and tail-splice declarations were already inspected
in my separate review of the predecessor notebook. Section 1's architecture
no-go was checked against the named uniqueness, exploitability, comparison,
and uniform-target declarations in
`FinFourHardDeadlineTimingNashUniqueness.lean` and
`FinFourHardDeadlineTimingNashBarrier.lean`, both under
`UniformEquilibrium/Diagnostics/Quitting/`. No new proof of that existing
no-go is claimed.

No Lean file was changed or built. No exports or commits were made. The next
mathematical check is the source production of a sufficiently reached,
sufficiently charged long prefix in the required error/charge order; it is
not resolved merely by naming the positive parameter ρ.

## Addendum: bounded source-novelty check for Section 12

This addendum checks interface strength, not the separate first-crossing
proof, which SKEPTIC is independently reviewing. The earlier review above
remains the frozen assessment of Sections 1–11. The Section 12 output is

    no uniform payoff ⇒ ∃ H≥1, e_*>0, ρ>0,
      ∀ N≥H, ∀ finite-menu e_*-Nash p, R_p(N−H)≥ρ.

The source is every independent finite timing near-equilibrium, not a
chosen exact Nash selector, an unrestricted terminal approximate equilibrium,
or an already supplied support-perfect root chain. The positive error,
window length, and reach floor are all fixed before the deadline and profile.
No Nε→0 assumption is present.

I used the maintained FRONTIER and TOOLKIT descriptions to inspect the
following nearby declarations. This is a bounded comparison, not a claim to
have surveyed every theorem in the repository.

1. `punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash` in
   `UniformEquilibrium/Quitting/Boundary/Holonomy/TwoOwnerCommonWordRealization.lean`
   requires Nash inequalities against every complete behavioral deviation.
   A finite-menu e_*-Nash profile does not meet that hypothesis: its omitted
   date can retain positive debt. Thus this existing approximate punishment
   floor cannot replace Section 11.

2. `IsCanonicalExactQuittingNashBellmanSpine.punishmentValue_le_of_all_normal_and_summable`
   in
   `UniformEquilibrium/Quitting/Bellman/Finite/SummableExactNashBellmanPunishmentFloor.lean`
   requires a supplied bounded exact spine with summable absorption and
   all-player normality. It contains no finite-source/deadline statement.
   Section 11's compactness argument is a new source adapter to this theorem;
   the theorem by itself does not produce a finite-menu floor or reach.

3. `reached_supportPurifiedPrefix_compatible` in
   `UniformEquilibrium/Quitting/Classification/SimonFiniteOrbit/FinitePrefixCompatibility.lean`
   assumes an unrestricted root-sequence approximate Nash condition and a
   supplied reach floor. Its recomputed-tail error includes
   `2 M · m · displacement · (fuel−offset)`. The related
   `lowSurvival_or_sourceMatchedSupportPrefix_of_approximateEquilibriumExistence`
   and
   `lowSurvivalPrefix_or_exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence`
   in `ReachedPrefixCompactification.lean` additionally assume the existing
   infinite-horizon approximate-equilibrium-existence interface. They retain
   low survival as an unresolved alternative, and their source accuracy
   depends on the requested horizon. They do not imply a fixed positive
   finite-menu accuracy threshold uniform over all deadlines. The whole-word
   one-sided slack budget removes precisely this length-dependent
   purification expenditure in the present argument.

4. `exists_pos_ratio_forall_exists_jointSurvivalWeight_mem_survivalWindow`
   in `UniformEquilibrium/Quitting/Boundary/Repair/BoundedWindowLanding.lean`
   supplies a crossing-window ratio from no instant approximate equilibria
   and stationary punishment data, but still assumes an unrestricted global
   Nash plan and conditional reservation throughout. Its conclusion locates
   a survival crossing; it does not prevent crossing before a bounded final
   deadline window. Neither the input class nor the conclusion substitutes
   for Section 12.

5. `terminalGap_retainedTailFiniteTimingNash_jointReturn_ge` in
   `UniformEquilibrium/Diagnostics/Quitting/RetainedTailFiniteTimingReturnFloor.lean`
   does give a joint-return floor, but requires an exact finite timing Nash
   graft over one retained tail, a positive coordinatewise separation of
   that tail's payoff above supplied punishment caps, and those actual
   punishments. A hard-deadline finite near-equilibrium does not supply this
   separated-tail certificate. Section 11 only supplies an approximate lower
   punishment floor, not the strict positive separation required there.

6. The bounded exact-block hazard-capacity route used in the predecessor
   note concerns exact Nash–Bellman blocks. For example,
   `quittingFullBoxExactPredecessor_hasFiniteBudget_of_boundedHazardCapacity`
   in `UniformEquilibrium/Quitting/Bellman/Finite/FullBoxExactPredecessorAbsorptionBudget.lean`
   retains exact predecessor equations and exact endpoint Nash conditions.
   It does not automatically extend the all-exact finite-source conclusion
   to one positive error neighborhood uniformly over unbounded deadlines.

Verdict: none of these inspected neighboring declarations already gives the
Section 12 output. The concrete source-strength change is a conditional,
table-dependent robustness theorem for the entire finite-menu Nash class:
exact error zero is replaced by one fixed positive allowable error, while
the literal final-window joint reach remains uniform over every deadline and
every selector. Sections 8–11 provide the missing finite-source budget,
length-independent rounding, and punishment-floor adapters; Section 12
uses the existing finite-forward consumer rather than introducing a new
uniform-equilibrium compiler.

This does not by itself decrease unrestricted terminal debt on the bounded
final window, construct a paid return, or contradict no uniform payoff.
The omitted-date defect remains a genuine surviving interface. No source
implementation, export, or constant optimization was attempted here.
