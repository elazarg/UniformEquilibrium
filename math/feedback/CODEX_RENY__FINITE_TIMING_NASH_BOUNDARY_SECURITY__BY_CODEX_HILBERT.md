# Independent check of limiting Never floors and the reached final window

Reviewer: `CODEX_HILBERT`.

Reviewed note:
[`CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md`](../notes/CODEX_RENY__FINITE_TIMING_NASH_BOUNDARY_SECURITY.md),
frozen Sections 7–9, including their dependencies in Sections 1–3.

Status: **review passes in ordinary mathematics; no unresolved mathematical
objection found**. This is an independent adversarial source/proof check, not
a Lean build or a second review of an unrestricted existence claim. No
export decision is made. The result supplies a new conditional restriction
on finite timing Nash sources, within the bounded source lookup below; it
does not construct a terminal approximate equilibrium or close the conjecture.

## Claim checked

Fix a finite quitting reward table with |rᵢ(S)| ≤ M, M > 0, zero Never
payoff, and a global unrestricted terminal exploitability gap Γ > 0. All
profiles are independent behavioral profiles, represented by independent
stopping laws; each unilateral deviation can replace the full strategy.

For exact finite timing Nash profiles at deadlines tending to infinity,
take any subsequence with convergent finite atoms and payoff vectors, and
then a fixed owner k of omitted-date debt at least Γ. The claim is:

1. Every limiting stopping marginal has Never mass aᵢ ≥ Γ/M.
2. There is a table-and-gap dependent H₀ ≥ 1 such that every finite timing
   Nash profile with deadline at least H₀ has initial Quit probabilities
   at most 1 − Γ/(2M).
3. In Fin4, the existing bounded exact Nash–Bellman hazard-capacity theorem
   then makes the final H₀ dates of every such source reachable through a
   literal exact prefix with joint probability at least
   exp(−2MC/Γ) > 0, uniformly in the deadline and selected finite Nash profile.

The first conclusion concerns limiting Never mass. It does not bound the
fixed owner's literal finite-profile Never mass away from zero. The second
conclusion concerns the initial root of every sufficiently long finite
Nash game, and is applied to later roots only through reached-tail Nash.

## 1. Zero limiting Never is handled correctly

If aₖ = 0, fix H and write each payoff as the contribution from absorption
before H plus the remainder. The finite-prefix contribution is continuous
in finitely many stopping atoms. Each remainder has absolute value at most
M P(Tₖ ≥ H), because absorption at or after H requires player k not to have
stopped before H. Thus, after the finite-prefix limit, the discrepancy of
the two full payoffs is at most 2M P_p(Tₖ ≥ H), which tends to zero.

This proves u = U(p) coordinatewise. It does not require any other player's
stopping laws to be tight on finite dates. All fixed finite deviations are
therefore capped by Uᵢ(p). If two aᵢ vanish, every opponent Never product is
zero and the limit of late finite deviations equals the Never payoff, so
Never is also capped for every player. With a unique zero coordinate k,
only k's Never payoff can exceed the limit of finite deviations, by at most
−sₖA₋ₖ when sₖ < 0. These arguments verify Section 7.1, including its sign
exception. Dropping that exception would be false reasoning.

## 2. The omitted owner makes the new all-player limit floor work

At a finite deadline every later pure date pays

    Vₖ(p₋ₖⁿ) + sₖ ∏[j ≠ k] Zⱼⁿ.

The finite-game Nash inequality caps Never by Uₖ(pⁿ). Thus a boundary debt
at least Γ forces sₖ > 0 and every opponent's literal Never mass to be at
least Γ/M. Passing to the compact stopping limit gives the same opponent
lower bounds, since aⱼ is at least any limiting literal Never mass.

If the owner's limiting aₖ were zero, the preceding zero-a argument with
sₖ > 0 would produce an exact terminal Nash profile and contradict the
global gap. Hence all aᵢ > 0 and the escaped payoff b is well-defined.

For the delicate bound |bᵢ| ≤ M, fix H first. For sufficiently large n,
joint survival through H is positive, and the actual conditional tail payoff

    (U(pⁿ) − Pᴴ(pⁿ))/Aᴴ(pⁿ)

lies in [−M,M]. Its n-limit is (u−Pᴴ(p))/Aᴴ(p), also in that box. Only now
let H tend to infinity. The denominator tends to A > 0 and the numerator
to u−U(p), proving |bᵢ| ≤ M. No H depending on n, convergence of literal
Never mass to aᵢ, or executable continuation at b is needed.

The complete cap bound Bᵢ ≤ max(uᵢ,Vᵢ) yields

    dᵢ(p) ≤ max(A bᵢ, −(1−aᵢ)A₋ᵢbᵢ).

For i ≠ k, both relevant products contain aₖ and |bᵢ| ≤ M, giving
dᵢ(p) ≤ M aₖ for either sign of bᵢ. For i = k, the positive singleton
gives bₖ ≥ sₖ > 0, so the bound is M A ≤ M aₖ. Applying the gap to the
actual limiting profile p proves aₖ ≥ Γ/M. This is the extra step beyond
the previously known literal opponent floor. I find the constant Γ/M,
rather than Γ/(2M), correct.

## 3. Fixed-date limits are not applied illicitly to moving roots

The proof of the uniform initial-root bound argues by contradiction. If
there is no H₀, select deadlines Nₙ → ∞ with a violating initial atom, and
pass to a fixed violating player and fixed omitted-date owner. Here the
initial hazard is exactly the date-zero stopping atom. Its limit is at
least 1 − Γ/(2M), forcing that limiting player's Never mass to be at most
Γ/(2M), contrary to the all-player floor Γ/M.

This uses a fixed date zero throughout; there is no inference from pointwise
hazard convergence to uniform convergence over moving dates. To apply the
bound at date t in a single source, the author first proves that t is
reached and conditions to an exact finite timing Nash profile with remaining
deadline N−t. That profile is separately covered by the uniform initial-root
statement. Induction supplies positive reach at every t ≤ N−H₀.

The final H₀-date root may be sure. No statement constrains its continuation
probability or transfers Nash past an unreachable event there. This is why
the construction stops at that window rather than claiming a full exact
zero-tail stack under an unproved Never-positivity hypothesis.

## 4. The prefix really fits the capacity theorem

At each date before the final window, all players continue with positive
probability. Nash of the reached finite timing profile permits both current
Quit and current Continue followed by that player's prescribed conditional
tail. The resulting two-action inequalities give an exact root Nash against
the actual successor conditional payoff. Independent marginal conditioning
preserves the opponent product law. The expectation identity is precisely
the Bellman equation.

Every displayed conditional payoff lies in the canonical reward cube,
because it is an actual expected terminal reward with zero Never payoff.
The checked block definition requires only positive length, membership in
that cube, and the exact Bellman/root-Nash edges. It requires no positive
Never atom, absorbing terminal annotation, or Nash property of a continuation
after the final displayed state. The final state's root coordinate is
irrelevant to its incoming edge. Therefore the reached prefix is a valid
input to the bounded-capacity theorem. When it is empty its charge is zero
and survival one, so the positive-length block convention causes no gap.

For η = Γ/(2M), the root bound gives −log(1−q) ≤ q/η on every included
coordinate. Summing and using charge ≤ C gives joint survival ≥ exp(−C/η).
The asserted bound on each marginal prefix survival follows because the
joint product is no greater than any marginal factor. This completes the
check of the literal rather than merely limiting conclusion.

## 5. Falsification attempts and limits

The following plausible failures were checked and do not apply:

- Escaping finite mass can make aᵢ positive while Zᵢⁿ tends to zero. The
  proof allows this for the owner and uses the all-player bound only after
  passing to limiting laws.
- One hazard approaching one defeats survival bounds from total hazard
  alone. The H₀ argument excludes this outside the final window before
  total hazard is used.
- A root after a sure absorbing date need not have a useful prescribed
  continuation. The proof never needs such a root: its induction stops
  before the unconstrained final window.
- A limiting escaped payoff need not be executable. Its only use in the
  floor proof is the bounded real vector b and the support/cap identities.
- The delayed one-date finite Nash examples in Section 4 satisfy the final
  window structure but need not approximate their escaped payoff by terminal
  equilibria. The result does not claim that final-window structure alone
  supplies this missing consumer.

No exact counterexample to the reviewed implications was found. The global
gap remains a real hypothesis at both uses: the actual finite profile has a
positive omitted-date owner, and the actual compact-law profile p must also
have positive debt. Removing either use would invalidate the derivation.

## 6. Source audit and novelty assessment

Declarations inspected under their imports:

- `QuittingFiniteDeadlineNashProfile.bestResponseValue_eq_max_boundary` and
  `QuittingFiniteDeadlineNashProfile.semanticDebt_eq_boundaryGain_pospart`
  in `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`.
- `timingMixedPayoff_bellman`, `timingMixedPayoff_withTail_sub`, and
  `timingLawTail_isNash_of_isNash_of_positiveContinue` in
  `UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineTimingRecursion.lean`.
- `QuittingNashBellmanPoint`, `quittingNashBellmanBox`, and
  `IsQuittingNashBellmanEdge` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanSpine.lean`.
- `QuittingFiniteExactNashBellmanBlock`, its `hazardCharge`, and
  `HasBoundedFiniteExactNashBellmanHazardCapacity` in
  `UniformEquilibrium/Quitting/Bellman/Finite/UnboundedExactBlockHazardCapacity.lean`.
- `finFour_hasBoundedFiniteExactNashBellmanHazardCapacity_of_no_uniformPayoff`
  in `UniformEquilibrium/Diagnostics/Quitting/FinFourUnboundedExactBlockHazardCapacity.lean`.
- `IsCanonicalExactQuittingNashBellmanSpine` in
  `UniformEquilibrium/Quitting/Bellman/Finite/NashBellmanClockReduction.lean`.

The global gap and terminal-equilibrium bridge were separately inspected in
`UniformEquilibrium/Quitting/Terminal/ExploitabilityGap.lean` for my own
variational note. Narrow searches also located the existing
`QuittingFiniteDeadlineBoundaryResponseCollision.opponentNever_ge` in
`UniformEquilibrium/Diagnostics/Quitting/FiniteDeadlineBoundaryResponseCollision.lean`.
No exhaustive novelty or trust audit, literature theorem invocation, or
Lean build was performed.

The old floor controls the omitted owner's opponents at each finite law.
The reviewed addition controls all players at the compact limit, derives a
uniform forbidden near-sure initial root for long deadlines, and then feeds
an actual reached prefix into the existing capacity theorem. That is a
concrete finite-source reduction and more than a restatement of bounded
capacity. Its constants H₀ and C are non-effective existence constants.

Recommended next mathematical question: identify a terminal consumer for
the uniformly reached bounded final window that uses the global gap and
preserves the exact prefix, without requiring the escaped payoff b as the
new continuation target. This remains open in the reviewed sections.

## 7. Follow-up check of the added Section 10

Section 10 was checked after Sections 7–9 were frozen. Its added deductions
also pass, with the author retaining the necessary nonclaims.

For Section 10.1, all-Never has exploitability maxᵢ max(0,sᵢ), so the gap
supplies *some* player with sᵢ ≥ Γ. For an arbitrary positive-deadline finite
Nash profile with absorption probability β, the probability of any opponent
quitting at date zero is at most β. On its complement the selected player's
Quit-zero deviation pays sᵢ; on that event it pays at least −M. Therefore
the deviation pays at least sᵢ−(sᵢ+M)β. Comparing with Uᵢ ≤ Mβ gives
β ≥ sᵢ/(sᵢ+2M) ≥ Γ/(Γ+2M). This reasoning accommodates simultaneous
quitting at date zero. Multiplying by prefix reach and pigeonholing among
the 15H₀ date/coalition pairs proves the claimed absolute atom bound.

For Section 10.2, the positive omitted-date debt in the conditional window
is attained by its first excluded date. Copying the mover's behavior before
entry preserves the original joint reach; conditioning the payoff difference
on that event gives exactly reach times suffix gain, at least ρΓ. The
opponent strategies are unchanged, so the mover's complete cap is unchanged
and its own debt decreases by exactly that gain. No other player's cap or
debt is held fixed by this argument.

For Section 10.3 I inspected `QuittingPositiveMinimumTwoCutBlock`,
`QuittingUniformlyReachedPostMarkTwoCutBlock`, and the statement of
`QuittingUniformlyReachedPostMarkTwoCutBlock.offMinimum_or_exists_paidSplice`
in `UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticPositiveMinimumTwoCutPaidSplice.lean`.
The minimal record indeed stores a separate positive global carrier minimum;
it does not identify that minimum with either actual endpoint. The extension
adds only a preceding marked date, positive total marginal hazard, and
positive absolute entry reach. Choosing entry N−H₀, exit N, and mark zero
when N > H₀ therefore matches the stated data once that minimum is supplied.
The atom/absorption bound supplies the required hazard floor by the elementary
union bound. This is a valid interface match, whose existing disjunction
does not assert minimum preservation or a renewable paid child.

These additions turn the final-window result into an absolute atom and one
paid same-source update. They still leave the terminal consumer and control
of other players' debt changes open. No additional mathematical objection
arose in this follow-up check.
