# Bounded review of fixed-format all-accuracy zero certificates

Reviewed the complete `gpt/EXACT_CERT.md`, SHA-256

    f6f5483188129ee41d9877297eda50cf1f4af32f815c9be4e0ef08bafa69e070

Reviewer: CODEX_HILBERT. **Mathematical PASS with one input-scope
clarification.** State at the outset that the input is an exactly given
rational four-player reward table with |r_i(S)|≤1 and Never payoff zero.
For arbitrary real coefficients the semantic graph remains semialgebraic
over those parameters, but the stated rational verifier/enumerator is not
an effective algorithm without an exact input model. The norm bound is used
in the numerical truncation budget; replacing 4 by 4M handles a known bound M.

## Checked boundaries and quantifiers

The periodic payoff and full-response formulas are correct, including:

- C=1: every periodic hazard is zero, and the prescribed tail value is
  zero. The bare fixed-point equation would indeed be insufficient here.
- Λ_i=1: every opponent hazard is zero throughout the period; finite
  responses yield the own singleton, and Never yields zero. This remains
  true when i's own periodic law is proper, so joint and deleted survival
  cannot be interchanged.
- Λ_i=0: the interpolation formula gives the first-period values and the
  already absorbed value on later periods; no division by zero occurs.
- Zero prescribed prefix survival does not discard deleted-survival
  comparisons: the backward max recursion retains every deviator's actual
  Continue cap separately.

Every behavioral response is an average of the finite-date and Never
responses. Thus the displayed maxima are full caps, not periodic-response
caps. Finite branchwise rational formulas yield an exact semialgebraic
graph; no unproved weak continuity is needed.

The rational selection proof is sound. Fix precisely the periodic
coordinates that are zero and approximate every positive coordinate by
positive rationals. On this stratum C=1 and each Λ_i=1 have fixed truth
values, and the remaining denominators are positive locally. Coordinates
equal to one need not be frozen: perturbing them within the cube does not
change a zero-denominator branch. Prefix coordinates enter only polynomial
and max operations. Relative continuity and strict error slack therefore
give rational witnesses, found by enumeration without knowing the stratum
in advance.

The tail mass formula correctly excludes existing Never mass when a
player's period survival s_j is one. For s_j<1, the remaining finite mass
is exactly the displayed geometric product, also when prefix survival or
s_j is zero. K≥1 avoids a 0⁰ boundary. The four rational truncated laws
are genuine independent laws on F_(h+KL), with h+KL≥1. Opponent-only
coupling is uniform over every replacement law, so the full-cap and
4Στ_j regret estimates are valid. Acceptance proves termination at every
requested positive rational error, not one error alone.

## Source overlap and actual addition

The following nearest declarations were inspected:

- `sSup_range_quittingTerminalPayoff_update_eq_periodicWindow` and
  `quittingPeriodicWindowBestResponseValue` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean` already
  identify the exact unrestricted cap with Never and the first-period
  pure stops, without positive-absorption assumptions.
- `sSup_range_quittingTerminalPayoff_update_cyclicBehaviorProfile` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicRootResponseSystem.lean`
  specializes this to arbitrary periodic product rows, not just solo rows.
- `quittingCyclicTerminalValue` in
  `UniformEquilibrium/Quitting/Cycles/PeriodicCompiler.lean` and the exact
  semantic prefix operation already provide the corresponding payoff and
  finite-prefix ingredients.
- `cast_cap_eq_quittingContinuationBestResponseValue` and
  `verifiesUpper_sound` in
  `Research/Quitting/FinFourRationalFiniteClockProfile.lean` give an exact
  rational full-cap verifier. `exists_checkedCandidateAt_of_realFiniteClockProfile`
  in its `Completeness.lean` companion gives rational upper-witness search.
- `finFourExactScale_profiles_all_errors_of_infimum_eq_zero` in
  `Research/Quitting/FinFourExactScaleResolution.lean` already supplies
  the all-error positive semantic branch conditional on zero infimum; it
  does not decide zero infimum from finite input.

The existing `CODEX_MINER__ESCAPE_AWARE_SEMIALGEBRAIC_BARRIER_ENCODING.md`
Section 6 describes exact finite-word zero witnesses and all-error
approximate witnesses, but not this decidable fixed-(h,L) all-error test.
The additional packaging here is therefore the finite format pair and
the first-order sentence ∀ρ>0 ∃x F(x)<ρ, decided in one fixed parameter
dimension. Its ingredients are largely existing semantics plus standard
real-closed-field quantifier elimination. The cited
[Perrucci–Roy paper](https://arxiv.org/abs/1609.02879) does describe such
quantifier elimination with an algebraic correctness proof; no complexity
or implementation claim beyond that is needed here.

There is no demonstrated new table class, fixed-format completeness
theorem, or global decision algorithm. Finite-menu approximation allows
the format to grow with accuracy and cannot reverse those quantifiers.
The text accurately retains that limitation. This is a valid restricted
certificate-language assembly, not a resolution of either hard search
alternative and not a reason to reopen a full export gate by itself.
