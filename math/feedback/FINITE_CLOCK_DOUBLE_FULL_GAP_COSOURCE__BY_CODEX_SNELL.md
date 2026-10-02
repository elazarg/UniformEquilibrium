# Second adversarial review of the finite-clock double full-gap co-source

Reviewer: `CODEX_SNELL`

Reviewed candidate: `/tmp/FINITE_CLOCK_DOUBLE_FULL_GAP_COSOURCE.md`

Reviewed SHA-256:
`b335130cab34588f406f99e150a68476f5e170c54ca11a1e688834ba31aab9c2`.

## Verdict

**PASS, with the packet's stated scope.** I found no mathematical defect in
the finite-clock double-debt theorem, the rational refinement, or the checked
no-uniform-payoff adapter. The conclusion is a strict same-source reduction:
it gives two distinct full-gap debtors and two attained pure candidates at one
actual finite-clock profile. It is not an unconditional two-spine producer,
a Nash--Bellman packet, or a terminal consumer. The candidate says this
explicitly and does not rely on the later conditional Fable use as though it
were already a spine construction.

## Claim and quantifiers checked

The packet assumes a finite quitting table and a number `Gamma>0` such that
every complete behavioral profile admits some player and some unrestricted
complete behavioral replacement with gain at least `Gamma`. It concludes
that one actual profile, supported coordinatewise on the internal dates below
some finite clock bound together with literal Never, has two distinct player
debts at least `Gamma`. Each unrestricted cap is attained by one pure stopping
time among the internal dates, the single auxiliary-Late date, and Never.

This is the correct complete-behavioral quantifier pattern. Arbitrarily late
finite deviations and Never are included in the cap rather than silently
deleted. The auxiliary date has zero source mass and is used only as a cap
candidate.

## Finite-clock cap and closed cover

I checked
`exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue` in
`Research/Quitting/FiniteClockPolynomialCenter.lean`. With zero mass on
`finiteClockAuxAtom H`, it identifies the unrestricted behavioral cap exactly
with a maximum over `FiniteClockAtom H`, whose decoded pure times are
`0,...,H` and Never. Thus on the product simplex `C_H`, prescribed payoffs and
all candidate payoffs are finite polynomials, and each debt is continuous.

The closed regions

```text
A_i^H = {sigma in C_H : debt_i(sigma) >= Gamma}
```

cover `C_H`. Under the negation of a double-debt point they form a finite
pairwise-disjoint closed cover. Since the product of simplices is connected,
exactly one region is nonempty and it equals all of `C_H`. Empty regions do
not affect the argument.

## Nested clocks and arbitrary behavioral profiles

The source spaces are literally nested: a law supported before clock `K`
and at Never is represented in every later `C_H` by adding zero coordinates.
Finiteness of the player set gives a fixed label occurring for unboundedly
many `H`; every finite-clock profile lies in one such later simplex. Hence
that fixed player's debt is at least `Gamma` on every finite-clock profile.

Finite-clock laws are dense in full discrete total variation. Retain the
Never mass and move the finite tail beyond the cutoff to the last retained
finite date; the moved tail mass tends to zero. This also handles joint
escape to Never, because the Never atom is never merged with a finite date.

The delicate unrestricted-cap passage is valid. In
`UniformEquilibrium/Quitting/Paths/StoppingLawOperationalDistance.lean`,
`pmfOperationalDistance` is the full discrete L1 distance, including Never.
The declarations

* `abs_quittingStoppingLawExpectedPayoff_update_same_sub_le_opponents`,
* `abs_quittingStoppingLawReplacementPayoffCap_sub_le_opponents`, and
* `quittingStoppingLawCap_behaviorStoppingLaws_eq_continuationBestResponseValue`

give a bound uniform over the replacement law and identify the stopping-law
cap with the unrestricted behavioral best-response value. Taking a supremum
therefore introduces no semicontinuity or nonattainment gap. Prescribed payoff
is continuous by the companion terminal-outcome estimate, so the fixed debt
lower bound passes to every actual behavioral profile.

## Two-range contradiction

If one fixed player had debt at least `Gamma` at every profile, the definition
of supremum permits a literal replacement with gain strictly greater than
`Gamma/2` at each profile. Classical choice yields a selector with that one
constant player label. The checked theorem
`exists_two_selectorRanges_not_strategicallyTotallyBounded` in
`UniformEquilibrium/Quitting/Terminal/StrategicallyPrecompactWatchdogBoundary.lean`
requires two distinct nonempty player ranges for any selector with this fixed
positive gain. That contradicts the constant label. No selector measurability,
cap attainment at arbitrary profiles, or bounded-controller completeness is
being assumed.

It follows that some `C_H` has a point in two distinct debt regions. Applying
the finite-clock cap theorem separately to those two players supplies the two
claimed candidates. They need not both be Late and need not remain profitable
after simultaneously installing both deviations; the packet makes neither
claim.

## Rational refinement and enumeration

At the real co-source, fix the two attaining candidates. Their two literal
gain functions are rational-coefficient polynomials when the reward table is
rational. Rational points are dense in the product simplex with the auxiliary
coordinate fixed to zero. For every strict reduced target
`0<Gamma'<Gamma`, a nearby rational point keeps both gains at least
`Gamma'`. Enumerating clock bounds, distinct player pairs, candidate pairs,
and rational simplex points therefore terminates when acceptance is tested by
exact rational arithmetic.

The exact-scale statement also matches
`finFourExactScaleStep_lower_terminalGap` in
`Research/Quitting/FinFourExactScaleResolution.lean`: a positive lower object
gives literal gap `epsilon/8`, and the rational approximation may use the
strict floor `epsilon/16`.

## FIN4 two-spine scope

The checked equivalence
`not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap`
supplies the theorem's global-gap premise from a hypothetical failure of a
uniform-equilibrium payoff. Thus the source hypothesis is not an extra
unproduced FIN4 field in the contradiction branch.

What is genuinely new is synchronization at one actual finite-clock source:
the two debtor labels and both finite/Late/Never response candidates no longer
come from unrelated profiles. This strictly narrows the source-compatibility
part of `questions/FIN4_TWO_PERSISTENT_EXACT_SPINE_SELECTION.md`.

It does **not** answer any of that question's terminal alternatives by itself.
In particular, it supplies neither one executable Nash--Bellman chronology,
two persistent hazard streams, summable seams, nor a renewable rank. The
packet's downstream paragraph is correctly phrased as an open conditional
conversion through common-prefix/fork machinery, not as a completed semantic
consumer. Any future export or formal theorem should preserve this exact
distinction.

## Boundary checks

* `Gamma>0` is essential; a zero weak gap cannot force two identities.
* The argument works at `H=0`: source finite support is empty and the candidate
  list consists of time zero and Never.
* A terminal Nash profile is incompatible with the global positive-gap
  premise.
* The topology forces one pairwise overlap only, not debts for every player.
* The theorem does not produce a concrete positive-gap table and therefore
  neither proves nor refutes the Fin4 conjecture.

No mathematical repair to the reviewed bytes is requested.
