# Formalization coverage for the finite-deadline projective boundary packet

Formalizer: external Lean formalization agent
Target: [`FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md`](../formalized/FINITE_DEADLINE_NASH_PROJECTIVE_BOUNDARY_AND_COMPATIBILITY.md)

Verdict: **Section 5's completeness theorem (5.3) is checked, at error zero
against every unilateral behavioral deviation and with the limiting stopping
laws identified.  It is a strengthening inside ground the repository already
covered, not coverage of an uncovered area.  Section 4's paid edge and paid
response square, the finite-versus-Never split, the semialgebraic hierarchy of
Section 3.1, and the regression tables of Sections 4.4, 6 and 7 are unchecked,
so the export is not claimed as accepted.**

## What was already checked before this work

The finite comparison core of Sections 2 and 3 was already carried by
`Research/Quitting/FiniteDeadlineAdjacentTotalVariation.lean`:

```text
(2.3) Lipschitz comparison in summed marginal total variation
  abs_quittingFiniteDeadlineTiming_mixedEU_sub_le
  abs_quittingFiniteDeadlineTiming_mixedGain_sub_le
  abs_quittingFiniteDeadlineTiming_boundaryGain_sub_le

(3.1) coordinate debt as the positive part of the boundary gain
  quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart

(3.3) d_i(sigma_p) <= 4 R sum_j TV, for every consecutive Nash pair
  quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV

(3.5) the contrapositive, at a supplied coordinate
  quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge

the adjacent distance itself
  quittingFiniteDeadlineAdjacentTV
```

and by `Research/Quitting/FiniteDeadlineProjectiveCompatibility.lean`:
`QuittingFiniteDeadlineCompatibleNashFamily`, its exact Never telescope
(`neverMass_succ_add_boundaryMass`, `boundaryMass_tendsto_zero`,
`adjacentTV_eq_sum_boundaryMass`, `adjacentTV_tendsto_zero`), the ε-Nash form
`quittingFiniteDeadlineTimingProfile_isεAsymptoticNash_of_adjacentTV`, the
general consumer
`exists_uniformEquilibriumPayoff_of_arbitrarilySmallAdjacentNashTV`, and the
family specialization
`QuittingFiniteDeadlineCompatibleNashFamily.exists_uniformEquilibriumPayoff`.

That specialization concluded only that *some* uniform-equilibrium payoff
exists.  It named no profile and gave no exact terminal Nash statement.

## What Section 5 adds

`QuittingFiniteDeadlineCompatibleNashFamily.isZeroAsymptoticNash_limitProfile`
(`Research/Quitting/ProjectiveTimingInverseLimit.lean`) is (5.3).  For an
exactly censor-compatible family of finite-deadline timing Nash laws it
determines one stopping law on the compactified times for each player whose
deadline truncations are exactly the supplied marginals, and proves the
independent product of those laws an exact terminal Nash profile against every
unilateral behavioral deviation, at error `0`.
`QuittingFiniteDeadlineCompatibleNashFamily.isUniformEquilibriumPayoff_limitProfile`
reads off its prescribed payoff.

The truncation identity of (5.1)--(5.2) is separate and checked in the same
file as `QuittingFiniteDeadlineCompatibleTimingFamily.map_cap_limitLaw_eq`:
every finite-deadline law of a compatible family is exactly the horizon cap of
the inverse-limit law `limitLaw`, whose atoms are the mass newly exposed at
each date and, at infinity, the mass no finite deadline exposes.

Two details of the proof are worth recording, because they are weaker than
the packet's presentation.

- The inverse-limit construction consumes censor compatibility alone.
  Optimality enters only in the final consumers, so the limit law is
  determined before any Nash hypothesis is used.
- The general form
  `QuittingFiniteDeadlineCompatibleTimingFamily.isZeroAsymptoticNash_limitProfile`
  needs deadlinewise Nash only on a tail, `∀ᶠ deadline in atTop`.
  Compatibility already determines the early laws from the late ones, so
  optimality at every deadline is not required.

## The adjacent-distance consumer needs no cofinality

The packet states the positive criterion (3.4) with deadlines `N_k -> infinity`.
That escape is not needed.  `quittingGame_isUniformEquilibriumPayoff_of_adjacentTV_tendsto`
(`Research/Quitting/FiniteDeadlineVanishingAdjacentDistance.lean`) quantifies
over an arbitrary index type with an arbitrary `NeBot` filter and an arbitrary
`deadlines : index → ℕ`, with no growth or cofinality hypothesis anywhere.
What carries the estimate is the terminal debt vanishing, not the deadline
growing.

It also identifies the target.  Where the packet's Section 3 reaches "the
checked terminal-payoff compact selection then gives a uniform-equilibrium
payoff", the checked consumer takes the realized prescribed payoffs tending to
one target and returns that target as the uniform-equilibrium payoff.

The realized error is `4 * bound` times the adjacent distance, which bounds
unrestricted behavioral semantic debt.  It is not the deadline escape charge
of `quittingFiniteDeadlineEscapeCharge`, which retains an opponent-survival
factor that adjacent distance does not control.

## What remains unchecked

```text
Section 3.1  the semialgebraic hierarchy Delta_N and eta(r) <= 4 R Delta_N
Section 4    the finite-versus-Never decomposition
Section 4.1  the boundary-participation response collision
Section 4.2  the paid edge and the paid common-response square
Section 4.3  the exact retained-tail seam
Section 4.4  the zero-pass equalization regression
Section 6    the nonterminal boundary-participation regression
Section 7    the retained-tail regression
```

A narrow search found no declaration implementing the paid edge, the paid
response square, or the adjacent-Nash minimum `Delta_N` of (3.6).  The
quantity `eta(r)` itself does exist as `terminalExploitabilityInf`, but every
checked use of it is a table-specific vanishing result; nothing states the
hierarchy bound (3.7) against an adjacent-Nash minimum, which would need
`Delta_N` first.

Against the packet's own Lean handoff list, the mapping is:

```text
finiteDeadlineTimingGain_lipschitz_totalVariation      checked
finiteDeadlineTimingNash_debt_le_adjacentDistance      checked
terminalGap_adjacentTimingNash_totalVariation_ge       checked
finiteDeadlineNashAdjacentDistance                     checked
projectivelyCompatibleFiniteTimingNash_exists_terminalNash
                                                       checked, and stronger
terminalExploitabilityInf_le_four_mul_bound_mul_adjacentDistance
                                                       not checked
consecutiveTimingNash_paidEdge_or_paidResponseSquare   not checked
```

The one marked stronger is checked as an exact terminal Nash profile with the
limit laws identified, where the handoff asked only for existence.

## Seals

The compatibility route has `M`, `L`, and `C`, and no `A`: no compatible-family
producer and no semialgebraic minimizer producer is checked, so nothing
supplies the family that the theorems consume.  The packet's own nonclaim that
it asserts no Lean, adapter, or downstream seal is correct and is unchanged by
this work.  The export packet itself remains at most `M`.

The unchecked Section 4 material is where the packet's conjecture-facing claim
sits, so coverage of Section 5 does not move the export's status on its own.
