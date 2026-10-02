# Fin4 full-support proof mining

Author: `CODEX_FERMAT`
Status: `MATH_REVIEWED`

Independent review:
[`CODEX_AUDITOR`](../feedback/CODEX_FERMAT__FIN4_FULL_SUPPORT_PROOF_MINING__BY_CODEX_AUDITOR.md)

## Exact question

Let

```text
reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)
```

be a bounded four-player quitting reward table. Suppose, contrapositively, that
it has no uniform-equilibrium payoff. What can be deduced from the actual
terminal-exploitability witness, the same-table quantitatively full-support
normalized singleton packet, full normal core, and punishment normality? In
particular:

1. can any branch of the existing projective-Q-bar, strict-toggle, paid-cell,
   or three-player machinery be closed unconditionally;
2. can the remaining algebraic obstruction be reduced to an exact finite list;
3. which missing links really use nonsingleton rewards or terminal-witness data,
   rather than merely reformulating the singleton matrix obstruction?

The starting residual is not an arbitrary packet. The counterexample assumption
supplies a `QuittingTerminalExploitabilityWitness`, and for every coordinate
bound it supplies on the same reward table:

- `normalCore (normalizedSoloMatrix reward) = Finset.univ`;
- `IsQuittingNormalPlayer reward who` for every player;
- a `QuittingNormalizedSingletonSourcePacket reward` with support `univ` and a
  quantitative positive mass floor depending on the reward bound and terminal
  gap.

These fields are packaged, after eliminating projective Q-bar, by
`FinFourQuantitativeFullSupportHardResidual` in
`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.

## Why it could matter

For four players this produces a genuine finite narrowing. Projective Q-bar is
no longer a live counterexample chamber. The remaining nonprojective principal
has exactly two or three coordinates, and each size admits a sharper exact
dispatch. Independently, the terminal witness feeds an actual strict-toggle
cycle whose large-base branch enters the paid pure/mixed descent.

This is not a proof of the conjecture. The surviving outputs do not yet enter a
checked all-behavior compiler. The value of the reduction is that future work
can target named source-alignment and ambient-reattachment lemmas, instead of
re-proving singleton LCP facts or assuming an unjustified second-order sign.

## Sources checked

- `QuittingTerminalExploitabilityWitness.fullSupport_fullNormalCore_of_finFour`
  and
  `exists_quantitative_fullSupport_fullNormalCore_of_finFour_of_no_uniformPayoff`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapConstrainedStationary.lean`.
- `exists_uniformEquilibriumPayoff_of_projectiveQBar_snell` in
  `UniformEquilibrium/Quitting/AbsorptionPath/PunishmentNormalPathStrategicSnell.lean`.
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff` and
  `uniformPayoff_or_nonempty_finFourQuantitativeFullSupportHardResidual` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`.
- `ResidualHardClass.exists_proper_nonprojectivePrincipal` and
  `FinFourQuantitativeFullSupportHardResidual.exists_nonprojectivePrincipal_card_two_or_three`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalSize.lean`.
- `FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing`,
  `FinFourQuantitativeFullSupportHardResidual.cardThree_externalHelper_or_cyclicBoundary`,
  and `FinFourQuantitativeFullSupportHardResidual.hardPrincipalDispatch` in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportHardPrincipalDispatch.lean`.
- `QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle.hasLargeBasePaidChainResidual`,
  `QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle.hasPaidRefinedSemanticResidual`,
  and
  `QuittingTerminalExploitabilityWitness.fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/StrictToggleLargeBasePaidChain.lean`.
- `ConstrainedFaceDirectionMotionRegression.constrainedFaceNash_with_positiveRadialPairCoefficient`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/NormalTerminalGapSecondOrder.lean`.
  This independently checked regression was developed by another agent; it is
  included here as a route constraint, not claimed as this notebook's work.
- `FourPointCrossedRowsNoCyclicSign.fullCoreMatrix_not_exists_relabelledCyclicOpenSignSkeleton`
  in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportLCPSignBarrier.lean`.
- The concrete source-matching obstruction in
  `UniformEquilibrium/Diagnostics/Quitting/Collision/Toggles/PaidMixedPureDeletedNashBarrier.lean`.

## Work

### 1. The projective-Q-bar chamber is closed

The projective-Q-bar implication is unconditional:

```text
IsProjectiveQBarMatrix (normalizedSoloMatrix reward)
  ⇒ ∃ payoff, (quittingGame reward).IsUniformEquilibriumPayoff none payoff.
```

It uses the punishment-normal path and strategic Snell compiler, not a supplied
stationary candidate. Consequently, a table with no uniform-equilibrium payoff
cannot be projective Q-bar. The theorem
`nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
combines this exclusion with the actual terminal witness, full normal core,
all-player punishment normality, and the quantitative full-support packet.

For this chamber the evidence seals are `M=yes`, `L=yes`, `A=yes`, `C=yes`:
the source is derived from the actual no-payoff assumption, and the rejected
projective-Q-bar branch has a checked unrestricted consumer.

### 2. The failed principal has size two or three

Full normal core transports the hard class's standard-Q theorem to the literal
full principal. Therefore the full principal cannot witness failure of
projective Q. A singleton principal is projective Q because its normalized
diagonal is zero. Since a projective-Q-bar failure is witnessed by a nonempty
principal, on `Fin 4` the witness has cardinality exactly two or three.

This is formalized by
`FinFourQuantitativeFullSupportHardResidual.exists_nonprojectivePrincipal_card_two_or_three`.
It is a strict reduction of the final residual, not a restatement of the
definition.

Evidence seals for the reduction are `M=yes`, `L=yes`, `A=yes`, `C=no`: the
principal is derived from the actual same-table residual, but the two surviving
sizes are not yet consumed into a uniform-equilibrium construction.

### 3. Exact dispatch of the two-coordinate principal

For a two-coordinate nonprojective principal `{first, second}`, both reciprocal
off-diagonal normalized singleton entries are strictly negative:

```text
normalizedSoloMatrix reward first second < 0,
normalizedSoloMatrix reward second first < 0.
```

The full-support packet's row-average inequalities then provide a positive
helper outside the principal for each harmed row. This is packaged by
`FinFourHardCardTwoCrossing` and produced by
`FinFourQuantitativeFullSupportHardResidual.cardTwoCrossing`.

The helpers need not be distinct. Moreover, the packet still has support on all
four players. Thus this does not manufacture a support-two packet and does not
yet align with the support-two collision compiler. It is exact crossed singleton
data with two outside helper labels, not a semantic collision source.

Evidence seals are `M=yes`, `L=yes`, `A=yes`, `C=no`.

### 4. Exact dispatch of the three-coordinate principal

For a three-coordinate hard principal, every principal column has an internal
negative entry. The full-support packet supplies a positive helper for the
corresponding harmed row. There are two exhaustive cases.

1. A helper is the unique player outside the principal. This is
   `FinFourHardCardThreeExternalHelper`: an internal negative owner/harmed pair
   is compensated positively through the outsider.
2. Every selected helper remains internal. The existing three-point sign graph
   then yields a forward or reverse cyclic orientation. If its cyclic
   determinant were positive, the existing three-player criterion would make
   the principal standard Q, hence projective Q, contradicting the selected
   failure. Therefore the determinant is nonpositive. This is
   `FinFourHardCardThreeCyclicBoundary`.

The theorem
`FinFourQuantitativeFullSupportHardResidual.cardThree_externalHelper_or_cyclicBoundary`
proves the dichotomy. `hardPrincipalDispatch` combines it with the card-two
branch.

The determinant conclusion points in the opposite direction from the existing
positive-determinant three-player compiler. The external-helper case also
records exactly why a restricted three-player solution cannot simply be lifted:
the fourth label is strategically visible in the singleton row, and arbitrary
deviations involving it still require control.

Evidence seals are `M=yes`, `L=yes`, `A=yes`, `C=no`.

### 5. Actual strict-toggle and paid-chain connector

The terminal witness also yields a reachable strict-toggle simple cycle from
every seed. On four players, a large persistent base on such a cycle is exactly
a `2+2` partition between persistent and free labels.
Its positive semantic `G`-gap enters the source-native paid-cell dispatch and
then the punishment-normal finite descent. This replaces the coarse large-base
cycle output by `HasLargeBasePaidChainResidual`.

The final cycle output `HasPaidRefinedSemanticResidual` is exactly one of:

1. a large-base support-two paid-chain residual;
2. a singleton persistent-base positive excess gap;
3. an empty persistent base with no interior simplex solution and positive
   defect gaps on every sufficiently small rho box.

The theorem
`QuittingTerminalExploitabilityWitness.fullSupport_fullNormalCore_with_paidRefinedCycle_of_finFour`
packages, on one reward table, the full packet/full-normal data and a reachable
cycle with this refined residual.

The source caveat is essential. The packet contributes only the initial seed
`packet.support`. The strict-cycle existence theorem works from every seed; its
terminal witness and toggle semantics, not the packet's mass equations,
produce the cycle and `G`-gap. No theorem currently says that the
eventual cycle preserves packet weights, crossing helpers, or the hard
principal labels. Thus this is a genuine same-table source-to-consumer
connection for the strict-toggle route, but not an alignment between the LCP
principal and the strict-toggle cycle.

Evidence seals for the aggregate connector are `M=yes`, `L=yes`, `A=yes`,
`C=no`: the actual terminal witness reaches checked consumers inside the paid
descent, but its surviving pure/mixed finite residues, the singleton-base gap,
and the empty-base gap have no complete downstream consumer. In particular,
the checked paid-mixed deletion regression shows that an arbitrary deleted pure
Nash cell need not retain the original paid premium; a source-matching theorem
is genuinely needed.

### 6. Second-order direction motion is a real obstruction

The independently checked theorem
`ConstrainedFaceDirectionMotionRegression.constrainedFaceNash_with_positiveRadialPairCoefficient`
constructs, for every scale in `(0, 1/3)`, a literal constrained stationary
face-Nash source whose hazards are positive and quantitatively comparable. Its
normalized directions converge to a full-support base direction. The fixed
radial polynomial has a positive quadratic coefficient, yet the exact face
numerator at the moving lower coordinate is negative.

Therefore constrained complementarity and hazard comparability alone do not
determine the sign of the pair layer. A valid compact-limit argument must retain
the direction-motion correction, or pass to a singleton-linear image and use a
preimage theorem such as
`exists_preimage_of_tendsto_apply_of_finiteDimensional`. This blocks a tempting
but false shortcut; it does not produce a terminal counterexample.

Evidence seals for this route constraint are `M=yes`, `L=yes`, `A=no`, `C=no`:
the regression is an exact constrained stationary source, but it has not been
derived from the final terminal-exploitability residual and is not itself a
uniform-equilibrium consumer.

### 7. Exact surviving chambers

After the checked reductions, a hypothetical four-player counterexample still
has both of the following descriptions on the same reward table, without any
known alignment between their selected labels.

**Singleton/LCP description:**

- card two: mutually harmful principal labels, each with an outside positive
  helper; the two helpers may coincide;
- card three, external-helper arm: an internal harmed row whose positive
  compensation passes through the unique outsider;
- card three, cyclic arm: forward or reverse cyclic orientation with cyclic
  determinant at most zero.

**Strict-toggle/semantic description:**

- large base: a `2+2` support-two paid chain, ending in either the normality-
  sharpened pure paid finite residual or the actual paid mixed finite residual;
- singleton base: a uniform positive singleton-base excess gap;
- empty base: no interior solution plus uniform positive rho-box defects.

No present theorem identifies the hard principal with the toggle cycle's base
or free set. No present theorem turns the full-support packet into a support-two
packet. No present theorem controls the fourth player's arbitrary deviations
after solving only a three-player principal. Those are mathematical residuals,
not documentation gaps.

### 8. High-value next lemmas

The following would be substantive because each would either align an actual
source with an existing consumer or remove a named chamber.

1. **Card-two semantic alignment.** From the actual terminal witness plus
   `FinFourHardCardTwoCrossing`, produce either an actual nonsingleton
   collision/toggle source on the harmed pair and its helpers, or a checked
   all-behavior stationary/sure-exit block. The theorem must handle coincident
   helpers explicitly; distinctness cannot be assumed.
2. **Card-three ambient reattachment.** Given
   `FinFourHardCardThreeExternalHelper`, solve or contract the restricted
   three-player block while controlling every deviation involving the unique
   outsider. A restricted LCP solution without this control is insufficient.
3. **Nonpositive cyclic determinant analysis.** Split the cyclic arm into
   determinant `< 0` and `= 0`, apply the exact existing three-by-three
   classification, and either produce an ambient four-player compiler input or
   prove a sharper obstruction. Do not invoke the positive-determinant compiler
   in this chamber.
4. **LCP-cycle label connector.** Use nonsingleton rewards or terminal-witness
   provenance to relate the selected hard principal to a reachable strict-toggle
   base/free partition. Same-table coexistence alone is not alignment.
5. **Paid source matching.** Strengthen the paid pure/mixed descent with a
   source-native correction or selected cell that preserves the paid premium.
   Any proposed statement must survive the concrete barrier in
   `PaidMixedPureDeletedNashBarrier.lean`.
6. **Singleton/empty cycle consumers.** Convert the singleton-base excess gap or
   the empty-base rho-box defect into an executable all-behavior block or a
   strict finite descent. These remain separate semantic chambers.
7. **Correct second-order compact limit.** Track the radial quadratic term and
   the first-order direction-motion correction jointly, and prove a range or
   sign constraint derived from the actual terminal residual. A sign theorem
   for the radial coefficient alone is false.

## Checks and open objections

The three new proof-mining modules compile directly and as named Lake targets:

- `StrictToggleLargeBasePaidChain.lean`;
- `FullSupportHardPrincipalSize.lean`;
- `FullSupportHardPrincipalDispatch.lean`.

Their capstone declarations report only the permitted axioms `propext`,
`Classical.choice`, and `Quot.sound`. The duplicate-proof check, derivable-
telescope check, whitespace check, trust-term scan, and non-import line-length
check pass for these modules.

The repository-wide trust command is not a clean signal in the current shared
worktree: it separately reports an unowned `DepProbe.lean`, deliberate
placeholders in `ephemeral/QuestionBankFakeProof.closed.lean`, and a stale
shared `AxiomAudit.lean`. None is imported by the three modules above. The root
integrator must regenerate the exhaustive audit after deciding which concurrent
new modules enter the production umbrellas.

Open objections:

- The principal dispatch uses only singleton rewards and packet averaging. It
  may still be too weak unless nonsingleton collision data is brought in.
- The strict-toggle connector is actual but label-agnostic relative to the hard
  principal.
- The paid route has checked intermediate consumers but no `C` seal for its
  aggregate residual; it must not be advertised as conjecture closure.
- The second-order regression prevents a naive sign proof but does not rule out
  a corrected jet argument tied to terminal provenance.

## Feedback wanted

1. In the card-two branch, can terminal exploitability force the two outside
   helpers to be distinct, or is the coincident-helper chamber realizable by a
   full quitting table satisfying the entire final residual?
2. Which existing all-behavior compiler has the weakest ambient hypothesis that
   could consume `FinFourHardCardThreeExternalHelper` without discarding the
   outsider?
3. Can a reachable strict-toggle cycle be selected so that its base or free set
   contains the hard nonprojective principal, using actual nonsingleton rewards
   rather than singleton sign data alone?
4. What is the correct finite-dimensional target space for the combined radial
   quadratic and direction-motion correction in the terminal compact limit?
