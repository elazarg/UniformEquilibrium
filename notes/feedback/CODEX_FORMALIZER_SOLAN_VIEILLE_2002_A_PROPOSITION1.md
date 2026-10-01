# Solan–Vieille 2002a Proposition 1 source producers

Source: [author-hosted journal PDF](https://www.math.tau.ac.il/~eilons/notequitting4.pdf),
Section 2, pages 366–370.

## Literal result and checked scope

`proposition1` (`Literature/future/SolanAndVieille2002a.lean`) is proved for
every reward table, every positive terminal accuracy, and every player count
at most three. The production theorem
`QuittingThreePlayerStrategyClass.of_card_le_three`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardAllSigns.lean`)
also permits any finite decidable player type of that cardinality.

The conclusion retains the paper's strategy-class disjunction: an actual
stationary root, or an actual date-indexed independent root sequence whose
every date/player Quit hazard is at most the requested accuracy. The selected
profile is terminal approximate Nash against every complete behavioral
replacement. All reward signs and zero Never payoff are retained. The profile
may depend on the accuracy; the statement does not select a fixed payoff target.

Both named modules and the full default build pass silently. The production
assembly is included in the exhaustive axiom audit; a separate transitive axiom
check of the public assembly and Literature theorem reports only `propext`,
`Quot.sound`, and `Classical.choice`.

## Existing proofs supplying the unrestricted result

1. `hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide`
   (`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`)
   supplies actual stationary roots or the remaining standard-Q normal-core side.
2. On exactly three players, the nonempty standard-Q normal core has at least
   three members, hence is the full player set. The actual full-core equivalence
   transfers Q and absence of homogeneous solutions to the original matrix
   (`UniformEquilibrium/Quitting/Classification/LCP/FullNormalCoreHomogeneousTransfer.lean`).
3. The three-dimensional classification constructs a labeled strict directed
   cycle of singleton differences. Its reward-level cycle and existing
   small-hazard compiler have no own-singleton sign hypothesis.
4. Canonical player reindexing transports the selected roots or root sequence
   with unchanged hazards and full behavioral terminal regrets. At cardinalities
   zero, one and two, the existing stationary producer already retains all signs.

This is source-to-strategy assembly, not a projection of ordinary three-player
uniform-payoff existence. Production does not import Literature or use an open
paper theorem.

## Other reusable source producers

`QuittingThreePlayerStrategyClass.of_normalizedThreePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`)
handles unit own-singletons, including weak and degenerate mixture supports.
Positive coordinate scaling and player-cardinality transport retain actual
strategies and Never payoff zero
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardTransport.lean`).
These scoped results remain useful; the unrestricted assembly removes the
need for a separate missing mixed-sign producer.

`exists_quiet_smallHazard_terminalNash_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowSmallHazard.lean`)
accepts independent positive accuracy and hazard budgets, retaining literal
Always Continue outside the child. It is stronger on its raw inverse/passive-row
subclass, not a replacement for the unrestricted strategy-class statement.

## Printed proof details and separate source status

The production subdivision uses `1 - (1 - beta)^(1/M)`, preserving block
survival `1 - beta`. The paper's printed `beta/M` has block survival tending
to `exp(-beta)` at fixed beta. The rates are distinct. Proposition 1's proof
does not establish the printed rate construction, constrained-map Case 0
argument, or intersection-triangle description. Those are proof-method details,
not remaining obligations for the literal proposition.

The introduction's solo-payoff-convex-hull assertion is separate.
`NoSoloHullUniformEquilibriumPayoffClaim`
(`Literature/future/SolanAndVieille2002a.lean`) remains an open proposition
definition in the audit. Stationary and near-Continue exclusions alone do not
establish a restriction on every uniform-equilibrium payoff. The paper remains
in the future lane pending that source coverage.

`Schedule.one_over_sixtyEight_lt_literal_exploitability`
(`UniformEquilibrium/Quitting/Examples/SolanVieilleBoundarySoloHazardSemantic.lean`)
also excludes every actual solo-hazard calendar, without a small-hazard or
periodicity premise. Applying it to an arbitrary hull-target equilibrium still
requires a source-supported conversion preserving full deviation caps. The
checked serialization theorem requires pointwise small hazards; a bound on
on-path collision mass alone does not control deleted-opponent histories or Never.
Alternatively, a direct terminal-payoff exclusion near each point of the
singleton hull would feed the existing fixed-target terminal-Nash consumer.
Neither bridge is supplied by the named profile-class exclusions.
