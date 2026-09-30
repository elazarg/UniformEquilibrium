# Solan–Vieille 2002a Proposition 1 source producers

Source: [author-hosted journal PDF](https://www.math.tau.ac.il/~eilons/notequitting4.pdf),
Section 2, pages 366–370. This source-coverage record distinguishes targeted
Lean checks from full-build and unconditional-integration claims.

## Literal scope

`Proposition1Claim` (`Literature/future/SolanAndVieille2002a.lean`) retains every
reward table, every positive terminal accuracy, and every player count at most
three. Its conclusion is the source strategy-class disjunction: one stationary
root, or one date-indexed independent root sequence with every player's Quit
hazard bounded by the requested accuracy. It does not substitute uniform-payoff
existence for that disjunction. The unrestricted theorem remains `sorry` in
Literature.

## Concrete producer wave

The PairRepair proofs already construct stationary roots. They are exposed by
`exists_stationaryRoot_terminalNash_approxTarget_all_errors_of_pairRepair`,
`exists_stationaryRoot_terminalNash_approxTarget_all_errors_of_mirrorPairRepair`,
and `exists_stationaryRoot_terminalNash_approxTarget_all_errors_of_bool_pairRepair`
(`UniformEquilibrium/Quitting/Classification/TwoPlayer/PairRepair.lean`). Their
original behavioral-profile APIs project these stronger results.

`quittingGame_exists_stationary_terminalApproximateEquilibrium_twoPlayer`
(`UniformEquilibrium/Quitting/Classification/TwoPlayer/Existence.lean`) retains
the original four-way source split and returns an actual stationary root at
every positive accuracy. The original uniform-payoff theorem now selects its
fixed target from those roots. This is not an additional mathematical
existence assumption.

The Literature adapters `proposition1_twoPlayer`, `proposition1_zeroSolo`,
`proposition1_of_soloStationaryCertification`, `proposition1_case1`, and
`proposition1_case4` retain the stationary roots supplied by these producers.
Case 1 retains weak inactive-player comparisons; Case 4 includes simplex
vertices and nonvertices. Both geometric cases retain the source normalization
that each own-singleton reward is one.

`proposition1_of_singletonArcCycle` uses
`singletonArcCycle_isTerminalNash_and_hasValue`
(`UniformEquilibrium/Quitting/Cycles/SingletonArcCycle.lean`) and its explicit
subdivided root. Choosing the subdivision count large enough simultaneously
bounds terminal exploitability and every date/player hazard. It consumes the
coarse arc certificate.

`proposition1_of_normalizedFeasibleSingletonMixture` assembles
`three_singleton_source_alternative`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/SingletonAlternative.lean`).
The complementary branch retains stationary roots, including vertices; strict
right/left branches use the existing concrete coarse arcs and the small-hazard
adapter. The finite alternative already includes degenerate source supports.
The matrix-to-cycle adapters `rightCycle_of_excess` and `leftCycle_of_excess`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/SingletonDispatch.lean`)
are public with unchanged proof bodies, avoiding a duplicated geometric proof.

`proposition1_case2` uses the generic original-reward
`quittingGerm_allContinue_zeroSolo_or_projectivePacket`
(`UniformEquilibrium/Quitting/Classification/LCP/OrdinaryNonQProducer.lean`).
The packet's positive singleton mass normalizes to a feasible mixture, so the
source infeasibility hypothesis forces an absorbing analytic endpoint. The
existing endpoint compiler and nonnegative own-singletons give an actual exact
stationary terminal Nash root, not merely an unspecified uniform-payoff target.

`proposition1_normalizedThreePlayer` combines the feasible and infeasible
branches for every table with own-singleton rewards one and every positive
accuracy. The proof closure resides in
`QuittingThreePlayerStrategyClass.of_normalizedThreePlayer`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`).
The Literature declarations are thin wrappers; production does not import
Literature. The normalized producer, its feasible/infeasible branches, and all
preceding Proposition 1 adapters passed the build owner's targeted check of
`Literature.future.SolanAndVieille2002a`. A separate declaration-existence and
axiom audit of every positive adapter also passed: only `propext`, `Quot.sound`,
and `Classical.choice` were used. The intentional `proposition1` sorry was
excluded from that positive-adapter audit. The two-player production target
passes separately. The full default repository build, including the
regenerated exhaustive production axiom audit, also passes without diagnostics.

## Remaining source adapters

The targeted-checked normalized producer uses an existing analytic-germ and finite-alternative
route to the strategy-class conclusion. It does not formalize the source's
constrained-map proof of Case 0, the compact separation gap reducing Case 2 to
Case 0, the explicit finite Case 3 reduction, or the source's intersection
triangle description. These source-method obligations are separate from the
normalized strategy-class producer and are not missing new mathematics.

Strict right/left cycle tables already have concrete rates and coarse arc
certificates in `UniformEquilibrium/Quitting/Classification/ThreePlayer/CyclicCompiler.lean`:
`right_coarse_arc`, `left_coarse_arc`, the active-coordinate and floor lemmas,
and the opponent contraction lemmas. The normalized feasible adapter consumes
them through the existing finite alternative; it does not reprove the source
triangle description.

## Printed subdivision distinction

The journal PDF prints the Case 5 rate `beta_i/M` at each of the owner's `M`
block stages. The exact subdivision used by the production compiler is
`1 - (1 - beta_i)^(1/M)`, which preserves block survival `1 - beta_i`.
For fixed `beta_i`, the survival of the printed rate tends instead to
`exp(-beta_i)`. The rates are therefore distinct. The strategy-class adapters
do not prove the literal printed-rate construction; this source-audit issue
is separate from Proposition 1's strategy-class conclusion.

The production three-player unconditional uniform-payoff theorem separates
analytic endpoints and may use punishment-completed cycles. Its uniform-payoff
conclusion alone does not prove Proposition 1's restricted strategy class.

The source only mentions the remaining own-singleton sign cases; it does not
give the complete argument there. An all-sign, at-most-three-player
stationary-or-small-hazard producer, positive coordinate-payoff scaling, and
the player-type/cardinality transports
must still be supplied to discharge the literal theorem. These are outstanding
formalization/source-adapter obligations, not a claim that Proposition 1 is false.
