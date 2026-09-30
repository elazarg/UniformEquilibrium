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

The paper imposes no global reward-sign or normalization restriction on that
statement. Its Section 2.2 discussion subsequently restricts to strictly
positive own-singletons and normalizes those coordinates to one. That local
proof-discussion restriction does not narrow the literal Proposition 1.
The source defines Never payoff as zero, so multiplicative coordinate
scaling is appropriate; additive terminal-only translation is not a neutral
normalization of this strategy-class claim.

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

## Transport adapter scope

`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazardTransport.lean`
passed the build owner's targeted Literature closure check, including the
canonical player-reindexing proofs and thin Literature wrappers. The separate
positive-adapter axiom audit also passed, with declaration existence checked
and only `propext`, `Quot.sound`, and `Classical.choice`; none of the proved
wrappers depends on the unrestricted Literature sorry. The full silent default
build, including the exhaustive production axiom audit, also passes. Its
`QuittingThreePlayerStrategyClass.of_positiveSoloThreePlayer` multiplies each
reward coordinate by its positive own-singleton reciprocal and uses the
checked normalized producer. Scaling back with zero shift retains the same
root or root sequence and preserves Never payoff zero. The normalized accuracy
is chosen small enough to bound both terminal exploitability and the original
date/player hazard accuracy.

`QuittingThreePlayerStrategyClass.of_reindex` uses the existing behavioral
pullback and finite-average payoff equality. The generic
`quittingTerminalPayoff_quittingProfilePullback` and
`isεAsymptoticNash_quittingProfilePullback` proofs live in
`UniformEquilibrium/Quitting/Classification/PlayerReindex.lean`.
Terminal payoff equality follows from the existing finite-average convergence theorem;
complete behavioral
unilateral deviations are transported through the existing history equivalence
and profile-update identity. Stationary roots remain stationary, and a literal
date-indexed root sequence remains such a sequence with unchanged hazards.

`QuittingThreePlayerStrategyClass.exists_stationaryTerminalNash_of_card_le_two`
uses the actual Bool stationary producer and the existing empty/unique-player
branches. All reward signs are retained at those cardinalities.
`QuittingThreePlayerStrategyClass.of_positiveSolo_of_card_eq_three` and
`QuittingThreePlayerStrategyClass.of_card_le_three_of_positiveSolo_when_three`
cover arbitrary finite player types. The latter requires strictly positive
own-singletons only when there are exactly three players. Thin Literature
wrappers retain this distinction; the unrestricted `proposition1` remains
`sorry`. The adapter wave passes both targeted and full-build checks.

## Remaining source adapters

### Existing all-sign stationary branches

`QuittingThreePlayerStrategyClass.of_stationaryApproximateEquilibria`,
`of_homogeneousMatrixBranch`, `stationaryAlternative_or_standardQMatrixSide`,
and `of_not_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`)
retain actual stationary roots from the existing producers for arbitrary
finite player types and reward signs. Their four thin Literature consumers
pass the targeted Literature build and a separate declaration-existence and
axiom audit. Only the allowed three axioms occur. The full silent default
build, exhaustive production axiom audit and repository CI script gates pass
for this adapter wave.

The unconditional matrix alternative is supplied by
`hasQuittingStationaryApproximateEquilibria_or_standardQMatrixSide`
(`UniformEquilibrium/Quitting/Classification/LCP/StationaryExistence.lean`).
The remaining side has a nonempty normal core, no homogeneous simplex
solution and a standard-Q normal-core matrix. Neither reward signs alone
nor ordinary UE existence supplies its source strategies. The all-nonpositive
own-singleton case already has the literal all-Continue branch. Together
with the checked positive-singleton and low-cardinality transports, these
results restrict unfinished unrestricted Proposition 1 coverage to
three-player source cases on that matrix side with both a positive and a
nonpositive own-singleton reward.

### Source reconstruction still needed

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
give the complete argument there and cites Solan (1999) for the unrestricted
result. An actual stationary-or-small-hazard producer for three-player tables
with nonpositive or mixed-sign own-singletons is still needed to discharge
the literal theorem. The all-nonpositive zero-solo branch is already available.
Ordinary all-sign uniform-payoff existence does not itself supply the required
strategy classes. This is a known-source proof-reconstruction and formalization
boundary, not a newly proposed mathematical conjecture or a claim that
Proposition 1 is false. No conference question is created for the routine
scaling or relabeling adapters.

## Nearest all-sign source dependency

Bounded inspection of the [author-hosted Solan (1999) scan](https://www.math.tau.ac.il/~eilons/three.pdf)
identifies Theorems 4.5 and 4.7 and Lemmas 5.2, 5.3, and 5.5 as the relevant
endpoint, finite-alternative, and strategy-construction interfaces.
Lemma 5.2 literally builds an almost-stationary profile with statistical-test
punishment. Its equilibrium-payoff conclusion is not by itself a theorem
about an actual stationary root in the present quitting model.

The existing production consumers already supply actual roots in several
all-sign branches:

- `isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo`
  (`UniformEquilibrium/Quitting/Punishment/ZeroSoloDisjunct.lean`);
- `isεQuittingStationaryNash_zero_of_shiftedGerm_absorbingEndpoint_contracts`
  (`UniformEquilibrium/Quitting/Classification/LCP/OrdinaryNonQProducer.lean`),
  when every fixed-opponent product contracts;
- `isQuittingStationaryUniformEquilibriumPayoff_of_shiftedGerm_isolatedEndpoint_of_blocker`
  (the same file), when a distinct nonpositive singleton-matrix blocker is supplied;
- `isεAsymptoticNash_homogeneousScaledRoot_of_nonvertex`
  (`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProducer.lean`),
  for a supplied nonvertex complementary mixture;
- `QuittingThreePlayerStrategyClass.of_rightSingletonCycle` and
  `QuittingThreePlayerStrategyClass.of_leftSingletonCycle`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/StationaryOrSmallHazard.lean`),
  for supplied strict cycles, without own-singleton positivity assumptions.

These are straightforward strategy-class projection/assembly inputs, but do
not yet exhaust arbitrary sign tables. In particular, the auxiliary absorbing
endpoint compiler currently closes a punishment-admissible cycle rather than
a stationary root; a noncontracting negative-solo endpoint needs an actual
stationary repair or another source alternative. The complementary singleton
dispatch likewise closes through finite circulation and does not expose the
stationary-or-small-hazard class in its vertex/boundary cases. A distinct
source-to-strategy-class sign-case assembly is therefore needed, not a
projection of the unconditional uniform-payoff theorem. No new Lean or new
mathematical claim is introduced by this dependency inspection.
