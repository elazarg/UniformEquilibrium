# Absorption-weighted finite forward packets: Lean coverage

Packet: `ABSORPTION_WEIGHTED_FORWARD_PACKET_REDUCTION.md`.
Frozen SHA-256:
`5657d96e7a4da5decc9debc0a0499a587074ba523626ac3d7e3d0d4bce906359`.

Paths below are relative to the project root. The packet is retained unchanged;
its statements that the combined results are not yet Lean-checked describe
the export's preparation, not the coverage recorded here.

## Finite repair

`QuittingAbsorptionWeightedForwardPacket`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacket.lean`)
uses actual independent Boolean roots, displayed values, and a finite horizon.
Bellman residual and ordinary mixed-root regret are bounded by tolerance times
row absorption. Carrier membership and punishment floors include both endpoints;
only the first horizon roots and horizon-plus-one values are constrained.

`QuittingAbsorptionWeightedForwardPacket.repair`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketRepair.lean`)
constructs the exact packet at error `32 * B * ρ` from tolerance `B * ρ²`,
for `B > 0` and `0 < ρ ≤ 1/8`. Its literal quantitative projections are:

- `repair_horizon` and `repair_value_zero`: same length and initial annotation;
- `repair_root_coordinate_close`: root-coordinate change at most original
  row absorption times `ρ`;
- `repair_value_close`: value error at most `17 * B * ρ` at every displayed date;
- `half_total_charge_le_repair_total_charge`: at least half the entire input
  charge, not merely half a requested lower bound.

The output packet contains exact Bellman equations and the stated support,
floor, and box bounds. No lower bound on a nonzero row absorption is assumed.
Root purification and endpoint stability use the shared root interfaces in
`UniformEquilibrium/Quitting/Root/SupportPurification.lean`,
`UniformEquilibrium/Quitting/Root/AbsorptionWeightedRootPurification.lean`, and
`UniformEquilibrium/Quitting/Root/EndpointOpponentStability.lean`.
The generic Boolean-product comparison is in
`MathUE/PMFProduct/BooleanCoordinateStability.lean`.

## Producer equivalence and reward box

`HasExactFiniteForwardPackets` and `HasAbsorptionWeightedFiniteForwardPackets`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`)
keep the box fixed before every accuracy and charge request. They are source
propositions, not proofs that arbitrary games supply these families.

`exists_exactFiniteForwardPacketBox_iff_exists_absorptionWeightedBox`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`)
proves both directions of the exported equivalence. The upward translation
keeps roots and charge, enlarges the fixed box by two, and has the exact
Bellman residual stated by `quittingPayoffUpwardTranslate_sub_successor_eq`:
`2 * δ` times row absorption. Its ordinary regret is at most `3 * δ` times
row absorption.

`QuittingFiniteForwardPacket.clipSuffixLogarithmic`
(`UniformEquilibrium/Quitting/Projective/FiniteForwardPacketRewardBoxReduction.lean`)
proves the exported logarithmic charge estimate. Given sufficient input charge,
it returns a cut whose discarded charge is at most
`max 0 (log ((B-M)/η)) + 1`, and an exact packet with the required retained
charge. The returned packet is literally tied to this cut: its horizon is the
suffix length, its roots are the original suffix roots, its first value is
the clipped boundary value, and every retained value changes by at most `η`.
Its support and floor error increase by at most `η`.
The proof includes zero excess, zero reward bound, and an empty retained suffix.

`hasExactFiniteForwardPackets_rewardBox_of_box` uses that finite compiler.
`hasExactFiniteForwardPackets_rewardBox_iff_exists_absorptionWeightedBox`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketTranslation.lean`)
states the combined equivalence with the exact reward box on the exact side.

## Uniform-payoff consumer

`quittingGame_exists_uniformEquilibriumPayoff_of_absorptionWeightedPackets`
(`UniformEquilibrium/Quitting/Projective/AbsorptionWeightedForwardPacketProducer.lean`)
composes the repair with the existing compact finite-forward consumer. It
produces one fixed uniform-equilibrium payoff target from a supplied weighted
producer. The profile and horizon threshold may depend on accuracy; the target
does not. Deviations are unrestricted unilateral behavioral replacements.

## Boundary examples

`UniformEquilibrium/Diagnostics/Quitting/AbsorptionWeightedZeroChargeRampBoundary.lean`
proves the zero-table ramp's residual `1/H`, zero ordinary regret, unit-box
membership, zero punishment values, and zero charge. Exact recursive
recomputation is identically zero, while the final annotation error is one.
`ramp_residual_not_absorptionWeighted` records the failure of a weighted
residual bound. This is not a counterexample to a different charged producer.

`UniformEquilibrium/Diagnostics/Quitting/AbsorptionWeightedRareInferiorActionBoundary.lean`
constructs the actual one-row weighted packet `rareRoot_weightedPacket` with
ordinary defect `ε` but a supported Quit gap of one. All other defects,
the full successor vector, absorption, and punishment values are computed.
`supportPurifiedRoot_eq_prunedRoot` identifies the actual purifier, and
`prunedRoot_hasExactFiniteForwardPackets` proves all accuracy and charge
quantifiers for the repeated exact root.

## Scope and verification

These results prove the finite compiler, producer equivalence, reward-box
reduction, boundary examples, and the conditional uniform-payoff consumer.
They do not produce weighted packets for arbitrary Fin4 tables, prove a
converse from uniform-payoff existence, prescribe endpoints or source ancestry,
or realize arbitrary annotations as behavioral continuation payoffs.

Independent declaration review checked the core finite repair, producer
quantifiers, translation, and consumer scope. The final logarithmic compiler
was checked separately, including its literal suffix identities. The full
`lake --quiet --iofail build` passed with zero output after integration,
including the exhaustive axiom audit. Trust, import-graph, documentation,
cross-lane proof-duplicate, and redundant-hypothesis checks passed.
