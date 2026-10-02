# Response-invariant partitions and the scope of degree escape

Status: ordinary-mathematics criterion using integer Brouwer degree; no new
Lean declaration is asserted here. This note records the mathematical
increment and its implementation boundary, not an export decision.

## Exact question

For a finite quitting game with independent private clocks and zero Never
payoff, can an invariant subspace of the individual stationary-response
equations detect absorbing equilibria when the full singleton matrix has
integer LCP degree +1?

Write sᵢ=rᵢ({i}) and Γᵢⱼ=rᵢ({j})−sᵢ. For stationary hazards q, let αᵢ
be the probability that every opponent Continues, Qᵢ the expected Quit-now
reward, and Hᵢ the unconditional reward from nonempty opponent quitting sets
while i Continues. Put Δᵢ=(1−αᵢ)Qᵢ−Hᵢ.

Partition players into nonempty blocks and let E repeat one hazard per block.
Assume Δᵢ(Ex)=Δⱼ(Ex) for players in the same block and every x in the block
cube. This is a polynomial identity in hazards and a finite linear condition
on reward entries. Differentiation at zero defines a quotient matrix A with
ΓE=EA. Its entries are sums over blocks, not averages.

## Criterion and semantic scope

If A is R0 and its integer LCP degree κ(A) differs from +1, a nonzero
block-constant product hazard q satisfies exact Nash–Bellman equations at
its actual stationary terminal payoff. The proof compares the global degree
+1 of x↦x−clip(x+Δ̄(x)) with its local degree κ(A) at zero.

The quotient is not a smaller quitting game. Equal hazards do not correlate
the coins, and each original player's unilateral condition remains separate.

- With at least two active original players, the stationary profile is exact
  terminal Nash against every behavioral deviation and is uniform at its
  payoff.
- A sole active player can only belong to a singleton block. A nonnegative
  own-singleton reward makes Never unprofitable. Under punishment normality,
  a negative sole owner is instead handled by finite solo prefixes followed
  by independent punishment plans, giving terminal approximants at one target.
- For Fin4, the no-UE hypothesis supplies same-table punishment normality.
  Thus the raw quotient criterion gives UE for arbitrary signed rewards.

Consequently a Fin4 counterexample must have R0 and degree +1 on every
response-invariant partition, not only on the discrete partition.

## Strict change relative to the full-matrix test

For

    Γ = [ 0  3 −1 −1
          3  0 −1 −1
         −1 −1  0  3
         −1 −1  3  0 ],

the full matrix is R0 of degree +1. If the centered recipient rows of
players 0 and 1 match after swapping their labels, the partition
{0,1},{2},{3} is response-invariant and has quotient

    A = [ 3 −1 −1
         −2  0  3
         −2  3  0 ].

Here det A=−15 and A⁻¹>0, so its degree is −1. This covers 33 freely
chosen nonsingleton reward entries and four arbitrary own-singleton levels.
The other two recipients' nonsingleton rows need not respect the swap.

The direct zero-discount local-degree argument itself is also present in
the cardinal-free stationary repair analysis. The additional restriction
on counterexamples is the response-invariant quotient criterion. It is
not a new exclusion of every full-matrix degree-one table.

A generic reward table may admit no nondiscrete response-invariant partition.
The theorem neither creates that identity by averaging games nor supplies
an invariant partition for every table. The explicit fixture also has a
nondegenerate stationary solution, hence persists under small arbitrary
symmetry-breaking perturbations; this does not extend the full unrestricted
33-coordinate class without its defining row identity.

## Named tracked dependencies inspected

- `isR0Matrix_quittingSingletonMatrix_of_normal_of_no_uniformPayoff`
  (`UniformEquilibrium/Quitting/Classification/LCP/PunishmentNormalR0.lean`).
- `exists_uniformEquilibriumPayoff_of_homogeneous_supported_normal`
  (`UniformEquilibrium/Quitting/Classification/LCP/HomogeneousProductionNormalDispatch.lean`).
- `nonempty_finFourQuantitativeFullSupportHardResidual_of_no_uniformPayoff`
  (`UniformEquilibrium/Diagnostics/Quitting/Collision/SingletonPacket/FullSupportProjectiveQBarResidual.lean`).
- `quittingStationaryFullRateUnilateralCap_le_of_fixedPoint_endpointNash`
  and `isZeroAsymptoticNash_stationary_iff_endpointNash_and_boundary`
  (`UniformEquilibrium/Quitting/Stationary/EndpointCompiler.lean`).
- `quittingGame_isUniformEquilibriumPayoff_of_terminalNash_tendsto`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).

These cover the strategic endpoints, not the new quotient degree producer.
The implementation question is to formalize that producer with the same
ambient min-map convention, retaining boundary and nonisolated roots.
