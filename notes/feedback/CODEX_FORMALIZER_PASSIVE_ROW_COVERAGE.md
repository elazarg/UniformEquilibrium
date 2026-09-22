# Three-player passive-row packet: Lean coverage

This is a declaration-level audit of
`math/exports/THREE_PLAYER_CYCLE_PASSIVE_ROW_EXTENSION.md`. It records the
route checked by direct Lean and named builds; the repository-wide build and
generated audits are separate checks.

## Checked raw-table route

`exists_uniformEquilibriumPayoff_of_raw_nonnegativeInverse_triple`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/RawPassiveRowInverseCriterion.lean`)
states the packet's raw criterion for any finite parent player type and a
selected survivor subtype of cardinality three. Its hypotheses are
invertibility of the literal child singleton-difference matrix `T`,
entrywise nonnegativity of `T⁻¹`, and entrywise nonnegativity of each outside
row `ΓₖS T⁻¹`. The conclusion is one uniform-equilibrium payoff of the
original parent quitting game. No cycle, strategy, payoff target, or
factorization certificate is a hypothesis. The `inverseWeight` and
`factorization` declarations in the same file establish the receiver-row,
singleton-owner-column orientation and derive `ΓₖS = (ΓₖS T⁻¹)T` by the
matrix inverse identity.

The construction reuses
`exists_balancedCertificate_of_strictlyPositiveInverse_child`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/StrictInversePassiveRowCycle.lean`)
and the generic `PassiveSingletonRowFactorization.certificate`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonPassiveRows.lean`).
The weak inverse boundary is covered by
`exists_uniformEquilibriumPayoff_of_nonnegativeInverse_passiveRows`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/WeakInversePassiveRowCycle.lean`):
its nearby parent tables perturb only child singleton columns, preserve the
same outside weights, and use reward-table closure to select a fixed target
for the original table. The semantic endpoint is
`BalancedSingletonCycleCertificate.isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`).

## Exact fixture and open class

`childMatrix_inverse`, `outside_row_factorization`, `certificate`, and
`target_isUniformEquilibriumPayoff`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourFixture.lean`)
check the displayed rational four-player singleton matrix, its selected
triple inverse, the outside weights `(8,2,11)/7`, and the fixed target with
surplus `(0,1,0,2/7)`. The target result applies to every reward completion
with that singleton-difference matrix; nonsingleton rewards and own
singleton levels are unrestricted.

`strict_support_inventory`, `admissible_supports_eq`, and `r0Degree_eq_one`
(`UniformEquilibrium/Quitting/Classification/LCP/ThreeCore/PassiveRowFourDegreeNeighborhood.lean`)
check the exact finite-support inventory and R₀ degree `+1` for the displayed
matrix. `exists_open_reward_neighborhood` gives a nonempty open set in the
entire terminal reward-table space, not a relative zero-diagonal matrix
space. Every table in this set retains degree `+1`, a strictly positive
selected inverse, and positive outside inverse weights.
`exists_open_degree_one_uniformPayoff_class` transports these matrix facts to
the literal subtype-indexed raw criterion and proves that every game in the
open set has a fixed uniform-equilibrium payoff. These declarations passed
silent direct Lean checks and named builds; repository-wide checks are
separate.

## Remaining packet outputs

The comparisons excluding the packet matrix from the named full-inverse,
projective Q-bar principal, integral-tournament, and once-per-owner
signed-four-cycle classes lack literal fixture declarations. The four
attempted-falsifier tables and the weak-boundary hazard limit have not been
checked as packet-specific results.

The balanced-certificate compiler gives terminal and finite-horizon control,
but the packet's sharper calendar bound `O(η⁻¹ log(1/η))` and exact rational
stopping-law claim are not stated by this route. A named four-player
contrapositive and a named conclusion exposing Never for every outside
player are likewise absent, although the raw existence theorem and the
owner-only cyclic profile give their respective underlying implications.
