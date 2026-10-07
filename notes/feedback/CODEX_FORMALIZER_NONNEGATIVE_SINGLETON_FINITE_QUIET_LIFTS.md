# Nonnegative-singleton finite quiet lifts: completion evidence

This record maps the frozen mathematical packet to integrated Lean declarations.
It supports completion review of this packet, not a claim about every four-player
quitting game or preservation of an arbitrary supplied child target.

## Frozen packet and checked snapshot

Packet: `math/exports/NONNEGATIVE_SINGLETON_FINITE_QUIET_LIFTS.md`.
Its SHA256 is
`7eab3636400635720e5379ed646c08a836a34e1df12147836eecdbb72e232134`.
The packet's archival “not yet implemented” sentence is not current Lean status.
The export was neither edited nor moved for this review.

The evidence snapshot is commit
`a0dc24b5e9ab1550e8b0533da44c29ece71eb209`. Its full default check,
`LEAN_NUM_THREADS=1 lake --quiet --iofail build`, completed silently with exit
zero (authoritative session 82927). Fresh trust, import-graph, 14 import-graph
regression tests, proof-duplicate, derivable-telescope, documentation, width,
and diff checks passed. The exhaustive default `AxiomAudit` permits only
`propext`, `Quot.sound`, and `Classical.choice`.

The producer and boundary sources listed below were directly imported by both
`UniformEquilibrium.lean` and `AxiomAudit.lean` at that snapshot. Their current
contents were compared against its Git blobs and are unchanged. This is
full-build evidence for those sources, not just a lexical scan or a claim based
on an unbuilt draft. New unrelated work in the checkout is outside that seal.

## Packet-to-declaration map

All unqualified declarations below are in namespace `GameTheory`.
The table separates actual source selection from the already checked debt and
finite-horizon consumers it uses.

| Packet section / obligation | Checked declaration and source |
| --- | --- |
| Statement from finite reward data: actual finite independent quiet laws, quantitative bounds, no supplied child profile | `exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily` in [WithdrawalFiniteQuietSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean) |
| Statement: one fixed target selected before accuracy, with witnesses from the same actual finite quiet family | `exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily` in [WithdrawalFiniteQuietSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean) |
| Proof, equations (2)–(3): move only the original Never atom to a legal finite date; no attained best response | `quittingTerminalPayoff_moveNeverToFinite_sub_eq`, `neverMass_mul_opponentNeverProduct_mul_singleton_le_terminalDebt`, and `prod_stoppingLaw_none_mul_singleton_le_terminalExploitability` in [SingletonJointNeverDebt.lean](../../UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean) |
| Proof, equation (4): select in the perturbed low-player game and evaluate the same laws at original rewards | `exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton` in [NonnegativeSingletonEarlyAbsorption.lean](../../UniformEquilibrium/Quitting/Classification/ThreePlayer/NonnegativeSingletonEarlyAbsorption.lean) |
| Proof, equations (5)–(6): use original certificates, retain the Never residual, and choose finite constants before accuracy | `exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily` in [WithdrawalFutureJoinFixedTarget.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinFixedTarget.lean), using `withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess` in [WithdrawalFutureJoinDebt.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinDebt.lean) |
| Proof, equation (7): finite censoring with the stated original-game regret and joint-Never bounds | `exists_finiteQuietProfiles_of_withdrawalFutureJoinFamily` in [WithdrawalFiniteQuietSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean), using `exists_finiteQuietLift_of_profile` in [QuietLiftFiniteCensor.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/QuietLiftFiniteCensor.lean) |
| Five-kind withdrawal extension: independently chosen patient, deadline, evaluated-security, terminal-security, or cancellation certificates | `exists_uniformFiniteQuietFamily_of_withdrawalFutureJoinFamily` and `quittingGame_exists_uniformEquilibriumPayoff_of_nonnegativeSingleton_withdrawalFamily` in [WithdrawalFiniteQuietSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean); inputs are `WithdrawalFutureJoinRewardCertificate` in [WithdrawalFutureJoinRaw.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFutureJoinRaw.lean) |
| Five-kind extension / Lean handoff: zero-singleton Fin4 boundary and canonical pivot repair | `quittingGame_exists_uniformEquilibriumPayoff_of_finFour_nonnegativeWithdrawalFamily` in [WithdrawalFiniteQuietSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalFiniteQuietSource.lean); `smallPivotRepairValue_of_deleted_nonnegativeSingleton_withdrawalFamily` and `smallPivotRepairValue_of_finFour_singlePivotSingletons_withdrawalFamily` in [WithdrawalSmallPivotRepairSource.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalSmallPivotRepairSource.lean) |
| Source boundary: the omitted Never residual cannot be removed for arbitrary supplied child profiles | `CappedClockMissingNeverFixture.neverExcess_eq_one`, `.childProfile_exactTerminalNash`, and `.liftedProfile_outsiderDebt_eq_one` in [CappedClockMissingNeverFixture.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/CappedClockMissingNeverFixture.lean); actual correction and positive-singleton charging are `withdrawalOutsideTerminalDebt_le_shiftedDebt_add_neverMass` and `withdrawalNeverResidual_le_pivotDebt` in [WithdrawalNeverResidual.lean](../../UniformEquilibrium/Quitting/Classification/QuietExtension/WithdrawalNeverResidual.lean) |
| Source boundary: removing the nonnegative sign fails for every quiet profile, including literal Fin4, but not for parent equilibrium | `NegativeSingletonQuietBoundary.debts_eq_childClockMasses`, `.exploitability_ge_half`, `.finFour_quietLift_exploitability_ge_half`, and `.outsiderQuitProfile_exactNash` in [NegativeSingletonQuietBoundary.lean](../../UniformEquilibrium/Quitting/Examples/NegativeSingletonQuietBoundary.lean) |
| Why a prescribed child target cannot be retained: original five-kind certificates and exact zero child equilibrium | `PrescribedChildTargetQuietBoundary.certificate`, `.childAllNever_exactNash`, and `.childAllNever_payoff_zero` in [PrescribedChildTargetQuietBoundary.lean](../../UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean) |
| Prescribed-target obstruction: actual unrestricted debts, asymptotic obstruction, and quiet uniform witnesses | `PrescribedChildTargetQuietBoundary.one_le_three_exploitability_add_childPayoffs`, `.not_tendsto_zero_regret_and_childPayoffs`, and `.no_quiet_uniformWitnesses_extending_zeroChild` in [PrescribedChildTargetQuietBoundary.lean](../../UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean) |
| Prescribed-target boundary: alternative exact quiet equilibria with the two different selected child targets | `PrescribedChildTargetQuietBoundary.firstChildQuit_exactNash`, `.secondChildQuit_exactNash`, `.alternative_childPayoffs`, and `.alternative_equilibria_quiet` in [PrescribedChildTargetQuietBoundary.lean](../../UniformEquilibrium/Quitting/Examples/PrescribedChildTargetQuietBoundary.lean) |

## Exact scope of the source theorem

The parent is any finite player set. The child is nonempty and proper, has at
most three players, and contains at least one nonnegative own singleton. Each
outsider supplies one original finite five-kind certificate; no certificate for
the perturbed reward table, prescribed child laws, Never inequality, or favorable
child target is an input.

The finite producer chooses constants `factor` and `residual` before any positive
`delta`, then selects actual independent finite child marginals and a positive
deadline. For a valid original reward bound `bound`, it proves

- parent full exploitability at most
  `(factor + residual) * delta + (factor + 4 * bound) * delta²`;
- actual child joint-Never probability at most `delta + delta²`.

The indexed-family theorem proves both quantities tend to zero. It selects one
parent payoff before the requested accuracy and retains a member of this same
family for delivery and every behavioral deviation over all sufficiently large
finite horizons. The Fin4 wrapper derives the child-cardinality bound internally.

The pivot adapter allows any actual parent repair pivot, independently of the
deleted set or the child singleton used for selection. Its LP competitor is the
produced finite quiet profile; no optimal-pivot compatibility premise is added.
The literal canonical own-singleton vector `(1,0,0,0)` is covered at any pivot
label, conditional on its original certificates.

## Boundary interpretation and completion verdict

The omitted-Never fixture has an exact zero-debt all-Never child and outsider
debt one. The negative-singleton fixture has all original five-kind zero-weight
certificates but every quiet profile has exploitability at least one half; it
also exhibits an exact nonquiet parent equilibrium. The prescribed-target
fixture is literal Fin4 with two children and two outsiders, one payoff-neutral;
it denies quiet uniform witnesses extending child target `(0,0)` while supplying
exact quiet alternatives with child targets `(0,1)` and `(1,0)`.

Thus the packet's source theorem, quantitative finite-family bounds, fixed-target
quantifier order, five-kind extension, canonical pivot source, and both sign and
target-selection boundaries have integrated checked declarations. No remaining
Lean obligation from this packet was found in this audit. Completion does not
assert that all Fin4 tables admit the certificates, that every child target can
be extended, or that this class is disjoint from other solved classes. Export
retirement remains a separate mathematical-owner decision.
