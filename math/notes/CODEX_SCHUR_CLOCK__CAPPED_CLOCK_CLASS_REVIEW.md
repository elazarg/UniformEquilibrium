# Capped-clock class comparison

The reviewed capped-clock criterion gives a valid conditional construction for
independent private quitting laws. Its paired family lies strictly beyond the
exact dispensability gate and has no balanced singleton certificate. These are
ordinary mathematical conclusions, not new Lean-checked declarations.

The self-contained question is whether fifteen raw reward inequalities for a
fixed nonnegative multiplier vector compare every outside stopping-law
replacement with separately legal unilateral child replacements, and whether
their accepted four-player class is distinct from existing deletion and
balanced-singleton classes. The detailed answer and infinite-spine proof are
in [the independent feedback](../feedback/CAPPED_CLOCK_DEVIATION_DOMINATION__BY_CODEX_SCHUR_CLOCK.md).

The bounded route selection uses the cyclic singleton escort route in
`docs/FRONTIER.md` and the finite-menu/full-cap interfaces in `docs/TOOLKIT.md`.
The source dependencies inspected are:

- `BalancedSingletonCycleCertificate`
  (`UniformEquilibrium/Quitting/Cycles/BalancedSingletonCertificate.lean`):
  hazard bounds, exact arcs, owner ties, singleton floors, opponent divergence.
- `IsQuittingSingletonEscortEdge`,
  `BalancedSingletonCycleCertificate.escortEdge_of_coarse_bridge`,
  `BalancedSingletonCycleCertificate.escortEdge_of_owner_change`, and
  `BalancedSingletonCycleCertificate.exists_escortCycle`
  (`UniformEquilibrium/Quitting/Cycles/CyclicSingletonEscort.lean`).
- `QuittingBlockJoinAntitone`, `quittingBlockContinueFloor`,
  `le_quittingBlockContinueFloor`, `QuittingBlockDispensable`, and
  `quittingGame_exists_uniformEquilibriumPayoff_of_blockDispensable`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletion.lean`).
- `quittingBlockJoinCap` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_vanishingAbsorption`
  (`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_threePlayer`
  (`UniformEquilibrium/Quitting/Classification/ThreePlayer/Existence.lean`).
- `quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors` and
  `quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors`
  (`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`).
- `exists_finiteDeadlineTimingProfile_approximation` and
  `isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation`
  (`UniformEquilibrium/Quitting/Terminal/FiniteMenuFullProfileApproximation.lean`).
- `prod_stoppingLaw_none_mul_singleton_le_terminalDebt`
  (`UniformEquilibrium/Quitting/Terminal/SingletonJointNeverDebt.lean`).

The strict-triple argument uses exact balance, all-player floors, actual
continuations, and joint absorption. The initial owner block can be partial;
its survival is bounded below by the corresponding full canonical block's
survival. This preserves the claimed one-revolution response lower bound.
Approximate balance and unrestricted child-strategy completeness are outside
that statement.

No paper theorem is a mathematical premise of this review. The literature
transcription README and narrow distinctive-phrase searches provide overlap
navigation only. Exact checker calls are finite regression evidence; the
universal assertions rest on the written proofs and the cited source inputs.
