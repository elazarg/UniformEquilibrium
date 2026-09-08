# Simon path-law reuse audit

This is a static, declaration-level audit for the path-law obligation in Simon (2007). It does
not claim that `inducedLawSemantics_exists` is proved.

## Reusable results

- `ProbabilityTheory.Kernel.traj` in Mathlib's
  `Probability/Kernel/IonescuTulcea/Traj.lean` constructs a trajectory law from an arbitrary
  finite coordinate prefix. `traj_map_frestrictLe_apply` supplies every finite marginal.
- `traj_comp_partialTraj` is the exact continuation-composition identity.
  `partialTraj_compProd_eq_map_traj` supplies the joint law of a finite prefix and its next
  continuation. These are stronger and more appropriate here than constructing a second
  countable-product law.
- `condDistrib_trajMeasure` identifies the next-coordinate conditional kernel only almost
  everywhere. It does not by itself imply Simon's pointwise restriction identity for every
  positive finite history.
- `PMF.bindOnSupport`, `support_bindOnSupport`, `mem_support_bindOnSupport_iff`, and
  `bindOnSupport_pure` in Mathlib's probability-mass-function monad retain the proof that a
  successor has positive mass. `PMF.toMeasure_apply_eq_one_iff` and
  `PMF.restrict_toMeasure_support` transport support facts to measures.
- `Measure.comap` along `Subtype.val`, `map_comap_subtype_coe`, and
  `Measure.restrict_eq_self_of_ae_mem` transport a law concentrated on a measurable coherent
  set to the corresponding subtype. This avoids inventing a total repair of invalid paths.
- `StochasticGame.infinitePlayMeasureFromStagePMF` and
  `map_frestrictLe_infinitePlayMeasureFromStagePMF` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Core/Probability/InfinitePlayMeasure.lean`
  already instantiate Ionescu--Tulcea for fixed action carriers and prove finite marginals.
- `StochasticGame.DependentAction.histDist_game_eq_rawGame` in
  `UniformEquilibrium/ProofView/Concepts/Stochastic/Transform/ActionLegality/
  DependentActionPadding.lean` is a finite-law adapter only.
- `Math.Probability.HasAdaptiveFiniteMarginals` in
  `MathUE/Probability/FinitePathLawAdapter.lean` assumes an infinite law and therefore cannot
  provide the missing existence theorem.

The pinned experimental `StochasticInfinitePlayMeasure.lean` contains the closest implementation
pattern: exact-length accumulated histories, a support-dependent one-step law, a trajectory kernel,
and coordinate marginals. It starts only at the root, does not package coherent streams into a
path subtype, and proves no exact cylinder restriction identity. It is not a production dependency.

## Irreducible Simon adapters

`ae_follows_of_transition` and `map_supportedLawFrom`
(`MathUE/Probability/MarkovPathConcentration.lean`) supply the generic
concentration step and exact map-back for the carrier with a prescribed
initial state and allowed adjacent transitions. They reuse the trajectory
and subtype-measure APIs above. The paper-specific `historyTransitionKernel`
and `ae_historyTransitionKernel_extension` (`Literature/Simon2007.lean`)
retain positive transition support in possible finite histories.

The remaining paper-facing work is:

1. specialize the generic coherent-carrier concentration theorem;
2. identify coherent streams of accumulated histories with Simon's `InfiniteHistory`;
3. compute cylinder masses and prove the exact restriction identity at every positive extension.

Regularity is separate and already follows from the countable-observation topology once the
probability law has been constructed.
