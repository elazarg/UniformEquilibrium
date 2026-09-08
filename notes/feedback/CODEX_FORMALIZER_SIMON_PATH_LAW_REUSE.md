# Simon path-law reuse audit

`inducedLawSemantics_exists` (`Literature/Simon2007.lean`) is proved in Lean
from the profile-generated history laws. Its axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`; no unfinished paper proof is
used. The reuse map below records the construction's dependencies.

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

## Constructed Simon adapters

`ae_follows_of_transition` and `map_supportedLawFrom`
(`MathUE/Probability/MarkovPathConcentration.lean`) supply the generic
concentration step and exact map-back for the carrier with a prescribed
initial state and allowed adjacent transitions. They reuse the trajectory
and subtype-measure APIs above. The paper-specific `historyTransitionKernel`
and `ae_historyTransitionKernel_extension` (`Literature/Simon2007.lean`)
retain positive transition support in possible finite histories.

`coherentHistoryStreamLaw` and `profileHistoryLaw`
(`Literature/Simon2007.lean`) instantiate the coherent-carrier construction
and map accumulated histories to Simon's infinite histories. Their probability,
support, and one-step cylinder theorems retain the supplied behavioral profile
and starting history.

`lawFrom_restrict_next_eq_smul_map_prependFirst`
(`MathUE/Probability/MarkovPathRestart.lean`) gives exact restriction and restart
for a homogeneous Markov kernel on a measurable state space with measurable
singletons. It does not require countability or positive transition mass.
`coherentHistoryStreamLaw_restrict_child` and `profileHistoryLaw_condition`
(`Literature/Simon2007.lean`) transport it through the actual history maps.
The latter supplies the required cylinder restriction identity, including
extensions with zero behavioral one-step probability.

`profileHistoryLaw_regular` (`Literature/Simon2007.lean`) delegates to the
generic countable-observation regularity theorem. Together these declarations
construct every field of the paper's induced-law semantics; other Simon
proof obligations remain separate.
