import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPreemptedOwnerQuadraticMargin
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates

/-! # Uniform payoff from signed designated weak-subset exclusion

Only the designated owners need nonnegative singleton rewards.  At a
hypothetical positive minimum of total terminal debt, the quadratic
nonnegative-owner margin puts every designated prescribed payoff strictly
above its singleton.  One actual profile approximating the semantic carrier
point then contradicts weak subset exclusion simultaneously on the finite
designated set.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual weak exclusion on a nonempty designated subset, with nonnegative
singletons required only on that subset, implies a uniform-equilibrium payoff.
The player type is proved inhabited from the exclusion witness. -/
theorem exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingActualWeakSubsetExclusion reward owners) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨inhabitant, -, -⟩ :=
    hexclusion.2 (quittingAlwaysContinueProfile reward)
  letI : Nonempty ι := ⟨inhabitant⟩
  by_contra hno
  obtain ⟨pair, hpair, hminimum, hpositive⟩ :=
    (not_exists_uniformEquilibriumPayoff_iff_hasPositiveMinimumTerminalSemanticDebt
      reward).mp hno
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp only [M]
      linarith)
  have hstrict : ∀ owner ∈ owners,
      reward (quittingSingletonTerminal owner) owner < pair.1 owner := by
    intro owner howner
    obtain ⟨blocker, hpreempted⟩ :=
      exists_strict_preemptor_of_positive_minimum_nonnegative_singleton
        reward pair hminimum hpositive owner (hexclusion.1 owner howner)
    have hmargin := positive_minimum_preemptedOwner_prescribedMargin
      reward pair hpair hminimum owner blocker hM hreward hpositive hpreempted
    have hmarginPositive : 0 <
        quittingTerminalSemanticDebtSum pair ^ 2 / (8 * M) := by
      positivity
    linarith
  obtain ⟨profiles, hprofiles⟩ :=
    exists_terminalProfile_sequence_tendsto_semanticPair reward pair hpair
  have hpayoffTendsto : ∀ owner,
      Tendsto (fun time => quittingTerminalPayoff reward (profiles time) owner)
        atTop (nhds (pair.1 owner)) := by
    intro owner
    change Tendsto
      (fun time => (quittingTerminalSemanticPair reward (profiles time)).1 owner)
      atTop (nhds (pair.1 owner))
    exact (((continuous_apply owner).comp continuous_fst).tendsto pair).comp hprofiles
  have heventually : ∀ᶠ time in atTop, ∀ owner ∈ owners,
      reward (quittingSingletonTerminal owner) owner <
        quittingTerminalPayoff reward (profiles time) owner := by
    apply (Finset.eventually_all owners).2
    intro owner howner
    exact (tendsto_order.1 (hpayoffTendsto owner)).1 _ (hstrict owner howner)
  obtain ⟨time, htime⟩ := heventually.exists
  obtain ⟨owner, howner, hle⟩ := hexclusion.2 (profiles time)
  exact (not_lt_of_ge hle) (htime owner howner)

/-- The exact raw finite-calendar weak-subset predicate has the same
uniform-payoff consequence.  Inhabitation is again derived from the raw
exclusion witness rather than exposed as an assumption. -/
theorem exists_uniformEquilibriumPayoff_of_finiteCalendarRawWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let deadline := Fintype.card ι * (Fintype.card ι + 1)
  let allNever : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline) := fun _ =>
    Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)
  obtain ⟨inhabitant, -, -⟩ := hexclusion.2 allNever
  letI : Nonempty ι := ⟨inhabitant⟩
  apply exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion
    reward owners
  exact (hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
    reward owners).mp hexclusion

end GameTheory
