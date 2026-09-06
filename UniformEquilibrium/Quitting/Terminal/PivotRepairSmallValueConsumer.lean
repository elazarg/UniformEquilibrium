import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteMenuConsumer
import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueSource
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Conditional full early absorption from small actual repair LP values -/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive pivot singleton turns the actual nonpivot-law small-LP source
into finite menus with unrestricted regret and all requested absorption windows. -/
theorem finiteMenuFullEarlyAbsorption_of_smallPivotRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpositive : 0 < reward (quittingSingletonTerminal pivot) pivot)
    (hsource : HasQuittingSmallPivotRepairValue reward pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  letI : Nonempty ι := ⟨pivot⟩
  intro error herror horizon hhorizon reach hreach lowerDeadline
  let singleton := reward (quittingSingletonTerminal pivot) pivot
  let bound := quittingRewardBound reward
  have hbound : 0 ≤ bound := quittingRewardBound_nonneg reward
  have hsourceError : 0 < min (error / 3) (singleton * reach / 3) := by
    apply lt_min <;> positivity
  obtain ⟨deadline, hdeadline, opponents, hfinite, mass, hmass, hvalue⟩ :=
    hsource _ hsourceError
  let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
    pivot deadline hdeadline opponents hfinite
  let tolerance := min (error / (12 * (bound + 1))) (reach / 3)
  have htolerance : 0 < tolerance := by
    apply lt_min <;> positivity
  obtain ⟨law, cutoff, displayed, _, hdisplayed, mixed, _, htail, _, hexploit, hsurvival⟩ :=
    input.exists_finite_menu_of_feasible_mass mass hmass hpositive
      (error / 3) (by positivity) tolerance htolerance horizon hhorizon lowerDeadline
  refine ⟨displayed, hdisplayed, mixed, ?_, ?_⟩
  · have hsmall : input.objective mass < error / 3 := hvalue.trans_le (min_le_left _ _)
    have htailSmall : stoppingLawLateFiniteMass law cutoff < error / (12 * (bound + 1)) :=
      htail.trans_le (min_le_left _ _)
    have hdenom : 0 < 12 * (bound + 1) := by positivity
    have hscaled := (lt_div_iff₀ hdenom).mp htailSmall
    have hnonneg : 0 ≤ stoppingLawLateFiniteMass law cutoff := pmfFiniteComplementMass_nonneg _ _
    change quittingTerminalExploitability reward _ ≤ input.objective mass + error / 3 +
      4 * bound * stoppingLawLateFiniteMass law cutoff at hexploit
    nlinarith
  · have hsmall : input.objective mass < singleton * reach / 3 :=
      hvalue.trans_le (min_le_right _ _)
    have hdiv : input.objective mass / singleton < reach / 3 := by
      apply (div_lt_iff₀ hpositive).mpr
      nlinarith
    have htailSmall : stoppingLawLateFiniteMass law cutoff < reach / 3 :=
      htail.trans_le (min_le_right _ _)
    change quittingJointSurvivalWeight _ _ _ ≤
      input.objective mass / singleton + stoppingLawLateFiniteMass law cutoff at hsurvival
    linarith

/-- For a positive pivot singleton, the nonpivot-law small-value source is
exactly the full finite-menu early-absorption source. Other own singletons
remain arbitrary signed real numbers. -/
theorem smallPivotRepairValue_iff_finiteMenuFullEarlyAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpositive : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    letI : Nonempty ι := ⟨pivot⟩
    HasQuittingSmallPivotRepairValue reward pivot ↔
      HasQuittingFiniteMenuFullEarlyAbsorption reward := by
  letI : Nonempty ι := ⟨pivot⟩
  exact ⟨finiteMenuFullEarlyAbsorption_of_smallPivotRepairValue reward pivot hpositive,
    smallPivotRepairValue_of_finiteMenuFullEarlyAbsorption reward pivot⟩

/-- The actual small-LP source conditionally yields one fixed uniform payoff
target. The profile may depend on the accuracy; the payoff target does not. -/
theorem exists_uniformEquilibriumPayoff_of_smallPivotRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hsource : HasQuittingSmallPivotRepairValue reward pivot) :
    ∃ payoff : Payoff ι, (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty ι := ⟨pivot⟩
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro error herror
  obtain ⟨deadline, hdeadline, opponents, hfinite, mass, hmass, hvalue⟩ :=
    hsource (error / 2) (half_pos herror)
  let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
    pivot deadline hdeadline opponents hfinite
  obtain ⟨law, _, hexploit, _⟩ :=
    input.exists_law_payoff_eq_and_exploitability_le_objective_add
      mass hmass (error / 2) (half_pos herror)
  refine ⟨quittingStoppingLawProfile reward (Function.update input.opponents pivot law), ?_⟩
  apply isεAsymptoticNash_of_quittingTerminalExploitability_le
  change quittingTerminalExploitability reward
    (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤ _
  linarith

end GameTheory
