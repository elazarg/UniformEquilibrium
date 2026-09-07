import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Source
import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueSource

/-! # Optimal pivot repair for the same paired-cycle finite-menu marginals -/

noncomputable section

namespace GameTheory.PairedCycle

open _root_.Math.LinearProgramming

/-- The selected menu's actual nonpivot laws have an attained finite-LP optimum
bounded by the same geometric full-regret estimate. No nonpivot laws are reselected. -/
theorem Fin4PivotCycleMenu.exists_repair_minimizer_le_geometric
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)} {q : Fin 4 → ℝ}
    {hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1} {turns : ℕ} (hturns : 1 ≤ turns)
    {mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction (turns * 2))}
    (hmenu : Fin4PivotCycleMenu reward q hq turns mixed) :
    let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := fin4PivotReward reward)
      0 (turns * 2) (by omega)
      (fun who : {who : Fin 4 // who ≠ 0} =>
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF)
      (fun who => isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who))
    ∃ mass : PivotRepairMass (turns * 2), IsPivotRepairMassFeasible mass ∧
      IsMinOn input.objective (pivotRepairMassFeasibleSet (turns * 2)) mass ∧
      input.objective mass ≤ 5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) := by
  obtain ⟨mass, hfeasible, hmin, hbound⟩ :=
    exists_pivotRepairMinimizer_objective_le_finiteMenu_exploitability
      (fin4PivotReward reward) 0 (turns * 2) (by omega) mixed
  exact ⟨mass, hfeasible, hmin, hbound.trans hmenu.fullBound⟩

/-- The raw paired region supplies the existing outer small-repair source through
its fixed menu family, retaining that family's actual nonpivot marginals. -/
theorem hasSmallPivotRepairValue_fin4PivotReward_of_rawRegion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) :
    HasQuittingSmallPivotRepairValue (fin4PivotReward reward) 0 := by
  obtain ⟨q, hinterior, menus, _, _, haccuracy⟩ :=
    exists_one_hazards_fin4PivotMenus_all_accuracies reward hregion
  intro error herror
  obtain ⟨cutoff, hcutoff, hbound⟩ := haccuracy (error / 2) (by linarith)
  obtain ⟨mass, hfeasible, hobjective⟩ :=
    exists_pivotRepairMass_objective_le_finiteMenu_exploitability
      (fin4PivotReward reward) 0 (cutoff * 2) (by omega) (menus cutoff)
  refine ⟨cutoff * 2, by omega,
    (fun who : {who : Fin 4 // who ≠ 0} =>
      (quittingFiniteDeadlineTimingLaw (menus cutoff who)).toPMF),
    (fun who => isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (menus cutoff who)),
    mass, hfeasible, ?_⟩
  have hfull := (hbound cutoff le_rfl).1
  exact lt_of_le_of_lt (hobjective.trans hfull) (by linarith)

end GameTheory.PairedCycle
