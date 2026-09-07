import UniformEquilibrium.Quitting.Cycles.PairedCycleFin4Menu

/-! # One hazard vector and one finite-menu family for every Fin4 accuracy -/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

/-- Exact finite-menu data of the displayed pivot-normalized paired cycle. -/
structure Fin4PivotCycleMenu
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (q : Fin 4 → ℝ)
    (hq : ∀ player, q player ∈ Set.Icc (0 : ℝ) 1) (turns : ℕ)
    (mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction (turns * 2))) : Prop where
  laws : ∀ player, (quittingFiniteDeadlineTimingLaw (mixed player)).toPMF =
    quittingBehaviorStoppingLaw (fin4PivotReward reward)
      (quittingCyclicFiniteProfile (fin4PivotReward reward)
        (cycle fin4Schedule q hq) 0 (turns * 2) player)
  semanticPair : quittingTerminalSemanticPair (fin4PivotReward reward)
      (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) =
    (fun player => (1 - jointCycleSurvival q ^ turns) * fin4PivotValue reward q hq player,
      fin4PivotValue reward q hq)
  fullBound : quittingTerminalExploitability (fin4PivotReward reward)
      (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward) (turns * 2) mixed) ≤
    5 / 3 * (99 / 100 : ℝ) ^ (4 * turns)

/-- The raw table selects hazards once and fixes one finite-menu family. Every
positive cycle count has exact semantic data, and the same menus satisfy both
canonical inequalities at all sufficiently large counts for every accuracy. -/
theorem exists_one_hazards_fin4PivotMenus_all_accuracies
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hregion : RawRegion reward fin4Schedule) :
    ∃ q : Fin 4 → ℝ, ∃ hinterior : ∀ player, q player ∈ Set.Ioo (1 / 100 : ℝ) (1 / 2),
      let hq := unitBoundsOfInterior q hinterior
      ∃ menus : (turns : ℕ) → Fin 4 → PMF (QuittingFiniteDeadlineTimingAction (turns * 2)),
        (∀ player, playerGap fin4Schedule.partner (singleton reward)
          (partnerReward reward fin4Schedule) (jointReward reward fin4Schedule)
          (quietRows reward fin4Schedule) q player = 0) ∧
        (∀ turns, 1 ≤ turns → Fin4PivotCycleMenu reward q hq turns (menus turns)) ∧
        ∀ error : ℝ, 0 < error → ∃ cutoff : ℕ, 1 ≤ cutoff ∧ ∀ turns ≥ cutoff,
          quittingTerminalExploitability (fin4PivotReward reward)
              (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward)
                (turns * 2) (menus turns)) ≤ error ∧
          quittingFiniteDeadlineMenuExploitability (fin4PivotReward reward)
              (turns * 2) (menus turns) ≤ error ∧
          quittingFiniteDeadlineNeverPayoff (fin4PivotReward reward)
              (turns * 2) (menus turns) 0 +
            quittingFiniteDeadlineOpponentNeverProduct (turns * 2) (menus turns) 0 -
            quittingTerminalPayoff (fin4PivotReward reward)
              (quittingFiniteDeadlineTimingProfile (fin4PivotReward reward)
                (turns * 2) (menus turns)) 0 ≤ error := by
  obtain ⟨q, hinterior, hzero⟩ := exists_hazards_of_rawRegion reward fin4Schedule (by omega) hregion
  let hq := unitBoundsOfInterior q hinterior
  have hexists (turns : ℕ) :
      ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction (turns * 2)),
        1 ≤ turns → Fin4PivotCycleMenu reward q hq turns mixed := by
    by_cases hturns : 1 ≤ turns
    · obtain ⟨mixed, hlaws, hpair, hfull, _, _⟩ := exists_fin4PivotMenu_exact_of_selected
        reward hregion q hq hinterior hzero turns hturns
      exact ⟨mixed, fun _ => ⟨hlaws, hpair, hfull⟩⟩
    · exact ⟨fun _ => PMF.pure none, fun h => (hturns h).elim⟩
  choose menus hmenus using hexists
  refine ⟨q, hinterior, menus, hzero, hmenus, ?_⟩
  intro error herror
  obtain ⟨cutoff, hcutoff, hbound⟩ := eventually_geometric_error_le 4 (by omega) error herror
  refine ⟨cutoff, hcutoff, fun turns hturns => ?_⟩
  have hfull := (hmenus turns (hcutoff.trans hturns)).fullBound
  have hpower : 0 ≤ (99 / 100 : ℝ) ^ (4 * turns) := by positivity
  have herrorBound : 5 / 3 * (99 / 100 : ℝ) ^ (4 * turns) ≤ error := by
    have h := hbound turns hturns
    nlinarith
  have hfullError := hfull.trans herrorBound
  have hidentity := singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    (fin4PivotReward reward) 0
    (fin4PivotReward_isSinglePivotSingletonTable reward hregion) (turns * 2) (menus turns)
  refine ⟨hfullError, ?_, ?_⟩
  · exact (le_max_left _ _).trans (hidentity.symm.le.trans hfullError)
  · exact (le_max_right _ _).trans (hidentity.symm.le.trans hfullError)

end GameTheory.PairedCycle
