import UniformEquilibrium.Diagnostics.Quitting.PivotRepairRationalOptimizer
import UniformEquilibrium.Quitting.Terminal.PivotRepairSourceCompression
import UniformEquilibrium.Quitting.Terminal.StoppingLawExploitability

noncomputable section

namespace GameTheory.PivotRepairRationalOptimality

open PivotRepairRationalFixture
open PivotRepairRationalLowerBound
open PivotRepairRationalOptimizer

/-- Every actual behavioral pivot replacement against the fixture opponents has at least
the rational certificate's terminal exploitability. -/
theorem exploitability_ge_1584_div_5243_of_pivotBehavior
    (N : ℕ) (hN : 1 ≤ N)
    (deviation : (quittingGame reward).BehaviorStrategy (0 : Fin 4)) :
    1584 / 5243 ≤ quittingTerminalExploitability reward
      (Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0 deviation) := by
  let law := quittingBehaviorStoppingLaw reward deviation
  obtain ⟨mass, hfeasible, -, hobjective⟩ :=
    (input N hN).exists_feasible_mass_payoff_eq_and_objective_le law
  have hlower := objective_ge_1584_div_5243 hN mass hfeasible
  have hvalue :
      quittingTerminalExploitability reward
          (Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0 deviation) =
        quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update (opponents N hN) 0 law)) := by
    rw [← quittingTerminalExploitability_stoppingLawProfile_behaviorLaws_eq,
      quittingBehaviorStoppingLaws_update,
      quittingBehaviorStoppingLaws_stoppingLawProfile]
  rw [hvalue]
  exact hlower.trans hobjective

/-- The explicit optimizer law, reconstructed as an actual pivot behavior strategy. -/
def optimizerPivotBehavior (N : ℕ) (hN : 1 ≤ N) :
    (quittingGame reward).BehaviorStrategy (0 : Fin 4) :=
  quittingStoppingLawBehaviorStrategy reward 0 (optimizerGeometricLaws N hN 0)

theorem optimizerPivotBehavior_profile_eq (N : ℕ) (hN : 1 ≤ N) :
    Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0
        (optimizerPivotBehavior N hN) =
      optimizerGeometricProfile N hN := by
  funext player
  by_cases hplayer : player = 0
  · subst player
    simp [optimizerPivotBehavior, optimizerGeometricProfile,
      quittingStoppingLawProfile]
  · simp [optimizerPivotBehavior, optimizerGeometricProfile, optimizerGeometricLaws,
      QuittingPivotRepairLPInput.geometricLaws, quittingStoppingLawProfile,
      Function.update_of_ne hplayer]

theorem optimizerPivotBehavior_exploitability_eq (N : ℕ) (hN : 1 ≤ N) :
    quittingTerminalExploitability reward
        (Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0
          (optimizerPivotBehavior N hN)) =
      1584 / 5243 := by
  rw [optimizerPivotBehavior_profile_eq]
  simpa [optimizerGeometricProfile, optimizerGeometricLaws] using
    optimizerMass_geometric_exploitability_eq N hN

/-- The behavioral pivot-repair infimum is attained by the displayed optimizer behavior. -/
theorem pivotBehavior_exploitability_isGLB (N : ℕ) (hN : 1 ≤ N) :
    IsGLB (Set.range fun deviation : (quittingGame reward).BehaviorStrategy (0 : Fin 4) ↦
      quittingTerminalExploitability reward
        (Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0 deviation))
      (1584 / 5243) := by
  constructor
  · rintro value ⟨deviation, rfl⟩
    exact exploitability_ge_1584_div_5243_of_pivotBehavior N hN deviation
  · intro bound hbound
    rw [← optimizerPivotBehavior_exploitability_eq N hN]
    exact hbound ⟨optimizerPivotBehavior N hN, rfl⟩

theorem pivotBehavior_exploitability_infimum_eq (N : ℕ) (hN : 1 ≤ N) :
    sInf (Set.range fun deviation : (quittingGame reward).BehaviorStrategy (0 : Fin 4) ↦
      quittingTerminalExploitability reward
        (Function.update (quittingStoppingLawProfile reward (opponents N hN)) 0 deviation)) =
      1584 / 5243 := by
  apply (pivotBehavior_exploitability_isGLB N hN).csInf_eq
  exact ⟨_, ⟨optimizerPivotBehavior N hN, rfl⟩⟩

end GameTheory.PivotRepairRationalOptimality
