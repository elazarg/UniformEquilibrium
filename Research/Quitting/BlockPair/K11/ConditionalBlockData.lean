import Research.Quitting.BlockPair.K11.PhaseValueRecurrence
import UniformEquilibrium.Quitting.Cycles.AdmissibleCycleTerminalEquilibrium

noncomputable section

namespace GameTheory.BlockPairK11.ConditionalData

open Math.ProbabilityMassFunction StochasticGame

def simplexRoot (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : QuittingRootSimplex Player :=
  fun who ↦ stdSimplexEquiv (phaseRoot x hx phase who)

def phasePoint (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) : QuittingNashBellmanPoint Player :=
  (phaseValue x phase, simplexRoot x hx phase)

def pathPhase (time : Fin 12) : Phase := Fin.ofNat 11 time.val

def block (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1) :
    QuittingFiniteNashBellmanPath Player 11 :=
  fun time ↦ phasePoint x hx (pathPhase time)

@[simp] theorem pathPhase_zero : pathPhase 0 = 0 := rfl

@[simp] theorem pathPhase_last : pathPhase (Fin.last 11) = 0 := rfl

theorem pathPhase_succ (time : Fin 11) :
    pathPhase (Fin.succ time) =
      nextPhase (pathPhase (Fin.castSucc time)) := by
  fin_cases time <;> rfl

@[simp] theorem pathPhase_castSucc (phase : Phase) :
    pathPhase (Fin.castSucc phase) = phase := by
  fin_cases phase <;> rfl

@[simp] theorem rootOfSimplex_phasePoint
    (x : HazardIndex → ℝ)
    (hx : ∀ index, 0 < x index ∧ x index < 1)
    (phase : Phase) :
    quittingRootOfSimplex (phasePoint x hx phase).2 =
      phaseRoot x hx phase := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
    (phaseRoot x hx phase who)

end GameTheory.BlockPairK11.ConditionalData
