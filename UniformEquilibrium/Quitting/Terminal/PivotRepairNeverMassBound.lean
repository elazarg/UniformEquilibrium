import UniformEquilibrium.Quitting.Terminal.PivotRepairPivotCap

/-! # Positive pivot singleton controls the LP joint-Never mass -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Pivot debt is the actual mass-weighted sum of its pure candidate gaps. -/
theorem pivot_debt_eq_weighted_gaps
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    input.pivotCap - input.prescribedPayoff mass input.pivot =
      (∑ time, pivotRepairHead mass time *
        (input.pivotCap - input.purePivotPayoff (some time.val) input.pivot)) +
      pivotRepairLate mass * (input.pivotCap - input.pivotLatePayoff) +
      pivotRepairNever mass * (input.pivotCap - input.pivotNeverPayoff) := by
  unfold prescribedPayoff
  rw [input.purePivotPayoff_late_eq (time := input.deadline) le_rfl]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsum := hfeasible.2.2.2.1
  unfold pivotNeverPayoff
  linear_combination -input.pivotCap * hsum

/-- The objective bounds the signed pivot singleton times joint Never mass.
No positivity assumption is needed until dividing by the singleton reward. -/
theorem pivot_singleton_mul_jointNever_le_objective
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass) :
    reward (quittingSingletonTerminal input.pivot) input.pivot *
        (pivotRepairNever mass * ∏ j ∈ Finset.univ.erase input.pivot,
          (input.opponents j none).toReal) ≤ input.objective mass := by
  have hhead (time : Fin input.deadline) :
      0 ≤ input.pivotCap - input.purePivotPayoff (some time.val) input.pivot := by
    exact sub_nonneg.mpr (Finset.le_sup' input.pivotCapCandidateValue
      (Finset.mem_univ (Sum.inl time)))
  have hlate : input.pivotLatePayoff ≤ input.pivotCap :=
    Finset.le_sup' input.pivotCapCandidateValue
      (Finset.mem_univ (Sum.inr true : Fin input.deadline ⊕ Bool))
  have hsum : 0 ≤ ∑ time, pivotRepairHead mass time *
      (input.pivotCap - input.purePivotPayoff (some time.val) input.pivot) :=
    Finset.sum_nonneg fun time _ ↦ mul_nonneg (hfeasible.1 time) (hhead time)
  have hlateGap : 0 ≤ pivotRepairLate mass * (input.pivotCap - input.pivotLatePayoff) :=
    mul_nonneg hfeasible.2.1 (sub_nonneg.mpr hlate)
  have hnever := mul_le_mul_of_nonneg_left hlate hfeasible.2.2.1
  unfold pivotLatePayoff at hnever
  have hdebt := input.pivot_debt_eq_weighted_gaps mass hfeasible
  have hobjective : input.pivotCap - input.prescribedPayoff mass input.pivot ≤
      input.objective mass :=
    Finset.le_sup' (input.constraintGain mass)
      (Finset.mem_univ (Sum.inr (Sum.inl ()) : input.ConstraintIndex))
  nlinarith

/-- A positive pivot singleton gives the exact LP joint-Never budget. -/
theorem jointNever_le_objective_div_pivot_singleton
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hpositive : 0 < reward (quittingSingletonTerminal input.pivot) input.pivot) :
    pivotRepairNever mass * ∏ j ∈ Finset.univ.erase input.pivot,
        (input.opponents j none).toReal ≤
      input.objective mass / reward (quittingSingletonTerminal input.pivot) input.pivot := by
  apply (le_div_iff₀ hpositive).mpr
  simpa only [mul_comm] using input.pivot_singleton_mul_jointNever_le_objective mass hfeasible

end GameTheory.QuittingPivotRepairLPInput
