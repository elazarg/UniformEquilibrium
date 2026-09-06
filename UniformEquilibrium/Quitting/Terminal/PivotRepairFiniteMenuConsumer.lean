import UniformEquilibrium.Quitting.Terminal.FiniteOpponentPivotCensor
import UniformEquilibrium.Quitting.Terminal.PivotRepairBehavioralApproximation
import UniformEquilibrium.Quitting.Terminal.PivotRepairNeverMassBound

/-! # Actual finite-menu consumers of feasible pivot repair points -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

omit [Fintype ι] [DecidableEq ι] in
private theorem exists_cutoff_lateFiniteMass_lt (law : PMF (Option ℕ))
    (tolerance : ℝ) (htolerance : 0 < tolerance) :
    ∃ cutoff : ℕ, input.deadline ≤ cutoff + 1 ∧
      stoppingLawLateFiniteMass law cutoff < tolerance := by
  obtain ⟨first, hfirst⟩ := exists_horizon_sum_stoppingLawLateFiniteMass_lt
    (fun _ : Unit ↦ law) htolerance
  have hsmall : stoppingLawLateFiniteMass law first < tolerance := by simpa using hfirst
  refine ⟨max first (input.deadline - 1), by have := input.deadline_pos; omega, ?_⟩
  apply (pmfFiniteComplementMass_anti law ?_).trans_lt hsmall
  intro choice hchoice
  cases choice with
  | none => exact none_mem_stoppingLawFinitePrefix _
  | some time =>
      rw [some_mem_stoppingLawFinitePrefix] at hchoice ⊢
      exact hchoice.trans (le_max_left _ _)

private theorem opponentNeverProduct_le_one :
    (∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal) ≤ 1 := by
  apply Finset.prod_le_one
  · intro who _
    exact ENNReal.toReal_nonneg
  · intro who _
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by norm_num)).mpr
      (PMF.coe_le_one _ _) |>.trans_eq (by simp)

/-- Every signed feasible repair point produces actual finite laws with
the censor source retained, full-deviation error control, and exact survival.
Approximation does not change the pivot Never atom. -/
theorem exists_finite_menu_of_feasible_mass_signed
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (error : ℝ) (herror : 0 < error) (tolerance : ℝ) (htolerance : 0 < tolerance)
    (horizon : ℕ) (hhorizon : 1 ≤ horizon) (lowerDeadline : ℕ) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ (law : PMF (Option ℕ)) (cutoff deadline : ℕ),
      input.deadline ≤ cutoff + 1 ∧ max horizon lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (law none).toReal = pivotRepairNever mass ∧
        stoppingLawLateFiniteMass law cutoff < tolerance ∧
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          Function.update input.opponents input.pivot
            (censorLateFiniteStoppingLaw law cutoff) who) ∧
        quittingTerminalExploitability reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ≤
          input.objective mass + error +
            4 * quittingRewardBound reward * stoppingLawLateFiniteMass law cutoff ∧
        quittingJointSurvivalWeight
            (quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed)) 0 (deadline - horizon) =
          (pivotRepairNever mass + stoppingLawLateFiniteMass law cutoff) *
            ∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal := by
  letI : Nonempty ι := ⟨input.pivot⟩
  obtain ⟨law, _, hlawError, hnone⟩ :=
    input.exists_law_payoff_eq_and_exploitability_le_objective_add mass hfeasible error herror
  obtain ⟨cutoff, hcutoff, htail⟩ := input.exists_cutoff_lateFiniteMass_lt law tolerance htolerance
  obtain ⟨deadline, hdeadline, mixed, hmixed, hexploit, hsurvival⟩ :=
    input.exists_finite_censor_menu law cutoff hcutoff horizon hhorizon lowerDeadline
  refine ⟨law, cutoff, deadline, hcutoff, hdeadline, mixed, hnone, htail, hmixed, ?_, ?_⟩
  · linarith
  · rw [hsurvival, hnone]

/-- A positive pivot singleton converts the exact finite-censor survival
identity into the sharp LP objective budget. The finite producer itself is signed. -/
theorem exists_finite_menu_of_feasible_mass
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hpositive : 0 < reward (quittingSingletonTerminal input.pivot) input.pivot)
    (error : ℝ) (herror : 0 < error) (tolerance : ℝ) (htolerance : 0 < tolerance)
    (horizon : ℕ) (hhorizon : 1 ≤ horizon) (lowerDeadline : ℕ) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ (law : PMF (Option ℕ)) (cutoff deadline : ℕ),
      input.deadline ≤ cutoff + 1 ∧ max horizon lowerDeadline ≤ deadline ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
        (law none).toReal = pivotRepairNever mass ∧
        stoppingLawLateFiniteMass law cutoff < tolerance ∧
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          Function.update input.opponents input.pivot
            (censorLateFiniteStoppingLaw law cutoff) who) ∧
        quittingTerminalExploitability reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) ≤
          input.objective mass + error +
            4 * quittingRewardBound reward * stoppingLawLateFiniteMass law cutoff ∧
        quittingJointSurvivalWeight
            (quittingProfileLiveRoot reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed)) 0 (deadline - horizon) ≤
          input.objective mass / reward (quittingSingletonTerminal input.pivot) input.pivot +
            stoppingLawLateFiniteMass law cutoff := by
  letI : Nonempty ι := ⟨input.pivot⟩
  obtain ⟨law, cutoff, deadline, hcutoff, hdeadline, mixed, hnone, htail, hmixed,
      hexploit, hsurvival⟩ := input.exists_finite_menu_of_feasible_mass_signed
    mass hfeasible error herror tolerance htolerance horizon hhorizon lowerDeadline
  refine ⟨law, cutoff, deadline, hcutoff, hdeadline, mixed, hnone, htail, hmixed, hexploit, ?_⟩
  rw [hsurvival, add_mul]
  have hnever := input.jointNever_le_objective_div_pivot_singleton mass hfeasible hpositive
  have htailBound := mul_le_mul_of_nonneg_left input.opponentNeverProduct_le_one
    (pmfFiniteComplementMass_nonneg law (stoppingLawFinitePrefix cutoff))
  change stoppingLawLateFiniteMass law cutoff *
    (∏ who ∈ Finset.univ.erase input.pivot, (input.opponents who none).toReal) ≤
    stoppingLawLateFiniteMass law cutoff * 1 at htailBound
  linarith

end GameTheory.QuittingPivotRepairLPInput
