import UniformEquilibrium.Quitting.Terminal.PivotRepairExactObjective

/-! # Literal realization and the unattained first-atom boundary -/

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open _root_.Math.LinearProgramming _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Positive first atom, or a zero finite tail, gives a literal actual law
with exactly the LP payoff vector and objective. -/
theorem exists_law_payoff_eq_and_exploitability_eq_objective
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hrealizable : 0 < pivotRepairFirstAtom mass ∨ pivotRepairLate mass = 0) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.objective mass ∧ (law none).toReal = pivotRepairNever mass := by
  letI : Nonempty ι := ⟨input.pivot⟩
  have hexists : ∃ (hazard : ℝ) (hpositive : 0 < hazard) (hle : hazard ≤ 1),
      pivotRepairLate mass * hazard = pivotRepairFirstAtom mass := by
    rcases hrealizable with hpositive | hzero
    · have htail : 0 < pivotRepairLate mass := hpositive.trans_le hfeasible.2.2.2.2.2
      refine ⟨pivotRepairFirstAtom mass / pivotRepairLate mass,
        div_pos hpositive htail, (div_le_one htail).mpr hfeasible.2.2.2.2.2, ?_⟩
      exact mul_div_cancel₀ _ htail.ne'
    · have hatom : pivotRepairFirstAtom mass = 0 := by
        have hnonneg := hfeasible.2.2.2.2.1
        have hle := hfeasible.2.2.2.2.2
        linarith
      exact ⟨1, zero_lt_one, le_rfl, by rw [hzero, hatom, zero_mul]⟩
  obtain ⟨hazard, hpositive, hle, hmatch⟩ := hexists
  refine ⟨geometricPivotStoppingLaw (pivotRepairProvisionalStoppingLaw mass hfeasible)
    input.deadline hazard hpositive hle, ?_, ?_, ?_⟩
  · funext observer
    exact input.geometric_payoff_eq_prescribedPayoff mass hfeasible hazard hpositive hle observer
  · exact input.geometric_exploitability_eq_objective mass hfeasible hazard hpositive hle hmatch
  · simp only [geometricPivotStoppingLaw_none, pivotRepairProvisionalStoppingLaw_none_toReal]

/-- The zero-tail corner is realized by the provisional finite law itself,
not by assuming a positive hazard for a nonexistent finite tail. -/
theorem provisional_exploitability_eq_objective_of_late_eq_zero
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairLate mass = 0) :
    letI : Nonempty ι := ⟨input.pivot⟩
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward (input.provisionalLaws mass hfeasible)) =
      input.objective mass := by
  letI : Nonempty ι := ⟨input.pivot⟩
  have hatom : pivotRepairFirstAtom mass = 0 := by
    have hnonneg := hfeasible.2.2.2.2.1
    have hle := hfeasible.2.2.2.2.2
    linarith
  have h := input.geometric_exploitability_eq_objective mass hfeasible 1 zero_lt_one le_rfl
    (by rw [hzero, hatom, zero_mul])
  have htail : stoppingLawLateFiniteMass
      (pivotRepairProvisionalStoppingLaw mass hfeasible) (input.deadline - 1) = 0 := by
    rw [pivotRepairProvisionalStoppingLaw_lateFiniteMass input.deadline_pos, hzero]
  simpa only [geometricLaws, geometricPivotStoppingLaw_eq_of_lateFiniteMass_eq_zero
    _ input.deadline_pos htail, provisionalLaws] using h

/-- A positive replacement first atom realizes the same prescribed payoff
exactly, with error controlled by a tie-minus-later coefficient bound. -/
theorem exists_law_boundary_approximation_of_coefficient_bound
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairFirstAtom mass = 0) (firstAtom coefficientBound : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass)
    (hbound : 0 ≤ coefficientBound)
    (hcoefficient : ∀ responder, responder ≠ input.pivot →
      |input.responderTieReward responder -
        responderLaterReward (reward := reward) responder| ≤ coefficientBound) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + coefficientBound * firstAtom ∧
      (law none).toReal = pivotRepairNever mass := by
  letI : Nonempty ι := ⟨input.pivot⟩
  let changed := pivotRepairMassWithFirstAtom mass firstAtom
  have hchanged : IsPivotRepairMassFeasible changed :=
    isPivotRepairMassFeasible_withFirstAtom hfeasible hpositive.le hle
  obtain ⟨law, hpayoff, hobjective, hnone⟩ :=
    input.exists_law_payoff_eq_and_exploitability_eq_objective changed hchanged
      (Or.inl (by simpa [changed] using hpositive))
  refine ⟨law, ?_, ?_, ?_⟩
  · funext observer
    have h := congrFun hpayoff observer
    simpa only [changed, prescribedPayoff_withFirstAtom] using h
  · rw [hobjective]
    have h := input.abs_objective_withFirstAtom_sub_le_of_coefficient_bound
      mass firstAtom coefficientBound hbound hcoefficient
    rw [hzero, sub_zero, abs_of_pos hpositive] at h
    have hupper := (le_abs_self _).trans h
    change input.objective changed - input.objective mass ≤ _ at hupper
    linarith
  · simpa only [changed, pivotRepairNever_withFirstAtom] using hnone

/-- An arbitrary supplied coordinate reward bound gives the explicit
`2 * bound * firstAtom` boundary error. -/
theorem exists_law_boundary_approximation_of_reward_bound
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairFirstAtom mass = 0) (firstAtom bound : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + 2 * bound * firstAtom ∧
      (law none).toReal = pivotRepairNever mass := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward (quittingSingletonTerminal input.pivot) input.pivot)).trans
      (hreward (quittingSingletonTerminal input.pivot) input.pivot)
  apply input.exists_law_boundary_approximation_of_coefficient_bound mass hfeasible hzero
    firstAtom (2 * bound) hpositive hle (by positivity)
  intro responder _
  calc
    |_ - _| ≤ |input.responderTieReward responder| +
        |responderLaterReward (reward := reward) responder| := abs_sub _ _
    _ ≤ bound + bound := add_le_add (hreward _ _) (hreward _ _)
    _ = 2 * bound := by ring

/-- Zero nonpivot singleton rewards sharpen the boundary error to
`bound * firstAtom`. -/
theorem exists_law_boundary_approximation_of_reward_bound_of_later_zero
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairFirstAtom mass = 0) (firstAtom bound : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hlater : ∀ responder, responder ≠ input.pivot →
      responderLaterReward (reward := reward) responder = 0) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + bound * firstAtom ∧
      (law none).toReal = pivotRepairNever mass := by
  have hbound : 0 ≤ bound :=
    (abs_nonneg (reward (quittingSingletonTerminal input.pivot) input.pivot)).trans
      (hreward (quittingSingletonTerminal input.pivot) input.pivot)
  apply input.exists_law_boundary_approximation_of_coefficient_bound mass hfeasible hzero
    firstAtom bound hpositive hle hbound
  intro responder hne
  rw [hlater responder hne, sub_zero]
  exact hreward _ _

/-- The summed project reward bound is a convenient specialization of the
coefficient-parametric boundary theorem. -/
theorem exists_law_boundary_approximation
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (hzero : pivotRepairFirstAtom mass = 0) (firstAtom : ℝ)
    (hpositive : 0 < firstAtom) (hle : firstAtom ≤ pivotRepairLate mass) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + 2 * quittingRewardBound reward * firstAtom ∧
      (law none).toReal = pivotRepairNever mass := by
  exact input.exists_law_boundary_approximation_of_reward_bound mass hfeasible hzero firstAtom
    (quittingRewardBound reward) hpositive hle (abs_reward_le_quittingRewardBound reward)

/-- Every feasible relaxed point has actual independent-law approximants
with the very same payoff vector and arbitrarily small objective error. -/
theorem exists_law_payoff_eq_and_exploitability_le_objective_add
    (mass : PivotRepairMass input.deadline) (hfeasible : IsPivotRepairMassFeasible mass)
    (error : ℝ) (herror : 0 < error) :
    letI : Nonempty ι := ⟨input.pivot⟩
    ∃ law : PMF (Option ℕ),
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) =
        input.prescribedPayoff mass ∧
      quittingTerminalExploitability reward
          (quittingStoppingLawProfile reward (Function.update input.opponents input.pivot law)) ≤
        input.objective mass + error ∧ (law none).toReal = pivotRepairNever mass := by
  letI : Nonempty ι := ⟨input.pivot⟩
  by_cases hrealizable : 0 < pivotRepairFirstAtom mass ∨ pivotRepairLate mass = 0
  · obtain ⟨law, hpayoff, hobjective, hnone⟩ :=
      input.exists_law_payoff_eq_and_exploitability_eq_objective mass hfeasible hrealizable
    exact ⟨law, hpayoff, by rw [hobjective]; linarith, hnone⟩
  · have hzero : pivotRepairFirstAtom mass = 0 := by
      have hnonneg := hfeasible.2.2.2.2.1
      push Not at hrealizable
      linarith [hrealizable.1]
    have htail : 0 < pivotRepairLate mass := by
      have hnonneg := hfeasible.2.1
      exact lt_of_le_of_ne hnonneg (Ne.symm (fun h ↦ hrealizable (Or.inr h)))
    let firstAtom := min (pivotRepairLate mass) (error / (2 * quittingRewardBound reward + 1))
    have hbound : 0 ≤ quittingRewardBound reward := quittingRewardBound_nonneg reward
    have hdenom : 0 < 2 * quittingRewardBound reward + 1 := by positivity
    have hpositive : 0 < firstAtom := lt_min htail (div_pos herror hdenom)
    have hle : firstAtom ≤ pivotRepairLate mass := min_le_left _ _
    obtain ⟨law, hpayoff, hcap, hnone⟩ :=
      input.exists_law_boundary_approximation mass hfeasible hzero firstAtom hpositive hle
    refine ⟨law, hpayoff, hcap.trans ?_, hnone⟩
    have hsmall : firstAtom * (2 * quittingRewardBound reward + 1) ≤ error :=
      (le_div_iff₀ hdenom).mp (min_le_right _ _)
    linarith

end GameTheory.QuittingPivotRepairLPInput
