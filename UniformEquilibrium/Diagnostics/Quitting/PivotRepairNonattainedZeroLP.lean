import MathUE.LinearProgramming.PivotRepairMassPerturbation
import UniformEquilibrium.Quitting.Terminal.PivotRepairExactObjective

/-! # A zero LP boundary optimum with positive geometric realization errors -/

noncomputable section

namespace GameTheory.PivotRepairNonattainedZeroLP

open Math.LinearProgramming

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who ↦
    if who = 0 then if 0 ∈ terminal.1 then 1 else 0
    else if who = 1 then if 0 ∈ terminal.1 ∧ 1 ∈ terminal.1 then 1 else 0
    else 0

def opponents : Fin 4 → PMF (Option ℕ) := fun _ ↦ PMF.pure none

def input : QuittingPivotRepairLPInput reward where
  opponents := opponents
  pivot := 0
  deadline := 1
  deadline_pos := by omega
  opponents_finite := by
    intro j hj choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice

@[simp] private theorem input_opponents : input.opponents = opponents := rfl

@[simp] private theorem input_pivot : input.pivot = 0 := rfl

@[simp] private theorem input_deadline : input.deadline = 1 := rfl

def zeroBoundaryMass : PivotRepairMass 1
  | Sum.inl _ => 0
  | Sum.inr .late => 1
  | Sum.inr .never => 0
  | Sum.inr .firstAtom => 0

def massAt (firstAtom : ℝ) : PivotRepairMass 1 :=
  pivotRepairMassWithFirstAtom zeroBoundaryMass firstAtom

theorem zeroBoundaryMass_feasible : IsPivotRepairMassFeasible zeroBoundaryMass := by
  norm_num [IsPivotRepairMassFeasible, pivotRepairHead, pivotRepairLate,
    pivotRepairNever, pivotRepairFirstAtom, zeroBoundaryMass, Fin.sum_univ_succ]

theorem massAt_feasible {firstAtom : ℝ} (hzero : 0 ≤ firstAtom)
    (hone : firstAtom ≤ 1) : IsPivotRepairMassFeasible (massAt firstAtom) := by
  apply isPivotRepairMassFeasible_withFirstAtom zeroBoundaryMass_feasible hzero
  simpa [pivotRepairLate, zeroBoundaryMass] using hone

@[simp] private theorem massAt_head (firstAtom : ℝ) (time : Fin 1) :
    pivotRepairHead (massAt firstAtom) time = 0 := by
  fin_cases time
  simp [massAt, pivotRepairHead, pivotRepairMassWithFirstAtom, zeroBoundaryMass]

@[simp] private theorem massAt_late (firstAtom : ℝ) :
    pivotRepairLate (massAt firstAtom) = 1 := by
  simp [massAt, pivotRepairLate, pivotRepairMassWithFirstAtom, zeroBoundaryMass]

@[simp] private theorem massAt_never (firstAtom : ℝ) :
    pivotRepairNever (massAt firstAtom) = 0 := by
  simp [massAt, pivotRepairNever, pivotRepairMassWithFirstAtom, zeroBoundaryMass]

@[simp] private theorem massAt_firstAtom (firstAtom : ℝ) :
    pivotRepairFirstAtom (massAt firstAtom) = firstAtom := by
  simp [massAt, pivotRepairFirstAtom, pivotRepairMassWithFirstAtom]

private theorem stoppingLawBehavior_pure_none (player : Fin 4) :
    quittingStoppingLawBehaviorStrategy reward player (PMF.pure none) =
      quittingPureTimeBehaviorStrategy reward player none := by
  unfold quittingStoppingLawBehaviorStrategy quittingPureTimeBehaviorStrategy
  funext time history
  simp [Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard,
    Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.StoppingLaw.finiteMass,
    Math.Probability.DiscreteHazard.StoppingLaw.survival,
    quittingPureTimeHazard]
  apply PMF.ext
  intro stop
  cases stop <;> simp [Math.Probability.DiscreteHazard.booleanCoin,
    PMF.pure_apply]

private theorem purePivotPayoff_none (observer : Fin 4) :
    input.purePivotPayoff none observer = 0 := by
  rw [show input.purePivotPayoff none observer =
      quittingTerminalPayoff reward
        (quittingPureTimeProfileBehavior reward (fun _ ↦ none)) observer by
    unfold QuittingPivotRepairLPInput.purePivotPayoff input opponents
    congr 2
    funext player
    simp [quittingStoppingLawProfile, quittingPureTimeProfileBehavior,
      stoppingLawBehavior_pure_none]]
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  simp [quittingFirstStoppingOutcome, quittingEarliestStoppingValue,
    quittingStoppingTimeValue, quittingTerminalOutcomeReward]

private theorem allNeverPayoff (observer : Fin 4) :
    quittingTerminalPayoff reward (quittingStoppingLawProfile reward opponents) observer = 0 := by
  have h := purePivotPayoff_none observer
  change quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update opponents 0 (PMF.pure none))) observer = 0 at h
  have hup : Function.update opponents 0 (PMF.pure none) = opponents := by
    funext player
    simp [opponents, Function.update_apply]
  rwa [hup] at h

private theorem purePivotPayoff_one (observer : Fin 4) :
    input.purePivotPayoff (some 1) observer = if observer = 0 then 1 else 0 := by
  unfold QuittingPivotRepairLPInput.purePivotPayoff input
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward opponents 0 observer 1]
  · rw [show Function.update opponents 0 (PMF.pure none) = opponents by
      funext player
      simp [opponents, Function.update_apply]]
    rw [allNeverPayoff]
    fin_cases observer <;> norm_num [opponents, reward, quittingSingletonTerminal]
  · intro j hj choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice
  · omega

private theorem pureResponse_zero (responder : Fin 4) (hne : responder ≠ 0) :
    input.purePivotResponderPayoff responder (some 1) (some 0) responder = 0 := by
  change quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (Function.update opponents 0 (PMF.pure (some 1)))
          responder (PMF.pure (some 0)))) responder = 0
  have hcomm :
      Function.update (Function.update opponents 0 (PMF.pure (some 1))) responder
          (PMF.pure (some 0)) =
        Function.update (Function.update opponents responder (PMF.pure (some 0))) 0
          (PMF.pure (some 1)) := by
    exact Function.update_comm hne.symm _ _ _
  rw [hcomm]
  rw [quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
    reward opponents responder 0 responder hne.symm 0 0 1]
  · rw [allNeverPayoff]
    fin_cases responder <;> simp_all [opponents, reward, quittingSingletonTerminal]
  · omega
  · omega
  · rfl
  · rfl
  · intro j hj hr choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice

private theorem purePivotPayoff_zero (observer : Fin 4) :
    input.purePivotPayoff (some 0) observer = if observer = 0 then 1 else 0 := by
  unfold QuittingPivotRepairLPInput.purePivotPayoff input
  rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward opponents 0 observer 0]
  · have hup : Function.update opponents 0 (PMF.pure none) = opponents := by
      funext player
      simp [opponents, Function.update_apply]
    rw [hup, allNeverPayoff]
    fin_cases observer <;> norm_num [opponents, reward, quittingSingletonTerminal]
  · intro j hj choice hchoice
    left
    simpa [opponents, PMF.pure_apply] using hchoice
  · omega

private theorem pureResponderNever (responder observer : Fin 4) :
    input.purePivotResponderPayoff responder none none observer = 0 := by
  change quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update (Function.update opponents 0 (PMF.pure none)) responder
        (PMF.pure none))) observer = 0
  have hup : Function.update (Function.update opponents 0 (PMF.pure none)) responder
      (PMF.pure none) = opponents := by
    funext player
    simp [opponents, Function.update_apply]
  rw [hup, allNeverPayoff]

private theorem pivotCap_eq_one : input.pivotCap = 1 := by
  unfold QuittingPivotRepairLPInput.pivotCap
  apply le_antisymm
  · apply Finset.sup'_le
    intro candidate _
    rcases candidate with time | endpoint
    · fin_cases time
      simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
      rw [input_pivot, purePivotPayoff_zero]
      simp
    · cases endpoint
      · simp [QuittingPivotRepairLPInput.pivotCapCandidateValue,
          QuittingPivotRepairLPInput.pivotNeverPayoff, purePivotPayoff_none]
      · simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue,
          QuittingPivotRepairLPInput.pivotLatePayoff,
          QuittingPivotRepairLPInput.pivotNeverPayoff]
        rw [purePivotPayoff_none]
        norm_num [opponents, reward, quittingSingletonTerminal]
  · have hle := Finset.le_sup' (f := input.pivotCapCandidateValue)
      (show (Sum.inl ⟨0, input.deadline_pos⟩ : Fin input.deadline ⊕ Bool) ∈
        Finset.univ by exact Finset.mem_univ _)
    rw [show input.pivotCapCandidateValue (Sum.inl ⟨0, input.deadline_pos⟩) = 1 by
      simp only [QuittingPivotRepairLPInput.pivotCapCandidateValue]
      rw [input_pivot, purePivotPayoff_zero]
      simp] at hle
    exact hle

private theorem prescribedPayoff_massAt (firstAtom : ℝ) (observer : Fin 4) :
    input.prescribedPayoff (massAt firstAtom) observer = if observer = 0 then 1 else 0 := by
  unfold QuittingPivotRepairLPInput.prescribedPayoff
  change (∑ time : Fin 1, pivotRepairHead (massAt firstAtom) time *
      input.purePivotPayoff (some time.1) observer) +
      pivotRepairLate (massAt firstAtom) * input.purePivotPayoff (some 1) observer +
      pivotRepairNever (massAt firstAtom) * input.purePivotPayoff none observer = _
  rw [Fin.sum_univ_one]
  simp only [massAt, pivotRepairHead, pivotRepairLate, pivotRepairNever,
    pivotRepairMassWithFirstAtom]
  simp [Function.update, zeroBoundaryMass]
  rw [purePivotPayoff_one]

private theorem constraintGain_massAt_le {firstAtom : ℝ} (hzero : 0 ≤ firstAtom)
    (constraint : input.ConstraintIndex) :
    input.constraintGain (massAt firstAtom) constraint ≤ firstAtom := by
  rcases constraint with (_ | _ | ⟨responder, response | endpoint⟩)
  · simpa [QuittingPivotRepairLPInput.constraintGain] using hzero
  · simp only [QuittingPivotRepairLPInput.constraintGain]
    rw [pivotCap_eq_one, prescribedPayoff_massAt]
    simp [input_pivot, hzero]
  · fin_cases response
    have hr : (responder : Fin 4) ≠ 0 := by
      simpa only [input_pivot] using responder.property
    simp only [QuittingPivotRepairLPInput.constraintGain,
      QuittingPivotRepairLPInput.pureResponsePayoff, input_deadline]
    simp only [massAt_head, zero_mul, Finset.sum_const_zero, massAt_late,
      massAt_never, zero_add, one_mul]
    rw [pureResponse_zero responder hr, prescribedPayoff_massAt]
    simp [hr, hzero]
  · fin_cases endpoint <;> fin_cases responder
    all_goals
      simp only [QuittingPivotRepairLPInput.constraintGain,
        QuittingPivotRepairLPInput.responderNeverEndpoint,
        QuittingPivotRepairLPInput.responderFirstEndpoint,
        QuittingPivotRepairLPInput.responderLimitEndpoint,
        QuittingPivotRepairLPInput.earlyContribution, input_deadline]
      simp [massAt_head, Finset.sum_const_zero, massAt_late, massAt_never,
        massAt_firstAtom,
        QuittingPivotRepairLPInput.otherNeverProduct,
        QuittingPivotRepairLPInput.responderEarlierReward,
        QuittingPivotRepairLPInput.responderTieReward,
        QuittingPivotRepairLPInput.responderLaterReward, opponents, reward,
        quittingSingletonTerminal, pureResponderNever, prescribedPayoff_massAt,
        input_pivot, hzero]

private def bindingConstraint : input.ConstraintIndex :=
  Sum.inr (Sum.inr (⟨1, by norm_num [input]⟩, Sum.inr 1))

private theorem bindingConstraint_gain (firstAtom : ℝ) :
    input.constraintGain (massAt firstAtom) bindingConstraint = firstAtom := by
  simp only [bindingConstraint, QuittingPivotRepairLPInput.constraintGain,
    QuittingPivotRepairLPInput.responderFirstEndpoint,
    QuittingPivotRepairLPInput.earlyContribution, input_deadline]
  simp [massAt_head, Finset.sum_const_zero, massAt_late, massAt_never,
    massAt_firstAtom, QuittingPivotRepairLPInput.otherNeverProduct,
    QuittingPivotRepairLPInput.responderLaterReward,
    QuittingPivotRepairLPInput.responderTieReward, opponents, reward,
    quittingSingletonTerminal, pureResponderNever, prescribedPayoff_massAt]

/-- The concrete finite LP objective on the boundary ray is exactly its
first-atom coordinate. -/
theorem objective_massAt {firstAtom : ℝ} (hzero : 0 ≤ firstAtom) :
    input.objective (massAt firstAtom) = firstAtom := by
  unfold QuittingPivotRepairLPInput.objective
  apply le_antisymm
  · apply Finset.sup'_le
    intro constraint _
    exact constraintGain_massAt_le hzero constraint
  · have hle := Finset.le_sup' (f := input.constraintGain (massAt firstAtom))
      (show bindingConstraint ∈ Finset.univ by exact Finset.mem_univ _)
    rwa [bindingConstraint_gain] at hle

/-- The boundary mass is an attained zero minimizer of the concrete finite LP. -/
theorem zeroBoundaryMass_is_zero_minimizer :
    input.objective zeroBoundaryMass = 0 ∧
      ∀ mass, IsPivotRepairMassFeasible mass →
        input.objective zeroBoundaryMass ≤ input.objective mass := by
  have hmass : massAt 0 = zeroBoundaryMass := by
    funext coordinate
    rcases coordinate with head | tail
    · fin_cases head
      rfl
    · cases tail <;> rfl
  have hzero : input.objective zeroBoundaryMass = 0 := by
    rw [← hmass, objective_massAt (firstAtom := 0) (by norm_num)]
  refine ⟨hzero, ?_⟩
  intro mass _
  rw [hzero]
  unfold QuittingPivotRepairLPInput.objective
  have hle := Finset.le_sup' (f := input.constraintGain mass)
    (show (Sum.inl () : input.ConstraintIndex) ∈ Finset.univ by exact Finset.mem_univ _)
  change (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty
    (input.constraintGain mass) at hle
  exact hle

/-- Every positive first atom on the feasible boundary ray has strictly
positive objective, despite the zero boundary optimum. -/
theorem objective_massAt_pos {firstAtom : ℝ} (hpositive : 0 < firstAtom)
    (hone : firstAtom ≤ 1) :
    IsPivotRepairMassFeasible (massAt firstAtom) ∧
      0 < input.objective (massAt firstAtom) := by
  exact ⟨massAt_feasible hpositive.le hone,
    objective_massAt hpositive.le |>.symm ▸ hpositive⟩

/-- Every positive-hazard geometric realization of the boundary ray has
actual exploitability equal to that hazard. -/
theorem geometric_exploitability_massAt {hazard : ℝ} (hpositive : 0 < hazard)
    (hle : hazard ≤ 1) :
    let feasible := massAt_feasible hpositive.le hle
    quittingTerminalExploitability reward
        (quittingStoppingLawProfile reward
          (input.geometricLaws (massAt hazard) feasible hazard hpositive hle)) = hazard := by
  let feasible := massAt_feasible hpositive.le hle
  dsimp only
  rw [input.geometric_exploitability_eq_objective
    (massAt hazard) feasible hazard hpositive hle]
  · exact objective_massAt hpositive.le
  · simp [massAt_late, massAt_firstAtom]

end GameTheory.PivotRepairNonattainedZeroLP
