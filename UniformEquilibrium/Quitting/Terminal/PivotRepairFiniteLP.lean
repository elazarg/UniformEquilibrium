import MathUE.LinearProgramming.PivotRepairMassPolytope
import UniformEquilibrium.Quitting.Terminal.FiniteOpponentPivotResponseFormula

noncomputable section

namespace GameTheory

open Math.LinearProgramming
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual fixed opponent laws and their common strict finite support deadline. -/
structure QuittingPivotRepairLPInput
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  opponents : ι → PMF (Option ℕ)
  pivot : ι
  deadline : ℕ
  deadline_pos : 0 < deadline
  opponents_finite : ∀ j, j ≠ pivot →
    IsFiniteClockStoppingLaw deadline (opponents j)

namespace QuittingPivotRepairLPInput

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

/-- Payoff of an actual pure pivot stopping time against the fixed opponent laws. -/
def purePivotPayoff (choice : Option ℕ) (observer : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update input.opponents input.pivot (PMF.pure choice))) observer

/-- The unique prescribed-payoff affine map, for every payoff observer. -/
def prescribedPayoff (mass : PivotRepairMass input.deadline) (observer : ι) : ℝ :=
  (∑ time, pivotRepairHead mass time *
      input.purePivotPayoff (some time.1) observer) +
    pivotRepairLate mass * input.purePivotPayoff (some input.deadline) observer +
    pivotRepairNever mass * input.purePivotPayoff none observer

/-- Actual pure responder payoff for one pure pivot time and one pure response. -/
def purePivotResponderPayoff (responder : ι) (choice response : Option ℕ)
    (observer : ι) : ℝ :=
  quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update
        (Function.update input.opponents input.pivot (PMF.pure choice))
        responder (PMF.pure response))) observer

/-- Affine payoff of a pure response against the provisional pivot mass split. -/
def pureResponsePayoff (mass : PivotRepairMass input.deadline)
    (responder : ι) (response : Option ℕ) (observer : ι) : ℝ :=
  (∑ time, pivotRepairHead mass time *
      input.purePivotResponderPayoff responder (some time.1) response observer) +
    pivotRepairLate mass * input.purePivotResponderPayoff responder
      (some input.deadline) response observer +
    pivotRepairNever mass * input.purePivotResponderPayoff responder none response observer

def pivotNeverPayoff : ℝ := input.purePivotPayoff none input.pivot

def pivotLatePayoff : ℝ :=
  input.pivotNeverPayoff +
    reward (quittingSingletonTerminal input.pivot) input.pivot *
      ∏ j ∈ Finset.univ.erase input.pivot, (input.opponents j none).toReal

def pivotCapCandidateValue : Fin input.deadline ⊕ Bool → ℝ
  | Sum.inl time => input.purePivotPayoff (some time.1) input.pivot
  | Sum.inr false => input.pivotNeverPayoff
  | Sum.inr true => input.pivotLatePayoff

/-- Finite maximum of the pivot's head, Never, and late-payoff candidates. -/
def pivotCap : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty input.pivotCapCandidateValue

def otherNeverProduct (responder : ι) : ℝ :=
  ∏ j ∈ (Finset.univ.erase input.pivot).erase responder,
    (input.opponents j none).toReal

/-- Actual censored-head contribution with the responder choosing Never. -/
def earlyContribution (mass : PivotRepairMass input.deadline)
    (responder : ι) : ℝ :=
  (∑ time, pivotRepairHead mass time * input.purePivotResponderPayoff responder
      (some time.1) none responder) +
    (pivotRepairLate mass + pivotRepairNever mass) *
      input.purePivotResponderPayoff responder none none responder

def responderEarlierReward (responder : ι) : ℝ :=
  reward (quittingSingletonTerminal input.pivot) responder

def responderTieReward (responder : ι) : ℝ :=
  reward ⟨{input.pivot, responder}, by simp⟩ responder

def responderLaterReward (responder : ι) : ℝ :=
  reward (quittingSingletonTerminal responder) responder

def responderNeverEndpoint (mass : PivotRepairMass input.deadline)
    (responder : ι) : ℝ :=
  input.earlyContribution mass responder + input.otherNeverProduct responder *
    (input.responderEarlierReward responder * pivotRepairLate mass)

def responderFirstEndpoint (mass : PivotRepairMass input.deadline)
    (responder : ι) : ℝ :=
  input.earlyContribution mass responder + input.otherNeverProduct responder *
    (responderLaterReward (reward := reward) responder *
        (pivotRepairLate mass + pivotRepairNever mass) +
      (input.responderTieReward responder -
        responderLaterReward (reward := reward) responder) *
        pivotRepairFirstAtom mass)

def responderLimitEndpoint (mass : PivotRepairMass input.deadline)
    (responder : ι) : ℝ :=
  input.earlyContribution mass responder + input.otherNeverProduct responder *
    (input.responderEarlierReward responder * pivotRepairLate mass +
      responderLaterReward (reward := reward) responder * pivotRepairNever mass)

abbrev Nonpivot := {j : ι // j ≠ input.pivot}

abbrev ConstraintIndex :=
  Unit ⊕ (Unit ⊕ (input.Nonpivot × (Fin input.deadline ⊕ Fin 3)))

def constraintGain (mass : PivotRepairMass input.deadline) :
    input.ConstraintIndex → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => input.pivotCap - input.prescribedPayoff mass input.pivot
  | Sum.inr (Sum.inr ⟨responder, Sum.inl time⟩) =>
      input.pureResponsePayoff mass responder (some time.1) responder -
        input.prescribedPayoff mass responder
  | Sum.inr (Sum.inr ⟨responder, Sum.inr endpoint⟩) =>
      (match endpoint with
        | 0 => input.responderNeverEndpoint mass responder
        | 1 => input.responderFirstEndpoint mass responder
        | 2 => input.responderLimitEndpoint mass responder) -
          input.prescribedPayoff mass responder

/-- Epigraph-free LP objective: the maximum of zero and all affine gains. -/
def objective (mass : PivotRepairMass input.deadline) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (input.constraintGain mass)

theorem continuous_prescribedPayoff (observer : ι) :
    Continuous (input.prescribedPayoff · observer) := by
  unfold prescribedPayoff
  unfold pivotRepairHead pivotRepairLate pivotRepairNever
  fun_prop

theorem continuous_pureResponsePayoff (responder : ι) (response : Option ℕ)
    (observer : ι) :
    Continuous (input.pureResponsePayoff · responder response observer) := by
  unfold pureResponsePayoff
  unfold pivotRepairHead pivotRepairLate pivotRepairNever
  fun_prop

theorem continuous_earlyContribution (responder : ι) :
    Continuous (input.earlyContribution · responder) := by
  unfold earlyContribution
  unfold pivotRepairHead pivotRepairLate pivotRepairNever
  fun_prop

theorem continuous_responderNeverEndpoint (responder : ι) :
    Continuous (input.responderNeverEndpoint · responder) := by
  unfold responderNeverEndpoint pivotRepairLate
  exact (input.continuous_earlyContribution responder).add
    (continuous_const.mul (continuous_const.mul (continuous_apply _)))

theorem continuous_responderFirstEndpoint (responder : ι) :
    Continuous (input.responderFirstEndpoint · responder) := by
  unfold responderFirstEndpoint pivotRepairLate pivotRepairNever pivotRepairFirstAtom
  exact (input.continuous_earlyContribution responder).add
    (continuous_const.mul
      ((continuous_const.mul
          ((continuous_apply (Sum.inr PivotRepairTailCoordinate.late)).add
            (continuous_apply (Sum.inr PivotRepairTailCoordinate.never)))).add
        (continuous_const.mul
          (continuous_apply (Sum.inr PivotRepairTailCoordinate.firstAtom)))))

theorem continuous_responderLimitEndpoint (responder : ι) :
    Continuous (input.responderLimitEndpoint · responder) := by
  unfold responderLimitEndpoint pivotRepairLate pivotRepairNever
  exact (input.continuous_earlyContribution responder).add
    (continuous_const.mul
      ((continuous_const.mul (continuous_apply _)).add
        (continuous_const.mul (continuous_apply _))))

theorem continuous_constraintGain (index : input.ConstraintIndex) :
    Continuous (input.constraintGain · index) := by
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · exact continuous_const
  · change Continuous ((fun _ : PivotRepairMass input.deadline ↦ input.pivotCap) -
      fun mass ↦ input.prescribedPayoff mass input.pivot)
    exact continuous_const.sub (input.continuous_prescribedPayoff input.pivot)
  · change Continuous
      ((fun mass ↦ input.pureResponsePayoff mass responder (some time.1) responder) -
        fun mass ↦ input.prescribedPayoff mass responder)
    exact (input.continuous_pureResponsePayoff responder (some time.1) responder).sub
      (input.continuous_prescribedPayoff responder)
  · fin_cases endpoint
    · exact (input.continuous_responderNeverEndpoint responder).sub
        (input.continuous_prescribedPayoff responder)
    · exact (input.continuous_responderFirstEndpoint responder).sub
        (input.continuous_prescribedPayoff responder)
    · exact (input.continuous_responderLimitEndpoint responder).sub
        (input.continuous_prescribedPayoff responder)

theorem continuous_objective : Continuous input.objective := by
  unfold objective
  exact Continuous.finset_sup'_apply Finset.univ_nonempty fun index _ ↦
    input.continuous_constraintGain index

/-- The finite signed repair LP attains its minimum on the literal mass polytope. -/
theorem exists_objective_minimizer :
    ∃ mass ∈ pivotRepairMassFeasibleSet input.deadline,
      IsMinOn input.objective (pivotRepairMassFeasibleSet input.deadline) mass := by
  exact (isCompact_pivotRepairMassFeasibleSet input.deadline).exists_isMinOn
    (pivotRepairMassFeasibleSet_nonempty input.deadline)
    input.continuous_objective.continuousOn

end QuittingPivotRepairLPInput
end GameTheory
