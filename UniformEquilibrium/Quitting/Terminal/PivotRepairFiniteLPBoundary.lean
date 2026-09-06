import UniformEquilibrium.Quitting.Terminal.PivotRepairFiniteLP
import MathUE.Finset.SupNonexpansive
import MathUE.LinearProgramming.PivotRepairMassPerturbation

noncomputable section

namespace GameTheory.QuittingPivotRepairLPInput

open Math.LinearProgramming

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (input : QuittingPivotRepairLPInput reward)

@[simp] theorem prescribedPayoff_withFirstAtom
    (mass : PivotRepairMass input.deadline) (firstAtom : ℝ) (observer : ι) :
    input.prescribedPayoff (pivotRepairMassWithFirstAtom mass firstAtom) observer =
      input.prescribedPayoff mass observer := by
  simp [prescribedPayoff]

theorem objective_nonneg (mass : PivotRepairMass input.deadline) :
    0 ≤ input.objective mass := by
  unfold objective
  exact Finset.le_sup' (fun index ↦ input.constraintGain mass index)
    (show Sum.inl () ∈ Finset.univ by simp)

omit [Fintype ι] [DecidableEq ι] in
private theorem headWeightedSum_affine
    (coefficient : Fin input.deadline → ℝ)
    (first second : PivotRepairMass input.deadline) (scale : ℝ) :
    (∑ time, pivotRepairHead (scale • first + (1 - scale) • second) time *
        coefficient time) =
      scale * (∑ time, pivotRepairHead first time * coefficient time) +
        (1 - scale) *
          (∑ time, pivotRepairHead second time * coefficient time) := by
  simp only [pivotRepairHead, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, mul_assoc]
  rw [Finset.mul_sum, Finset.mul_sum]

theorem prescribedPayoff_affine
    (first second : PivotRepairMass input.deadline) (scale : ℝ) (observer : ι) :
    input.prescribedPayoff (scale • first + (1 - scale) • second) observer =
      scale * input.prescribedPayoff first observer +
        (1 - scale) * input.prescribedPayoff second observer := by
  unfold prescribedPayoff
  rw [input.headWeightedSum_affine]
  simp only [pivotRepairLate, pivotRepairNever, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem pureResponsePayoff_affine
    (first second : PivotRepairMass input.deadline) (scale : ℝ)
    (responder : ι) (response : Option ℕ) (observer : ι) :
    input.pureResponsePayoff (scale • first + (1 - scale) • second)
        responder response observer =
      scale * input.pureResponsePayoff first responder response observer +
        (1 - scale) * input.pureResponsePayoff second responder response observer := by
  unfold pureResponsePayoff
  rw [input.headWeightedSum_affine]
  simp only [pivotRepairLate, pivotRepairNever, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem earlyContribution_affine
    (first second : PivotRepairMass input.deadline) (scale : ℝ) (responder : ι) :
    input.earlyContribution (scale • first + (1 - scale) • second) responder =
      scale * input.earlyContribution first responder +
        (1 - scale) * input.earlyContribution second responder := by
  unfold earlyContribution
  rw [input.headWeightedSum_affine]
  simp only [pivotRepairLate, pivotRepairNever, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem constraintGain_affine
    (first second : PivotRepairMass input.deadline) (scale : ℝ)
    (index : input.ConstraintIndex) :
    input.constraintGain (scale • first + (1 - scale) • second) index =
      scale * input.constraintGain first index +
        (1 - scale) * input.constraintGain second index := by
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · simp [constraintGain]
  · rw [show input.constraintGain _ (Sum.inr (Sum.inl ())) =
        input.pivotCap - input.prescribedPayoff
          (scale • first + (1 - scale) • second) input.pivot by rfl,
      input.prescribedPayoff_affine]
    simp only [constraintGain]
    ring
  · rw [show input.constraintGain _
        (Sum.inr (Sum.inr ⟨responder, Sum.inl time⟩)) =
        input.pureResponsePayoff (scale • first + (1 - scale) • second)
            responder (some time.1) responder -
          input.prescribedPayoff (scale • first + (1 - scale) • second)
            responder by rfl,
      input.pureResponsePayoff_affine, input.prescribedPayoff_affine]
    simp only [constraintGain]
    ring
  · fin_cases endpoint <;> simp only [constraintGain] <;>
      simp [responderNeverEndpoint, responderFirstEndpoint,
        responderLimitEndpoint, input.earlyContribution_affine,
        input.prescribedPayoff_affine, pivotRepairLate, pivotRepairNever,
        pivotRepairFirstAtom, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring

theorem constraintGain_withFirstAtom_sub
    (mass : PivotRepairMass input.deadline) (firstAtom : ℝ)
    (index : input.ConstraintIndex) :
    input.constraintGain (pivotRepairMassWithFirstAtom mass firstAtom) index -
        input.constraintGain mass index =
      match index with
      | Sum.inr (Sum.inr ⟨responder, Sum.inr 1⟩) =>
          input.otherNeverProduct responder *
            (input.responderTieReward responder -
              responderLaterReward (reward := reward) responder) *
            (firstAtom - pivotRepairFirstAtom mass)
      | _ => 0 := by
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · simp [constraintGain]
  · simp [constraintGain]
  · simp [constraintGain, pureResponsePayoff]
  · fin_cases endpoint <;> (
      simp [constraintGain, responderNeverEndpoint, responderFirstEndpoint,
        responderLimitEndpoint, earlyContribution] <;> ring)

private theorem otherNeverProduct_nonneg (responder : ι) :
    0 ≤ input.otherNeverProduct responder := by
  unfold otherNeverProduct
  exact Finset.prod_nonneg fun j _ ↦ ENNReal.toReal_nonneg

private theorem otherNeverProduct_le_one (responder : ι) :
    input.otherNeverProduct responder ≤ 1 := by
  unfold otherNeverProduct
  exact Finset.prod_le_one (fun j _ ↦ ENNReal.toReal_nonneg)
    (fun j _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (input.opponents j) none))

private theorem abs_tie_sub_later_le (responder : ι) :
    |input.responderTieReward responder -
        responderLaterReward (reward := reward) responder| ≤
      2 * quittingRewardBound reward := by
  calc
    |_ - _| ≤ |input.responderTieReward responder| +
        |responderLaterReward (reward := reward) responder| := abs_sub _ _
    _ ≤ quittingRewardBound reward + quittingRewardBound reward := by
      exact add_le_add (abs_reward_le_quittingRewardBound reward _ _)
        (abs_reward_le_quittingRewardBound reward _ _)
    _ = 2 * quittingRewardBound reward := by ring

theorem abs_constraintGain_withFirstAtom_sub_le
    (mass : PivotRepairMass input.deadline) (firstAtom : ℝ)
    (index : input.ConstraintIndex) :
    |input.constraintGain (pivotRepairMassWithFirstAtom mass firstAtom) index -
        input.constraintGain mass index| ≤
      2 * quittingRewardBound reward *
        |firstAtom - pivotRepairFirstAtom mass| := by
  rw [input.constraintGain_withFirstAtom_sub mass firstAtom index]
  rcases index with _ | (_ | ⟨responder, time | endpoint⟩)
  · simp only [abs_zero]
    positivity [quittingRewardBound_nonneg reward]
  · simp only [abs_zero]
    positivity [quittingRewardBound_nonneg reward]
  · simp only [abs_zero]
    positivity [quittingRewardBound_nonneg reward]
  · fin_cases endpoint
    · norm_num
      positivity [quittingRewardBound_nonneg reward]
    · norm_num
      have hdabs : |input.otherNeverProduct responder| ≤ 1 := by
        rw [abs_of_nonneg (input.otherNeverProduct_nonneg responder)]
        exact input.otherNeverProduct_le_one responder
      have hreward := input.abs_tie_sub_later_le responder
      calc
        |input.otherNeverProduct responder| *
              |input.responderTieReward responder -
                responderLaterReward (reward := reward) responder| *
            |firstAtom - pivotRepairFirstAtom mass| ≤
            1 * (2 * quittingRewardBound reward) *
              |firstAtom - pivotRepairFirstAtom mass| := by gcongr
        _ = 2 * quittingRewardBound reward *
              |firstAtom - pivotRepairFirstAtom mass| := by ring
    · norm_num
      positivity [quittingRewardBound_nonneg reward]

theorem abs_objective_withFirstAtom_sub_le
    (mass : PivotRepairMass input.deadline) (firstAtom : ℝ) :
    |input.objective (pivotRepairMassWithFirstAtom mass firstAtom) -
        input.objective mass| ≤
      2 * quittingRewardBound reward *
        |firstAtom - pivotRepairFirstAtom mass| := by
  unfold objective
  apply Math.Finset.abs_sup'_sub_sup'_le_const Finset.univ_nonempty
  intro index _
  exact input.abs_constraintGain_withFirstAtom_sub_le mass firstAtom index

end GameTheory.QuittingPivotRepairLPInput
