import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement

/-! # Actual stationary payoff and full-cap continuity in hazard coordinates

Continuity is relative to the closed probability cube with every deleted-opponent
survival strictly below one. Zero and sure hazards are included. The polynomial-
quotient formulas equal the actual payoff and complete behavioral cap; they are
not merely endpoint verifiers for supplied deviations.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The closed hazard cube with strictly contracting deleted opponents. -/
def quittingStationaryContractingHazardCube : Set (ι → ℝ) :=
  {hazard | (∀ who, 0 ≤ hazard who ∧ hazard who ≤ 1) ∧
    ∀ who, continueMassExcl hazard who < 1}

/-- Deleted-opponent contraction persists in an ambient neighborhood. Intersecting
this open set with the closed cube retains all probability-boundary faces. -/
theorem isOpen_setOf_continueMassExcl_lt_one :
    IsOpen {hazard : ι → ℝ | ∀ who, continueMassExcl hazard who < 1} := by
  have heq : {hazard : ι → ℝ | ∀ who, continueMassExcl hazard who < 1} =
      ⋂ who, {hazard : ι → ℝ | continueMassExcl hazard who < 1} := by
    ext hazard
    simp
  rw [heq]
  exact isOpen_iInter_of_finite fun who =>
    isOpen_lt (continuous_continueMassExcl who) continuous_const

/-- The stationary payoff quotient, written only in actual hazard coordinates. -/
def quittingStationaryHazardPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hazard : ι → ℝ) : Payoff ι :=
  fun who =>
    (hazard who * sigmaValue (weightOfReward reward) hazard who +
      (1 - hazard who) * excludedValue (weightOfReward reward) hazard who) /
        (1 - (1 - hazard who) * continueMassExcl hazard who)

/-- The full behavioral cap in the strictly contracting deleted-opponents regime. -/
def quittingStationaryHazardCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (hazard : ι → ℝ) : Payoff ι :=
  fun who => max (sigmaValue (weightOfReward reward) hazard who)
    (excludedValue (weightOfReward reward) hazard who / (1 - continueMassExcl hazard who))

/-- The fixed-opponent survival is exactly the deleted-coordinate product. -/
theorem quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass root who =
      continueMassExcl (hazardOfRoot root) who := by
  change quittingStationaryContinueMass (Function.update root who (PMF.pure false)) = _
  rw [quittingStationaryContinueMass_eq_hazard_split _ who]
  have hself : hazardOfRoot (Function.update root who (PMF.pure false)) who = 0 := by
    simp [hazardOfRoot]
  rw [hself, sub_zero, one_mul]
  unfold continueMassExcl
  apply Finset.prod_congr rfl
  intro other hother
  simp [hazardOfRoot, Finset.ne_of_mem_erase hother]

theorem quittingStationaryFixedOpponentsQuitValue_eq_sigmaValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsQuitValue reward root who =
      sigmaValue (weightOfReward reward) (hazardOfRoot root) who := by
  change quittingRootQuitPayoff reward 0 root who = _
  exact quittingRootQuitPayoff_eq_sigmaValue reward 0 root who

theorem quittingStationaryFixedOpponentsContinueReward_eq_excludedValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryFixedOpponentsContinueReward reward root who =
      excludedValue (weightOfReward reward) (hazardOfRoot root) who := by
  change quittingRootContinuePayoff reward 0 root who = _
  rw [quittingRootContinuePayoff_eq_gammaValue]
  simp [gammaValue]

/-- One strictly contracting deleted row already ensures joint absorption. -/
theorem quittingStationaryContinueMass_lt_one_of_deleted_contracts
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryContinueMass root < 1 :=
  (quittingStationaryContinueMass_le_update_pure_false root who).trans_lt hcontracts

/-- The actual payoff agrees with the hazard quotient; no own-hazard interiority is needed. -/
theorem quittingTerminalPayoff_stationary_eq_hazardPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) who =
      quittingStationaryHazardPayoff reward (hazardOfRoot root) who := by
  rw [quittingTerminalPayoff_stationary_eq_absorbingContribution_div reward root who
    (quittingStationaryContinueMass_lt_one_of_deleted_contracts root who hcontracts),
    quittingRootAbsorbingContribution_eq_hazard_mixture,
    quittingStationaryContinueMass_eq_hazard_split root who]
  rfl

/-- The exact complete cap has the displayed polynomial-quotient coordinates. -/
theorem quittingStationaryFullRateUnilateralCap_eq_hazardCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι)
    (hcontracts : quittingStationaryFixedOpponentsContinueMass root who < 1) :
    quittingStationaryFullRateUnilateralCap reward root who =
      quittingStationaryHazardCap reward (hazardOfRoot root) who := by
  rw [quittingStationaryFullRateUnilateralCap_of_lt reward root who hcontracts]
  simp only [quittingStationaryUnilateralCap, quittingStationarySelectedCap,
    quittingStationaryNeverValue, quittingStationaryFixedOpponentsQuitValue_eq_sigmaValue,
    quittingStationaryFixedOpponentsContinueReward_eq_excludedValue,
    quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl,
    quittingStationaryHazardCap]

/-- Positivity of the actual prescribed-payoff denominator on the contracting cube. -/
theorem quittingStationaryHazardPayoff_denominator_pos
    (hazard : ι → ℝ) (hmem : hazard ∈ quittingStationaryContractingHazardCube)
    (who : ι) : 0 < 1 - (1 - hazard who) * continueMassExcl hazard who := by
  have hmass : 0 ≤ continueMassExcl hazard who := by
    unfold continueMassExcl
    exact Finset.prod_nonneg fun other _ => sub_nonneg.mpr (hmem.1 other).2
  have hle : (1 - hazard who) * continueMassExcl hazard who ≤
      continueMassExcl hazard who := by
    nlinarith [mul_nonneg (hmem.1 who).1 hmass]
  exact sub_pos.mpr (hle.trans_lt (hmem.2 who))

theorem continuousOn_quittingStationaryHazardPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ContinuousOn (quittingStationaryHazardPayoff reward)
      quittingStationaryContractingHazardCube := by
  apply continuousOn_pi.mpr
  intro who
  have hnumerator : Continuous fun hazard : ι → ℝ =>
      hazard who * sigmaValue (weightOfReward reward) hazard who +
        (1 - hazard who) * excludedValue (weightOfReward reward) hazard who :=
    ((continuous_apply who).mul (continuous_sigmaValue _ who)).add
      ((continuous_const.sub (continuous_apply who)).mul (continuous_excludedValue _ who))
  have hdenominator : Continuous fun hazard : ι → ℝ =>
      1 - (1 - hazard who) * continueMassExcl hazard who :=
    continuous_const.sub ((continuous_const.sub (continuous_apply who)).mul
      (continuous_continueMassExcl who))
  exact hnumerator.continuousOn.div hdenominator.continuousOn
    (fun hazard hmem => ne_of_gt
      (quittingStationaryHazardPayoff_denominator_pos hazard hmem who))

theorem continuousOn_quittingStationaryHazardCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ContinuousOn (quittingStationaryHazardCap reward)
      quittingStationaryContractingHazardCube := by
  apply continuousOn_pi.mpr
  intro who
  exact (continuous_sigmaValue (weightOfReward reward) who).continuousOn.sup
    ((continuous_excludedValue (weightOfReward reward) who).continuousOn.div
      (continuous_const.sub (continuous_continueMassExcl who)).continuousOn
      (fun hazard hmem => ne_of_gt (sub_pos.mpr (hmem.2 who))))

/-- Compile a point of the relatively open contracting part of the closed cube. -/
def quittingStationaryContractingHazardRoot
    (hazard : quittingStationaryContractingHazardCube (ι := ι)) : ι → PMF Bool :=
  rootOfHazard hazard.val (fun who => (hazard.property.1 who).1)
    (fun who => (hazard.property.1 who).2)

@[simp]
theorem hazardOfRoot_quittingStationaryContractingHazardRoot
    (hazard : quittingStationaryContractingHazardCube (ι := ι)) :
    hazardOfRoot (quittingStationaryContractingHazardRoot hazard) = hazard.val :=
  hazardOfRoot_rootOfHazard _ _ _

theorem quittingStationaryContractingHazardRoot_contracts
    (hazard : quittingStationaryContractingHazardCube (ι := ι)) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
      (quittingStationaryContractingHazardRoot hazard) who < 1 := by
  rw [quittingStationaryFixedOpponentsContinueMass_eq_continueMassExcl,
    hazardOfRoot_quittingStationaryContractingHazardRoot]
  exact hazard.property.2 who

/-- Continuity of the actual prescribed terminal payoff, including cube faces. -/
theorem continuous_quittingTerminalPayoff_contractingHazardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingStationaryContractingHazardRoot hazard)) := by
  have heq : (fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingStationaryContractingHazardRoot hazard))) =
        fun hazard => quittingStationaryHazardPayoff reward hazard.val := by
    funext hazard who
    rw [quittingTerminalPayoff_stationary_eq_hazardPayoff reward _ who
      (quittingStationaryContractingHazardRoot_contracts hazard who),
      hazardOfRoot_quittingStationaryContractingHazardRoot]
  rw [heq]
  exact (continuousOn_quittingStationaryHazardPayoff reward).domRestrict

/-- Continuity of the actual full-rate cap, not just selected deviation payoffs. -/
theorem continuous_quittingStationaryFullRateUnilateralCap_contractingHazardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      quittingStationaryFullRateUnilateralCap reward
        (quittingStationaryContractingHazardRoot hazard) := by
  have heq : (fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      quittingStationaryFullRateUnilateralCap reward
        (quittingStationaryContractingHazardRoot hazard)) =
        fun hazard => quittingStationaryHazardCap reward hazard.val := by
    funext hazard who
    rw [quittingStationaryFullRateUnilateralCap_eq_hazardCap reward _ who
      (quittingStationaryContractingHazardRoot_contracts hazard who),
      hazardOfRoot_quittingStationaryContractingHazardRoot]
  rw [heq]
  exact (continuousOn_quittingStationaryHazardCap reward).domRestrict

/-- Joint continuity of actual payoff and the supremum over every behavioral deviation. -/
theorem continuous_quittingStationaryPayoff_fullCap_contractingHazardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      (quittingTerminalPayoff reward
          (quittingStationaryProfile reward (quittingStationaryContractingHazardRoot hazard)),
        quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward (quittingStationaryContractingHazardRoot hazard))) := by
  apply (continuous_quittingTerminalPayoff_contractingHazardRoot reward).prodMk
  have heq : (fun hazard : quittingStationaryContractingHazardCube (ι := ι) =>
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (quittingStationaryContractingHazardRoot hazard))) =
        fun hazard => quittingStationaryFullRateUnilateralCap reward
          (quittingStationaryContractingHazardRoot hazard) := by
    funext hazard who
    exact quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap _ _ _
  rw [heq]
  exact continuous_quittingStationaryFullRateUnilateralCap_contractingHazardRoot reward

end GameTheory
