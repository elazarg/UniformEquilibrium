import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumInwardViolation

/-! # Polynomial endpoints along a common support hazard -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Hazard `t` on `active` and zero off it. -/
def commonSupportHazard (active : Finset ι) (t : ℝ) (player : ι) : ℝ :=
  if player ∈ active then t else 0

/-- Opponents' all-Continue mass as a real polynomial in hazards. -/
def hazardOpponentContinueMass (hazard : ι → ℝ) (player : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase player, (1 - hazard other)

/-- The zero-continuation Continue endpoint, extended polynomially to every
real hazard vector. -/
def hazardContinueZeroPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (player : ι) : ℝ :=
  ∑ coalition ∈ (Finset.univ.erase player).powerset,
    ((∏ other ∈ coalition, hazard other) *
      ∏ other ∈ Finset.univ.erase player \ coalition,
        (1 - hazard other)) *
      if h : coalition.Nonempty then reward ⟨coalition, h⟩ player else 0

omit [Fintype ι] in
theorem continuous_commonSupportHazard
    (active : Finset ι) (player : ι) :
    Continuous (fun t => commonSupportHazard active t player) := by
  by_cases hmem : player ∈ active
  · simpa only [commonSupportHazard, hmem, if_true] using
      (continuous_id' : Continuous fun t : ℝ => t)
  · simpa only [commonSupportHazard, hmem, if_false] using
      (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))

theorem continuous_hazardOpponentContinueMass
    (player : ι) :
    Continuous (fun hazard : ι → ℝ =>
      hazardOpponentContinueMass hazard player) := by
  exact continuous_finsetProd _ fun other _ =>
    continuous_const.sub (continuous_apply other)

theorem continuous_hazardContinueZeroPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    Continuous (fun hazard => hazardContinueZeroPayoff reward hazard player) := by
  apply continuous_finsetSum
  intro coalition _
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_finsetProd _ fun other _ => continuous_apply other
    · exact continuous_finsetProd _ fun other _ =>
        continuous_const.sub (continuous_apply other)
  · by_cases hcoalition : coalition.Nonempty
    · simp only [hcoalition, dite_true]
      exact continuous_const
    · simp only [hcoalition, dite_false]
      exact continuous_const

@[simp] theorem hazardContinueZeroPayoff_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    hazardContinueZeroPayoff reward 0 player = 0 := by
  unfold hazardContinueZeroPayoff
  apply Finset.sum_eq_zero
  intro coalition _
  by_cases hcoalition : coalition.Nonempty
  · rw [Finset.prod_eq_zero (s := coalition) hcoalition.choose_spec (by simp)]
    simp
  · simp [hcoalition]

@[simp] theorem hazardOpponentContinueMass_zero (player : ι) :
    hazardOpponentContinueMass (0 : ι → ℝ) player = 1 := by
  simp [hazardOpponentContinueMass]

theorem continuous_commonSupportOpponentContinueMass
    (active : Finset ι) (player : ι) :
    Continuous (fun t => hazardOpponentContinueMass
      (commonSupportHazard active t) player) := by
  apply (continuous_hazardOpponentContinueMass player).comp
  rw [continuous_pi_iff]
  exact fun other => continuous_commonSupportHazard active other

omit [Fintype ι] in
@[simp] theorem commonSupportHazard_zero (active : Finset ι) :
    commonSupportHazard active 0 = 0 := by
  funext player
  simp [commonSupportHazard]

theorem hazardOpponentContinueMass_eq_root_emptyMass
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) (player : ι) :
    hazardOpponentContinueMass hazard player =
      quittingOpponentCoalitionMass
        (rootOfHazard hazard hzero hone) player ∅ := by
  simp [hazardOpponentContinueMass, quittingOpponentCoalitionMass,
    rootOfHazard, pmfBool_false_toReal]

theorem hazardContinueZeroPayoff_eq_rootContinuePayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hazard : ι → ℝ) (hzero : ∀ player, 0 ≤ hazard player)
    (hone : ∀ player, hazard player ≤ 1) (player : ι) :
    hazardContinueZeroPayoff reward hazard player =
      quittingRootContinuePayoff reward 0
        (rootOfHazard hazard hzero hone) player := by
  rw [quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
  apply Finset.sum_congr rfl
  intro coalition _
  congr 1
  · simp [quittingOpponentCoalitionMass, rootOfHazard,
      pmfBool_false_toReal]
  · by_cases hcoalition : coalition.Nonempty
    · simp [quittingStageCoalitionPayoff, hcoalition]
    · simp [quittingStageCoalitionPayoff, hcoalition]

end GameTheory
