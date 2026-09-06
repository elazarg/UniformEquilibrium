import UniformEquilibrium.Quitting.Root.EndpointOpponentStability
import UniformEquilibrium.Quitting.Root.NashDefect
import UniformEquilibrium.Quitting.Root.SupportPurification
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import MathUE.PMFProduct.Bool
import MathUE.SurvivalProduct

/-! # Absorption-weighted support purification of quitting roots -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem badAction_mass_mul_le_ordinaryRegret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {β : ℝ} (who : ι) :
    (IsQuittingRootBadQuitAt reward tail β root who →
      (root who true).toReal = 0 ∨ (root who true).toReal * β <
        quittingRootCoordinateNashDefect reward tail root who) ∧
    (IsQuittingRootBadContinueAt reward tail β root who →
      (root who false).toReal = 0 ∨ (root who false).toReal * β <
        quittingRootCoordinateNashDefect reward tail root who) := by
  have hmix := quittingRootSuccessorPayoff_eq_endpointMix reward tail root who
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hq : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hc : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  constructor
  · intro hbad
    dsimp only [IsQuittingRootBadQuitAt] at hbad
    unfold quittingRootCoordinateNashDefect
    have hid : quittingRootContinuePayoff reward tail root who -
        quittingRootSuccessorPayoff reward tail root who =
      (root who true).toReal *
        (quittingRootContinuePayoff reward tail root who -
          quittingRootQuitPayoff reward tail root who) := by
      rw [hmix]
      calc
        _ = ((root who false).toReal + (root who true).toReal) *
              quittingRootContinuePayoff reward tail root who -
            ((root who true).toReal *
              quittingRootQuitPayoff reward tail root who +
            (root who false).toReal *
              quittingRootContinuePayoff reward tail root who) := by rw [hsum, one_mul]
        _ = _ := by ring
    by_cases hzero : (root who true).toReal = 0
    · exact Or.inl hzero
    · refine Or.inr (lt_of_lt_of_le ?_ (sub_le_sub_right (le_max_right _ _) _))
      rw [hid]
      exact mul_lt_mul_of_pos_left (by linarith) (lt_of_le_of_ne hq (Ne.symm hzero))
  · intro hbad
    dsimp only [IsQuittingRootBadContinueAt] at hbad
    unfold quittingRootCoordinateNashDefect
    have hid : quittingRootQuitPayoff reward tail root who -
        quittingRootSuccessorPayoff reward tail root who =
      (root who false).toReal *
        (quittingRootQuitPayoff reward tail root who -
          quittingRootContinuePayoff reward tail root who) := by
      rw [hmix]
      calc
        _ = ((root who false).toReal + (root who true).toReal) *
              quittingRootQuitPayoff reward tail root who -
            ((root who true).toReal *
              quittingRootQuitPayoff reward tail root who +
            (root who false).toReal *
              quittingRootContinuePayoff reward tail root who) := by rw [hsum, one_mul]
        _ = _ := by ring
    by_cases hzero : (root who false).toReal = 0
    · exact Or.inl hzero
    · refine Or.inr (lt_of_lt_of_le ?_ (sub_le_sub_right (le_max_left _ _) _))
      rw [hid]
      exact mul_lt_mul_of_pos_left (by linarith) (lt_of_le_of_ne hc (Ne.symm hzero))

/-- Weighted ordinary regret makes every action deleted at threshold `Bρ`
carry less than `ρ` times the row absorption.  No division by absorption is
used, so the zero-absorption case is included. -/
theorem supportPurifiedRoot_badAction_mass_le_absorptionScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ)
    (hregret : ∀ who, quittingRootCoordinateNashDefect reward tail root who ≤
      B * ρ ^ 2 * quittingRootAbsorptionMass root) :
    (∀ who, IsQuittingRootBadQuitAt reward tail (B * ρ) root who →
      (root who true).toReal ≤ ρ * quittingRootAbsorptionMass root) ∧
    (∀ who, IsQuittingRootBadContinueAt reward tail (B * ρ) root who →
      (root who false).toReal ≤ ρ * quittingRootAbsorptionMass root) := by
  constructor <;> intro who hbad
  · rcases
      (badAction_mass_mul_le_ordinaryRegret reward tail root who).1 hbad
      with hzero | hstrict
    · rw [hzero]
      exact mul_nonneg hρ.le (quittingRootAbsorptionMass_nonneg root)
    have hupper := hregret who
    nlinarith [mul_pos hB hρ]
  · rcases
      (badAction_mass_mul_le_ordinaryRegret reward tail root who).2 hbad
      with hzero | hstrict
    · rw [hzero]
      exact mul_nonneg hρ.le (quittingRootAbsorptionMass_nonneg root)
    have hupper := hregret who
    nlinarith [mul_pos hB hρ]

/-- Simultaneous deletion at threshold `Bρ` changes each Quit coordinate by
at most `ρ` times the original row absorption, including zero absorption. -/
theorem supportPurifiedRoot_coordinate_close_of_weighted_regret
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ)
    (hregret : ∀ who, quittingRootCoordinateNashDefect reward tail root who ≤
      B * ρ ^ 2 * quittingRootAbsorptionMass root) :
    ∀ who,
      |(quittingSupportPurifiedRoot reward tail (B * ρ) root who true).toReal -
          (root who true).toReal| ≤ ρ * quittingRootAbsorptionMass root := by
  obtain ⟨hbadQuit, hbadContinue⟩ :=
    supportPurifiedRoot_badAction_mass_le_absorptionScale
      reward tail root hB hρ hregret
  intro who
  by_cases ha : quittingRootAbsorptionMass root = 0
  · have hquit : (root who true).toReal = 0 := by
      have := quittingQuitProbability_le_absorptionMass root who
      exact le_antisymm (by simpa [ha] using this) ENNReal.toReal_nonneg
    have hroot : root who = PMF.pure false :=
      Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero _ hquit
    by_cases hbad : IsQuittingRootBadQuitAt reward tail (B * ρ) root who
    · rw [quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
        reward tail (B * ρ) root who hbad, hroot]
      simp [ha]
    · have hnotContinue :
        ¬IsQuittingRootBadContinueAt reward tail (B * ρ) root who := by
        intro hbadC
        have := hbadContinue who hbadC
        have hfalse : (root who false).toReal = 1 := by
          linarith [quittingRoot_continueProbability_add_quitProbability root who]
        rw [ha, mul_zero] at this
        linarith
      rw [quittingSupportPurifiedRoot_eq_self_of_not_bad
        reward tail (B * ρ) root who hbad hnotContinue]
      simp [ha]
  · have haPos : 0 < quittingRootAbsorptionMass root :=
      lt_of_le_of_ne (quittingRootAbsorptionMass_nonneg root) (Ne.symm ha)
    have hbadQuit' : ∀ player,
        IsQuittingRootBadQuitAt reward tail (B * ρ) root player →
          (root player true).toReal < ρ * quittingRootAbsorptionMass root := by
      intro player hbad
      by_cases hzero : (root player true).toReal = 0
      · rw [hzero]
        exact mul_pos hρ haPos
      · have hstrict := ((badAction_mass_mul_le_ordinaryRegret
          reward tail root player).1 hbad).resolve_left hzero
        have hupper := hregret player
        nlinarith [mul_pos hB hρ]
    have hbadContinue' : ∀ player,
        IsQuittingRootBadContinueAt reward tail (B * ρ) root player →
          (root player false).toReal < ρ * quittingRootAbsorptionMass root := by
      intro player hbad
      by_cases hzero : (root player false).toReal = 0
      · rw [hzero]
        exact mul_pos hρ haPos
      · have hstrict := ((badAction_mass_mul_le_ordinaryRegret
          reward tail root player).2 hbad).resolve_left hzero
        have hupper := hregret player
        nlinarith [mul_pos hB hρ]
    exact (supportPurifiedRoot_coordinate_close_of_badAction_small
      reward tail (B * ρ) (ρ * quittingRootAbsorptionMass root) root
      (mul_pos hρ haPos) hbadQuit' hbadContinue' who).le

/-- Changing Boolean Quit coordinates changes one-stage absorption by at most
the sum of their coordinate changes. -/
theorem abs_quittingRootAbsorptionMass_sub_le_sum_quitProbability
    (first second : ι → PMF Bool) :
    |quittingRootAbsorptionMass first - quittingRootAbsorptionMass second| ≤
      ∑ who, |(first who true).toReal - (second who true).toReal| := by
  unfold quittingRootAbsorptionMass
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  have hproduct := Math.abs_prod_sub_prod_le_sum_abs Finset.univ
    (fun who ↦ (first who false).toReal)
    (fun who ↦ (second who false).toReal)
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun who _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _))
    (fun _ _ ↦ ENNReal.toReal_nonneg)
    (fun who _ ↦ ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _))
  calc
    |1 - (∏ player, (first player false).toReal) -
        (1 - ∏ player, (second player false).toReal)| =
        |(∏ player, (second player false).toReal) -
          ∏ player, (first player false).toReal| := by
          congr 1
          ring_nf
    _ = |(∏ player, (first player false).toReal) -
          ∏ player, (second player false).toReal| := abs_sub_comm _ _
    _ ≤ ∑ who, |(first who false).toReal - (second who false).toReal| := hproduct
    _ = _ := by
      apply Finset.sum_congr rfl
      intro who _
      have hfirst := quittingRoot_continueProbability_add_quitProbability first who
      have hsecond := quittingRoot_continueProbability_add_quitProbability second who
      have heq : (first who false).toReal - (second who false).toReal =
          -((first who true).toReal - (second who true).toReal) := by linarith
      rw [heq, abs_neg]

/-- For four players and `ρ ≤ 1/8`, weighted support purification retains at
least half of the original row absorption. -/
theorem finFour_half_absorption_le_supportPurifiedRoot
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (root : Fin 4 → PMF Bool) {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ) (hρmax : ρ ≤ 1 / 8)
    (hregret : ∀ who, quittingRootCoordinateNashDefect reward tail root who ≤
      B * ρ ^ 2 * quittingRootAbsorptionMass root) :
    quittingRootAbsorptionMass root / 2 ≤
      quittingRootAbsorptionMass
        (quittingSupportPurifiedRoot reward tail (B * ρ) root) := by
  have hclose := supportPurifiedRoot_coordinate_close_of_weighted_regret
    reward tail root hB hρ hregret
  have habs := abs_quittingRootAbsorptionMass_sub_le_sum_quitProbability
    root (quittingSupportPurifiedRoot reward tail (B * ρ) root)
  have hsum : (∑ who : Fin 4,
      |(root who true).toReal -
        (quittingSupportPurifiedRoot reward tail (B * ρ) root who true).toReal|) ≤
      4 * (ρ * quittingRootAbsorptionMass root) := by
    calc
      _ ≤ ∑ _who : Fin 4, ρ * quittingRootAbsorptionMass root :=
        Finset.sum_le_sum fun who _ ↦ by simpa [abs_sub_comm] using hclose who
      _ = _ := by simp
  have ha := quittingRootAbsorptionMass_nonneg root
  rw [abs_le] at habs
  nlinarith

/-- For four players, simultaneous weighted purification is support-local
`13Bρ` Nash at the original annotation. The constant uses only the three
opponents of the tested player. -/
theorem finFour_isSupportApproxNash_supportPurifiedRoot_of_weighted_regret
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (root : Fin 4 → PMF Bool) {B ρ : ℝ}
    (hB : 0 < B) (hρ : 0 < ρ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B)
    (htail : ∀ player, |tail player| ≤ B)
    (hregret : ∀ who, quittingRootCoordinateNashDefect reward tail root who ≤
      B * ρ ^ 2 * quittingRootAbsorptionMass root) :
    IsQuittingRootSupportApproxNash reward tail (13 * B * ρ)
      (quittingSupportPurifiedRoot reward tail (B * ρ) root) := by
  let purified := quittingSupportPurifiedRoot reward tail (B * ρ) root
  have hclose := supportPurifiedRoot_coordinate_close_of_weighted_regret
    reward tail root hB hρ hregret
  have habsUpper : quittingRootAbsorptionMass root ≤ 1 := by
    unfold quittingRootAbsorptionMass
    linarith [quittingStationaryContinueMass_nonneg root]
  intro who
  have htv : quittingRootOpponentTVSum purified root who ≤
      3 * (ρ * quittingRootAbsorptionMass root) := by
    unfold quittingRootOpponentTVSum
    calc
      _ ≤ ∑ _other ∈ Finset.univ.erase who,
          ρ * quittingRootAbsorptionMass root := by
        apply Finset.sum_le_sum
        intro other _
        rw [Math.Probability.pmfTV_bool_eq_abs_apply_true]
        simpa [purified] using hclose other
      _ = _ := by simp
  have hdiff := abs_quittingRootEndpointDifference_sub_le_opponentTVSum
    reward tail purified root who hreward htail
  have hdiffBound :
      |quittingRootEndpointDifference reward tail purified who -
        quittingRootEndpointDifference reward tail root who| ≤ 12 * B * ρ := by
    refine hdiff.trans ?_
    have hrhoa : ρ * quittingRootAbsorptionMass root ≤ ρ :=
      mul_le_of_le_one_right hρ.le habsUpper
    calc
      4 * B * quittingRootOpponentTVSum purified root who ≤
          4 * B * (3 * (ρ * quittingRootAbsorptionMass root)) :=
        mul_le_mul_of_nonneg_left htv (by positivity)
      _ = 12 * B * (ρ * quittingRootAbsorptionMass root) := by ring
      _ ≤ 12 * B * ρ := mul_le_mul_of_nonneg_left hrhoa (by positivity)
  constructor
  · intro hquit
    have hnotBad : ¬IsQuittingRootBadQuitAt reward tail (B * ρ) root who := by
      intro hbad
      have hpure := quittingSupportPurifiedRoot_eq_pure_false_of_badQuit
        reward tail (B * ρ) root who hbad
      change 0 < (purified who true).toReal at hquit
      rw [show purified who = PMF.pure false by exact hpure] at hquit
      simp at hquit
    dsimp only [IsQuittingRootBadQuitAt] at hnotBad
    have hrootBound : -(B * ρ) ≤
        quittingRootEndpointDifference reward tail root who := by
      unfold quittingRootEndpointDifference
      linarith
    rw [abs_le] at hdiffBound
    nlinarith [hrootBound]
  · intro hcontinue
    have hnotBad :
        ¬IsQuittingRootBadContinueAt reward tail (B * ρ) root who := by
      intro hbad
      have hnotBadQuit : ¬IsQuittingRootBadQuitAt reward tail (B * ρ) root who :=
        fun hbadQuit ↦ not_badContinue_of_badQuit reward tail
          (mul_nonneg hB.le hρ.le) root who hbadQuit hbad
      have hpure := quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
        reward tail (B * ρ) root who hnotBadQuit hbad
      change 0 < (purified who false).toReal at hcontinue
      rw [show purified who = PMF.pure true by exact hpure] at hcontinue
      simp at hcontinue
    dsimp only [IsQuittingRootBadContinueAt] at hnotBad
    have hrootBound :
        quittingRootEndpointDifference reward tail root who ≤ B * ρ := by
      unfold quittingRootEndpointDifference
      linarith
    rw [abs_le] at hdiffBound
    nlinarith [hrootBound]

end GameTheory
