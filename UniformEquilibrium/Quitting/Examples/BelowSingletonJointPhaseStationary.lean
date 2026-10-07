import UniformEquilibrium.Quitting.Examples.BelowSingletonJointPhaseFixture
import UniformEquilibrium.Quitting.Stationary.ProperMixingBalance
import UniformEquilibrium.Quitting.Stationary.RewardCoordinatePerturbation
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Robust exclusion of proper-three stationary supports

The literal fixture and every reward table within `1 / 1000` in all sixty
coordinates exclude actual terminal Nash with exactly three proper active
hazards. This does not exclude full support, sure hazards or uniform equilibrium.
-/

noncomputable section

namespace GameTheory.BelowSingletonJointPhaseFixture

open QuittingFinFourEndpointRows

private def firstOfMissing : Fin 4 → Fin 4 := ![3, 2, 1, 0]
private def zeroRowOfMissing : Fin 4 → Fin 4 := ![1, 0, 3, 2]
private def favoriteOfMissing : Fin 4 → Fin 4 := ![2, 3, 0, 1]

private def erasedGrand : Fin 4 → Finset (Fin 4) :=
  ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}]

private theorem erase_grand_eq (player : Fin 4) :
    ({0, 1, 2, 3} : Finset (Fin 4)).erase player = erasedGrand player := by
  fin_cases player <;> decide

private def quitZeroRow (a x : ℝ) : ℝ :=
  1 - (11 / 10) * a - x / 2 + (503 / 5) * a * x

private def quitFavorite (a c : ℝ) : ℝ := 1 - (a + c) / 2 - 3 * a * c

private def continueFavorite (a c : ℝ) : ℝ :=
  4 * a * (1 - c) - (119 / 60) * a * c

private def favoriteGap (a c : ℝ) : ℝ :=
  continueFavorite a c - (a + c - a * c) * quitFavorite a c

private theorem quitZeroRow_lower {a x : ℝ}
    (ha : 0 ≤ a) (ha9 : a ≤ 9 / 10) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 / 100 ≤ quitZeroRow a x := by
  have hleft : 1 / 100 ≤ 1 - (11 / 10) * a := by linarith
  have hright : 1 / 100 ≤ 1 / 2 + (199 / 2) * a := by linarith
  have hcombine := add_nonneg
    (mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hleft))
    (mul_nonneg hx.1 (sub_nonneg.mpr hright))
  dsimp [quitZeroRow]
  nlinarith [hcombine]

private theorem favoriteGap_lower {a c : ℝ}
    (ha : 9 / 10 ≤ a) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    173 / 200 ≤ favoriteGap a c := by
  let g : ℝ := (1 - c) * ((a + 9 / 10) / 2 + 3) + c * (91 / 60) +
    (3 * (a + 9 / 10) - 5 / 2) * c * (1 - c)
  have hg : 0 ≤ g := by
    dsimp [g]
    apply add_nonneg
    · exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr hc.2) (by linarith))
        (mul_nonneg hc.1 (by norm_num))
    · exact mul_nonneg (mul_nonneg (by linarith) hc.1) (sub_nonneg.mpr hc.2)
  have hbase : 173 / 200 ≤ favoriteGap (9 / 10) c := by
    have hprod := mul_nonneg (sub_nonneg.mpr hc.2)
      (show 0 ≤ 448 - 64 * c by linarith [hc.2])
    dsimp [favoriteGap, continueFavorite, quitFavorite]
    nlinarith [hprod]
  have hidentity : favoriteGap a c = favoriteGap (9 / 10) c + (a - 9 / 10) * g := by
    dsimp [favoriteGap, continueFavorite, quitFavorite, g]
    ring
  rw [hidentity]
  exact hbase.trans (le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ha) hg))

private theorem literal_zero_quit (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    sigmaValue (weightOfReward reward) hazard (zeroRowOfMissing missing) =
      quitZeroRow (hazard (firstOfMissing missing)) (hazard (favoriteOfMissing missing)) := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, zeroRowOfMissing, favoriteOfMissing, quitZeroRow,
    pureQuitEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_zero_continue (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    excludedValue (weightOfReward reward) hazard (zeroRowOfMissing missing) = 0 := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [zeroRowOfMissing, excludedEndpointRowSum, opponentCoalitionMass,
    weightOfReward, Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ,
    Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]

private theorem literal_zero_mass (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    continueMassExcl hazard (zeroRowOfMissing missing) =
      (1 - hazard (firstOfMissing missing)) * (1 - hazard (favoriteOfMissing missing)) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, zeroRowOfMissing, favoriteOfMissing,
    continueMassExcl, Fin.prod_univ_succ, huniv, erase_grand_eq, erasedGrand]
  all_goals norm_num +decide [Finset.prod_insert, Finset.prod_singleton, hmissing]
  all_goals ring

private theorem literal_favorite_quit (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    sigmaValue (weightOfReward reward) hazard (favoriteOfMissing missing) =
      quitFavorite (hazard (firstOfMissing missing)) (hazard (zeroRowOfMissing missing)) := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, zeroRowOfMissing, favoriteOfMissing, quitFavorite,
    pureQuitEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_favorite_continue (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    excludedValue (weightOfReward reward) hazard (favoriteOfMissing missing) =
      continueFavorite (hazard (firstOfMissing missing)) (hazard (zeroRowOfMissing missing)) := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, zeroRowOfMissing, favoriteOfMissing, continueFavorite,
    excludedEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_favorite_mass (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    continueMassExcl hazard (favoriteOfMissing missing) =
      (1 - hazard (firstOfMissing missing)) * (1 - hazard (zeroRowOfMissing missing)) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, zeroRowOfMissing, favoriteOfMissing,
    continueMassExcl, Fin.prod_univ_succ, huniv, erase_grand_eq, erasedGrand]
  all_goals norm_num +decide [Finset.prod_insert, Finset.prod_singleton, hmissing]
  all_goals ring

private theorem center_mixing_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : ∀ terminal player, |other terminal player - reward terminal player| ≤ 1 / 1000)
    (root : Fin 4 → PMF Bool) (player : Fin 4)
    (hproper : hazardOfRoot root player ∈ Set.Ioo (0 : ℝ) 1)
    (hnash : (quittingGame other).IsεAsymptoticNash (quittingTerminalPayoff other) 0
      (quittingStationaryProfile other root)) :
    |sigmaValue (weightOfReward reward) (hazardOfRoot root) player *
        (1 - continueMassExcl (hazardOfRoot root) player) -
      excludedValue (weightOfReward reward) (hazardOfRoot root) player| ≤
      (1 / 500) * (1 - continueMassExcl (hazardOfRoot root) player) := by
  have hbalance := stationary_proper_mixing_balance other root player hproper hnash
  have herror := abs_quittingDiscountedDisplacement_sub_le_of_coordinate_error
    reward other (1 / 1000) hclose (hazardOfRoot root) player
    (fun coordinate _ => ⟨hazardOfRoot_nonneg root coordinate, hazardOfRoot_le_one root coordinate⟩)
  simp only [quittingDiscountedDisplacement, sub_zero, one_mul] at herror
  have hzero : (1 - continueMassExcl (hazardOfRoot root) player) *
      sigmaValue (weightOfReward other) (hazardOfRoot root) player -
        excludedValue (weightOfReward other) (hazardOfRoot root) player = 0 := by
    nlinarith [hbalance]
  rw [hzero, zero_sub, abs_neg] at herror
  rw [mul_comm (sigmaValue (weightOfReward reward) (hazardOfRoot root) player)]
  convert herror using 1
  norm_num

/-- Every reward coordinate may vary independently within the closed radius.
The excluded profiles have exactly three positive hazards, all strictly below one. -/
theorem not_exact_stationaryNash_of_three_proper_support_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : ∀ terminal player, |other terminal player - reward terminal player| ≤ 1 / 1000)
    (root : Fin 4 → PMF Bool)
    (hcard : (quittingPositiveHazardSupport root).card = 3)
    (hproper : ∀ player ∈ quittingPositiveHazardSupport root, hazardOfRoot root player < 1) :
    ¬ (quittingGame other).IsεAsymptoticNash (quittingTerminalPayoff other) 0
      (quittingStationaryProfile other root) := by
  intro hnash
  obtain ⟨missing, hmissing⟩ : ∃ player, player ∉ quittingPositiveHazardSupport root := by
    by_contra hnone
    push Not at hnone
    have heq := Finset.eq_univ_iff_forall.mpr hnone
    rw [heq] at hcard
    norm_num at hcard
  have hsubset : quittingPositiveHazardSupport root ⊆ Finset.univ.erase missing := by
    intro player hplayer
    exact Finset.mem_erase.mpr ⟨by intro heq; subst player; exact hmissing hplayer,
      Finset.mem_univ player⟩
  have hs : quittingPositiveHazardSupport root = Finset.univ.erase missing :=
    Finset.eq_of_subset_of_card_le hsubset (by simp [hcard])
  have hz : hazardOfRoot root missing = 0 := by
    have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport root hmissing
    simp only [hazardOfRoot, hpure, PMF.pure_apply, Bool.true_eq_false,
      ↓reduceIte, ENNReal.toReal_zero]
  have hactive (player : Fin 4) (hne : player ≠ missing) :
      hazardOfRoot root player ∈ Set.Ioo (0 : ℝ) 1 := by
    have hmem : player ∈ quittingPositiveHazardSupport root := by simp [hs, hne]
    exact ⟨(Finset.mem_filter.mp hmem).2, hproper player hmem⟩
  have hai := hactive (firstOfMissing missing) (by fin_cases missing <;> decide)
  have hac := hactive (zeroRowOfMissing missing) (by fin_cases missing <;> decide)
  have hax := hactive (favoriteOfMissing missing) (by fin_cases missing <;> decide)
  let a := hazardOfRoot root (firstOfMissing missing)
  let c := hazardOfRoot root (zeroRowOfMissing missing)
  let x := hazardOfRoot root (favoriteOfMissing missing)
  have hzero := center_mixing_error other hclose root _ hac hnash
  rw [literal_zero_quit _ _ hz, literal_zero_continue _ _ hz,
    literal_zero_mass _ _ hz, sub_zero, abs_mul] at hzero
  have hden : 0 < 1 - (1 - a) * (1 - x) := by
    nlinarith [hai.1, hax.1, mul_pos hai.1 (sub_pos.mpr hax.2)]
  change |quitZeroRow a x| * |1 - (1 - a) * (1 - x)| ≤
    (1 / 500) * (1 - (1 - a) * (1 - x)) at hzero
  rw [abs_of_pos hden] at hzero
  have hsmall : |quitZeroRow a x| ≤ 1 / 500 :=
    (mul_le_mul_iff_left₀ hden).mp hzero
  have ha9 : 9 / 10 < a := by
    by_contra hnot
    have hlower := quitZeroRow_lower hai.1.le (le_of_not_gt hnot) ⟨hax.1.le, hax.2.le⟩
    have hu := (abs_le.mp hsmall).2
    linarith
  have hfavorite := center_mixing_error other hclose root _ hax hnash
  rw [literal_favorite_quit _ _ hz, literal_favorite_continue _ _ hz,
    literal_favorite_mass _ _ hz] at hfavorite
  have hgap : 173 / 200 ≤ favoriteGap a c := favoriteGap_lower ha9.le ⟨hac.1.le, hac.2.le⟩
  have hmass : 1 - (1 - a) * (1 - c) ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hai.2.le) (sub_nonneg.mpr hac.2.le)]
  have hid : quitFavorite a c * (1 - (1 - a) * (1 - c)) - continueFavorite a c =
      -favoriteGap a c := by dsimp [favoriteGap]; ring
  change |quitFavorite a c * (1 - (1 - a) * (1 - c)) - continueFavorite a c| ≤
    (1 / 500) * (1 - (1 - a) * (1 - c)) at hfavorite
  rw [hid, abs_neg] at hfavorite
  have hup := (abs_le.mp hfavorite).2
  linarith

/-- The center exclusion is a specialization of the full-coordinate theorem. -/
theorem not_exact_stationaryNash_of_three_proper_support
    (root : Fin 4 → PMF Bool)
    (hcard : (quittingPositiveHazardSupport root).card = 3)
    (hproper : ∀ player ∈ quittingPositiveHazardSupport root, hazardOfRoot root player < 1) :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) :=
  not_exact_stationaryNash_of_three_proper_support_of_coordinate_error reward
    (by intro terminal player; simp) root hcard hproper

end GameTheory.BelowSingletonJointPhaseFixture
