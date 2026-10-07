import UniformEquilibrium.Quitting.Examples.CrossedMatchingFixture
import UniformEquilibrium.Quitting.Stationary.ProperMixingBalance
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exclusion of proper-three stationary supports at the literal fixture

This concerns actual stationary terminal Nash and its actual payoff. It does
not exclude full-support stationary profiles or arbitrary behavioral profiles.
-/

noncomputable section

namespace GameTheory.CrossedMatchingFixture

open QuittingFinFourEndpointRows

private def firstOfMissing : Fin 4 → Fin 4 := ![3, 2, 1, 0]
private def partnerOfMissing : Fin 4 → Fin 4 := ![1, 0, 3, 2]
private def thirdOfMissing : Fin 4 → Fin 4 := ![2, 3, 0, 1]
private def pairPremium : Fin 4 → ℝ := ![99 / 14, 145 / 32, 99 / 14, 145 / 32]
private def favoriteReward : Fin 4 → ℝ := ![61 / 8, 61 / 8, 61 / 8, 289 / 40]

private def erasedGrand : Fin 4 → Finset (Fin 4) :=
  ![{1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}]

private theorem erase_grand_eq (player : Fin 4) :
    ({0, 1, 2, 3} : Finset (Fin 4)).erase player = erasedGrand player := by
  fin_cases player <;> decide

private theorem scalar_three_support_impossible
    {a c x premium favorite : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1)
    (hp : 0 < premium) (hp9 : premium < 9) (hf : 0 < favorite)
    (hpf : 9 < premium + favorite)
    (hk : 1 + premium * a - 2 * x - (premium + 9) * a * x = 0)
    (hi : ((premium + 9) * x - premium) * (a - c) * (x + c - x * c) =
      favorite * x * (1 - c)) : False := by
  let D := (premium + 9) * x - premium
  have hbalance : a * D = 1 - 2 * x := by dsimp [D]; nlinarith [hk]
  have hD : 0 < D := by
    by_contra hnot
    have hnonpos : D ≤ 0 := le_of_not_gt hnot
    have hax : a * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.1.le hnonpos
    have hxhalf : 1 / 2 ≤ x := by nlinarith [hbalance]
    dsimp [D] at hnonpos
    nlinarith [mul_nonneg (show 0 ≤ premium + 9 by linarith) (sub_nonneg.mpr hxhalf)]
  have hxhalf : x < 1 / 2 := by nlinarith [mul_pos ha.1 hD, hbalance]
  have hden : 0 < x + c - x * c := by
    nlinarith [mul_pos hc.1 (sub_pos.mpr hx.2)]
  have hdenOne : x + c - x * c ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hc.2.le)]
  have hright : 0 < favorite * x * (1 - c) :=
    mul_pos (mul_pos hf hx.1) (sub_pos.mpr hc.2)
  have hQ : 0 < D * (a - c) := by
    by_contra hnot
    have hmul := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hden.le
    change D * (a - c) * (x + c - x * c) = _ at hi
    linarith
  have hQlower : favorite * x * (1 - c) ≤ D * (a - c) := by
    change D * (a - c) * (x + c - x * c) = _ at hi
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hdenOne)]
  have hQupper : D * (a - c) < D * (1 - c) := by
    nlinarith [mul_pos hD (sub_pos.mpr ha.2)]
  have hFx : D < favorite * x := by
    have hterm := mul_pos hp (show 0 < 1 - 2 * x by linarith)
    have hterm2 := mul_pos (sub_pos.mpr hpf) hx.1
    dsimp [D]
    nlinarith
  nlinarith [mul_pos (sub_pos.mpr hFx) (sub_pos.mpr hc.2)]

private theorem active_stationary_balance
    (root : Fin 4 → PMF Bool) (player : Fin 4)
    (hproper : hazardOfRoot root player ∈ Set.Ioo (0 : ℝ) 1)
    (hnash : (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root)) :
    sigmaValue (weightOfReward reward) (hazardOfRoot root) player *
      (1 - continueMassExcl (hazardOfRoot root) player) =
        excludedValue (weightOfReward reward) (hazardOfRoot root) player := by
  exact stationary_proper_mixing_balance reward root player hproper hnash

private theorem literal_partner_quit (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    sigmaValue (weightOfReward reward) hazard (partnerOfMissing missing) =
      1 + pairPremium missing * hazard (firstOfMissing missing) -
        2 * hazard (thirdOfMissing missing) - (pairPremium missing + 9) *
          hazard (firstOfMissing missing) * hazard (thirdOfMissing missing) := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, partnerOfMissing, thirdOfMissing, pairPremium,
    pureQuitEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_partner_continue_reward (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    excludedValue (weightOfReward reward) hazard (partnerOfMissing missing) = 0 := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [partnerOfMissing, excludedEndpointRowSum,
    opponentCoalitionMass, weightOfReward, Math.Finset.finFourCoalitionOfRow,
    Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]

private theorem literal_partner_continue_mass (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    continueMassExcl hazard (partnerOfMissing missing) =
      (1 - hazard (firstOfMissing missing)) * (1 - hazard (thirdOfMissing missing)) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, partnerOfMissing, thirdOfMissing,
    continueMassExcl, Fin.prod_univ_succ, huniv, erase_grand_eq, erasedGrand]
  all_goals norm_num +decide [Finset.prod_insert, Finset.prod_singleton, hmissing]
  all_goals ring

private theorem literal_first_quit (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    sigmaValue (weightOfReward reward) hazard (firstOfMissing missing) =
      1 - 2 * hazard (thirdOfMissing missing) -
        ((pairPremium missing + 9) * hazard (thirdOfMissing missing) - pairPremium missing) *
          hazard (partnerOfMissing missing) := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, partnerOfMissing, thirdOfMissing, pairPremium,
    pureQuitEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_first_continue_reward (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    excludedValue (weightOfReward reward) hazard (firstOfMissing missing) =
      favoriteReward missing * hazard (thirdOfMissing missing) *
        (1 - hazard (partnerOfMissing missing)) := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, partnerOfMissing, thirdOfMissing, favoriteReward,
    excludedEndpointRowSum, opponentCoalitionMass, weightOfReward,
    Math.Finset.finFourCoalitionOfRow, Fin.sum_univ_succ, Fin.prod_univ_succ, hmissing]
  all_goals norm_num [reward, Math.FiniteCoalition.binaryCode_finFour]
  all_goals ring

private theorem literal_first_continue_mass (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    continueMassExcl hazard (firstOfMissing missing) =
      (1 - hazard (partnerOfMissing missing)) * (1 - hazard (thirdOfMissing missing)) := by
  have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  fin_cases missing
  all_goals norm_num only at hmissing
  all_goals first
    | change hazard (0 : Fin 4) = 0 at hmissing
    | change hazard (1 : Fin 4) = 0 at hmissing
    | change hazard (2 : Fin 4) = 0 at hmissing
    | change hazard (3 : Fin 4) = 0 at hmissing
  all_goals norm_num [firstOfMissing, partnerOfMissing, thirdOfMissing,
    continueMassExcl, Fin.prod_univ_succ, huniv, erase_grand_eq, erasedGrand]
  all_goals norm_num +decide [Finset.prod_insert, Finset.prod_singleton, hmissing]
  all_goals ring

private theorem literal_endpoint_rows (hazard : Fin 4 → ℝ) (missing : Fin 4)
    (hmissing : hazard missing = 0) :
    let i := firstOfMissing missing
    let k := partnerOfMissing missing
    let j := thirdOfMissing missing
    let a := hazard i
    let c := hazard k
    let x := hazard j
    sigmaValue (weightOfReward reward) hazard k =
        1 + pairPremium missing * a - 2 * x - (pairPremium missing + 9) * a * x ∧
    excludedValue (weightOfReward reward) hazard k = 0 ∧
    continueMassExcl hazard k = (1 - a) * (1 - x) ∧
    sigmaValue (weightOfReward reward) hazard i =
        1 - 2 * x - ((pairPremium missing + 9) * x - pairPremium missing) * c ∧
    excludedValue (weightOfReward reward) hazard i =
        favoriteReward missing * x * (1 - c) ∧
    continueMassExcl hazard i = (1 - c) * (1 - x) := by
  exact ⟨literal_partner_quit hazard missing hmissing,
    literal_partner_continue_reward hazard missing hmissing,
    literal_partner_continue_mass hazard missing hmissing,
    literal_first_quit hazard missing hmissing,
    literal_first_continue_reward hazard missing hmissing,
    literal_first_continue_mass hazard missing hmissing⟩

/-- Every literal proper-three stationary support fails full behavioral
terminal Nash. No externally supplied continuation payoff occurs. -/
theorem not_exact_stationaryNash_of_three_proper_support
    (root : Fin 4 → PMF Bool)
    (hcard : (quittingPositiveHazardSupport root).card = 3)
    (hproper : ∀ player ∈ quittingPositiveHazardSupport root, hazardOfRoot root player < 1) :
    ¬ (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) := by
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
  have hi : firstOfMissing missing ≠ missing := by fin_cases missing <;> decide
  have hk : partnerOfMissing missing ≠ missing := by fin_cases missing <;> decide
  have hj : thirdOfMissing missing ≠ missing := by fin_cases missing <;> decide
  have hai := hactive _ hi
  have hak := hactive _ hk
  have haj := hactive _ hj
  obtain ⟨hQk, hNk, hmk, hQi, hNi, hmi⟩ := literal_endpoint_rows (hazardOfRoot root) missing hz
  have hbk := active_stationary_balance root _ hak hnash
  have hbi := active_stationary_balance root _ hai hnash
  rw [hQk, hNk, hmk] at hbk
  rw [hQi, hNi, hmi] at hbi
  have hden : 0 < 1 -
      (1 - hazardOfRoot root (firstOfMissing missing)) *
        (1 - hazardOfRoot root (thirdOfMissing missing)) := by
    nlinarith [haj.1, mul_pos hai.1 (sub_pos.mpr haj.2)]
  have hzero := (mul_eq_zero.mp hbk).resolve_right (ne_of_gt hden)
  apply scalar_three_support_impossible
    (premium := pairPremium missing) (favorite := favoriteReward missing) hai hak haj
    (by fin_cases missing <;> norm_num [pairPremium])
    (by fin_cases missing <;> norm_num [pairPremium])
    (by fin_cases missing <;> norm_num [favoriteReward])
    (by fin_cases missing <;> norm_num [pairPremium, favoriteReward]) hzero
  have hrewrite :
      ((pairPremium missing + 9) * hazardOfRoot root (thirdOfMissing missing) -
        pairPremium missing) *
        (hazardOfRoot root (firstOfMissing missing) -
          hazardOfRoot root (partnerOfMissing missing)) =
      1 - 2 * hazardOfRoot root (thirdOfMissing missing) -
        ((pairPremium missing + 9) * hazardOfRoot root (thirdOfMissing missing) -
          pairPremium missing) * hazardOfRoot root (partnerOfMissing missing) := by
    nlinarith [hzero]
  rw [hrewrite]
  convert hbi using 1; ring

/-- Relabeling transport delegates to the canonical behavioral pullback; no
affine or full-support stationary exclusion is asserted. -/
theorem not_exact_stationaryNash_reindex_of_three_proper_support
    {κ : Type} [Fintype κ] [DecidableEq κ] (e : Fin 4 ≃ κ)
    (root : Fin 4 → PMF Bool)
    (hcard : (quittingPositiveHazardSupport root).card = 3)
    (hproper : ∀ player ∈ quittingPositiveHazardSupport root, hazardOfRoot root player < 1) :
    ¬ (quittingGame (quittingRewardReindex e reward)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingRewardReindex e reward)) 0
      (quittingStationaryProfile (quittingRewardReindex e reward)
        (quittingRootReindex e root)) := by
  intro hnash
  apply not_exact_stationaryNash_of_three_proper_support root hcard hproper
  have hpull := isεAsymptoticNash_quittingProfilePullback e reward _ hnash
  have hprofile : quittingProfilePullback e reward
      (quittingStationaryProfile (quittingRewardReindex e reward)
        (quittingRootReindex e root)) = quittingStationaryProfile reward root := by
    funext player time history
    change root (e.symm (e player)) = root player
    exact congrArg root (e.symm_apply_apply player)
  rw [hprofile] at hpull
  exact hpull

end GameTheory.CrossedMatchingFixture
