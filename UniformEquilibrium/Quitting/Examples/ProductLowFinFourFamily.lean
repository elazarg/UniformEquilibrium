import UniformEquilibrium.Quitting.Classification.QuittingPremiumReward
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremium
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumBalanceAt
import UniformEquilibrium.Quitting.Classification.Existence.ProductLowPremiumUniformPayoff
import MathUE.Probability

/-! # A Fin4 product-low premium family beyond supportwise balance -/

noncomputable section

namespace GameTheory.ProductLowFinFourFamily

open GameTheory Math.Probability Math.PMFProduct

def premium (scale : Payoff (Fin 4)) (terminal : Finset (Fin 4)) :
    Payoff (Fin 4) := fun player =>
  if player = 0 then
    scale player * ((if 1 ∈ terminal then 1 else 0) -
      if 2 ∈ terminal then 1 else 0)
  else if player = 1 then
    scale player * ((if 2 ∈ terminal then 1 else 0) -
      if 0 ∈ terminal then 1 else 0)
  else if player = 2 then
    scale player * (if 3 ∉ terminal then
      (if 0 ∈ terminal then 1 else 0) -
        if 1 ∈ terminal then 1 else 0
      else 0)
  else
    scale player * (if ({0, 1, 2} : Finset (Fin 4)) ⊆ terminal then 1 else 0)

def reward (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rewardOfOwnPremium singleton (premium scale) passive

@[simp] theorem premium_singleton (scale : Payoff (Fin 4)) (player : Fin 4) :
    premium scale {player} player = 0 := by
  fin_cases player <;> simp +decide [premium]

@[simp] theorem reward_singleton (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (player : Fin 4) :
    reward singleton scale passive (quittingSingletonTerminal player) player =
      singleton player := by
  unfold reward rewardOfOwnPremium
  simp [quittingSingletonTerminal]

theorem reward_sub_singleton (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (player : Fin 4) (hplayer : player ∈ terminal.val) :
    reward singleton scale passive terminal player -
        reward singleton scale passive
          (quittingSingletonTerminal player) player =
      premium scale terminal.val player :=
  rewardOfOwnPremium_sub_singleton singleton (premium scale) passive
    terminal player hplayer (premium_singleton scale player)

def quitPremiumPolynomial (root : Fin 4 → PMF Bool) : Payoff (Fin 4) :=
  fun player =>
    if player = 0 then
      (root 1 true).toReal - (root 2 true).toReal
    else if player = 1 then
      (root 2 true).toReal - (root 0 true).toReal
    else if player = 2 then
      (root 3 false).toReal *
        ((root 0 true).toReal - (root 1 true).toReal)
    else
      (root 0 true).toReal * (root 1 true).toReal *
        (root 2 true).toReal

/-- The four singleton-relative pure-Quit premiums are the literal closed-cube
polynomials from the product-low certificate. -/
theorem quitPremium_formula (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (root : Fin 4 → PMF Bool) (player : Fin 4) :
    quittingRootQuitPayoff (reward singleton scale passive) 0 root player -
        singleton player =
      scale player * quitPremiumPolynomial root player := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_fin4]
  fin_cases player <;>
    simp +decide [reward, rewardOfOwnPremium, premium,
      quitPremiumPolynomial, quittingRootPayoff,
      quittingQuitters, Math.Probability.expect_eq_sum,
      pmfBool_false_toReal] <;>
    ring

/-- Every absorbing product root has an active coordinate with nonpositive
singleton-relative Quit premium. -/
theorem exists_active_quitPayoff_le_singleton
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player)
    (root : Fin 4 → PMF Bool)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootQuitPayoff (reward singleton scale passive) 0 root player ≤
        reward singleton scale passive
          (quittingSingletonTerminal player) player := by
  have hfinish (player : Fin 4) (hactive : 0 < (root player true).toReal)
      (hlow : quitPremiumPolynomial root player ≤ 0) :
      ∃ marked, 0 < (root marked true).toReal ∧
        quittingRootQuitPayoff (reward singleton scale passive) 0 root marked ≤
          reward singleton scale passive
            (quittingSingletonTerminal marked) marked := by
    refine ⟨player, hactive, ?_⟩
    rw [reward_singleton]
    apply sub_nonpos.mp
    rw [quitPremium_formula]
    exact mul_nonpos_of_nonneg_of_nonpos (hscale player).le hlow
  have hmass : quittingStationaryContinueMass root < 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  obtain ⟨active, hactive⟩ :=
    exists_quitProbability_pos_of_continueMass_lt_one hmass
  by_cases h0 : 0 < (root 0 true).toReal
  · by_cases h1 : 0 < (root 1 true).toReal
    · by_cases h2 : 0 < (root 2 true).toReal
      · by_cases h01 : (root 0 true).toReal ≤ (root 1 true).toReal
        · apply hfinish 2 h2
          simp [quitPremiumPolynomial]
          exact mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
            (sub_nonpos.mpr h01)
        · have hsum : quitPremiumPolynomial root 0 +
              quitPremiumPolynomial root 1 < 0 := by
            simp [quitPremiumPolynomial]
            linarith
          by_cases hp0 : quitPremiumPolynomial root 0 < 0
          · exact hfinish 0 h0 hp0.le
          · apply hfinish 1 h1
            linarith
      · have hz2 : (root 2 true).toReal = 0 :=
          le_antisymm (le_of_not_gt h2) ENNReal.toReal_nonneg
        apply hfinish 1 h1
        simp [quitPremiumPolynomial, hz2]
    · have hz1 : (root 1 true).toReal = 0 :=
        le_antisymm (le_of_not_gt h1) ENNReal.toReal_nonneg
      by_cases h2 : 0 < (root 2 true).toReal
      · apply hfinish 0 h0
        simp [quitPremiumPolynomial, hz1]
      · have hz2 : (root 2 true).toReal = 0 :=
          le_antisymm (le_of_not_gt h2) ENNReal.toReal_nonneg
        apply hfinish 0 h0
        simp [quitPremiumPolynomial, hz1, hz2]
  · have hz0 : (root 0 true).toReal = 0 :=
      le_antisymm (le_of_not_gt h0) ENNReal.toReal_nonneg
    by_cases h1 : 0 < (root 1 true).toReal
    · by_cases h2 : 0 < (root 2 true).toReal
      · apply hfinish 2 h2
        simp [quitPremiumPolynomial, hz0]
        exact mul_nonneg ENNReal.toReal_nonneg h1.le
      · have hz2 : (root 2 true).toReal = 0 :=
          le_antisymm (le_of_not_gt h2) ENNReal.toReal_nonneg
        apply hfinish 1 h1
        simp [quitPremiumPolynomial, hz0, hz2]
    · have hz1 : (root 1 true).toReal = 0 :=
        le_antisymm (le_of_not_gt h1) ENNReal.toReal_nonneg
      by_cases h2 : 0 < (root 2 true).toReal
      · apply hfinish 2 h2
        simp [quitPremiumPolynomial, hz0, hz1]
      · have hz2 : (root 2 true).toReal = 0 :=
          le_antisymm (le_of_not_gt h2) ENNReal.toReal_nonneg
        have h3 : 0 < (root 3 true).toReal := by
          fin_cases active <;> simp_all
        apply hfinish 3 h3
        simp [quitPremiumPolynomial, hz0, hz1, hz2]

/-- Positive coordinate scales make every member of the family product-low,
independently of singleton levels and all passive rewards. -/
theorem hasProductLowQuittingPremium
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player) :
    GameTheory.HasProductLowQuittingPremium
      (reward singleton scale passive) := by
  intro root habsorption
  exact exists_active_quitPayoff_le_singleton
    singleton scale passive hscale root habsorption

private theorem coreTriple_hasSupportwiseCertificateAt
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player) :
    HasSupportwiseQuittingPremiumBalanceAt
      (reward singleton scale passive) {0, 1, 2} := by
  let total : ℝ := (scale 0)⁻¹ + (scale 1)⁻¹ + (scale 2)⁻¹
  let weight : Fin 4 → ℝ := fun player =>
    if player ∈ ({0, 1, 2} : Finset (Fin 4)) then (scale player)⁻¹ / total else 0
  have htotal : 0 < total := by
    dsimp only [total]
    exact add_pos (add_pos (inv_pos.mpr (hscale 0))
      (inv_pos.mpr (hscale 1))) (inv_pos.mpr (hscale 2))
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro player
    dsimp only [weight]
    split
    · exact div_nonneg (inv_nonneg.mpr (hscale player).le) htotal.le
    · exact le_rfl
  · intro player hout
    dsimp only [weight]
    rw [if_neg hout]
  · calc
      _ = (scale 0)⁻¹ / total + (scale 1)⁻¹ / total +
          (scale 2)⁻¹ / total := by
        rw [show ({0, 1, 2} : Finset (Fin 4)) =
          insert 0 (insert 1 {2}) by decide]
        simp [weight]
        ring
      _ = 1 := by
        rw [← add_div, ← add_div]
        exact div_self htotal.ne'
  · intro terminal hsubset
    apply le_of_eq
    calc
      _ = ∑ player ∈ terminal,
          weight player * premium scale terminal player := by
        apply Finset.sum_congr rfl
        intro player hplayer
        rw [reward_sub_singleton singleton scale passive terminal player hplayer]
      _ = 0 := by
        fin_cases terminal <;>
          simp_all +decide [weight, premium, total] <;>
          field_simp [(hscale 0).ne', (hscale 1).ne', (hscale 2).ne'] <;>
          ring

/-- Every nonempty proper support has a supportwise certificate; failure of
the family occurs only at the full four-player support. -/
theorem properSupport_hasSupportwiseCertificateAt
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player)
    (active : Finset (Fin 4)) (hactive : active.Nonempty)
    (hproper : active ≠ Finset.univ) :
    HasSupportwiseQuittingPremiumBalanceAt
      (reward singleton scale passive) active := by
  have hpoint (chosen : Fin 4) (hchosen : chosen ∈ active)
      (hlow : ∀ terminal : Finset (Fin 4), terminal ⊆ active →
        chosen ∈ terminal → premium scale terminal chosen ≤ 0) :
      HasSupportwiseQuittingPremiumBalanceAt
        (reward singleton scale passive) active := by
    apply hasSupportwiseQuittingPremiumBalanceAt_of_point _ active chosen hchosen
    intro terminal hsubset hmem
    apply sub_nonpos.mp
    rw [reward_sub_singleton singleton scale passive terminal chosen hmem]
    exact hlow terminal.val hsubset hmem
  by_cases h3 : (3 : Fin 4) ∈ active
  · by_cases h0 : (0 : Fin 4) ∈ active
    · by_cases h1 : (1 : Fin 4) ∈ active
      · have h2 : (2 : Fin 4) ∉ active := by
          intro h2
          apply hproper
          ext player
          fin_cases player <;> simp_all
        apply hpoint 1 h1
        intro terminal hsubset hmem
        have ht2 : (2 : Fin 4) ∉ terminal := fun h => h2 (hsubset h)
        simp [premium, ht2]
        split <;> linarith [hscale 1]
      · apply hpoint 0 h0
        intro terminal hsubset hmem
        have ht1 : (1 : Fin 4) ∉ terminal := fun h => h1 (hsubset h)
        simp [premium, ht1]
        split <;> linarith [hscale 0]
    · by_cases h2 : (2 : Fin 4) ∈ active
      · apply hpoint 2 h2
        intro terminal hsubset hmem
        have ht0 : (0 : Fin 4) ∉ terminal := fun h => h0 (hsubset h)
        by_cases ht3 : (3 : Fin 4) ∈ terminal
        · simp [premium, ht3]
        · by_cases ht1 : (1 : Fin 4) ∈ terminal
          · simp [premium, ht0, ht3, ht1]
            exact (hscale 2).le
          · simp [premium, ht0, ht3, ht1]
      · apply hpoint 3 h3
        intro terminal hsubset hmem
        have ht0 : (0 : Fin 4) ∉ terminal := fun h => h0 (hsubset h)
        simp only [premium, if_neg (by decide : (3 : Fin 4) ≠ 0),
          if_neg (by decide : (3 : Fin 4) ≠ 1),
          if_neg (by decide : (3 : Fin 4) ≠ 2)]
        rw [if_neg (fun hall => ht0 (hall (by simp)))]
        norm_num
  · by_cases h0 : (0 : Fin 4) ∈ active
    · by_cases h1 : (1 : Fin 4) ∈ active
      · by_cases h2 : (2 : Fin 4) ∈ active
        · have hactiveEq : active = ({0, 1, 2} : Finset (Fin 4)) := by
            ext player
            fin_cases player <;> simp_all
          subst active
          exact coreTriple_hasSupportwiseCertificateAt
            singleton scale passive hscale
        · apply hpoint 1 h1
          intro terminal hsubset hmem
          have ht2 : (2 : Fin 4) ∉ terminal := fun h => h2 (hsubset h)
          simp [premium, ht2]
          split <;> linarith [hscale 1]
      · apply hpoint 0 h0
        intro terminal hsubset hmem
        have ht1 : (1 : Fin 4) ∉ terminal := fun h => h1 (hsubset h)
        simp [premium, ht1]
        split <;> linarith [hscale 0]
    · by_cases h1 : (1 : Fin 4) ∈ active
      · by_cases h2 : (2 : Fin 4) ∈ active
        · apply hpoint 2 h2
          intro terminal hsubset hmem
          have ht0 : (0 : Fin 4) ∉ terminal := fun h => h0 (hsubset h)
          have ht3 : (3 : Fin 4) ∉ terminal := fun h => h3 (hsubset h)
          simp [premium, ht0, ht3]
          split <;> linarith [hscale 2]
        · apply hpoint 1 h1
          intro terminal hsubset hmem
          have ht0 : (0 : Fin 4) ∉ terminal := fun h => h0 (hsubset h)
          have ht2 : (2 : Fin 4) ∉ terminal := fun h => h2 (hsubset h)
          simp [premium, ht0, ht2]
      · have h2 : (2 : Fin 4) ∈ active := by
          rcases hactive with ⟨player, hplayer⟩
          fin_cases player <;> simp_all
        apply hpoint 2 h2
        intro terminal hsubset hmem
        have ht0 : (0 : Fin 4) ∉ terminal := fun h => h0 (hsubset h)
        have ht1 : (1 : Fin 4) ∉ terminal := fun h => h1 (hsubset h)
        simp [premium, ht0, ht1]

/-- Every family member fails supportwise balance already on the full
four-player support. -/
theorem not_fullSupportBalanceAt
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player) :
    ¬HasSupportwiseQuittingPremiumBalanceAt
      (reward singleton scale passive) Finset.univ := by
  intro hfull
  obtain ⟨weight, hweight, _hsupport, hsum, hpremium⟩ :=
    hfull
  have h01 := hpremium ⟨{0, 1}, by simp⟩
    (Finset.subset_univ _)
  have h02 := hpremium ⟨{0, 2}, by simp⟩
    (Finset.subset_univ _)
  have h123 := hpremium ⟨{1, 2, 3}, by simp⟩
    (Finset.subset_univ _)
  have hall := hpremium ⟨Finset.univ, Finset.univ_nonempty⟩
    (Finset.subset_univ _)
  rw [Fin.sum_univ_four] at hall
  norm_num +decide [reward, rewardOfOwnPremium, premium,
    quittingSingletonTerminal] at h01 h02 h123 hall
  rw [Fin.sum_univ_four] at hsum
  have hw1 : weight 1 = 0 := by
    nlinarith [hweight 1, hscale 1]
  have hw3 : weight 3 = 0 := by
    nlinarith [hweight 3, hscale 3]
  have hw0 : weight 0 = 0 := by
    nlinarith [hweight 0, hscale 0]
  have hw2 : weight 2 = 0 := by
    nlinarith [hweight 2, hscale 2]
  rw [hw0, hw1, hw2, hw3] at hsum
  norm_num at hsum

/-- Hence every family member fails the global supportwise LP condition. -/
theorem not_supportwiseBalance
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hscale : ∀ player, 0 < scale player) :
    ¬IsSupportwiseBalancedQuittingPremiumTable
      (reward singleton scale passive) := by
  intro hbalanced
  apply not_fullSupportBalanceAt singleton scale passive hscale
  obtain ⟨weight, hweight, hsupport, hsum, hpremium⟩ :=
    hbalanced Finset.univ Finset.univ_nonempty
  exact ⟨weight, hweight, hsupport, hsum, fun terminal hsubset =>
    hpremium terminal.val terminal.property hsubset⟩

/-- Nonnegative singleton levels give the family one literal periodic root
sequence whose every actual suffix is terminal approximate Nash. -/
theorem exists_periodic_allSuffix_terminalNash
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ singleton player)
    (hscale : ∀ player, 0 < scale player)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → Fin 4 → PMF Bool) (period : ℕ), 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      ∀ start,
        (quittingGame (reward singleton scale passive)).IsεAsymptoticNash
          (quittingTerminalPayoff (reward singleton scale passive)) ε
          (quittingRootSequenceProfile
            (reward singleton scale passive) roots start) := by
  apply exists_periodic_allSuffix_terminalNash_of_productLowPremium
  · simpa using hsingleton
  · exact hasProductLowQuittingPremium singleton scale passive hscale
  · exact hε

/-- Every member of the family with nonnegative singleton levels and
positive coordinate scales has a fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff
    (singleton scale : Payoff (Fin 4))
    (passive : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsingleton : ∀ player, 0 ≤ singleton player)
    (hscale : ∀ player, 0 < scale player) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame (reward singleton scale passive)).IsUniformEquilibriumPayoff
        none payoff := by
  apply exists_uniformEquilibriumPayoff_of_productLowPremium
  · simpa using hsingleton
  · exact hasProductLowQuittingPremium singleton scale passive hscale

end GameTheory.ProductLowFinFourFamily
