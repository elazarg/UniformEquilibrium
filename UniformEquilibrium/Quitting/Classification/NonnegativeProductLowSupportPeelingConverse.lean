import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowExactRootBoundary
import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumMonotonicity
import UniformEquilibrium.Quitting.Classification.QuittingPremiumSupportPeelingOrder
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumProductLow
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge

/-! # Nonnegative product-low premiums force support peeling -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Under nonnegative own premiums, the product-low condition is equivalent to
weak support peeling. -/
theorem hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward) :
    HasProductLowQuittingPremium reward ↔
      HasWeakQuittingPremiumSupportPeeling reward := by
  constructor
  · intro hlow
    apply (hasWeakQuittingPremiumSupportPeeling_iff reward).mpr
    intro active hactive
    let hazard : ι → ℝ := fun player => if player ∈ active then 1 / 2 else 0
    have hzero : ∀ player, 0 ≤ hazard player := by
      intro player
      simp only [hazard]
      split <;> norm_num
    have hone : ∀ player, hazard player ≤ 1 := by
      intro player
      simp only [hazard]
      split <;> norm_num
    let root := rootOfHazard hazard hzero hone
    have hrates : ∀ player, (root player true).toReal = hazard player := by
      intro player
      change hazardOfRoot root player = hazard player
      rw [show hazardOfRoot root = hazard from
        hazardOfRoot_rootOfHazard hazard hzero hone]
    have habsorption : 0 < quittingRootAbsorptionMass root := by
      let marked := hactive.choose
      have hmarked : marked ∈ active := hactive.choose_spec
      have hrate : 0 < (root marked true).toReal := by
        rw [hrates marked]
        simp [hazard, hmarked]
      have hcontinue :=
        quittingStationaryContinueMass_le_ownContinueProbability root marked
      have hsum := quittingRoot_continueProbability_add_quitProbability root marked
      unfold quittingRootAbsorptionMass
      linarith
    obtain ⟨chosen, hchosenActive, hchosenLow⟩ := hlow root habsorption
    have hchosenMem : chosen ∈ active := by
      rw [hrates chosen] at hchosenActive
      by_contra hnot
      simp [hazard, hnot] at hchosenActive
    refine ⟨chosen, hchosenMem, ?_⟩
    intro terminal hterminal hsubset hchosenTerminal
    by_contra hnot
    have hstrict : reward (quittingSingletonTerminal chosen) chosen <
        reward ⟨terminal, hterminal⟩ chosen := lt_of_not_ge hnot
    have hsumPositive : 0 <
        quittingRootQuitPayoff reward 0 root chosen -
          reward (quittingSingletonTerminal chosen) chosen := by
      rw [quittingRootQuitPremium_eq_sum_opponentCoalitionPremium]
      let coalition := terminal.erase chosen
      have hcoalitionPowerset : coalition ∈
          (Finset.univ.erase chosen).powerset := by
        apply Finset.mem_powerset.mpr
        intro player hplayer
        exact Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hplayer).1, Finset.mem_univ player⟩
      apply Finset.sum_pos'
      · intro other hother
        exact mul_nonneg
          (quittingOpponentCoalitionMass_nonneg root chosen other)
          (sub_nonneg.mpr (hnonnegative
            ⟨insert chosen other, Finset.insert_nonempty chosen other⟩ chosen
            (Finset.mem_insert_self chosen other)))
      · refine ⟨coalition, hcoalitionPowerset, ?_⟩
        have hinsert : insert chosen coalition = terminal :=
          Finset.insert_erase hchosenTerminal
        have hmass : 0 < quittingOpponentCoalitionMass root chosen coalition := by
          unfold quittingOpponentCoalitionMass
          rw [mul_pos_iff]
          left
          constructor
          · apply Finset.prod_pos
            intro player hplayer
            rw [hrates player]
            have hmem : player ∈ active := hsubset (by
              rw [← hinsert]
              exact Finset.mem_insert_of_mem hplayer)
            simp [hazard, hmem]
          · apply Finset.prod_pos
            intro player hplayer
            have hfalse := pmfBool_false_toReal (root player)
            rw [hrates player] at hfalse
            by_cases hmem : player ∈ active
            · simp [hazard, hmem] at hfalse ⊢
              linarith
            · simp [hazard, hmem] at hfalse ⊢
              linarith
        rw [show (⟨insert chosen coalition,
          Finset.insert_nonempty chosen coalition⟩ :
            {S : Finset ι // S.Nonempty}) = ⟨terminal, hterminal⟩ by
              exact Subtype.ext hinsert]
        exact mul_pos hmass (sub_pos.mpr hstrict)
    linarith
  · intro hpeel
    exact hasProductLowQuittingPremium_of_supportwiseBalance reward
      (supportwiseBalance_of_weakQuittingPremiumSupportPeeling reward hpeel)

end GameTheory
