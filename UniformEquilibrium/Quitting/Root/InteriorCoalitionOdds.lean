import UniformEquilibrium.Quitting.Root.FullCoalitionEndpointIdentities
import MathUE.PMFProduct.InteriorCoalitionOdds

/-! # Interior product-coalition odds

Positive Continue probabilities normalize every full coalition atom by the
same all-Continue mass. No Nash, reward-sign or support restriction is used.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingRootOdds (root : ι → PMF Bool) (player : ι) : ℝ :=
  (root player true).toReal / (root player false).toReal

theorem quittingRootCoalitionMass_eq_continueMass_mul_prod_odds
    (root : ι → PMF Bool) (hcontinue : ∀ player, 0 < (root player false).toReal)
    (coalition : Finset ι) :
    quittingRootCoalitionMass root coalition =
      quittingStationaryContinueMass root * ∏ player ∈ coalition, quittingRootOdds root player := by
  have hidentity := Math.PMFProduct.coalitionMass_eq_continueMass_mul_prod_odds
    (quittingRootQuitRates root) coalition
    (fun player _ => by
      simpa only [quittingRootQuitRates, Math.PMFProduct.pmfBool_false_toReal]
        using ne_of_gt (hcontinue player))
  simpa only [quittingRootCoalitionMass, quittingRootOdds,
    Math.PMFProduct.continueMass, quittingRootQuitRates,
    ← Math.PMFProduct.pmfBool_false_toReal,
    quittingStationaryContinueMass_eq_prod_continueProbability] using hidentity

omit [DecidableEq ι] in
theorem quittingStationaryContinueMass_pos_of_continue_pos
    (root : ι → PMF Bool) (hcontinue : ∀ player, 0 < (root player false).toReal) :
    0 < quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  exact Finset.prod_pos fun player _ => hcontinue player

/-- Multiplication by the player's Continue factor converts its normalized
inserted premium to the full product law with that player absent. -/
theorem quittingContinueProbability_mul_quitPremium_eq_fullCoalitionSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    (root player false).toReal * (quittingRootQuitPayoff reward tail root player -
        reward (quittingSingletonTerminal player) player) =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        (if player ∈ coalition then 0 else
          reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
            reward (quittingSingletonTerminal player) player) := by
  have hsum := quittingOpponentCoalitionMass_sum_powerset root player
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  have hsubtract : (∑ coalition ∈ (Finset.univ.erase player).powerset,
      quittingOpponentCoalitionMass root player coalition *
        quittingStageCoalitionPayoff reward tail (insert player coalition) player) -
      reward (quittingSingletonTerminal player) player =
      ∑ coalition ∈ (Finset.univ.erase player).powerset,
        quittingOpponentCoalitionMass root player coalition *
          (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
            reward (quittingSingletonTerminal player) player) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
    simp [quittingStageCoalitionPayoff]
  rw [hsubtract, Finset.mul_sum]
  have hfilter : (Finset.univ.erase player).powerset =
      (Finset.univ : Finset (Finset ι)).filter (fun coalition => player ∉ coalition) := by
    ext coalition
    simp [Finset.subset_erase]
  rw [hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro coalition _
  by_cases hnot : player ∉ coalition
  · simp only [hnot, not_false_eq_true, ite_true, ite_false]
    rw [← mul_assoc,
      quittingContinueProbability_mul_opponentCoalitionMass root player coalition hnot]
  · simp [hnot]

/-- Full finite Fubini for the inserted-premium coefficients. -/
theorem quittingContinuePremiumSum_eq_fullCoalitionPremiumSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (active : Finset ι) :
    (∑ player ∈ active, (root player false).toReal *
        (quittingRootQuitPayoff reward tail root player -
          reward (quittingSingletonTerminal player) player)) =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        ∑ player ∈ active \ coalition,
          (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
            reward (quittingSingletonTerminal player) player) := by
  simp_rw [quittingContinueProbability_mul_quitPremium_eq_fullCoalitionSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coalition _
  have hfilter : active.filter (fun player => player ∉ coalition) = active \ coalition := by
    ext player
    simp
  rw [← hfilter, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro player _
  by_cases hmember : player ∈ coalition <;> simp [hmember]

/-- With actual support contained in the carrier, the empty and full-carrier
premium coefficients vanish and all outside atoms have zero mass. -/
theorem quittingContinuePremiumSum_eq_properSubsetPremiumSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (active : Finset ι)
    (hsupport : quittingPositiveHazardSupport root ⊆ active) :
    (∑ player ∈ active, (root player false).toReal *
        (quittingRootQuitPayoff reward tail root player -
          reward (quittingSingletonTerminal player) player)) =
      ∑ coalition ∈ (active.powerset.erase ∅).erase active,
        quittingRootCoalitionMass root coalition *
          ∑ player ∈ active \ coalition,
            (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
              reward (quittingSingletonTerminal player) player) := by
  rw [quittingContinuePremiumSum_eq_fullCoalitionPremiumSum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro coalition _ houtside
  by_cases hempty : coalition = ∅
  · subst coalition
    simp [quittingSingletonTerminal]
  by_cases hsubset : coalition ⊆ active
  · have heq : coalition = active := by
      by_contra hne
      exact houtside (by simp_all)
    subst coalition
    simp
  · rw [quittingRootCoalitionMass_eq_zero_of_not_subset_supportContainer
      root active coalition hsupport hsubset, zero_mul]

end GameTheory
