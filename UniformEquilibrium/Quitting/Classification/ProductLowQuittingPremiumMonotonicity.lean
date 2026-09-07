import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-! # Downward closure of product-low quitting premiums -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every participant's singleton-relative premium in `lower` is no larger
than the corresponding premium in `upper`. Passive rewards are unrestricted. -/
def HasNoLargerOwnQuittingPremium
    (lower upper : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (terminal : {S : Finset ι // S.Nonempty}) player,
    player ∈ terminal.val →
    lower terminal player -
        lower (quittingSingletonTerminal player) player ≤
      upper terminal player -
        upper (quittingSingletonTerminal player) player

/-- A pure-Quit premium is the opponent-coalition average of the participant
premiums of the coalitions obtained by inserting the quitting player. -/
theorem quittingRootQuitPremium_eq_sum_opponentCoalitionPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (player : ι) :
    quittingRootQuitPayoff reward 0 root player -
        reward (quittingSingletonTerminal player) player =
      ∑ coalition ∈ (Finset.univ.erase player).powerset,
        quittingOpponentCoalitionMass root player coalition *
          (reward ⟨insert player coalition,
              Finset.insert_nonempty player coalition⟩ player -
            reward (quittingSingletonTerminal player) player) := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
  have hmass := quittingOpponentCoalitionMass_sum_powerset root player
  calc
    (∑ coalition ∈ (Finset.univ.erase player).powerset,
          quittingOpponentCoalitionMass root player coalition *
            reward ⟨insert player coalition,
              Finset.insert_nonempty player coalition⟩ player) -
        reward (quittingSingletonTerminal player) player =
      (∑ coalition ∈ (Finset.univ.erase player).powerset,
          quittingOpponentCoalitionMass root player coalition *
            reward ⟨insert player coalition,
              Finset.insert_nonempty player coalition⟩ player) -
        (∑ coalition ∈ (Finset.univ.erase player).powerset,
          quittingOpponentCoalitionMass root player coalition) *
            reward (quittingSingletonTerminal player) player := by
              rw [hmass, one_mul]
    _ = _ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro coalition _
      ring

/-- Pointwise downward movement of participant premiums moves every pure-Quit
premium downward at every independent product root. -/
theorem quittingRootQuitPremium_le_of_noLargerOwnPremium
    {lower upper : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hle : HasNoLargerOwnQuittingPremium lower upper)
    (root : ι → PMF Bool) (player : ι) :
    quittingRootQuitPayoff lower 0 root player -
        lower (quittingSingletonTerminal player) player ≤
      quittingRootQuitPayoff upper 0 root player -
        upper (quittingSingletonTerminal player) player := by
  rw [quittingRootQuitPremium_eq_sum_opponentCoalitionPremium,
    quittingRootQuitPremium_eq_sum_opponentCoalitionPremium]
  apply Finset.sum_le_sum
  intro coalition _
  apply mul_le_mul_of_nonneg_left
  · exact hle ⟨insert player coalition,
      Finset.insert_nonempty player coalition⟩ player
      (Finset.mem_insert_self player coalition)
  · exact quittingOpponentCoalitionMass_nonneg root player coalition

/-- The product-low premium class is downward closed in every participant
premium, without any condition on passive rewards. -/
theorem hasProductLowQuittingPremium_of_noLargerOwnPremium
    {lower upper : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hle : HasNoLargerOwnQuittingPremium lower upper)
    (hupper : HasProductLowQuittingPremium upper) :
    HasProductLowQuittingPremium lower := by
  intro root habsorption
  obtain ⟨player, hactive, hlow⟩ := hupper root habsorption
  refine ⟨player, hactive, ?_⟩
  have hpremium :=
    quittingRootQuitPremium_le_of_noLargerOwnPremium hle root player
  linarith

end GameTheory
