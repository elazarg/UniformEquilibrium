import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremium
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff

/-! # Exact-root lower boundary under nonnegative product-low premiums -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every participant's terminal reward is at least its own singleton
reward. Passive rewards remain unrestricted. -/
def HasNonnegativeOwnQuittingPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ terminal player, player ∈ terminal.val →
    reward (quittingSingletonTerminal player) player ≤ reward terminal player

/-- Nonnegative participant premiums put every pure-Quit endpoint above its
own singleton reward, at every product root and every continuation. -/
theorem quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    reward (quittingSingletonTerminal player) player ≤
      quittingRootQuitPayoff reward tail root player := by
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass]
  calc
    reward (quittingSingletonTerminal player) player =
        ∑ coalition ∈ (Finset.univ.erase player).powerset,
          quittingOpponentCoalitionMass root player coalition *
            reward (quittingSingletonTerminal player) player := by
      rw [← Finset.sum_mul,
        quittingOpponentCoalitionMass_sum_powerset, one_mul]
    _ ≤ ∑ coalition ∈ (Finset.univ.erase player).powerset,
        quittingOpponentCoalitionMass root player coalition *
          quittingStageCoalitionPayoff reward tail
            (insert player coalition) player := by
      apply Finset.sum_le_sum
      intro coalition _
      apply mul_le_mul_of_nonneg_left _
        (quittingOpponentCoalitionMass_nonneg root player coalition)
      simp only [quittingStageCoalitionPayoff, Finset.insert_nonempty, dite_true]
      exact hnonnegative
        ⟨insert player coalition, Finset.insert_nonempty player coalition⟩
        player (Finset.mem_insert_self player coalition)

/-- At every absorbing exact Nash root, all successor coordinates lie above
their singleton levels and at least one active coordinate binds exactly. -/
theorem exactRootSuccessor_mem_singletonLowerBoundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hlow : HasProductLowQuittingPremium reward)
    (tail : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (habsorption : 0 < quittingRootAbsorptionMass root) :
    (∀ player, reward (quittingSingletonTerminal player) player ≤
      quittingRootSuccessorPayoff reward tail root player) ∧
    ∃ player, 0 < (root player true).toReal ∧
      quittingRootSuccessorPayoff reward tail root player =
        reward (quittingSingletonTerminal player) player := by
  have hlower : ∀ player, reward (quittingSingletonTerminal player) player ≤
      quittingRootSuccessorPayoff reward tail root player := by
    intro player
    exact le_trans
      (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
        hnonnegative tail root player)
      (quittingRootQuitPayoff_le_successor_of_isZeroNash
        reward tail root player hnash)
  refine ⟨hlower, ?_⟩
  obtain ⟨player, hactive, hquitUpper⟩ := hlow root habsorption
  have hquitLower :=
    quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
      hnonnegative 0 root player
  have hquitZero : quittingRootQuitPayoff reward 0 root player =
      reward (quittingSingletonTerminal player) player :=
    le_antisymm hquitUpper hquitLower
  have hquitTail : quittingRootQuitPayoff reward tail root player =
      reward (quittingSingletonTerminal player) player := by
    rw [quittingRootQuitPayoff_continuation_invariant reward tail 0 root player]
    exact hquitZero
  have hrootNe : root player true ≠ 0 := by
    intro hzero
    rw [hzero] at hactive
    norm_num at hactive
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail root).mpr hnash
  refine ⟨player, hactive, ?_⟩
  rw [quittingRootSuccessorPayoff_eq_quitPayoff_of_isZeroEndpointNash
    hendpoint player hrootNe, hquitTail]

end GameTheory
