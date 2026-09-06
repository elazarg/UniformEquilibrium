import UniformEquilibrium.Diagnostics.Quitting.FinFourFullBoxExactPredecessorCapacity
import UniformEquilibrium.Quitting.Root.RenewedLiteralExactWordSequence

/-! # Linear capacity recharge along actual renewed Fin4 exact prefixes

A supplied source-coherent sequence of actual cap responses and exact words
must restore full-box capacity at least linearly in a game with no uniform
payoff. Horizontal cap responses are not claimed to be predecessor edges.
-/

noncomputable section

namespace GameTheory

/-- In a Fin4 game without a uniform-equilibrium payoff, the actual supplied
renewed exact words force linear recharge of canonical full-box capacity. -/
theorem finFour_renewedLiteralExactWord_capacityRecharge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (sequence : QuittingRenewedLiteralExactWordSequence reward)
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    (horizon : ℕ) :
    (horizon : ℝ) * sequence.minimumAbsorption -
        (quittingPunishmentFloorBoxChargedRelation reward).budget ≤
      ∑ phase ∈ Finset.range horizon,
        sequence.toRenewedPathSequence.potentialRecharge
          (quittingPunishmentFloorBoxChargedRelation reward).value phase := by
  exact finFour_card_mul_minimumCharge_sub_fullBoxBudget_le_sum_valueRecharge
    reward hnot sequence.toRenewedPathSequence horizon

end GameTheory

