import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches

/-! # Quitting rewards from singleton levels and participant premiums -/

namespace GameTheory

/-- Build a quitting reward table from prescribed singleton levels and own
premiums, while leaving every passive coordinate supplied by the caller. -/
def rewardOfOwnPremium {ι : Type} [DecidableEq ι]
    (singleton : Payoff ι) (premium : Finset ι → Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (player : ι) : ℝ :=
  if player ∈ terminal.val then singleton player + premium terminal.val player
  else passive terminal player

theorem rewardOfOwnPremium_sub_singleton {ι : Type} [DecidableEq ι]
    (singleton : Payoff ι) (premium : Finset ι → Payoff ι)
    (passive : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty})
    (player : ι) (hplayer : player ∈ terminal.val)
    (hsingleton : premium {player} player = 0) :
    rewardOfOwnPremium singleton premium passive terminal player -
        rewardOfOwnPremium singleton premium passive
          (quittingSingletonTerminal player) player =
      premium terminal.val player := by
  unfold rewardOfOwnPremium
  rw [if_pos hplayer]
  have hself : player ∈ (quittingSingletonTerminal player).val := by
    change player ∈ ({player} : Finset ι)
    simp
  rw [if_pos hself]
  change singleton player + premium terminal.val player -
      (singleton player + premium {player} player) = premium terminal.val player
  rw [hsingleton]
  ring

end GameTheory
