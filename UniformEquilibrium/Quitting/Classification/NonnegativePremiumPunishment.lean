import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowExactRootBoundary
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers

/-! # Unrestricted punishment values under nonnegative own premiums -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Nonnegative own premiums put the unrestricted behavioral punishment value
above the singleton reward. No sign condition on that reward is needed. -/
theorem quittingSingletonReward_le_punishmentValue_of_nonnegativePremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward) (who : ι) :
    reward (quittingSingletonTerminal who) who ≤ quittingPunishmentValue reward who := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
  apply le_ciInf
  intro root
  apply le_trans ?_ (le_max_left _ _)
  have hlower := quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
    hnonnegative (0 : Payoff ι) root who
  rwa [quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward (fun _ => root) who 0 0]
    at hlower

/-- For a nonnegative singleton reward, the NN lower guarantee and all-Never
opponent ceiling identify the full behavioral punishment value exactly. -/
theorem quittingPunishmentValue_eq_singleton_of_nonnegativePremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward) (who : ι)
    (hsingleton : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingPunishmentValue reward who = reward (quittingSingletonTerminal who) who := by
  apply le_antisymm
  · have hupper := quittingPunishmentValue_le_max_solo reward who
    have hrew : QuittingSureSetOwnerRepair.quittingSetReward reward {who} who =
        reward (quittingSingletonTerminal who) who := by
      simp [QuittingSureSetOwnerRepair.quittingSetReward, quittingSingletonTerminal]
    rw [hrew, max_eq_left hsingleton] at hupper
    exact hupper
  · exact quittingSingletonReward_le_punishmentValue_of_nonnegativePremium reward hnonnegative who

end GameTheory
