import MathUE.PMFProduct.Update
import UniformEquilibrium.Quitting.Classification.AbnormalPlayers
import UniformEquilibrium.Quitting.Punishment.ContinueFloor
import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityRewardRobustness

/-! # Literal normal table with a negative singleton

Every nonempty coalition pays the same vector `(1,-1,0,0)`.
Normality does not supply the singleton sign premise of the reflection packet.
-/

noncomputable section

namespace GameTheory.ConstantSignedNormalTable

open _root_.Math.Probability _root_.Math.ProbabilityMassFunction Math.PMFProduct
open QuittingSureSetOwnerRepair
open scoped Matrix

def target : Payoff (Fin 4) := ![1, -1, 0, 0]

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun _ => target

theorem singleton_vector :
    (fun who => reward (quittingSingletonTerminal who) who) = target := rfl

theorem rewards_bounded (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) : |reward terminal who| ≤ 1 := by
  fin_cases who <;> norm_num [reward, target]

theorem quit_value_eq (root : Fin 4 → PMF Bool) (who : Fin 4) :
    quittingStationaryFixedOpponentsQuitValue reward root who = target who := by
  change expect (pmfPi (Function.update root who (PMF.pure true)))
    (fun action => quittingRootPayoff reward (0 : Payoff (Fin 4)) action who) = _
  rw [← expect_const (pmfPi (Function.update root who (PMF.pure true))) (target who)]
  apply expect_congr_of_ne_zero
  intro action hmass
  have hwho := eq_of_mem_support_pmfPi_update_pure root who true
    ((PMF.mem_support_iff _ _).mpr hmass)
  have hquit : (quittingQuitters action).Nonempty :=
    (quittingQuitters_nonempty_iff action).mpr ⟨who, hwho⟩
  rw [quittingRootPayoff, dite_eq_left hquit]
  rfl

theorem punishment_eq (who : Fin 4) : quittingPunishmentValue reward who = target who := by
  apply le_antisymm
  · obtain ⟨other, hother⟩ := exists_ne who
    have hcap := quittingPunishmentValue_le_pureRowCap reward who {other}
    rw [Finset.erase_eq_of_notMem (by simp [Ne.symm hother]),
      quittingSetReward_of_nonempty reward (Finset.insert_nonempty _ _),
      quittingSetReward_of_nonempty reward (Finset.singleton_nonempty _)] at hcap
    simpa only [reward, max_self] using hcap
  · rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
    apply le_ciInf
    intro root
    rw [quittingStationaryUnilateralCap_eq_max_div, quit_value_eq]
    exact le_max_left _ _

theorem punishment_vector : (fun who => quittingPunishmentValue reward who) = target :=
  funext punishment_eq

theorem all_normal : ∀ who, IsQuittingNormalPlayer reward who := by
  intro who
  change quittingPunishmentValue reward who ≤ target who
  exact (punishment_eq who).le

theorem positive_and_negative_singletons :
    0 < reward (quittingSingletonTerminal 0) 0 ∧
      reward (quittingSingletonTerminal 1) 1 < 0 := by
  norm_num [reward, target]

theorem allNever_payoff_zero (who : Fin 4) :
    quittingTerminalPayoff reward (quittingAlwaysContinueProfile reward) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue reward who

theorem positive_scaling_preserves_negative_singleton {scale : ℝ} (hscale : 0 < scale) :
    scaleQuittingReward scale reward (quittingSingletonTerminal 1) 1 < 0 := by
  simpa [scaleQuittingReward, reward, target] using neg_lt_zero.mpr hscale

end GameTheory.ConstantSignedNormalTable
