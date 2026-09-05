import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentRecursion
import UniformEquilibrium.Quitting.Boundary.Repair.SureSetOwnerRepair

/-! # Signed two-player finite-menu punishment boundary -/

noncomputable section

namespace GameTheory.TwoPlayerNegativeFiniteMenuBoundary

open GameTheory QuittingSureSetOwnerRepair

def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun _ _ => -1

def sureOpponentRoot : Bool → PMF Bool
  | false => PMF.pure false
  | true => PMF.pure true

private theorem cap_sureOpponentRoot (value : ℝ) :
    quittingFiniteRootWordCap reward [sureOpponentRoot] false value = -1 := by
  rw [quittingFiniteRootWordCap_singleton_eq_fixedOpponents]
  have hquitRoot : Function.update sureOpponentRoot false (PMF.pure true) =
      quittingPureSetRoot (Finset.univ : Finset Bool) := by
    funext player
    fin_cases player <;> simp [sureOpponentRoot, quittingPureSetRoot,
      quittingSetAction]
  have hcontinueRoot : Function.update sureOpponentRoot false (PMF.pure false) =
      quittingPureSetRoot ({true} : Finset Bool) := by
    funext player
    fin_cases player <;> simp [sureOpponentRoot, quittingPureSetRoot,
      quittingSetAction]
  have hquit : quittingStationaryFixedOpponentsQuitValue reward
      sureOpponentRoot false = -1 := by
    unfold quittingStationaryFixedOpponentsQuitValue quittingFixedOpponentsQuitValue
    rw [hquitRoot, quittingRootAbsorbingContribution_pureSetRoot]
    simp [reward, QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty]
  have hcontinue : quittingStationaryFixedOpponentsContinueReward reward
      sureOpponentRoot false = -1 := by
    unfold quittingStationaryFixedOpponentsContinueReward
      quittingFixedOpponentsContinueReward
    rw [hcontinueRoot, quittingRootAbsorbingContribution_pureSetRoot]
    simp [reward, QuittingSureSetOwnerRepair.quittingSetReward_of_nonempty]
  have hmass : quittingStationaryFixedOpponentsContinueMass
      sureOpponentRoot false = 0 := by
    unfold quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueMass quittingStationaryContinueMass
    simp [sureOpponentRoot, quittingAllContinueAction]
  rw [hquit, hcontinue, hmass]
  norm_num

private theorem operator_eq_negOne (value : ℝ) (hvalue : |value| ≤ 1) :
    quittingFiniteMenuPunishmentOperator reward false value = -1 := by
  obtain ⟨root, heq, hlower⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer reward false value
  apply le_antisymm
  · calc
      _ ≤ quittingFiniteRootWordCap reward [sureOpponentRoot] false value :=
        hlower sureOpponentRoot
      _ = -1 := cap_sureOpponentRoot value
  · rw [← heq]
    exact (neg_le_of_abs_le (abs_quittingFiniteRootWordCap_singleton_le
      reward root false (bound := 1) (by simp [reward]) hvalue))

theorem finiteMenuPunishmentValue_eq_negOne {deadline : ℕ}
    (hdeadline : 1 ≤ deadline) :
    quittingFiniteMenuPunishmentValue reward deadline false = -1 := by
  rw [quittingFiniteMenuPunishmentValue_eq_operator_iterate]
  cases deadline with
  | zero => omega
  | succ n =>
      induction n with
      | zero =>
          rw [Function.iterate_succ_apply', Function.iterate_zero_apply,
            operator_eq_negOne 0 (by norm_num)]
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih (by omega),
            operator_eq_negOne (-1) (by norm_num)]

theorem punishmentValue_eq_negOne :
    quittingPunishmentValue reward false = -1 := by
  have htendsto := tendsto_quittingFiniteMenuPunishmentValue reward false
  have heventual : ∀ᶠ deadline in Filter.atTop,
      quittingFiniteMenuPunishmentValue reward deadline false = -1 :=
    Filter.eventually_atTop.2 ⟨1, fun deadline hdeadline =>
      finiteMenuPunishmentValue_eq_negOne hdeadline⟩
  exact tendsto_nhds_unique htendsto
    ((Filter.tendsto_congr' heventual).mpr tendsto_const_nhds)

end GameTheory.TwoPlayerNegativeFiniteMenuBoundary
