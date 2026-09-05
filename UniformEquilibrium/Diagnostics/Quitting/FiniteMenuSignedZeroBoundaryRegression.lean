import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentRecursion
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

noncomputable section

namespace GameTheory.FiniteMenuSignedBoundaryRegression

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology

def negativeReward : {S : Finset Bool // S.Nonempty} → Payoff Bool := fun _ _ ↦ -1

theorem negative_oneRowCap (root : Bool → PMF Bool) (value : ℝ) :
    quittingFiniteRootWordCap negativeReward [root] false value =
      max (-1) (-(root true true).toReal + (root true false).toReal * value) := by
  rw [quittingFiniteRootWordCap_singleton_eq_fixedOpponents]
  simp only [quittingStationaryFixedOpponentsQuitValue,
    quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass,
    quittingFixedOpponentsContinueReward, quittingFixedOpponentsQuitValue,
    quittingRootAbsorbingContribution, quittingRootExpectedPayoff]
  rw [Math.PMFProduct.expect_pmfPi_boolFamily,
    Math.PMFProduct.expect_pmfPi_boolFamily]
  simp_rw [Math.Probability.expect_eq_sum, Fintype.sum_bool]
  simp [quittingRootPayoff, negativeReward, quittingQuitters,
    Finset.nonempty_iff_ne_empty]
  rw [quittingFixedOpponentsContinueMass_bool_false,
    Math.PMFProduct.pmfBool_false_toReal]
  ring_nf

def sureOpponentQuitRoot : Bool → PMF Bool := fun _ ↦ PMF.pure true

theorem negative_operator_zero :
    quittingFiniteMenuPunishmentOperator negativeReward false 0 = -1 := by
  obtain ⟨root, hroot, hlower⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer negativeReward false 0
  apply le_antisymm
  · calc
      quittingFiniteMenuPunishmentOperator negativeReward false 0 ≤
          quittingFiniteRootWordCap negativeReward [sureOpponentQuitRoot] false 0 :=
        hlower sureOpponentQuitRoot
      _ = -1 := by simp [negative_oneRowCap, sureOpponentQuitRoot]
  · rw [← hroot, negative_oneRowCap]
    exact le_max_left _ _

theorem negative_operator_neg_one :
    quittingFiniteMenuPunishmentOperator negativeReward false (-1) = -1 := by
  obtain ⟨root, hroot, hlower⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer negativeReward false (-1)
  apply le_antisymm
  · calc
      quittingFiniteMenuPunishmentOperator negativeReward false (-1) ≤
          quittingFiniteRootWordCap negativeReward [sureOpponentQuitRoot] false (-1) :=
        hlower sureOpponentQuitRoot
      _ = -1 := by simp [negative_oneRowCap, sureOpponentQuitRoot]
  · rw [← hroot, negative_oneRowCap]
    exact le_max_left _ _

theorem negative_finiteMenuPunishmentValue_zero :
    quittingFiniteMenuPunishmentValue negativeReward 0 false = 0 :=
  quittingFiniteMenuPunishmentValue_zero negativeReward false

theorem negative_finiteMenuPunishmentValue {deadline : ℕ} (hdeadline : 1 ≤ deadline) :
    quittingFiniteMenuPunishmentValue negativeReward deadline false = -1 := by
  rw [quittingFiniteMenuPunishmentValue_eq_operator_iterate]
  induction deadline with
  | zero => omega
  | succ deadline ih =>
      cases deadline with
      | zero => exact negative_operator_zero
      | succ deadline =>
          rw [Function.iterate_succ_apply', ih (by omega), negative_operator_neg_one]

theorem negative_fullPunishmentValue :
    quittingPunishmentValue negativeReward false = -1 := by
  have hlimit := tendsto_quittingFiniteMenuPunishmentValue negativeReward false
  have heventual : ∀ᶠ deadline in atTop,
      quittingFiniteMenuPunishmentValue negativeReward deadline false = -1 :=
    (eventually_ge_atTop 1).mono fun deadline hdeadline ↦
      negative_finiteMenuPunishmentValue hdeadline
  exact tendsto_nhds_unique hlimit
    ((tendsto_congr' heventual).mpr tendsto_const_nhds)

def zeroReward {I : Type} : {S : Finset I // S.Nonempty} → Payoff I := fun _ _ ↦ 0

section Zero

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

omit [Nonempty I] in
theorem zero_finiteMenuPunishmentValue (deadline : ℕ) (who : I) :
    quittingFiniteMenuPunishmentValue (zeroReward (I := I)) deadline who = 0 := by
  have hbound := abs_quittingFiniteMenuPunishmentValue_le
    (zeroReward (I := I)) who deadline (bound := 0) (by simp [zeroReward])
  simpa using abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

omit [Nonempty I] in
theorem zero_fullPunishmentValue (who : I) :
    quittingPunishmentValue (zeroReward (I := I)) who = 0 := by
  have hlimit := tendsto_quittingFiniteMenuPunishmentValue (zeroReward (I := I)) who
  have hconstant : (fun deadline ↦
      quittingFiniteMenuPunishmentValue (zeroReward (I := I)) deadline who) = fun _ ↦ 0 := by
    funext deadline
    exact zero_finiteMenuPunishmentValue deadline who
  rw [hconstant] at hlimit
  exact tendsto_nhds_unique hlimit tendsto_const_nhds

omit [DecidableEq I] [Nonempty I] in
theorem zero_terminalPayoff
    (profile : (quittingGame (zeroReward (I := I))).BehaviorProfile) (who : I) :
    quittingTerminalPayoff zeroReward profile who = 0 := by
  have hbound := abs_quittingTerminalPayoff_le (zeroReward (I := I)) profile who
    (M := 0) (by simp [zeroReward])
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

theorem zero_terminalExploitability
    (profile : (quittingGame (zeroReward (I := I))).BehaviorProfile) :
    quittingTerminalExploitability zeroReward profile = 0 := by
  unfold quittingTerminalExploitability
  apply le_antisymm
  · apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    have hcap := abs_quittingContinuationBestResponseValue_le
      (zeroReward (I := I)) profile who (M := 0) (by simp [zeroReward])
    have hcapZero : quittingContinuationBestResponseValue zeroReward profile who = 0 :=
      abs_eq_zero.mp (le_antisymm hcap (abs_nonneg _))
    rw [hcapZero, zero_terminalPayoff]
    norm_num
  · exact quittingTerminalExploitability_nonneg zeroReward profile

end Zero

end GameTheory.FiniteMenuSignedBoundaryRegression
