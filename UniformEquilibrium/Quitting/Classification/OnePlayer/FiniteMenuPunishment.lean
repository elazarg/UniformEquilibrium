import UniformEquilibrium.Quitting.Punishment.FiniteMenuPunishmentRecursion
import UniformEquilibrium.Quitting.Classification.OnePlayer.Existence
import UniformEquilibrium.Quitting.Terminal.FiniteMenuEarlyAbsorptionNecessity

/-! # One-player finite-menu punishment boundaries -/

noncomputable section

namespace GameTheory.OnePlayerFiniteMenuBoundary

open GameTheory

/-- The one-player quitting table with singleton payoff `solo`. -/
def reward (solo : ℝ) : {S : Finset PUnit // S.Nonempty} → Payoff PUnit :=
  fun _ _ => solo

theorem finiteRootWordCap_singleton_eq (solo value : ℝ)
    (root : PUnit → PMF Bool) :
    quittingFiniteRootWordCap (reward solo) [root] PUnit.unit value =
      max solo value := by
  rw [quittingFiniteRootWordCap_singleton_eq_fixedOpponents]
  congr 1
  · unfold quittingStationaryFixedOpponentsQuitValue
      quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff
    have hroot : Function.update root PUnit.unit (PMF.pure true) =
        fun _ => PMF.pure true := by
      funext who
      simp [Subsingleton.elim who PUnit.unit]
    rw [hroot, Math.PMFProduct.pmfPi_pure, Math.Probability.expect_pure]
    simp [reward, quittingRootPayoff]
  · unfold quittingStationaryFixedOpponentsContinueReward
      quittingStationaryFixedOpponentsContinueMass
      quittingFixedOpponentsContinueReward quittingFixedOpponentsContinueMass
      quittingRootAbsorbingContribution quittingRootExpectedPayoff
      quittingStationaryContinueMass
    have hroot : Function.update root PUnit.unit (PMF.pure false) =
        fun _ => PMF.pure false := by
      funext who
      simp [Subsingleton.elim who PUnit.unit]
    rw [hroot, Math.PMFProduct.pmfPi_pure, Math.Probability.expect_pure]
    simp [quittingRootPayoff]
    have hall : quittingAllContinueAction = fun _ : PUnit => false := by
      funext who
      rfl
    rw [if_pos hall]
    simp

theorem punishmentOperator_eq (solo value : ℝ) :
    quittingFiniteMenuPunishmentOperator (reward solo) PUnit.unit value =
      max solo value := by
  obtain ⟨root, heq, _⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer
      (reward solo) PUnit.unit value
  rw [← heq, finiteRootWordCap_singleton_eq]

theorem finiteMenuPunishmentValue_eq_max {deadline : ℕ}
    (hdeadline : 1 ≤ deadline) (solo : ℝ) :
    quittingFiniteMenuPunishmentValue (reward solo) deadline PUnit.unit =
      max solo 0 := by
  rw [quittingFiniteMenuPunishmentValue_eq_operator_iterate]
  cases deadline with
  | zero => omega
  | succ n =>
      rw [Function.iterate_succ_apply', punishmentOperator_eq]
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply', punishmentOperator_eq, ih (by omega)]
          simp

theorem punishmentValue_eq_max (solo : ℝ) :
    quittingPunishmentValue (reward solo) PUnit.unit = max solo 0 := by
  have htendsto := tendsto_quittingFiniteMenuPunishmentValue
    (reward solo) PUnit.unit
  have heventual : ∀ᶠ deadline in Filter.atTop,
      quittingFiniteMenuPunishmentValue (reward solo) deadline PUnit.unit = max solo 0 :=
    Filter.eventually_atTop.2 ⟨1, fun deadline hdeadline =>
      finiteMenuPunishmentValue_eq_max hdeadline solo⟩
  exact tendsto_nhds_unique htendsto
    ((Filter.tendsto_congr' heventual).mpr tendsto_const_nhds)

theorem positive_finiteMenuPunishmentValue {deadline : ℕ}
    (hdeadline : 1 ≤ deadline) :
    quittingFiniteMenuPunishmentValue (reward 1) deadline PUnit.unit = 1 := by
  rw [finiteMenuPunishmentValue_eq_max hdeadline]
  norm_num

theorem zero_finiteMenuPunishmentValue (deadline : ℕ) :
    quittingFiniteMenuPunishmentValue (reward 0) deadline PUnit.unit = 0 := by
  cases deadline with
  | zero => exact quittingFiniteMenuPunishmentValue_zero _ _
  | succ n =>
      rw [finiteMenuPunishmentValue_eq_max (by omega)]
      norm_num

theorem positive_has_finiteMenuEarlyAbsorption :
    HasQuittingFiniteMenuEarlyAbsorption (reward 1) := by
  rw [← exists_uniformEquilibriumPayoff_iff_finiteMenuEarlyAbsorption_of_singleton_pos
    (reward 1) PUnit.unit]
  · exact quittingGame_exists_uniformEquilibriumPayoff_onePlayer (reward 1)
  · norm_num [reward, quittingSingletonTerminal]

theorem positive_punishmentValue :
    quittingPunishmentValue (reward 1) PUnit.unit = 1 := by
  rw [punishmentValue_eq_max]
  norm_num

theorem zero_punishmentValue :
    quittingPunishmentValue (reward 0) PUnit.unit = 0 := by
  rw [punishmentValue_eq_max]
  norm_num

end GameTheory.OnePlayerFiniteMenuBoundary
