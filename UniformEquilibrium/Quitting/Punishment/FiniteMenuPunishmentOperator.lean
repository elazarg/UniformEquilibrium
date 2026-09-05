/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import UniformEquilibrium.Quitting.Stationary.MinMax
import MathUE.MonotoneNonexpansiveIteration

/-! # The scalar Bellman operator for finite-menu punishment

The one-row map is the existing scalar cap fold with a supplied menu suffix
value. In particular, a zero suffix denotes the menu containing only Never,
not the unrestricted all-Never behavioral cap.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Minimum over independent product roots of the one-step response envelope. -/
def quittingFiniteMenuPunishmentOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (value : ℝ) : ℝ :=
  ⨅ root : QuittingRootSimplex ι,
    quittingFiniteRootWordCap reward [quittingRootOfSimplex root] who value

/-- The existing scalar fold is exactly the finite-menu Bellman row. -/
theorem quittingFiniteRootWordCap_singleton_eq_fixedOpponents
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (value : ℝ) :
    quittingFiniteRootWordCap reward [root] who value =
      max (quittingStationaryFixedOpponentsQuitValue reward root who)
        (quittingStationaryFixedOpponentsContinueReward reward root who +
          quittingStationaryFixedOpponentsContinueMass root who * value) := by
  change max (quittingRootQuitPayoff reward 0 root who)
    (quittingRootContinuePayoff reward (Function.update 0 who value) root who) = _
  congr 1
  simpa only [quittingStationaryFixedOpponentsContinueReward,
    quittingStationaryFixedOpponentsContinueMass, Function.update_self] using
    quittingRootContinuePayoff_eq_fixedOpponents reward (fun _ ↦ root) who
      (Function.update 0 who value) 0

theorem continuous_quittingFiniteRootWordCap_singleton_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (value : ℝ) :
    Continuous (fun root : QuittingRootSimplex ι ↦
      quittingFiniteRootWordCap reward [quittingRootOfSimplex root] who value) := by
  change Continuous (fun root : QuittingRootSimplex ι ↦
    max (quittingRootQuitPayoff reward 0 (quittingRootOfSimplex root) who)
      (quittingRootContinuePayoff reward (Function.update 0 who value)
        (quittingRootOfSimplex root) who))
  have hquit : Continuous (fun root : QuittingRootSimplex ι ↦ ((0 : Payoff ι), root)) :=
    continuous_const.prodMk continuous_id
  have hcontinue : Continuous (fun root : QuittingRootSimplex ι ↦
      (Function.update (0 : Payoff ι) who value, root)) :=
    continuous_const.prodMk continuous_id
  apply Continuous.max
  · simpa only [Function.comp_def] using
      (continuous_quittingRootQuitPayoff_simplex reward who).comp hquit
  · simpa only [Function.comp_def] using
      (continuous_quittingRootContinuePayoff_simplex reward who).comp hcontinue

/-- Root minimization is genuinely attained on the compact product simplex. -/
theorem exists_quittingFiniteMenuPunishmentOperator_minimizer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (value : ℝ) :
    ∃ root : ι → PMF Bool,
      quittingFiniteRootWordCap reward [root] who value =
        quittingFiniteMenuPunishmentOperator reward who value ∧
      ∀ other : ι → PMF Bool,
        quittingFiniteMenuPunishmentOperator reward who value ≤
          quittingFiniteRootWordCap reward [other] who value := by
  letI : Nonempty (QuittingRootSimplex ι) :=
    ⟨quittingSimplexOfRoot quittingAllContinueRoot⟩
  obtain ⟨root, _, hminimum⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (QuittingRootSimplex ι)).Nonempty)
    (continuous_quittingFiniteRootWordCap_singleton_simplex reward who value).continuousOn
  have hbound : BddBelow (Set.range fun other : QuittingRootSimplex ι ↦
      quittingFiniteRootWordCap reward [quittingRootOfSimplex other] who value) := by
    refine ⟨quittingFiniteRootWordCap reward [quittingRootOfSimplex root] who value, ?_⟩
    rintro _ ⟨other, rfl⟩
    exact hminimum (Set.mem_univ other)
  have heq : quittingFiniteRootWordCap reward [quittingRootOfSimplex root] who value =
      quittingFiniteMenuPunishmentOperator reward who value := by
    apply le_antisymm
    · exact le_ciInf fun other ↦ hminimum (Set.mem_univ other)
    · exact ciInf_le hbound root
  refine ⟨quittingRootOfSimplex root, heq, ?_⟩
  intro other
  simpa [quittingFiniteMenuPunishmentOperator] using ciInf_le hbound (quittingSimplexOfRoot other)

/-- The infimum inherits the one-sided nonexpansive bound, without any sign
restriction on either continuation value. -/
theorem quittingFiniteMenuPunishmentOperator_sub_le_posPart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (first second : ℝ) :
    quittingFiniteMenuPunishmentOperator reward who first -
      quittingFiniteMenuPunishmentOperator reward who second ≤ max 0 (first - second) := by
  obtain ⟨root, heq, _⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer reward who second
  obtain ⟨_, _, hlower⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer reward who first
  have hdiff := quittingFiniteRootWordCap_sub_le_opponentSurvival_mul_posPart
    reward [root] who first second
  have hmass : quittingLiteralRootStackOpponentSurvival [root] who ≤ 1 := by
    simpa [quittingLiteralRootStackOpponentSurvival] using
      quittingRootOpponentContinueMass_le_one root who
  have hscaled := mul_le_mul_of_nonneg_right hmass (le_max_left 0 (first - second))
  have hfirst := hlower root
  rw [← heq]
  linarith

theorem monotone_quittingFiniteMenuPunishmentOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Monotone (quittingFiniteMenuPunishmentOperator reward who) := by
  intro first second hle
  have h := quittingFiniteMenuPunishmentOperator_sub_le_posPart reward who first second
  rw [max_eq_left (sub_nonpos.mpr hle)] at h
  linarith

theorem lipschitzWith_quittingFiniteMenuPunishmentOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    LipschitzWith 1 (quittingFiniteMenuPunishmentOperator reward who) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro first second
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  have hforward := quittingFiniteMenuPunishmentOperator_sub_le_posPart reward who first second
  have hbackward := quittingFiniteMenuPunishmentOperator_sub_le_posPart reward who second first
  have hforwardBound : max 0 (first - second) ≤ |first - second| :=
    max_le (abs_nonneg _) (le_abs_self _)
  have hbackwardBound : max 0 (second - first) ≤ |first - second| := by
    rw [abs_sub_comm]
    exact max_le (abs_nonneg _) (le_abs_self _)
  exact abs_le.mpr ⟨by linarith, hforward.trans hforwardBound⟩

/-- The response envelope stays in any reward interval containing its suffix
value. This applies to negative values and to the zero-reward boundary. -/
theorem abs_quittingFiniteRootWordCap_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) {bound value : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hvalue : |value| ≤ bound) :
    |quittingFiniteRootWordCap reward [root] who value| ≤ bound := by
  have hbound : 0 ≤ bound := (abs_nonneg value).trans hvalue
  have hzero (player : ι) : |(0 : Payoff ι) player| ≤ bound := by simpa using hbound
  have hupdated (player : ι) : |Function.update (0 : Payoff ι) who value player| ≤ bound := by
    by_cases heq : player = who
    · subst player
      simpa using hvalue
    · simpa [Function.update_of_ne heq] using hbound
  have hquit := abs_quittingRootExpectedPayoff_le_bound reward 0
    (Function.update root who (PMF.pure true)) who hreward hzero
  have hcontinue := abs_quittingRootExpectedPayoff_le_bound reward (Function.update 0 who value)
    (Function.update root who (PMF.pure false)) who hreward hupdated
  change |max (quittingRootQuitPayoff reward 0 root who)
    (quittingRootContinuePayoff reward (Function.update 0 who value) root who)| ≤ bound
  exact abs_le.mpr ⟨(neg_le_of_abs_le hquit).trans (le_max_left _ _),
    max_le (le_of_abs_le hquit) (le_of_abs_le hcontinue)⟩

theorem mapsTo_quittingFiniteMenuPunishmentOperator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    MapsTo (quittingFiniteMenuPunishmentOperator reward who) (Icc (-bound) bound)
      (Icc (-bound) bound) := by
  intro value hvalue
  obtain ⟨root, heq, _⟩ := exists_quittingFiniteMenuPunishmentOperator_minimizer reward who value
  rw [← heq]
  exact abs_le.mp (abs_quittingFiniteRootWordCap_singleton_le reward root who
    hreward (abs_le.mpr hvalue))

/-- The Bellman iterates have a signed fixed-point limit. Identification with
actual finite-menu punishment values requires the separate menu recursion. -/
theorem exists_quittingFiniteMenuPunishmentOperator_iterate_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    ∃ limit ∈ Icc (-(quittingRewardBound reward)) (quittingRewardBound reward),
      Tendsto (fun index : ℕ ↦ (quittingFiniteMenuPunishmentOperator reward who)^[index] 0)
        atTop (nhds limit) ∧ quittingFiniteMenuPunishmentOperator reward who limit = limit :=
  Math.exists_fixedPoint_tendsto_iterate_zero_of_monotone_nonexpansive
    (quittingFiniteMenuPunishmentOperator reward who) (quittingRewardBound reward)
    (quittingRewardBound_nonneg reward) (monotone_quittingFiniteMenuPunishmentOperator reward who)
    (lipschitzWith_quittingFiniteMenuPunishmentOperator reward who)
    (mapsTo_quittingFiniteMenuPunishmentOperator reward who
      (abs_reward_le_quittingRewardBound reward))

/-- Every signed iterate limit bounds the full behavioral punishment value
from above. The negative, noncontracting root case is ruled out by iteration,
not by an unjustified nonnegative-payoff assumption. -/
theorem quittingPunishmentValue_le_operator_iterate_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {limit : ℝ}
    (htendsto : Tendsto (fun index : ℕ ↦
      (quittingFiniteMenuPunishmentOperator reward who)^[index] 0) atTop (nhds limit))
    (hfixed : quittingFiniteMenuPunishmentOperator reward who limit = limit) :
    quittingPunishmentValue reward who ≤ limit := by
  by_contra hnot
  have hgap : limit < quittingPunishmentValue reward who := lt_of_not_ge hnot
  let value := (limit + quittingPunishmentValue reward who) / 2
  have hvalue : limit < value := by dsimp [value]; linarith
  have hoperator := Math.map_le_of_fixedPoint_lt_of_nonexpansive
    (lipschitzWith_quittingFiniteMenuPunishmentOperator reward who) hfixed hvalue
  obtain ⟨root, hroot, _⟩ :=
    exists_quittingFiniteMenuPunishmentOperator_minimizer reward who value
  have hrow : max (quittingStationaryFixedOpponentsQuitValue reward root who)
      (quittingStationaryFixedOpponentsContinueReward reward root who +
        quittingStationaryFixedOpponentsContinueMass root who * value) ≤ value := by
    rw [← quittingFiniteRootWordCap_singleton_eq_fixedOpponents, hroot]
    exact hoperator
  have hquit := (max_le_iff.mp hrow).1
  have hcontinue := (max_le_iff.mp hrow).2
  have hmassLe := quittingStationaryFixedOpponentsContinueMass_le_one root who
  have hcap : quittingStationaryUnilateralCap reward root who ≤ value := by
    rw [quittingStationaryUnilateralCap_eq_max_div]
    apply max_le hquit
    by_cases hmass : quittingStationaryFixedOpponentsContinueMass root who = 1
    · have hzero := quittingStationaryFixedOpponentsContinueReward_eq_zero_of_mass_eq_one
        reward hmass
      have hvalueNonneg : 0 ≤ value := by
        by_contra hnegative
        have hfixValue : quittingFiniteMenuPunishmentOperator reward who value = value := by
          rw [← hroot, quittingFiniteRootWordCap_singleton_eq_fixedOpponents,
            hzero, hmass, one_mul, zero_add, max_eq_right hquit]
        exact Math.not_fixedPoint_lt_zero_above_iterateLimit
          (monotone_quittingFiniteMenuPunishmentOperator reward who) htendsto hvalue
          (lt_of_not_ge hnegative) hfixValue
      simpa [hmass] using hvalueNonneg
    · have hpositive : 0 < 1 - quittingStationaryFixedOpponentsContinueMass root who := by
        have hlt := lt_of_le_of_ne hmassLe hmass
        linarith
      apply (div_le_iff₀ hpositive).mpr
      nlinarith
  have hupper := (quittingPunishmentValue_le_stationaryUnilateralCap reward who root).trans hcap
  dsimp [value] at hupper
  linarith

end GameTheory
