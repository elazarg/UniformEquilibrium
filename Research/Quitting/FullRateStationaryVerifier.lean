/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.BestResponse
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanDebtMonotonicity

/-!
# The full-rate stationary repair verifier

P0 gate step ("exhaust full-rate finite stationary repairs"): one bundled
exact verifier for an arbitrary stationary product root.  For each player
there are exactly two regimes:

- **contracting opponents** (`quittingStationaryFixedOpponentsContinueMass
  root who < 1`): the landed Snell cap bounds every behavioral deviation,
  so `cap ≤ prescribed payoff` certifies that player; or
- **never-quitting opponents** (mass `= 1`): every opponent's marginal is
  forced to be pure Continue, the deviator faces the all-continue world,
  and `max 0 r_who({who}) ≤ prescribed payoff` certifies that player.

The theorem assembles both regimes into exact terminal Nash.  It subsumes
the owner-solo certification criterion (E39) and the concrete Q125
stationary assembly as special cases, and reduces the full-rate stationary
repair search to finitely many semialgebraic cap inequalities per support
regime.  No exhaustion/search claim, approximate form, or payoff-selection
corollary is made here.
-/


noncomputable section

namespace GameTheory
namespace FullRateStationaryVerifierResearch

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A `[0,1]`-valued finite family with product one is identically one. -/
private theorem factor_eq_one_of_prod_eq_one
    (f : ι → ℝ) (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1)
    (hprod : ∏ i, f i = 1) (i : ι) : f i = 1 := by
  classical
  refine le_antisymm (h1 i) ?_
  have hsplit := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)
  rw [hprod] at hsplit
  have herase1 : ∏ j ∈ Finset.univ.erase i, f j ≤ 1 :=
    Finset.prod_le_one (fun j _ ↦ h0 j) (fun j _ ↦ h1 j)
  have hle : f i * ∏ j ∈ Finset.univ.erase i, f j ≤ f i * 1 :=
    mul_le_mul_of_nonneg_left herase1 (h0 i)
  rw [mul_one] at hle
  linarith

/-- Saturated fixed-opponent mass forces every opponent marginal to be
pure Continue. -/
theorem opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
    (root : ι → PMF Bool) (who : ι)
    (hmass : quittingStationaryFixedOpponentsContinueMass root who = 1) :
    ∀ other, other ≠ who → root other = PMF.pure false := by
  intro other hne
  set updated : ι → PMF Bool := Function.update root who (PMF.pure false)
    with hupdateddef
  have hproduct : ∏ j, (updated j false).toReal = 1 := by
    have hmass' : quittingStationaryContinueMass updated = 1 := hmass
    rw [show quittingStationaryContinueMass updated =
        ((pmfPi updated) (quittingAllContinueAction : ι → Bool)).toReal
        from rfl, pmfPi_apply, ENNReal.toReal_prod] at hmass'
    exact hmass'
  have h0 : ∀ j, 0 ≤ (updated j false).toReal :=
    fun j ↦ ENNReal.toReal_nonneg
  have h1 : ∀ j, (updated j false).toReal ≤ 1 := by
    intro j
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (updated j) false)
  have hfactor := factor_eq_one_of_prod_eq_one _ h0 h1 hproduct other
  have hother : (root other false).toReal = 1 := by
    rw [show updated other = root other from
      Function.update_of_ne hne (PMF.pure false) root] at hfactor
    exact hfactor
  have hsum := pmf_toReal_sum_one (root other)
  rw [Fintype.sum_bool] at hsum
  exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root other)
    (by linarith)

/-- **Full-rate stationary repair verifier.**  A stationary product root is
an exact terminal Nash equilibrium provided each player is certified in its
regime: the Snell cap inequality under contracting opponents, or the
Never/solo cap inequality when the opponents never quit. -/
theorem isεAsymptoticNash_stationary_of_regime_caps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (hcap : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who < 1 →
        quittingStationaryUnilateralCap reward root who ≤
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who)
    (hnever : ∀ who,
      quittingStationaryFixedOpponentsContinueMass root who = 1 →
        max 0 (quittingSoloReward reward who who) ≤
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward root) who) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) := by
  intro who deviation
  rw [add_zero]
  by_cases hmass : quittingStationaryFixedOpponentsContinueMass root who < 1
  · exact (quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward root who deviation hmass).trans (hcap who hmass)
  · have hmassEq : quittingStationaryFixedOpponentsContinueMass root who
        = 1 := by
      have hle : quittingStationaryFixedOpponentsContinueMass root who ≤ 1 :=
        quittingStationaryContinueMass_le_one
          (Function.update root who (PMF.pure false))
      exact le_antisymm hle (not_lt.mp hmass)
    have hpure := opponents_pure_continue_of_fixedOpponentsContinueMass_eq_one
      root who hmassEq
    have hprofiles :
        Function.update (quittingStationaryProfile reward root) who
            deviation =
          Function.update (quittingAlwaysContinueProfile reward) who
            deviation := by
      funext player time history
      by_cases hp : player = who
      · subst player
        simp
      · simp only [Function.update_of_ne hp]
        rw [show quittingStationaryProfile reward root player =
            (quittingGame reward).stationaryBehaviorProfile root player
            from rfl]
        rw [show quittingAlwaysContinueProfile reward player =
            (quittingGame reward).stationaryBehaviorProfile
              (fun _ ↦ PMF.pure false) player from rfl]
        unfold StochasticGame.stationaryBehaviorProfile
        rw [hpure player hp]
        rfl
    rw [hprofiles]
    exact (quittingTerminalPayoff_update_quittingAlwaysContinue_le_max
      reward who deviation).trans (hnever who hmassEq)


end FullRateStationaryVerifierResearch
end GameTheory
