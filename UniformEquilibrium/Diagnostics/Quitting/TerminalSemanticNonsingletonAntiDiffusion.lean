/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.NonsingletonConcentration
import MathUE.Probability.SquareRootCoalitionClock
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit
import UniformEquilibrium.Quitting.Boundary.Exceptional.Hazard
import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# Nonsingleton terminal-coalition anti-diffusion

Independent stopping clocks cannot spread a fixed nonsingleton terminal
coalition arbitrarily thinly.  This module connects actual behavioral
stopping laws to chronological stage atoms, proves the sharp exponent
`k / (k - 1)` on finite windows and the full time axis, and rules out a
nonsingleton label in a reprojection diffuse-window packet.

The statements retain arbitrary history-dependent behavioral strategies and
Never mass.  They use only independence of the players' current
randomizations at the unique live history.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability Math.PMFProduct
open scoped Topology BigOperators

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

omit [DecidableEq iota] in
theorem quittingLiveMass_eq_prod_behaviorHazardSurvival
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingLiveMass reward profile time =
      ∏ who, quittingHazardSurvival
        (quittingBehaviorLiveHazard reward (profile who)) time := by
  induction time with
  | zero => simp
  | succ time ih =>
      rw [quittingLiveMass_succ, ih, quittingJointContinueMass_eq_product]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro who _
      rw [quittingHazardSurvival_succ]
      rfl

theorem quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal =
      (∏ who ∈ terminal.val,
        (quittingBehaviorStoppingLaw reward (profile who) (some time)).toReal) *
      ∏ who ∈ terminal.valᶜ,
        quittingHazardSurvival
          (quittingBehaviorLiveHazard reward (profile who)) (time + 1) := by
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_eq_prod_behaviorHazardSurvival]
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
  rw [← Finset.prod_mul_prod_compl terminal.val (fun who =>
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile who)) time)]
  rw [mul_assoc]
  rw [mul_left_comm (∏ who ∈ terminal.valᶜ,
    quittingHazardSurvival
      (quittingBehaviorLiveHazard reward (profile who)) time)]
  rw [← mul_assoc]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro who hwho
    rw [quittingBehaviorStoppingLaw_some_toReal,
      quittingHazardStopMass_eq_survival_mul_stop]
    rfl
  · apply Finset.prod_congr rfl
    intro who hwho
    rw [quittingHazardSurvival_succ]
    have hcontinue := quittingRoot_continueProbability_add_quitProbability
      (quittingProfileLiveRoot reward profile time) who
    change _ * (1 -
      (quittingProfileLiveRoot reward profile time who true).toReal) =
        _ * (quittingProfileLiveRoot reward profile time who false).toReal
    congr 1
    linarith

theorem quittingStageCoalitionMass_le_stoppingLawProduct
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      ∏ who ∈ terminal.val,
        (quittingBehaviorStoppingLaw reward (profile who) (some time)).toReal := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply mul_le_of_le_one_right
  · exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  · apply Finset.prod_le_one
    · exact fun who _ =>
        quittingHazardSurvival_nonneg
          (quittingBehaviorLiveHazard reward (profile who)) (time + 1)
    · exact fun who _ =>
        quittingHazardSurvival_le_one
          (quittingBehaviorLiveHazard reward (profile who)) (time + 1)

omit [DecidableEq iota] in
theorem sum_quittingBehaviorStoppingLaw_some_toReal_le_one
    {who : iota} (strategy : (quittingGame reward).BehaviorStrategy who)
    (dates : Finset ℕ) :
    ∑ time ∈ dates,
      (quittingBehaviorStoppingLaw reward strategy (some time)).toReal ≤ 1 := by
  let hazard := quittingBehaviorLiveHazard reward strategy
  have hsummable : Summable (quittingHazardStopMass hazard) :=
    (hasSum_quittingHazardStopMass hazard).summable
  calc
    (∑ time ∈ dates,
        (quittingBehaviorStoppingLaw reward strategy (some time)).toReal) =
        ∑ time ∈ dates, quittingHazardStopMass hazard time := by
      apply Finset.sum_congr rfl
      intro time _
      rw [quittingBehaviorStoppingLaw_some_toReal]
    _ ≤ ∑' time, quittingHazardStopMass hazard time :=
      hsummable.sum_le_tsum dates
        (fun time _ => quittingHazardStopMass_nonneg hazard time)
    _ = 1 - quittingHazardNeverMass hazard :=
      (hasSum_quittingHazardStopMass hazard).tsum_eq
    _ ≤ 1 := by
      linarith [quittingHazardNeverMass_nonneg hazard]

theorem sum_rpow_inv_card_quittingStageCoalitionMass_le_one
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (dates : Finset ℕ) :
    ∑ time ∈ dates,
      quittingStageCoalitionMass reward profile time terminal ^
        (1 / (terminal.val.card : ℝ)) ≤ 1 := by
  let k : ℝ := terminal.val.card
  have hkpos : 0 < k := by
    dsimp [k]
    exact_mod_cast terminal.property.card_pos
  have hkinv : 0 ≤ 1 / k := by positivity
  have hpoint : ∀ time,
      quittingStageCoalitionMass reward profile time terminal ^ (1 / k) ≤
        ∑ who ∈ terminal.val, (1 / k) *
          (quittingBehaviorStoppingLaw reward
            (profile who) (some time)).toReal := by
    intro time
    let p : iota → ℝ := fun who =>
      (quittingBehaviorStoppingLaw reward (profile who) (some time)).toReal
    have hstage := quittingStageCoalitionMass_le_stoppingLawProduct
      (reward := reward) profile time terminal
    have hpow : quittingStageCoalitionMass reward profile time terminal ^
        (1 / k) ≤ (∏ who ∈ terminal.val, p who) ^ (1 / k) :=
      Real.rpow_le_rpow
        (quittingStageCoalitionMass_nonneg reward profile time terminal)
        hstage hkinv
    have hweight : ∑ who ∈ terminal.val, (1 / k) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (terminal.val.card : ℝ) * (1 / k) = 1
      rw [show (terminal.val.card : ℝ) = k by rfl]
      field_simp
    have hamgm := Real.geom_mean_le_arith_mean_weighted terminal.val
      (fun _ => 1 / k) p (fun _ _ => hkinv) hweight
      (fun _ _ => ENNReal.toReal_nonneg)
    calc
      quittingStageCoalitionMass reward profile time terminal ^ (1 / k) ≤
          (∏ who ∈ terminal.val, p who) ^ (1 / k) := hpow
      _ = ∏ who ∈ terminal.val, p who ^ (1 / k) := by
        rw [Real.finsetProd_rpow terminal.val p
          (fun _ _ => ENNReal.toReal_nonneg)]
      _ ≤ ∑ who ∈ terminal.val, (1 / k) * p who := hamgm
  calc
    (∑ time ∈ dates,
        quittingStageCoalitionMass reward profile time terminal ^
          (1 / (terminal.val.card : ℝ))) =
        ∑ time ∈ dates,
          quittingStageCoalitionMass reward profile time terminal ^
            (1 / k) := rfl
    _ ≤ ∑ time ∈ dates, ∑ who ∈ terminal.val,
        (1 / k) *
          (quittingBehaviorStoppingLaw reward
            (profile who) (some time)).toReal := by
      exact Finset.sum_le_sum fun time _ => hpoint time
    _ = ∑ who ∈ terminal.val, (1 / k) *
        (∑ time ∈ dates,
          (quittingBehaviorStoppingLaw reward
            (profile who) (some time)).toReal) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro who _
      rw [Finset.mul_sum]
    _ ≤ ∑ who ∈ terminal.val, (1 / k) * 1 := by
      apply Finset.sum_le_sum
      intro who _
      exact mul_le_mul_of_nonneg_left
        (sum_quittingBehaviorStoppingLaw_some_toReal_le_one
          (reward := reward) (profile who) dates) hkinv
    _ = 1 := by
      simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
      change (terminal.val.card : ℝ) * (1 / k) = 1
      rw [show (terminal.val.card : ℝ) = k by rfl]
      field_simp

theorem sum_quittingStageCoalitionMass_le_one
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (dates : Finset ℕ) :
    ∑ time ∈ dates,
      quittingStageCoalitionMass reward profile time terminal ≤ 1 := by
  have hsummable :=
    (hasSum_quittingStageCoalitionMass reward profile terminal).summable
  have hfinite : (∑ time ∈ dates,
      quittingStageCoalitionMass reward profile time terminal) ≤
      ∑' time, quittingStageCoalitionMass reward profile time terminal :=
    hsummable.sum_le_tsum dates fun time _ =>
      quittingStageCoalitionMass_nonneg reward profile time terminal
  rw [tsum_quittingStageCoalitionMass] at hfinite
  have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hcoordinate : quittingTerminalOutcomeMass reward profile (some terminal) ≤
      ∑ outcome, quittingTerminalOutcomeMass reward profile outcome := by
    exact Finset.single_le_sum
      (fun outcome _ => hsimplex.1 outcome) (Finset.mem_univ (some terminal))
  rw [hsimplex.2] at hcoordinate
  exact hfinite.trans hcoordinate

theorem exists_quittingStageCoalitionMass_ge_finite_sum_rpow
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (dates : Finset ℕ) (hdates : dates.Nonempty)
    (hcard : 2 ≤ terminal.val.card) :
    ∃ peak ∈ dates,
      (∑ time ∈ dates,
        quittingStageCoalitionMass reward profile time terminal) ^
          ((terminal.val.card : ℝ) /
            ((terminal.val.card : ℝ) - 1)) ≤
        quittingStageCoalitionMass reward profile peak terminal := by
  apply finite_exists_rpow_ratio_le_of_sum_root_le_one dates
    (fun time => quittingStageCoalitionMass reward profile time terminal)
    (terminal.val.card : ℝ) hdates
  · exact_mod_cast hcard
  · exact fun time _ =>
      quittingStageCoalitionMass_nonneg reward profile time terminal
  · exact sum_rpow_inv_card_quittingStageCoalitionMass_le_one
      profile terminal dates

theorem exists_quittingStageCoalitionMass_ge_finite_sum_sq
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (dates : Finset ℕ) (hdates : dates.Nonempty)
    (hcard : 2 ≤ terminal.val.card) :
    ∃ peak ∈ dates,
      (∑ time ∈ dates,
        quittingStageCoalitionMass reward profile time terminal) ^ 2 ≤
        quittingStageCoalitionMass reward profile peak terminal := by
  obtain ⟨peak, hpeak, hsharp⟩ :=
    exists_quittingStageCoalitionMass_ge_finite_sum_rpow
      profile terminal dates hdates hcard
  refine ⟨peak, hpeak, ?_⟩
  let total := ∑ time ∈ dates,
    quittingStageCoalitionMass reward profile time terminal
  let k : ℝ := terminal.val.card
  have htotal0 : 0 ≤ total := Finset.sum_nonneg fun time _ =>
    quittingStageCoalitionMass_nonneg reward profile time terminal
  have htotal1 : total ≤ 1 :=
    sum_quittingStageCoalitionMass_le_one profile terminal dates
  have hk2 : 2 ≤ k := by
    dsimp [k]
    exact_mod_cast hcard
  have hk1 : 0 < k - 1 := by linarith
  have hexp0 : 0 ≤ k / (k - 1) := by positivity
  have hexp2 : k / (k - 1) ≤ 2 := by
    apply (div_le_iff₀ hk1).2
    linarith
  have hsquare : total ^ (2 : ℝ) ≤ total ^ (k / (k - 1)) :=
    Real.rpow_le_rpow_of_exponent_ge' htotal0 htotal1 hexp0 hexp2
  calc
    total ^ 2 = total ^ (2 : ℝ) := (Real.rpow_natCast total 2).symm
    _ ≤ total ^ (k / (k - 1)) := hsquare
    _ ≤ quittingStageCoalitionMass reward profile peak terminal := hsharp

theorem exists_maximal_quittingStageCoalitionMass_of_positive_total
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (hcard : 2 ≤ terminal.val.card)
    (hpositive : 0 < ∑' time,
      quittingStageCoalitionMass reward profile time terminal) :
    ∃ peak,
      (∀ time, quittingStageCoalitionMass reward profile time terminal ≤
        quittingStageCoalitionMass reward profile peak terminal) ∧
      (∑' time, quittingStageCoalitionMass reward profile time terminal) ^
          ((terminal.val.card : ℝ) /
            ((terminal.val.card : ℝ) - 1)) ≤
        quittingStageCoalitionMass reward profile peak terminal := by
  let mass : ℕ → ℝ := fun time =>
    quittingStageCoalitionMass reward profile time terminal
  have hsummable : Summable mass :=
    (hasSum_quittingStageCoalitionMass reward profile terminal).summable
  have htendsto : Tendsto mass atTop (nhds 0) := hsummable.tendsto_atTop_zero
  have hexists : ∃ time, 0 < mass time := by
    by_contra hnone
    push Not at hnone
    have hzero : mass = 0 := by
      funext time
      exact le_antisymm (hnone time)
        (quittingStageCoalitionMass_nonneg reward profile time terminal)
    change 0 < ∑' time, mass time at hpositive
    rw [hzero] at hpositive
    simp at hpositive
  obtain ⟨peak, hmax⟩ :=
    Math.Probability.exists_maximal_of_tendsto_zero_of_exists_pos
      mass htendsto hexists
  refine ⟨peak, hmax, ?_⟩
  let k : ℝ := terminal.val.card
  have hk2 : 2 ≤ k := by
    dsimp [k]
    exact_mod_cast hcard
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_two hk2
  have hk1 : 0 < k - 1 := by linarith
  have hexp : 0 < k / (k - 1) := div_pos hk0 hk1
  have hpartial : ∀ cutoff,
      (∑ time ∈ Finset.range cutoff, mass time) ^ (k / (k - 1)) ≤
        mass peak := by
    intro cutoff
    cases cutoff with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        rw [Real.zero_rpow hexp.ne']
        exact quittingStageCoalitionMass_nonneg reward profile peak terminal
    | succ cutoff =>
        obtain ⟨date, _hdate, hdate⟩ :=
          exists_quittingStageCoalitionMass_ge_finite_sum_rpow
            profile terminal (Finset.range (cutoff + 1))
              ⟨0, Finset.mem_range.mpr (Nat.succ_pos cutoff)⟩ hcard
        exact hdate.trans (hmax date)
  have hsum : Tendsto
      (fun cutoff => ∑ time ∈ Finset.range cutoff, mass time)
      atTop (nhds (∑' time, mass time)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hpow : Tendsto
      (fun cutoff =>
        (∑ time ∈ Finset.range cutoff, mass time) ^ (k / (k - 1)))
      atTop (nhds ((∑' time, mass time) ^ (k / (k - 1)))) := by
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hexp.le)).tendsto.comp hsum
  exact le_of_tendsto hpow (Filter.Eventually.of_forall hpartial)

theorem exists_quittingStageCoalitionMass_ge_tsum_rpow
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (hcard : 2 ≤ terminal.val.card) :
    ∃ peak,
      (∑' time, quittingStageCoalitionMass reward profile time terminal) ^
          ((terminal.val.card : ℝ) /
            ((terminal.val.card : ℝ) - 1)) ≤
        quittingStageCoalitionMass reward profile peak terminal := by
  by_cases hpositive : 0 < ∑' time,
      quittingStageCoalitionMass reward profile time terminal
  · obtain ⟨peak, _hmax, hlower⟩ :=
      exists_maximal_quittingStageCoalitionMass_of_positive_total
        profile terminal hcard hpositive
    exact ⟨peak, hlower⟩
  · refine ⟨0, ?_⟩
    have htotal0 : 0 ≤ ∑' time,
        quittingStageCoalitionMass reward profile time terminal :=
      tsum_nonneg fun time =>
        quittingStageCoalitionMass_nonneg reward profile time terminal
    have htotal : (∑' time,
        quittingStageCoalitionMass reward profile time terminal) = 0 :=
      le_antisymm (le_of_not_gt hpositive) htotal0
    rw [htotal]
    have hexp : 0 < (terminal.val.card : ℝ) /
        ((terminal.val.card : ℝ) - 1) := by
      have hk2 : (2 : ℝ) ≤ terminal.val.card := by exact_mod_cast hcard
      have hk0 : (0 : ℝ) < terminal.val.card := lt_of_lt_of_le zero_lt_two hk2
      have hk1 : (0 : ℝ) < terminal.val.card - 1 := by linarith
      exact div_pos hk0 hk1
    rw [Real.zero_rpow hexp.ne']
    exact quittingStageCoalitionMass_nonneg reward profile 0 terminal

theorem quittingStageCoalitionMass_tsum_rpow_le_sSup
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty})
    (hcard : 2 ≤ terminal.val.card) :
    (∑' time, quittingStageCoalitionMass reward profile time terminal) ^
        ((terminal.val.card : ℝ) /
          ((terminal.val.card : ℝ) - 1)) ≤
      sSup (Set.range fun time =>
        quittingStageCoalitionMass reward profile time terminal) := by
  obtain ⟨peak, hpeak⟩ :=
    exists_quittingStageCoalitionMass_ge_tsum_rpow
      profile terminal hcard
  apply hpeak.trans
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro value ⟨time, rfl⟩
    have hsummable :=
      (hasSum_quittingStageCoalitionMass reward profile terminal).summable
    have hstage : quittingStageCoalitionMass reward profile time terminal ≤
        ∑' other, quittingStageCoalitionMass reward profile other terminal :=
      hsummable.le_tsum time fun other _ =>
        quittingStageCoalitionMass_nonneg reward profile other terminal
    have hsimplex := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
    have hcoordinate : quittingTerminalOutcomeMass reward profile (some terminal) ≤
        ∑ outcome, quittingTerminalOutcomeMass reward profile outcome := by
      exact Finset.single_le_sum
        (fun outcome _ => hsimplex.1 outcome) (Finset.mem_univ (some terminal))
    rw [tsum_quittingStageCoalitionMass] at hstage
    rw [hsimplex.2] at hcoordinate
    change quittingAbsorbedMassLimit reward profile terminal ≤ 1 at hcoordinate
    exact hstage.trans hcoordinate
  · exact Set.mem_range_self peak

namespace QuittingReprojectionDiffuseWindowPacket

/-- A diffuse normalized finite-window clock cannot carry a nonsingleton
terminal coalition. -/
theorem terminal_card_eq_one
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {owner : iota} {terminal : {S : Finset iota // S.Nonempty}}
    {cutoff : ℕ → ℕ} {scale : ℕ → ℝ} {lower : ℝ}
    (packet : QuittingReprojectionDiffuseWindowPacket
      reward profiles owner terminal cutoff scale lower) :
    terminal.val.card = 1 := by
  have hcardpos : 0 < terminal.val.card := terminal.property.card_pos
  by_contra hne
  have hcard : 2 ≤ terminal.val.card := by omega
  obtain ⟨n, hwindow, hmesh⟩ :=
    (packet.windowMass.and
      (packet.clock_mesh lower packet.lower_pos)).exists
  have hmasspos : 0 <
      quittingFiniteWindowCoalitionMass
        (profiles n) terminal (cutoff n) :=
    packet.lower_pos.trans hwindow
  have hcutoff : cutoff n ≠ 0 := by
    intro hzero
    rw [hzero] at hwindow
    simp [quittingFiniteWindowCoalitionMass] at hwindow
    exact (not_lt_of_ge packet.lower_pos.le) hwindow
  have hrange : (Finset.range (cutoff n)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.pos_of_ne_zero hcutoff)⟩
  obtain ⟨peak, hpeak, hsquare⟩ :=
    exists_quittingStageCoalitionMass_ge_finite_sum_sq
      (profiles n) terminal (Finset.range (cutoff n)) hrange hcard
  have hpeakLt : peak < cutoff n := Finset.mem_range.mp hpeak
  have hratio :
      quittingFiniteWindowCoalitionMass (profiles n) terminal (cutoff n) ≤
        quittingStageCoalitionMass reward (profiles n) peak terminal /
          quittingFiniteWindowCoalitionMass
            (profiles n) terminal (cutoff n) := by
    apply (le_div_iff₀ hmasspos).2
    simpa only [quittingFiniteWindowCoalitionMass, pow_two] using hsquare
  have hlowerClock : lower <
      quittingFiniteWindowCoalitionClock
        (profiles n) terminal (cutoff n) peak := by
    rw [quittingFiniteWindowCoalitionClock, if_pos hpeakLt]
    exact hwindow.trans_le hratio
  exact (not_lt_of_ge (le_of_lt hlowerClock)) (hmesh peak)

end QuittingReprojectionDiffuseWindowPacket

end GameTheory
