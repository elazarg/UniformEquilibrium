/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Stationary.CompleteEndpointChoices

/-! # Eventual exact endpoint selection from strict stationary limits -/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def stationaryQuitNowPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update (quittingStationaryProfile reward root) who
      (quittingPureTimeBehaviorStrategy reward who (some 0))) who

def stationaryNeverPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update (quittingStationaryProfile reward root) who
      (quittingPureTimeBehaviorStrategy reward who none)) who

/-- Strict separation of the endpoint limits eventually makes Never the
exact complete behavioral cap, with half of its limiting gain retained. -/
theorem eventually_never_eq_completeCap_and_gain_ge_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool) (who : ι)
    (quitLimit neverLimit payoffLimit : ℝ)
    (hquit : Tendsto (fun n ↦ stationaryQuitNowPayoff reward (root n) who)
      atTop (nhds quitLimit))
    (hnever : Tendsto (fun n ↦ stationaryNeverPayoff reward (root n) who)
      atTop (nhds neverLimit))
    (hpayoff : Tendsto (fun n ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward (root n)) who) atTop (nhds payoffLimit))
    (hstrict : quitLimit < neverLimit) (hgain : 0 < neverLimit - payoffLimit) :
    ∀ᶠ n in atTop,
      stationaryNeverPayoff reward (root n) who =
        quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward (root n)) who ∧
      (neverLimit - payoffLimit) / 2 ≤
        stationaryNeverPayoff reward (root n) who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (root n)) who := by
  have hendpoint : ∀ᶠ n in atTop,
      stationaryQuitNowPayoff reward (root n) who <
        stationaryNeverPayoff reward (root n) who :=
    ((hquit.sub hnever).eventually_lt_const (sub_neg.mpr hstrict)).mono
      fun _ h ↦ sub_neg.mp h
  have hgainEventually : ∀ᶠ n in atTop,
      (neverLimit - payoffLimit) / 2 <
        stationaryNeverPayoff reward (root n) who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (root n)) who :=
    (hnever.sub hpayoff).eventually_const_lt (by linarith)
  filter_upwards [hendpoint, hgainEventually] with n hsep hgainN
  obtain ⟨choice, hchoice, hcap⟩ :=
    exists_stationary_quitNow_or_never_completeCap reward (root n) who
  have hneverLe := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingStationaryProfile reward (root n)) who
      (quittingPureTimeBehaviorStrategy reward who none)
  have hneverCap : stationaryNeverPayoff reward (root n) who =
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (root n)) who := by
    rcases hchoice with rfl | rfl
    · exact hcap
    · exfalso
      dsimp [stationaryQuitNowPayoff, stationaryNeverPayoff] at hsep hcap hneverLe
      linarith
  exact ⟨hneverCap, hgainN.le⟩

/-- Strict separation in the other direction eventually makes Quit-now the
exact complete behavioral cap, with half of its limiting gain retained. -/
theorem eventually_quitNow_eq_completeCap_and_gain_ge_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ℕ → ι → PMF Bool) (who : ι)
    (quitLimit neverLimit payoffLimit : ℝ)
    (hquit : Tendsto (fun n ↦ stationaryQuitNowPayoff reward (root n) who)
      atTop (nhds quitLimit))
    (hnever : Tendsto (fun n ↦ stationaryNeverPayoff reward (root n) who)
      atTop (nhds neverLimit))
    (hpayoff : Tendsto (fun n ↦ quittingTerminalPayoff reward
      (quittingStationaryProfile reward (root n)) who) atTop (nhds payoffLimit))
    (hstrict : neverLimit < quitLimit) (hgain : 0 < quitLimit - payoffLimit) :
    ∀ᶠ n in atTop,
      stationaryQuitNowPayoff reward (root n) who =
        quittingContinuationBestResponseValue reward
          (quittingStationaryProfile reward (root n)) who ∧
      (quitLimit - payoffLimit) / 2 ≤
        stationaryQuitNowPayoff reward (root n) who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (root n)) who := by
  have hendpoint : ∀ᶠ n in atTop,
      stationaryNeverPayoff reward (root n) who <
        stationaryQuitNowPayoff reward (root n) who :=
    ((hnever.sub hquit).eventually_lt_const (sub_neg.mpr hstrict)).mono
      fun _ h ↦ sub_neg.mp h
  have hgainEventually : ∀ᶠ n in atTop,
      (quitLimit - payoffLimit) / 2 <
        stationaryQuitNowPayoff reward (root n) who -
          quittingTerminalPayoff reward
            (quittingStationaryProfile reward (root n)) who :=
    (hquit.sub hpayoff).eventually_const_lt (by linarith)
  filter_upwards [hendpoint, hgainEventually] with n hsep hgainN
  obtain ⟨choice, hchoice, hcap⟩ :=
    exists_stationary_quitNow_or_never_completeCap reward (root n) who
  have hquitLe := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingStationaryProfile reward (root n)) who
      (quittingPureTimeBehaviorStrategy reward who (some 0))
  have hquitCap : stationaryQuitNowPayoff reward (root n) who =
      quittingContinuationBestResponseValue reward
        (quittingStationaryProfile reward (root n)) who := by
    rcases hchoice with rfl | rfl
    · exfalso
      dsimp [stationaryQuitNowPayoff, stationaryNeverPayoff] at hsep hcap hquitLe
      linarith
    · exact hcap
  exact ⟨hquitCap, hgainN.le⟩

end GameTheory
