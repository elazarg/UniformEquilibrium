/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.PathPayoffStability
import UniformEquilibrium.Quitting.PayoffProcess.TailApproximation
import UniformEquilibrium.Quitting.PayoffProcess.TailSplice

/-!
# Pointwise equilibrium of the selected payoff-process tail

On the uniform tail-close event, every future table is within `2η` of the
cutoff table.  The countable selector is a `5η` terminal equilibrium for the
cutoff table, and path stability costs `2η` on each side of a unilateral
comparison.  Thus the actual varying-payoff tail has deviation error `9η`.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The live-spine root sequence selected from the table observed at the
cutoff. -/
def QuittingPayoffProcess.soloExitTailRoots
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (η : ℝ) (hη : 0 < η) (ω : process.Ω) :
    ℕ → ι → PMF Bool :=
  quittingProfileLiveRoot (process.payoff cutoff ω)
    (soloExitTailStepProfile η hη (process.payoff cutoff ω))

/-- The actual future table sequence, re-indexed from the cutoff. -/
def QuittingPayoffProcess.shiftedPayoff
    (process : QuittingPayoffProcess ι) (cutoff : ℕ) (ω : process.Ω) :
    ℕ → ({S : Finset ι // S.Nonempty} → Payoff ι) :=
  fun offset => process.payoff (cutoff + offset) ω

omit [Nonempty ι] in
/-- On a tail-close path, every shifted table is within `2η` of the cutoff
table in every coordinate. -/
theorem QuittingPayoffProcess.shiftedPayoff_close_cutoff
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {η : ℝ} (hη : 0 < η) (ω : process.Ω)
    (hclose : ω ∈ process.TailClose cutoff η) :
    ∀ offset terminal player,
      |process.shiftedPayoff cutoff ω offset terminal player -
          process.payoff cutoff ω terminal player| ≤ 2 * η := by
  intro offset terminal player
  have hfuture := hclose (cutoff + offset) (Nat.le_add_right cutoff offset)
  have hcutoff := hclose cutoff le_rfl
  have hdist : dist (process.payoff (cutoff + offset) ω)
        (process.payoff cutoff ω) < 2 * η := by
    calc
      dist (process.payoff (cutoff + offset) ω)
          (process.payoff cutoff ω) ≤
        dist (process.payoff (cutoff + offset) ω) (process.limit ω) +
          dist (process.limit ω) (process.payoff cutoff ω) :=
        dist_triangle _ _ _
      _ < η + η := add_lt_add hfuture (by simpa [dist_comm] using hcutoff)
      _ = 2 * η := by ring
  have hterminal := (dist_pi_lt_iff (by positivity : 0 < 2 * η)).mp
    hdist terminal
  have hplayer := (dist_pi_lt_iff (by positivity : 0 < 2 * η)).mp
    hterminal player
  simpa only [QuittingPayoffProcess.shiftedPayoff, Real.dist_eq] using hplayer.le

/-- The selected tail's actual varying-table payoff is within `2η` of its
cutoff-table terminal payoff. -/
theorem QuittingPayoffProcess.abs_soloExitTailPathPayoff_sub_terminal_le
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {η : ℝ} (hη : 0 < η) (ω : process.Ω)
    (hclose : ω ∈ process.TailClose cutoff η) (who : ι) :
    |quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0 -
        quittingTerminalPayoff (process.payoff cutoff ω)
          (soloExitTailStepProfile η hη (process.payoff cutoff ω)) who| ≤
      2 * η := by
  have hpath := abs_quittingVariableTailValue_sub_le
    (process.shiftedPayoff cutoff ω) (process.payoff cutoff ω)
    (process.soloExitTailRoots cutoff η hη ω) who 0
    (hε := (by positivity : 0 ≤ 2 * η)) (by
      intro offset
      simpa only [Nat.zero_add] using
        process.shiftedPayoff_close_cutoff cutoff hη ω hclose offset)
  rw [show process.soloExitTailRoots cutoff η hη ω =
      quittingProfileLiveRoot (process.payoff cutoff ω)
        (soloExitTailStepProfile η hη (process.payoff cutoff ω)) from rfl]
    at hpath
  rw [quittingComplementarityTailValue_profileLiveRoot] at hpath
  exact hpath

/-- On the good tail event, the selected varying-table path is a `9η`
equilibrium against every time-dependent unilateral hazard. -/
theorem QuittingPayoffProcess.soloExitTailPath_isNash_on_good
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    {η : ℝ} (hη : 0 < η) (ω : process.Ω)
    (hlimit : QuittingUnitSoloExit (process.limit ω) ∧
      QuittingCappedJointExit (process.limit ω))
    (hclose : ω ∈ process.TailClose cutoff η)
    (who : ι) (deviation : ℕ → PMF Bool) :
    quittingVariableTailValue (process.shiftedPayoff cutoff ω)
          (process.soloExitTailRoots cutoff η hη ω) who 0 + 9 * η ≥
      quittingVariableTailValue (process.shiftedPayoff cutoff ω)
        (quittingRootSequenceUpdate
          (process.soloExitTailRoots cutoff η hη ω) who deviation) who 0 := by
  let cutoffReward := process.payoff cutoff ω
  let selected := soloExitTailStepProfile η hη cutoffReward
  let roots := process.soloExitTailRoots cutoff η hη ω
  let deviatedRoots := quittingRootSequenceUpdate roots who deviation
  have hcutoffClose : dist cutoffReward (process.limit ω) < η :=
    hclose cutoff le_rfl
  have hselected : (quittingGame cutoffReward).IsεAsymptoticNash
      (quittingTerminalPayoff cutoffReward) (5 * η) selected :=
    soloExitTailStepProfile_isNash hη cutoffReward
      ⟨process.limit ω, hlimit, hcutoffClose⟩
  let behaviorDeviation : (quittingGame cutoffReward).BehaviorStrategy who :=
    fun time _ => deviation time
  have hnash := hselected who behaviorDeviation
  have hrootUpdate : quittingProfileLiveRoot cutoffReward
        (Function.update selected who behaviorDeviation) = deviatedRoots := by
    rw [quittingProfileLiveRoot_update_eq_rootSequenceUpdate]
    rfl
  have hconstant : quittingComplementarityTailValue cutoffReward roots who 0 +
        5 * η ≥
      quittingComplementarityTailValue cutoffReward deviatedRoots who 0 := by
    rw [show roots = quittingProfileLiveRoot cutoffReward selected from rfl,
      quittingComplementarityTailValue_profileLiveRoot,
      show deviatedRoots = quittingProfileLiveRoot cutoffReward
        (Function.update selected who behaviorDeviation) from hrootUpdate.symm,
      quittingComplementarityTailValue_profileLiveRoot]
    exact hnash
  have hcloseTables := process.shiftedPayoff_close_cutoff cutoff hη ω hclose
  have hbase := abs_quittingVariableTailValue_sub_le
    (process.shiftedPayoff cutoff ω) cutoffReward roots who 0
    (hε := (by positivity : 0 ≤ 2 * η)) (by
      intro offset
      simpa only [Nat.zero_add] using hcloseTables offset)
  have hdeviation := abs_quittingVariableTailValue_sub_le
    (process.shiftedPayoff cutoff ω) cutoffReward deviatedRoots who 0
    (hε := (by positivity : 0 ≤ 2 * η)) (by
      intro offset
      simpa only [Nat.zero_add] using hcloseTables offset)
  rcases abs_le.mp hbase with ⟨_hbaseLower, hbaseUpper⟩
  rcases abs_le.mp hdeviation with ⟨hdeviationLower, _hdeviationUpper⟩
  dsimp only [roots, deviatedRoots] at hconstant hbaseUpper hdeviationLower ⊢
  linarith

end GameTheory
