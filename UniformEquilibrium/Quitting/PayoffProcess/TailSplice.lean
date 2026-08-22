/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.PayoffProcess.Basic
import UniformEquilibrium.Quitting.PayoffProcess.TailStepSelector

/-!
# Adapted finite-prefix and constant-table tail splices

The tail selected from the table observed at a deterministic cutoff is a
countable step function.  Its stage-`n` action reads only the cutoff table,
so it is adapted at every `n` after the cutoff.  This file makes both that
fact and the finite-prefix/tail splice explicit.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Read the selected constant-table behavior profile along its unique live
history, starting at the deterministic cutoff. -/
def QuittingPayoffProcess.soloExitTailProfile
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (ε : ℝ) (hε : 0 < ε) : QuittingProcessProfile process :=
  fun time who ω =>
    if _htime : cutoff ≤ time then
      soloExitTailStepProfile ε hε (process.payoff cutoff ω) who
        (time - cutoff)
        (quittingLiveHist (soloExitRewardCenter (ι := ι) 0)
          (time - cutoff))
    else
      PMF.pure false

/-- The countable-step tail is adapted after its cutoff.  The proof factors
through measurability of the observed cutoff table and monotonicity of the
natural filtration. -/
theorem QuittingPayoffProcess.soloExitTailProfile_adapted_after
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ time, cutoff ≤ time → ∀ (who : ι) (action : Bool),
      @Measurable process.Ω ℝ (process.filtration time) Real.measurableSpace
        (fun ω => (process.soloExitTailProfile cutoff ε hε
          time who ω action).toReal) := by
  intro time htime who action
  letI : MeasurableSpace process.Ω := process.filtration time
  have hreward : @Measurable process.Ω
      ({S : Finset ι // S.Nonempty} → Payoff ι)
      (process.filtration time) inferInstance
      (process.payoff cutoff) :=
    (process.payoffTable_measurable_filtration cutoff).mono
      (process.filtration_mono htime) le_rfl
  have hselector := measurable_soloExitTailStepProfile_apply
    (ι := ι) ε hε who (time - cutoff)
      (quittingLiveHist (soloExitRewardCenter (ι := ι) 0)
        (time - cutoff)) action
  have hcoordinate : @Measurable process.Ω ENNReal
      (process.filtration time) inferInstance (fun ω =>
      soloExitTailStepProfile ε hε (process.payoff cutoff ω) who
        (time - cutoff)
        (quittingLiveHist (soloExitRewardCenter (ι := ι) 0)
          (time - cutoff)) action) :=
    hselector.comp hreward
  simp only [QuittingPayoffProcess.soloExitTailProfile, htime, ↓reduceDIte]
  exact hcoordinate.ennreal_toReal

/-- Splice an arbitrary finite prefix to an infinite tail at a deterministic
cutoff. -/
def QuittingPayoffProcess.spliceProfile
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (preprofile tail : QuittingProcessProfile process) :
    QuittingProcessProfile process :=
  fun time => if time < cutoff then preprofile time else tail time

omit [Nonempty ι] in
/-- An adapted finite prefix and a tail adapted after the cutoff compile to
an adapted global profile. -/
theorem QuittingPayoffProcess.spliceProfile_adapted
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (preprofile tail : QuittingProcessProfile process)
    (hprefix : ∀ time, time < cutoff → ∀ (who : ι) (action : Bool),
      @Measurable process.Ω ℝ (process.filtration time) Real.measurableSpace
        (fun ω => (preprofile time who ω action).toReal))
    (htail : ∀ time, cutoff ≤ time → ∀ (who : ι) (action : Bool),
      @Measurable process.Ω ℝ (process.filtration time) Real.measurableSpace
        (fun ω => (tail time who ω action).toReal)) :
    process.Adapted (process.spliceProfile cutoff preprofile tail) := by
  intro time who action
  by_cases htime : time < cutoff
  · simpa only [QuittingPayoffProcess.spliceProfile, htime, ↓reduceIte] using
      hprefix time htime who action
  · have hcutoff : cutoff ≤ time := Nat.le_of_not_gt htime
    simpa only [QuittingPayoffProcess.spliceProfile, htime, ↓reduceIte] using
      htail time hcutoff who action

/-- In particular, any adapted finite prefix splices to the selected
constant-table tail. -/
theorem QuittingPayoffProcess.splice_soloExitTailProfile_adapted
    (process : QuittingPayoffProcess ι) (cutoff : ℕ)
    (preprofile : QuittingProcessProfile process)
    (ε : ℝ) (hε : 0 < ε)
    (hprefix : ∀ time, time < cutoff → ∀ (who : ι) (action : Bool),
      @Measurable process.Ω ℝ (process.filtration time) Real.measurableSpace
        (fun ω => (preprofile time who ω action).toReal)) :
    process.Adapted
      (process.spliceProfile cutoff preprofile
        (process.soloExitTailProfile cutoff ε hε)) :=
  process.spliceProfile_adapted cutoff preprofile
    (process.soloExitTailProfile cutoff ε hε) hprefix
    (process.soloExitTailProfile_adapted_after cutoff ε hε)

end GameTheory
