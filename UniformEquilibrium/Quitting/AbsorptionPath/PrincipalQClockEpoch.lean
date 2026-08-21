/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.AbsorptionPath.PrincipalQClockOrbit

/-!
# Principal-Q clock epochs

One adaptive orbit is treated as an epoch relative to a finite target clock.
Either a finite orbit node reaches that clock, or a Zeno limit supplies a new
boundary node at a strictly later clock. This is the restart interface needed
to concatenate countably many adaptive epochs without pretending that every
single orbit is non-Zeno.
-/

noncomputable section

namespace GameTheory.QuittingLCPClassification

open Filter Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The result of one complete adaptive epoch relative to a target clock. -/
inductive PrincipalQClockEpochOutcome
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    (target : ℝ) : Type
  | reaches (index : ℕ)
      (target_le : target ≤
        (principalQClockOrbit M hdiag hQ hstepBound initial index).time)
  | restarts (restart : PrincipalQClockNode ι)
      (time_strict : initial.time < restart.time)
      (state_tendsto : Tendsto (fun n =>
        (principalQClockOrbit M hdiag hQ hstepBound initial n).state)
          atTop (nhds restart.state))

/-- A finite target is crossed in one epoch, or that epoch has a strictly
later Zeno restart node. -/
theorem nonempty_principalQClockEpochOutcome
    (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0)
    (hQ : IsProjectiveQBarMatrix M) {stepBound : ℝ}
    (hstepBound : 0 < stepBound) (initial : PrincipalQClockNode ι)
    (target : ℝ) :
    Nonempty (PrincipalQClockEpochOutcome
      M hdiag hQ hstepBound initial target) := by
  rcases principalQClockOrbit_escape_or_zenoEndpoint
      M hdiag hQ hstepBound initial with hescape |
        ⟨timeLimit, scaledStateLimit, htime, hscaledMem, hscaled⟩
  · have heventually : ∀ᶠ n in atTop, target ≤
        (principalQClockOrbit M hdiag hQ hstepBound initial n).time :=
      hescape.eventually (eventually_ge_atTop target)
    obtain ⟨index, hindex⟩ := heventually.exists
    exact ⟨.reaches index hindex⟩
  · obtain ⟨restart, hrestartTime, hstate⟩ :=
      exists_principalQClockOrbit_zenoRestart
        M hdiag hQ hstepBound initial htime hscaledMem hscaled
    have hfirst : initial.time <
        (principalQClockOrbit M hdiag hQ hstepBound initial 1).time := by
      simpa only [principalQClockOrbit_zero] using
        principalQClockOrbit_time_lt_succ
          M hdiag hQ hstepBound initial 0
    have hfirstLeLimit :
        (principalQClockOrbit M hdiag hQ hstepBound initial 1).time ≤
          timeLimit := by
      apply ge_of_tendsto htime
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (strictMono_principalQClockOrbit_time
        M hdiag hQ hstepBound initial).monotone hn
    have hstrict : initial.time < restart.time := by
      rw [hrestartTime]
      exact hfirst.trans_le hfirstLeLimit
    exact ⟨.restarts restart hstrict hstate⟩

end GameTheory.QuittingLCPClassification
