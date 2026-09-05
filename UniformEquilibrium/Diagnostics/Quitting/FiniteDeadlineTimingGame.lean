/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingGame
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFiniteDeadlineNashEscalation

/-! # Finite timing Nash laws as finite-deadline behavioral certificates -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A mixed Nash equilibrium of the finite timing game realizes a literal
finite-deadline Nash profile. -/
theorem quittingFiniteDeadlineTimingProfile_isFiniteDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      mixed) :
    QuittingFiniteDeadlineNashProfile reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) deadline := by
  constructor
  · intro time htime
    exact
      quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
        reward deadline mixed htime
  · intro who quitTime htime
    have hprescribed :=
      quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
        reward deadline mixed who
    rcases htime with hnever | ⟨time, htime, rfl⟩
    · subst quitTime
      have hnashNever := hnash who (PMF.pure none)
      rw [← hprescribed,
        ← quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
          reward deadline mixed who none] at hnashNever
      exact hnashNever
    · let action : QuittingFiniteDeadlineTimingAction deadline :=
        some ⟨time, htime⟩
      have hnashTime := hnash who (PMF.pure action)
      rw [← hprescribed,
        ← quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
          reward deadline mixed who action] at hnashTime
      exact hnashTime

end GameTheory
