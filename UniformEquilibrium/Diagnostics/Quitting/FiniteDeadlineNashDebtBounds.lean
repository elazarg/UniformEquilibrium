/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFiniteDeadlineNashEscalation
import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail

/-!
# Generic finite-deadline Nash debt bounds

These bounds compare unrestricted behavioral deviations with the prescribed
finite-deadline timing choices. They are independent of any particular number
of live timing dates.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingFixedOpponentsContinueReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingFixedOpponentsContinueReward reward roots who time ≤
      bound * (1 - quittingFixedOpponentsContinueMass roots who time) := by
  exact (le_abs_self _).trans
    (abs_quittingFixedOpponentsContinueReward_le_hazard
      reward roots who time bound hbound (fun terminal => hreward terminal who))

theorem quittingFixedOpponentsContinue_add_solo_sub_quit_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (time : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingFixedOpponentsContinueReward reward roots who time +
          quittingFixedOpponentsContinueMass roots who time *
            reward (quittingSingletonTerminal who) who -
        quittingFixedOpponentsQuitValue reward roots who time ≤
      2 * bound *
        (1 - quittingFixedOpponentsContinueMass roots who time) := by
  have hcontinue := quittingFixedOpponentsContinueReward_le
    reward roots who time hbound hreward
  have hquit := neg_le_of_abs_le
    (abs_quittingFixedOpponentsQuitValue_sub_continueMass_mul_solo_le
      reward roots who time bound hbound (fun terminal => hreward terminal who))
  linarith

theorem QuittingFiniteDeadlineNashProfile.bestResponseValue_le_max_late
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι)
    (hsolo : 0 ≤ reward (quittingSingletonTerminal who) who) :
    quittingContinuationBestResponseValue reward profile who ≤
      max (quittingTerminalPayoff reward profile who)
        (quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who none)) who +
          quittingFiniteDeadlineOpponentSurvival reward profile deadline who *
            reward (quittingSingletonTerminal who) who) := by
  rw [quittingContinuationBestResponseValue]
  let values : Set ℝ := Set.range fun deviation :
      (quittingGame reward).BehaviorStrategy who =>
    quittingTerminalPayoff reward (Function.update profile who deviation) who
  have hvalues : values.Nonempty :=
    ⟨quittingTerminalPayoff reward
        (Function.update profile who (profile who)) who,
      ⟨profile who, rfl⟩⟩
  apply csSup_le hvalues
  rintro _ ⟨deviation, rfl⟩
  calc
    quittingTerminalPayoff reward (Function.update profile who deviation) who ≤
        sSup (Set.range fun quitTime : Option ℕ =>
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who quitTime)) who) :=
      quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
        reward profile who deviation
    _ ≤ max (quittingTerminalPayoff reward profile who)
          (quittingTerminalPayoff reward
              (Function.update profile who
                (quittingPureTimeBehaviorStrategy reward who none)) who +
            quittingFiniteDeadlineOpponentSurvival reward profile deadline who *
              reward (quittingSingletonTerminal who) who) := by
      apply csSup_le
      · exact ⟨_, ⟨none, rfl⟩⟩
      · rintro _ ⟨quitTime, rfl⟩
        cases quitTime with
        | none =>
            calc
              _ ≤ quittingTerminalPayoff reward
                    (Function.update profile who
                      (quittingPureTimeBehaviorStrategy reward who
                        (none : Option ℕ))) who +
                  quittingFiniteDeadlineOpponentSurvival
                    reward profile deadline who *
                      reward (quittingSingletonTerminal who) who := by
                apply le_add_of_nonneg_right
                exact mul_nonneg
                  (quittingFiniteDeadlineOpponentSurvival_nonneg
                    reward profile deadline who) hsolo
              _ ≤ _ := le_max_right _ _
        | some time =>
            by_cases htime : time < deadline
            · exact (certificate.pureTime_le who (some time)
                (Or.inr ⟨time, htime, rfl⟩)).trans (le_max_left _ _)
            · let roots := quittingProfileLiveRoot reward profile
              have hlate :=
                quittingRootSequencePureTimeTerminalValue_late_le_none_add_charge
                  reward roots who deadline time (Nat.le_of_not_gt htime)
                  certificate.allContinue_from
              rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
                    reward profile who (some time),
                ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
                    reward profile who none] at hlate
              dsimp only [quittingFiniteDeadlineOpponentSurvival] at hlate ⊢
              rw [max_eq_right hsolo] at hlate
              exact hlate.trans (le_max_right _ _)

end GameTheory
