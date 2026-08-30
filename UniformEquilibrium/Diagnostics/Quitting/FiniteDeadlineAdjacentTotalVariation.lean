/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.TotalVariation
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingGame

/-!
# Adjacent finite-deadline total-variation control

This file isolates the source-independent part of comparing finite timing
games at adjacent deadlines.  It proves Lipschitz bounds for prescribed
payoffs and pure-deviation gains and records the literal inclusion of an old
deadline law into the next deadline.

For a finite-deadline Nash law, pure-time extremality also identifies its
unrestricted behavioral terminal debt with the positive part of the first
excluded boundary-action gain.  Consecutive Nash laws therefore satisfy an
exact projective total-variation estimate.  No censor decomposition,
minimum-tail reprojection, or compatible-family consumer is asserted.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Payoff from the first pure quit time outside a finite-deadline Nash
certificate. -/
def quittingFiniteDeadlineBoundaryPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (deadline : ℕ) (who : ι) : ℝ :=
  quittingTerminalPayoff reward
    (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some deadline))) who

/-- Under a finite-deadline Nash certificate, every pure stopping time is
bounded by the larger of prescribed payoff and the first excluded date. -/
theorem QuittingFiniteDeadlineNashProfile.pureTime_le_max_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) (quitTime : Option ℕ) :
    quittingTerminalPayoff reward
        (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who ≤
      max (quittingTerminalPayoff reward profile who)
        (quittingFiniteDeadlineBoundaryPayoff reward profile deadline who) := by
  let roots := quittingProfileLiveRoot reward profile
  cases quitTime with
  | none =>
      exact (certificate.pureTime_le who none (Or.inl rfl)).trans
        (le_max_left _ _)
  | some time =>
      by_cases htime : time < deadline
      · exact (certificate.pureTime_le who (some time)
          (Or.inr ⟨time, htime, rfl⟩)).trans (le_max_left _ _)
      · have hlate :=
          quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
            reward roots who deadline time (Nat.le_of_not_gt htime)
            certificate.allContinue_from
        have hboundary :=
          quittingRootSequencePureTimeTerminalValue_late_sub_none_eq
            reward roots who deadline deadline le_rfl
            certificate.allContinue_from
        rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward profile who (some time),
            ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward profile who none] at hlate
        rw [← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward profile who (some deadline),
            ← quittingTerminalPayoff_update_pureTimeBehaviorStrategy
              reward profile who none] at hboundary
        by_cases hrewardsign :
            0 ≤ reward (quittingSingletonTerminal who) who
        · have hsurvival :
              quittingOpponentSurvivalWeight roots who 0 time ≤
                quittingOpponentSurvivalWeight roots who 0 deadline :=
            antitone_quittingOpponentSurvivalWeight roots who 0
              (Nat.le_of_not_gt htime)
          have hscaled := mul_le_mul_of_nonneg_right hsurvival hrewardsign
          unfold quittingFiniteDeadlineBoundaryPayoff
          have htimeBoundary :
              quittingTerminalPayoff reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who (some time))) who ≤
                quittingTerminalPayoff reward
                  (Function.update profile who
                    (quittingPureTimeBehaviorStrategy reward who
                      (some deadline))) who := by
            linarith
          exact htimeBoundary.trans (le_max_right _ _)
        · have hscaled :
              quittingOpponentSurvivalWeight roots who 0 time *
                  reward (quittingSingletonTerminal who) who ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos
              (quittingOpponentSurvivalWeight_nonneg roots who 0 time)
              (le_of_not_ge hrewardsign)
          have hnever := certificate.pureTime_le who none (Or.inl rfl)
          have hmax := le_max_left
            (quittingTerminalPayoff reward profile who)
            (quittingFiniteDeadlineBoundaryPayoff reward profile deadline who)
          linarith

/-- The unrestricted behavioral best-response cap is exactly the maximum of
prescribed payoff and the newly exposed boundary-date payoff. -/
theorem QuittingFiniteDeadlineNashProfile.bestResponseValue_eq_max_boundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) :
    quittingContinuationBestResponseValue reward profile who =
      max (quittingTerminalPayoff reward profile who)
        (quittingFiniteDeadlineBoundaryPayoff reward profile deadline who) := by
  rw [quittingContinuationBestResponseValue,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨quitTime, rfl⟩
    exact certificate.pureTime_le_max_boundary who quitTime
  · apply max_le
    · simpa only [Function.update_eq_self] using
        quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
          reward profile who (profile who)
    · unfold quittingFiniteDeadlineBoundaryPayoff
      exact quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
        reward profile who
          (quittingPureTimeBehaviorStrategy reward who (some deadline))

/-- Exact projective-boundary debt formula: the only unrestricted debt of a
finite-deadline Nash certificate is the positive gain at its first excluded
date. -/
theorem QuittingFiniteDeadlineNashProfile.semanticDebt_eq_boundaryGain_pospart
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profile : (quittingGame reward).BehaviorProfile} {deadline : ℕ}
    (certificate : QuittingFiniteDeadlineNashProfile reward profile deadline)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who =
      max 0 (quittingFiniteDeadlineBoundaryPayoff reward profile deadline who -
        quittingTerminalPayoff reward profile who) := by
  change quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who = _
  rw [certificate.bestResponseValue_eq_max_boundary who]
  rcases le_total (quittingTerminalPayoff reward profile who)
      (quittingFiniteDeadlineBoundaryPayoff reward profile deadline who) with
    hle | hle
  · rw [max_eq_right hle, max_eq_right]
    linarith
  · rw [max_eq_left hle, max_eq_left (sub_nonpos.mpr hle)]
    ring

/-- Include an action at deadline `deadline` into the next deadline without
changing its stopping date. -/
def quittingFiniteDeadlineTimingActionInclude {deadline : ℕ} :
    QuittingFiniteDeadlineTimingAction deadline →
      QuittingFiniteDeadlineTimingAction (deadline + 1)
  | none => none
  | some time => some time.castSucc

/-- The action at the new boundary date in the successor timing game. -/
def quittingFiniteDeadlineTimingBoundaryAction (deadline : ℕ) :
    QuittingFiniteDeadlineTimingAction (deadline + 1) :=
  some ⟨deadline, Nat.lt_succ_self deadline⟩

/-- Include every marginal of a timing law into the successor deadline. -/
def quittingFiniteDeadlineTimingProfileInclude {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
  fun player => (mixed player).map quittingFiniteDeadlineTimingActionInclude

/-- Sum of marginal total-variation distances between the literal inclusion
of an old timing law and a law at the successor deadline. -/
def quittingFiniteDeadlineAdjacentTV (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) : ℝ :=
  ∑ player, Math.Probability.pmfTV
    (quittingFiniteDeadlineTimingProfileInclude old player) (new player)

theorem quittingFiniteDeadlineTimingActionTime_include
    {deadline : ℕ} (action : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteDeadlineTimingActionTime
        (quittingFiniteDeadlineTimingActionInclude action) =
      quittingFiniteDeadlineTimingActionTime action := by
  cases action with
  | none => rfl
  | some time => rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Inclusion into the successor deadline preserves the complete
stopping-time law exactly. -/
theorem quittingFiniteDeadlineTimingProfileInclude_map_actionTime
    {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (player : ι) :
    (quittingFiniteDeadlineTimingProfileInclude mixed player).map
        quittingFiniteDeadlineTimingActionTime =
      (mixed player).map quittingFiniteDeadlineTimingActionTime := by
  rw [quittingFiniteDeadlineTimingProfileInclude, PMF.map_comp]
  congr 1
  funext action
  exact quittingFiniteDeadlineTimingActionTime_include action

omit [Fintype ι] in
/-- Literal deadline inclusion commutes with replacing a marginal by a pure
old-deadline action. -/
theorem quittingFiniteDeadlineTimingProfileInclude_update_pure
    {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteDeadlineTimingProfileInclude
        (Function.update mixed who (PMF.pure action)) =
      Function.update (quittingFiniteDeadlineTimingProfileInclude mixed) who
        (PMF.pure (quittingFiniteDeadlineTimingActionInclude action)) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [quittingFiniteDeadlineTimingProfileInclude, Function.update_self,
      Function.update_self, PMF.pure_map]
  · simp [quittingFiniteDeadlineTimingProfileInclude,
      Function.update_of_ne hplayer]

omit [DecidableEq ι] in
/-- Literal behavioral realization commutes exactly with inclusion into the
successor timing deadline. -/
theorem quittingFiniteDeadlineTimingProfile_include_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteDeadlineTimingProfile reward (deadline + 1)
        (quittingFiniteDeadlineTimingProfileInclude mixed) =
      quittingFiniteDeadlineTimingProfile reward deadline mixed := by
  funext player
  unfold quittingFiniteDeadlineTimingProfile
    quittingCompactStoppingLawProfile
  apply congrArg (quittingStoppingLawBehaviorStrategy reward player)
  simp only [quittingFiniteDeadlineTimingLaw,
    Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
  exact quittingFiniteDeadlineTimingProfileInclude_map_actionTime mixed player

/-- Prescribed payoff in a finite timing game is Lipschitz in the sum of the
marginal total-variation distances. -/
theorem abs_quittingFiniteDeadlineTiming_mixedEU_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |(quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
          first who -
        (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
          second who| ≤
      2 * bound * ∑ player,
        Math.Probability.pmfTV (first player) (second player) := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu,
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  exact Math.PMFProduct.abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV
    first second
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward fun player =>
        quittingFiniteDeadlineTimingActionTime (choices player)) who)
    hbound (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)

omit [DecidableEq ι] in
/-- Timing laws with the same stopping-time pushforward in every coordinate
have exactly the same prescribed payoff. -/
theorem quittingFiniteDeadlineTiming_mixedEU_eq_of_actionTime_map_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι)
    (hmarginal : ∀ player,
      (first player).map quittingFiniteDeadlineTimingActionTime =
        (second player).map quittingFiniteDeadlineTimingActionTime) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        first who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        second who := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu,
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  exact Math.PMFProduct.expect_pmfPi_coordwise_eq_of_maps_eq
    first second (fun _ => quittingFiniteDeadlineTimingActionTime)
    (fun _ => quittingFiniteDeadlineTimingActionTime)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who) hmarginal

omit [DecidableEq ι] in
/-- The successor timing game restricted to included old-deadline actions has
exactly the old timing-game payoff. -/
theorem quittingFiniteDeadlineTiming_mixedEU_include_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.eu
        (quittingFiniteDeadlineTimingProfileInclude mixed) who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        mixed who := by
  letI : Finite
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : Finite
      (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [(quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension_eu,
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  exact Math.PMFProduct.expect_pmfPi_coordwise_eq_of_maps_eq
    (quittingFiniteDeadlineTimingProfileInclude mixed) mixed
    (fun _ => quittingFiniteDeadlineTimingActionTime)
    (fun _ => quittingFiniteDeadlineTimingActionTime)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    (quittingFiniteDeadlineTimingProfileInclude_map_actionTime mixed)

/-- A pure-deviation gain in a finite timing game is Lipschitz in the sum of
the marginal total-variation distances, with the exact factor `4 * bound`. -/
theorem abs_quittingFiniteDeadlineTiming_mixedGain_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |(quittingFiniteDeadlineTimingGame reward deadline).mixedGain
          first who action -
        (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
          second who action| ≤
      4 * bound * ∑ player,
        Math.Probability.pmfTV (first player) (second player) := by
  let game := quittingFiniteDeadlineTimingGame reward deadline
  let updatedFirst := Function.update first who (PMF.pure action)
  let updatedSecond := Function.update second who (PMF.pure action)
  have hsum :
      (∑ player, Math.Probability.pmfTV
          (updatedFirst player) (updatedSecond player)) ≤
        ∑ player, Math.Probability.pmfTV
          (first player) (second player) := by
    apply Finset.sum_le_sum
    intro player _
    by_cases hplayer : player = who
    · subst player
      simpa [updatedFirst, updatedSecond] using
        Math.Probability.pmfTV_nonneg (first who) (second who)
    · simp [updatedFirst, updatedSecond, Function.update_of_ne hplayer]
  have hbase := abs_quittingFiniteDeadlineTiming_mixedEU_sub_le
    reward deadline first second who hbound hreward
  have hupdated := abs_quittingFiniteDeadlineTiming_mixedEU_sub_le
    reward deadline updatedFirst updatedSecond who hbound hreward
  have hupdated' :
      |game.mixedExtension.eu updatedFirst who -
          game.mixedExtension.eu updatedSecond who| ≤
        2 * bound * ∑ player,
          Math.Probability.pmfTV (first player) (second player) :=
    hupdated.trans (mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (by norm_num) hbound))
  unfold KernelGame.mixedGain
  change
    |(game.mixedExtension.eu updatedFirst who -
          game.mixedExtension.eu first who) -
        (game.mixedExtension.eu updatedSecond who -
          game.mixedExtension.eu second who)| ≤ _
  calc
    |(game.mixedExtension.eu updatedFirst who -
          game.mixedExtension.eu first who) -
        (game.mixedExtension.eu updatedSecond who -
          game.mixedExtension.eu second who)| =
        |(game.mixedExtension.eu updatedFirst who -
            game.mixedExtension.eu updatedSecond who) -
          (game.mixedExtension.eu first who -
            game.mixedExtension.eu second who)| := by ring_nf
    _ ≤ |game.mixedExtension.eu updatedFirst who -
          game.mixedExtension.eu updatedSecond who| +
        |game.mixedExtension.eu first who -
          game.mixedExtension.eu second who| := abs_sub _ _
    _ ≤ 2 * bound *
          (∑ player, Math.Probability.pmfTV (first player) (second player)) +
        2 * bound *
          (∑ player, Math.Probability.pmfTV (first player) (second player)) :=
      add_le_add hupdated' hbase
    _ = 4 * bound *
        ∑ player, Math.Probability.pmfTV (first player) (second player) := by ring

/-- Operationally equal stopping-time marginals give exactly equal gains for
every common pure timing action. -/
theorem quittingFiniteDeadlineTiming_mixedGain_eq_of_actionTime_map_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline)
    (hmarginal : ∀ player,
      (first player).map quittingFiniteDeadlineTimingActionTime =
        (second player).map quittingFiniteDeadlineTimingActionTime) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        first who action =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        second who action := by
  have hupdated : ∀ player,
      ((Function.update first who (PMF.pure action)) player).map
          quittingFiniteDeadlineTimingActionTime =
        ((Function.update second who (PMF.pure action)) player).map
          quittingFiniteDeadlineTimingActionTime := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simp
    · simpa [Function.update_of_ne hplayer] using hmarginal player
  have hdeviation := quittingFiniteDeadlineTiming_mixedEU_eq_of_actionTime_map_eq
      reward deadline (Function.update first who (PMF.pure action))
      (Function.update second who (PMF.pure action)) who hupdated
  have hprescribed := quittingFiniteDeadlineTiming_mixedEU_eq_of_actionTime_map_eq
    reward deadline first second who hmarginal
  unfold KernelGame.mixedGain
  convert congrArg₂ (fun x y : ℝ => x - y) hdeviation hprescribed using 1 <;>
    congr 1

/-- Pure-deviation gains of included old-deadline actions are exactly their
old timing-game gains. -/
theorem quittingFiniteDeadlineTiming_mixedGain_include_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline) :
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude mixed) who
        (quittingFiniteDeadlineTimingActionInclude action) =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        mixed who action := by
  have hdeviation := quittingFiniteDeadlineTiming_mixedEU_include_eq
    reward deadline (Function.update mixed who (PMF.pure action)) who
  rw [quittingFiniteDeadlineTimingProfileInclude_update_pure] at hdeviation
  have hprescribed := quittingFiniteDeadlineTiming_mixedEU_include_eq
    reward deadline mixed who
  unfold KernelGame.mixedGain
  convert congrArg₂ (fun x y : ℝ => x - y) hdeviation hprescribed using 1 <;>
    congr 1

/-- Exact projective compatibility: if the literal inclusion of an old timing
law is Nash in the successor game, then the old law was already Nash at its
original deadline.  The converse is not asserted because of the new boundary
action. -/
theorem quittingFiniteDeadlineTiming_isNash_of_include_isNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.IsNash
        (quittingFiniteDeadlineTimingProfileInclude mixed)) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      mixed := by
  rw [(quittingFiniteDeadlineTimingGame reward deadline).isNash_iff_gains_nonpos]
  rw [(quittingFiniteDeadlineTimingGame reward
      (deadline + 1)).isNash_iff_gains_nonpos] at hnash
  intro who action
  rw [← quittingFiniteDeadlineTiming_mixedGain_include_eq
    reward deadline mixed who action]
  exact hnash who (quittingFiniteDeadlineTimingActionInclude action)

/-- For a finite timing Nash law, unrestricted semantic debt is literally
the positive part of its gain from the new boundary action in the successor
timing game. -/
theorem quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      mixed)
    (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)) who =
      max 0
        ((quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          (quittingFiniteDeadlineTimingProfileInclude mixed) who
          (quittingFiniteDeadlineTimingBoundaryAction deadline)) := by
  let certificate := quittingFiniteDeadlineTimingProfile_isFiniteDeadline
    reward deadline mixed hnash
  rw [certificate.semanticDebt_eq_boundaryGain_pospart who]
  congr 1
  rw [← quittingFiniteDeadlineTimingProfile_include_eq reward deadline mixed]
  have hdeviation :=
    quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
      reward (deadline + 1) (quittingFiniteDeadlineTimingProfileInclude mixed)
      who (quittingFiniteDeadlineTimingBoundaryAction deadline)
  have hprescribed :=
    quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward (deadline + 1) (quittingFiniteDeadlineTimingProfileInclude mixed) who
  change quittingTerminalPayoff reward
      (Function.update
        (quittingFiniteDeadlineTimingProfile reward (deadline + 1)
          (quittingFiniteDeadlineTimingProfileInclude mixed)) who
        (quittingPureTimeBehaviorStrategy reward who (some deadline))) who = _
    at hdeviation
  unfold quittingFiniteDeadlineBoundaryPayoff KernelGame.mixedGain
  linarith

/-- If a common pure action has different gain under two timing laws, at least
one participant has a different operational stopping-time law. -/
theorem exists_actionTime_map_ne_of_mixedGain_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline)
    (hgain :
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
          first who action ≠
        (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
          second who action) :
    ∃ player,
      (first player).map quittingFiniteDeadlineTimingActionTime ≠
        (second player).map quittingFiniteDeadlineTimingActionTime := by
  by_contra hnone
  simp only [not_exists, not_not] at hnone
  exact hgain
    (quittingFiniteDeadlineTiming_mixedGain_eq_of_actionTime_map_eq
      reward deadline first second who action hnone)

/-- At adjacent deadlines, the old law's gain from the new boundary action is
within `4 * bound` times the adjacent marginal TV distance of the same gain in
the new law. -/
theorem abs_quittingFiniteDeadlineTiming_boundaryGain_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |(quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          (quittingFiniteDeadlineTimingProfileInclude old) who
          (quittingFiniteDeadlineTimingBoundaryAction deadline) -
        (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          new who (quittingFiniteDeadlineTimingBoundaryAction deadline)| ≤
      4 * bound * quittingFiniteDeadlineAdjacentTV deadline old new := by
  exact abs_quittingFiniteDeadlineTiming_mixedGain_sub_le reward (deadline + 1)
    (quittingFiniteDeadlineTimingProfileInclude old) new who
    (quittingFiniteDeadlineTimingBoundaryAction deadline) hbound hreward

/-- If the successor law is Nash, then the old law's gain from quitting at the
new boundary is controlled by its adjacent marginal TV distance to that law. -/
theorem quittingFiniteDeadlineTiming_boundaryGain_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (hnash :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.IsNash
        new)
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude old) who
        (quittingFiniteDeadlineTimingBoundaryAction deadline) ≤
      4 * bound * quittingFiniteDeadlineAdjacentTV deadline old new := by
  have htv := abs_quittingFiniteDeadlineTiming_boundaryGain_sub_le
    reward deadline old new who hbound hreward
  have hnashGain :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
          new who (quittingFiniteDeadlineTimingBoundaryAction deadline) ≤ 0 :=
    ((quittingFiniteDeadlineTimingGame reward (deadline + 1)).isNash_iff_gains_nonpos
      new).mp hnash who
        (quittingFiniteDeadlineTimingBoundaryAction deadline)
  exact le_trans (sub_le_iff_le_add.mp (le_abs_self
    ((quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
      (quittingFiniteDeadlineTimingProfileInclude old) who
        (quittingFiniteDeadlineTimingBoundaryAction deadline) -
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedGain
        new who (quittingFiniteDeadlineTimingBoundaryAction deadline))))
    (by linarith)

/-- Exact consecutive-Nash projective estimate: semantic debt of the old
finite-deadline realization is bounded by `4 * bound` times the sum of
adjacent marginal total-variation distances. -/
theorem quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (holdNash :
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash old)
    (hnewNash :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.IsNash
        new)
    (who : ι) {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline old)) who ≤
      4 * bound * quittingFiniteDeadlineAdjacentTV deadline old new := by
  rw [quittingFiniteDeadlineTimingProfile_semanticDebt_eq_boundaryGain_pospart
    reward deadline old holdNash who]
  apply max_le
  · exact mul_nonneg (mul_nonneg (by norm_num) hbound)
      (Finset.sum_nonneg fun player _ =>
        Math.Probability.pmfTV_nonneg
          (quittingFiniteDeadlineTimingProfileInclude old player) (new player))
  · exact quittingFiniteDeadlineTiming_boundaryGain_le reward deadline old new
      hnewNash who hbound hreward

/-- A supplied positive semantic-debt floor forces quantitative separation of
every consecutive pair of finite timing Nash laws. -/
theorem quittingFiniteDeadlineAdjacentTV_ge_div_of_semanticDebt_ge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (holdNash :
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash old)
    (hnewNash :
      (quittingFiniteDeadlineTimingGame reward (deadline + 1)).mixedExtension.IsNash
        new)
    (who : ι) {bound gap : ℝ} (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hgap : gap ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline old)) who) :
    gap / (4 * bound) ≤
      quittingFiniteDeadlineAdjacentTV deadline old new := by
  rw [div_le_iff₀ (mul_pos (by norm_num) hbound)]
  simpa only [mul_comm] using hgap.trans
    (quittingFiniteDeadlineTimingProfile_semanticDebt_le_adjacentTV
      reward deadline old new holdNash hnewNash who hbound.le hreward)

end GameTheory
