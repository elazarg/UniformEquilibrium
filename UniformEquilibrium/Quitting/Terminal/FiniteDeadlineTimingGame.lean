/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization
import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed

/-!
# Finite-deadline quitting timing games

This module owns the common finite timing-game encoding. A pure action is a
date below a fixed deadline or Never. Mixed timing laws are mapped to literal
stopping laws and then to behavioral quitting profiles.

The payoff and pure-deviation adapters identify the normal-form timing game
with that behavioral realization, including the literal all-Continue suffix
at and after the deadline.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Planned action in a finite hard-tail timing game: a date below the
deadline, or Never. -/
abbrev QuittingFiniteDeadlineTimingAction (deadline : ℕ) :=
  Option (Fin deadline)

/-- Read a finite timing action as a complete stopping time. -/
def quittingFiniteDeadlineTimingActionTime {deadline : ℕ} :
    QuittingFiniteDeadlineTimingAction deadline →
      Math.Probability.CompactStoppingTime
  | none => (⊤ : WithTop ℕ)
  | some time => WithTop.some time.val

/-- The finite strategic-form timing game whose pure payoffs are the literal
deterministic stopping-profile payoffs. -/
abbrev quittingFiniteDeadlineTimingGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => QuittingFiniteDeadlineTimingAction deadline)
    (fun choices who => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward fun player =>
        quittingFiniteDeadlineTimingActionTime (choices player)) who)

/-- The direct finite timing game has a finite outcome carrier. -/
instance quittingFiniteDeadlineTimingGame_finiteOutcome
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ) :
    Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
  unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
  infer_instance

/-- Complete stopping law obtained by mapping a mixed finite timing action to
its literal date or Never. -/
def quittingFiniteDeadlineTimingLaw {deadline : ℕ}
    (mixed : PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    Math.Probability.CompactStoppingLaw :=
  Math.Probability.CompactStoppingLaw.ofPMF
    (mixed.map quittingFiniteDeadlineTimingActionTime)

/-- Literal behavioral-hazard realization of independent finite timing laws. -/
def quittingFiniteDeadlineTimingProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (quittingGame reward).BehaviorProfile :=
  quittingCompactStoppingLawProfile reward fun who =>
    quittingFiniteDeadlineTimingLaw (mixed who)

/-- The behavioral realization has the same prescribed payoff as the mixed
extension of the finite timing game. -/
theorem quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        mixed who := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  rw [quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_compactStoppingLawProfile_eq_expect,
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension_eu]
  simp only [quittingFiniteDeadlineTimingLaw,
    Math.Probability.CompactStoppingLaw.toPMF_ofPMF,
    quittingFiniteDeadlineTimingGame, KernelGame.eu_ofPureEU]
  calc
    Math.Probability.expect
          (Math.PMFProduct.pmfPi fun player =>
            (mixed player).map quittingFiniteDeadlineTimingActionTime)
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) who) =
        Math.Probability.expect
          ((Math.PMFProduct.pmfPi mixed).map fun choices player =>
            quittingFiniteDeadlineTimingActionTime (choices player))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) who) := by
      congr 1
      exact (Math.PMFProduct.pmfPi_push_coordwise mixed
        (fun _ => quittingFiniteDeadlineTimingActionTime)).symm
    _ = _ := by
      rw [Math.Probability.expect_map]
      rfl

/-- Replacing one timing coordinate by a pure date or Never has the same
payoff as the corresponding pure-time behavioral deviation. -/
theorem quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (action : QuittingFiniteDeadlineTimingAction deadline) :
    quittingTerminalPayoff reward
        (Function.update
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
          (quittingPureTimeBehaviorStrategy reward who
            (quittingFiniteDeadlineTimingActionTime action))) who =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        (Function.update mixed who (PMF.pure action)) who := by
  rw [quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
    ← quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
    quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_compactStoppingLawProfile_eq_expect]
  congr 1
  apply congrArg Math.PMFProduct.pmfPi
  funext player
  by_cases hplayer : player = who
  · subst player
    rw [quittingPureDeviationCompactLaws, if_pos rfl,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF,
      Function.update_self, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    exact (PMF.pure_map quittingFiniteDeadlineTimingActionTime action).symm
  · rw [quittingPureDeviationCompactLaws, if_neg hplayer,
      quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF,
      Function.update_of_ne hplayer, quittingFiniteDeadlineTimingLaw,
      Math.Probability.CompactStoppingLaw.toPMF_ofPMF]

/-- A finite timing law has no atom at or after its deadline. -/
theorem quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
    {deadline : ℕ}
    (mixed : PMF (QuittingFiniteDeadlineTimingAction deadline))
    {time : ℕ} (htime : deadline ≤ time) :
    (quittingFiniteDeadlineTimingLaw mixed).toPMF (WithTop.some time) = 0 := by
  rw [quittingFiniteDeadlineTimingLaw,
    Math.Probability.CompactStoppingLaw.toPMF_ofPMF, PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro action
  split
  · next heq =>
      cases action with
      | none => simp [quittingFiniteDeadlineTimingActionTime] at heq
      | some finiteTime =>
          have hval : time = finiteTime.val := by
            exact Option.some.inj heq
          have hfiniteTime := finiteTime.isLt
          omega
  · rfl

omit [DecidableEq ι] in
/-- The behavioral realization is all-Continue from its deadline onward. -/
theorem quittingFiniteDeadlineTimingProfile_liveRoot_eq_allContinue_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    {time : ℕ} (htime : deadline ≤ time) :
    quittingProfileLiveRoot reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) time =
      quittingAllContinueRoot := by
  funext who
  have hfinite : Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
      (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF time = 0 := by
    unfold Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
    change ((quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
      (WithTop.some time)).toReal = 0
    rw [quittingFiniteDeadlineTimingLaw_some_eq_zero_of_le
      (mixed who) htime]
    rfl
  change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
    (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF).toBoolean time =
      PMF.pure false
  apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
  simp [Math.Probability.DiscreteHazard.ScalarHazard.toBoolean,
    Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard, hfinite]

end GameTheory

