/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FinFourHardDeadlineTimingNashBarrier
import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineTimingRecursion
import UniformEquilibrium.Diagnostics.FiniteMixedNashSupport

/-!
# Uniqueness of the Fin4 hard-deadline timing Nash law

This file supplies the conditioning infrastructure needed to prove that the
hard-deadline timing Nash law of the concrete Fin4 table is unique.  The key
distinction from rootwise uniqueness is that an arbitrary normal-form law may
correlate a player's current action with its planned later stopping time.  We
therefore split each marginal law into its current atom and its conditional
shifted tail before applying backward induction.
-/

noncomputable section

namespace GameTheory
namespace FinFourHardDeadlineTimingNashBarrier

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

/-! ## Table-specific elimination of current boundary actions -/

theorem rootExpectedPayoff_update_true_two
    (root : Player → PMF Bool) (continuation : Payoff Player) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (2 : Player) (PMF.pure true)) 2 = -1 := by
  have hzero := Math.Probability.pmf_toReal_sum_one (root 0)
  have hone := Math.Probability.pmf_toReal_sum_one (root 1)
  have hthree := Math.Probability.pmf_toReal_sum_one (root 3)
  simp only [Fintype.sum_bool] at hzero hone hthree
  have hzero' : ((root 0) false).toReal = 1 - ((root 0) true).toReal := by
    linarith
  have hone' : ((root 1) false).toReal = 1 - ((root 1) true).toReal := by
    linarith
  have hthree' : ((root 3) false).toReal = 1 - ((root 3) true).toReal := by
    linarith
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  rw [hzero', hone', hthree']
  ring

theorem rootExpectedPayoff_update_true_three
    (root : Player → PMF Bool) (continuation : Payoff Player) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (3 : Player) (PMF.pure true)) 3 = -1 := by
  have hzero := Math.Probability.pmf_toReal_sum_one (root 0)
  have hone := Math.Probability.pmf_toReal_sum_one (root 1)
  have htwo := Math.Probability.pmf_toReal_sum_one (root 2)
  simp only [Fintype.sum_bool] at hzero hone htwo
  have hzero' : ((root 0) false).toReal = 1 - ((root 0) true).toReal := by
    linarith
  have hone' : ((root 1) false).toReal = 1 - ((root 1) true).toReal := by
    linarith
  have htwo' : ((root 2) false).toReal = 1 - ((root 2) true).toReal := by
    linarith
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum]
  rw [hzero', hone', htwo']
  ring

theorem rootExpectedPayoff_update_false_two
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hcontinuation : continuation 2 = 0) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (2 : Player) (PMF.pure false)) 2 = 0 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum, hcontinuation]

theorem rootExpectedPayoff_update_false_three
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hcontinuation : continuation 3 = 0) :
    quittingRootExpectedPayoff reward continuation
        (Function.update root (3 : Player) (PMF.pure false)) 3 = 0 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [reward, quittingRootPayoff, quittingQuitters,
    Math.Probability.expect_eq_sum, hcontinuation]

theorem timingMixedPayoff_update_current_two
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    timingMixedPayoff reward (dates + 1)
        (Function.update mixed (2 : Player)
          (PMF.pure (some (0 : Fin (dates + 1))))) 2 = -1 := by
  rw [timingMixedPayoff_bellman reward]
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed (2 : Player)
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        (2 : Player) (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 2
    · subst player
      rw [Function.update_self]
      unfold pushforward
      rw [PMF.pure_map, Function.update_self]
      have hcurrent : timingActionCurrent
          (some (0 : Fin (dates + 1))) = true := by
        simp [timingActionCurrent]
      rw [hcurrent]
    · simp [Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_update_true_two]

theorem timingMixedPayoff_update_current_three
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) :
    timingMixedPayoff reward (dates + 1)
        (Function.update mixed (3 : Player)
          (PMF.pure (some (0 : Fin (dates + 1))))) 3 = -1 := by
  rw [timingMixedPayoff_bellman reward]
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed (3 : Player)
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update
        (fun player ↦ pushforward (mixed player) timingActionCurrent)
        (3 : Player) (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 3
    · subst player
      rw [Function.update_self]
      unfold pushforward
      rw [PMF.pure_map, Function.update_self]
      have hcurrent : timingActionCurrent
          (some (0 : Fin (dates + 1))) = true := by
        simp [timingActionCurrent]
      rw [hcurrent]
    · simp [Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_update_true_three]

theorem timingMixedPayoff_zero
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction 0))
    (who : Player) :
    timingMixedPayoff reward 0 mixed who = 0 := by
  unfold timingMixedPayoff
  calc
    Math.Probability.expect (pmfPi mixed)
        (fun choices ↦ timingPurePayoff reward 0 choices who) =
      Math.Probability.expect (pmfPi mixed) (fun _ ↦ 0) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro choices _
        have hchoices : choices = fun _ ↦ none := by
          funext player
          cases hchoice : choices player with
          | none => rfl
          | some impossible => exact Fin.elim0 impossible
        subst choices
        unfold timingPurePayoff
        have hprofile :
            quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤) =
              quittingAlwaysContinueProfile reward := by
          funext player time history
          simp [quittingPureStoppingTimeProfile,
            quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
            quittingAlwaysContinueProfile,
            StochasticGame.stationaryBehaviorProfile]
          rfl
        change quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤)) who = 0
        rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]
    _ = 0 := Math.Probability.expect_const (pmfPi mixed) 0

@[simp] theorem timingLawTail_pure_none {dates : ℕ} :
    timingLawTail
        (PMF.pure none :
          PMF (QuittingFiniteDeadlineTimingAction (dates + 1))) =
      (PMF.pure none : PMF (QuittingFiniteDeadlineTimingAction dates)) := by
  let law : PMF (QuittingFiniteDeadlineTimingAction (dates + 1)) :=
    PMF.pure none
  have hcontinue : pushforward law timingActionCurrent false ≠ 0 := by
    unfold law pushforward
    rw [PMF.pure_map]
    simp [timingActionCurrent]
  have hcond : condOn law timingActionCurrent false = law := by
    apply PMF.ext
    intro action
    rw [condOn_apply law timingActionCurrent false action hcontinue]
    cases action with
    | none =>
        unfold pushforward law
        rw [PMF.pure_map]
        simp [timingActionCurrent]
    | some time => simp [law]
  have hlift := timingLawTail_map_lift law hcontinue
  rw [hcond] at hlift
  have hmapped := congrArg (fun source ↦ source.map timingActionTail) hlift
  have hcomp :
      (timingActionTail (dates := dates)) ∘
          (timingActionLift (dates := dates)) =
        (id : QuittingFiniteDeadlineTimingAction dates →
          QuittingFiniteDeadlineTimingAction dates) := by
    funext action
    exact timingActionTail_lift action
  rw [PMF.map_comp, hcomp, PMF.map_id] at hmapped
  dsimp only [law] at hmapped
  simpa only [PMF.pure_map, timingActionTail] using hmapped

/-- A dummy player who deterministically never stops has zero payoff in every
finite timing game. -/
theorem timingMixedPayoff_update_never_two :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      timingMixedPayoff reward dates
        (Function.update mixed (2 : Player) (PMF.pure none)) 2 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro mixed
      exact timingMixedPayoff_zero _ 2
  | succ dates ih =>
      intro mixed
      rw [timingMixedPayoff_bellman reward]
      have hroot :
          (fun player ↦ pushforward
              (Function.update mixed (2 : Player) (PMF.pure none) player)
              timingActionCurrent) =
            Function.update
              (fun player ↦ pushforward (mixed player) timingActionCurrent)
              (2 : Player) (PMF.pure false) := by
        funext player
        by_cases hplayer : player = 2
        · subst player
          rw [Function.update_self, Function.update_self]
          unfold pushforward
          rw [PMF.pure_map]
          rfl
        · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      have htail :
          (fun player ↦ timingLawTail
              (Function.update mixed (2 : Player) (PMF.pure none) player)) =
            Function.update (fun player ↦ timingLawTail (mixed player))
              (2 : Player) (PMF.pure none) := by
        rw [timingLawTail_update, timingLawTail_pure_none]
      rw [hroot, htail, rootExpectedPayoff_update_false_two]
      exact ih _

/-- The second dummy coordinate has the same exact zero-payoff Never
certificate. -/
theorem timingMixedPayoff_update_never_three :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      timingMixedPayoff reward dates
        (Function.update mixed (3 : Player) (PMF.pure none)) 3 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro mixed
      exact timingMixedPayoff_zero _ 3
  | succ dates ih =>
      intro mixed
      rw [timingMixedPayoff_bellman reward]
      have hroot :
          (fun player ↦ pushforward
              (Function.update mixed (3 : Player) (PMF.pure none) player)
              timingActionCurrent) =
            Function.update
              (fun player ↦ pushforward (mixed player) timingActionCurrent)
              (3 : Player) (PMF.pure false) := by
        funext player
        by_cases hplayer : player = 3
        · subst player
          rw [Function.update_self, Function.update_self]
          unfold pushforward
          rw [PMF.pure_map]
          rfl
        · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
      have htail :
          (fun player ↦ timingLawTail
              (Function.update mixed (3 : Player) (PMF.pure none) player)) =
            Function.update (fun player ↦ timingLawTail (mixed player))
              (3 : Player) (PMF.pure none) := by
        rw [timingLawTail_update, timingLawTail_pure_none]
      rw [hroot, htail, rootExpectedPayoff_update_false_three]
      exact ih _

/-- In every positive-deadline Nash law, the first dummy player puts no mass
on the current stopping action. -/
theorem dummyTwo_current_eq_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    mixed 2 (some (0 : Fin (dates + 1))) = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hcurrent
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash 2
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_two] at hgain
  have hnever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 2 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_two] at hnever
  linarith

/-- The second dummy player likewise puts no mass on the current stopping
action in any positive-deadline Nash law. -/
theorem dummyThree_current_eq_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    mixed 3 (some (0 : Fin (dates + 1))) = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hcurrent
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash 3
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_three] at hgain
  have hnever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 3 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_three] at hnever
  linarith

/-- The first dummy's complete current Boolean marginal is deterministic
Continue. -/
theorem dummyTwo_currentLaw_eq_pure_false
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    pushforward (mixed 2) timingActionCurrent = PMF.pure false := by
  apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
  rw [timingActionCurrent_pushforward_true]
  have hzero :
      (some ⟨0, Nat.zero_lt_succ dates⟩ :
        QuittingFiniteDeadlineTimingAction (dates + 1)) =
        some (0 : Fin (dates + 1)) := by
    congr
  rw [hzero, dummyTwo_current_eq_zero dates mixed hnash]
  rfl

/-- The second dummy's complete current Boolean marginal is deterministic
Continue. -/
theorem dummyThree_currentLaw_eq_pure_false
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    pushforward (mixed 3) timingActionCurrent = PMF.pure false := by
  apply Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero
  rw [timingActionCurrent_pushforward_true]
  have hzero :
      (some ⟨0, Nat.zero_lt_succ dates⟩ :
        QuittingFiniteDeadlineTimingAction (dates + 1)) =
        some (0 : Fin (dates + 1)) := by
    congr
  rw [hzero, dummyThree_current_eq_zero dates mixed hnash]
  rfl

/-! ## The two active sure-current corners -/

theorem rootExpectedPayoff_one_of_zero_sure
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hzero : root 0 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 1 =
      -1 + (root 1 true).toReal := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hzero, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

theorem rootExpectedPayoff_zero_of_one_sure
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hone : root 1 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 0 =
      1 - (root 0 true).toReal := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hone, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]

/-- Under a sure current stop by player `0`, player `1`'s full timing payoff
depends only on its own current mass. -/
theorem timingMixedPayoff_one_of_zero_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff reward (dates + 1) mixed 1 =
      -1 + (pushforward (mixed 1) timingActionCurrent true).toReal := by
  rw [timingMixedPayoff_bellman reward]
  exact rootExpectedPayoff_one_of_zero_sure _ _ hzero htwo hthree

/-- Against a sure current stop by player `0`, stopping now gives player `1`
the collision payoff zero. -/
theorem timingMixedPayoff_update_current_one_of_zero_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff reward (dates + 1)
      (Function.update mixed 1
        (PMF.pure (some (0 : Fin (dates + 1))))) 1 = 0 := by
  rw [timingMixedPayoff_bellman reward]
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed 1
          (PMF.pure (some (0 : Fin (dates + 1)))) player)
        timingActionCurrent) =
      Function.update root 1 (PMF.pure true) := by
    funext player
    by_cases hplayer : player = 1
    · subst player
      rw [Function.update_self, Function.update_self]
      unfold pushforward
      rw [PMF.pure_map]
      rfl
    · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_one_of_zero_sure]
  · simp
  · simpa only [root, Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
      using hzero
  · simpa only [root, Function.update_of_ne (by decide : (2 : Player) ≠ 1)]
      using htwo
  · simpa only [root, Function.update_of_ne (by decide : (3 : Player) ≠ 1)]
      using hthree

/-- Under a sure current stop by player `1`, player `0` gets one precisely
when it continues at the current root. -/
theorem timingMixedPayoff_zero_of_one_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff reward (dates + 1) mixed 0 =
      1 - (pushforward (mixed 0) timingActionCurrent true).toReal := by
  rw [timingMixedPayoff_bellman reward]
  exact rootExpectedPayoff_zero_of_one_sure _ _ hone htwo hthree

/-- Against player `1` stopping now surely, player `0` gets one by Never. -/
theorem timingMixedPayoff_update_never_zero_of_one_current_sure
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff reward (dates + 1)
      (Function.update mixed 0 (PMF.pure none)) 0 = 1 := by
  rw [timingMixedPayoff_bellman reward]
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have hroot :
      (fun player ↦ pushforward
        (Function.update mixed 0 (PMF.pure none) player)
        timingActionCurrent) =
      Function.update root 0 (PMF.pure false) := by
    funext player
    by_cases hplayer : player = 0
    · subst player
      rw [Function.update_self, Function.update_self]
      unfold pushforward
      rw [PMF.pure_map]
      rfl
    · rw [Function.update_of_ne hplayer, Function.update_of_ne hplayer]
  rw [hroot, rootExpectedPayoff_zero_of_one_sure]
  · simp
  · simpa only [root, Function.update_of_ne (by decide : (1 : Player) ≠ 0)]
      using hone
  · simpa only [root, Function.update_of_ne (by decide : (2 : Player) ≠ 0)]
      using htwo
  · simpa only [root, Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
      using hthree

/-- Player `0` cannot stop surely at the current date in a positive-deadline
mixed Nash law. -/
theorem zero_currentMass_lt_one
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    (mixed 0 (some (0 : Fin (dates + 1)))).toReal < 1 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hnot
  have hle : (mixed 0 (some (0 : Fin (dates + 1)))).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (mixed 0) (some (0 : Fin (dates + 1))))
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have honeMass :
      (mixed 0 (some (0 : Fin (dates + 1)))).toReal = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have hzeroCurrent :
      pushforward (mixed 0) timingActionCurrent = PMF.pure true := by
    apply Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one
    rw [timingActionCurrent_pushforward_true]
    have hzero :
        (some ⟨0, Nat.zero_lt_succ dates⟩ :
          QuittingFiniteDeadlineTimingAction (dates + 1)) =
          some (0 : Fin (dates + 1)) := by
      congr
    rw [hzero, honeMass]
  have htwo := dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree := dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hgainOne :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 1
        (some (0 : Fin (dates + 1)))
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_one_of_zero_current_sure
      dates mixed hzeroCurrent htwo hthree,
    timingMixedPayoff_one_of_zero_current_sure
      dates mixed hzeroCurrent htwo hthree] at hgainOne
  have hqLe :
      (pushforward (mixed 1) timingActionCurrent true).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (pushforward (mixed 1) timingActionCurrent) true)
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have hqOne :
      (pushforward (mixed 1) timingActionCurrent true).toReal = 1 := by
    linarith
  have honeCurrent :
      pushforward (mixed 1) timingActionCurrent = PMF.pure true :=
    Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one _ hqOne
  have hgainNever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 0 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    timingMixedPayoff_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    hzeroCurrent] at hgainNever
  norm_num at hgainNever

/-! ### The finite-law collision deviation at player `1`'s sure corner -/

theorem timingPurePayoff_zero_dates
    (choices : Player → QuittingFiniteDeadlineTimingAction 0)
    (who : Player) :
    timingPurePayoff reward 0 choices who = 0 := by
  have hchoices : choices = fun _ ↦ none := by
    funext player
    cases hchoice : choices player with
    | none => rfl
    | some impossible => exact Fin.elim0 impossible
  subst choices
  unfold timingPurePayoff
  have hprofile :
      quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤) =
        quittingAlwaysContinueProfile reward := by
    funext player time history
    simp [quittingPureStoppingTimeProfile,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard,
      quittingAlwaysContinueProfile,
      StochasticGame.stationaryBehaviorProfile]
    rfl
  change quittingTerminalPayoff reward
    (quittingPureStoppingTimeProfile reward (fun _ : Player ↦ ⊤)) who = 0
  rw [hprofile, quittingTerminalPayoff_quittingAlwaysContinue]

/-- Player `1`'s pure payoff in this table is always either zero or minus
one, irrespective of the dummy players' timing actions. -/
theorem timingPurePayoff_one_eq_zero_or_neg_one :
    ∀ (dates : ℕ)
      (choices : Player → QuittingFiniteDeadlineTimingAction dates),
      timingPurePayoff reward dates choices 1 = 0 ∨
        timingPurePayoff reward dates choices 1 = -1 := by
  intro dates
  induction dates with
  | zero =>
      intro choices
      left
      exact timingPurePayoff_zero_dates choices 1
  | succ dates ih =>
      intro choices
      rw [timingPurePayoff_succ]
      by_cases hquit :
          (quittingQuitters (fun player ↦
            timingActionCurrent (choices player))).Nonempty
      · unfold quittingRootPayoff
        simp only [dif_pos hquit]
        simp only [reward_one]
        split_ifs <;> simp
      · unfold quittingRootPayoff
        simp only [dif_neg hquit]
        exact ih (timingChoicesTail choices)

/-- If the two active players select the same timing action, player `1`'s
pure payoff is zero, even when a dummy player stops earlier. -/
theorem timingPurePayoff_one_eq_zero_of_active_eq :
    ∀ (dates : ℕ)
      (choices : Player → QuittingFiniteDeadlineTimingAction dates),
      choices 0 = choices 1 → timingPurePayoff reward dates choices 1 = 0 := by
  intro dates
  induction dates with
  | zero =>
      intro choices _
      exact timingPurePayoff_zero_dates choices 1
  | succ dates ih =>
      intro choices heq
      rw [timingPurePayoff_succ]
      have hcurrent :
          timingActionCurrent (choices 0) =
            timingActionCurrent (choices 1) :=
        congrArg timingActionCurrent heq
      have htail :
          timingChoicesTail choices 0 = timingChoicesTail choices 1 :=
        congrArg timingActionTail heq
      by_cases hquit :
          (quittingQuitters (fun player ↦
            timingActionCurrent (choices player))).Nonempty
      · unfold quittingRootPayoff
        simp only [dif_pos hquit]
        simp only [reward_one]
        rw [if_pos]
        simp [quittingQuitters, hcurrent]
      · unfold quittingRootPayoff
        simp only [dif_neg hquit]
        exact ih (timingChoicesTail choices) htail

/-- A pure deviation by player `1` to an action used by player `0` improves
the pointwise floor from `-1` to `0` on the matching atom. -/
theorem timingPurePayoff_one_ge_matching_floor
    (dates : ℕ)
    (choices : Player → QuittingFiniteDeadlineTimingAction dates)
    (action : QuittingFiniteDeadlineTimingAction dates)
    (hone : choices 1 = action) :
    (if choices 0 = action then 0 else -1) ≤
      timingPurePayoff reward dates choices 1 := by
  by_cases hzero : choices 0 = action
  · rw [if_pos hzero,
      timingPurePayoff_one_eq_zero_of_active_eq dates choices
        (hzero.trans hone.symm)]
  · rw [if_neg hzero]
    rcases timingPurePayoff_one_eq_zero_or_neg_one dates choices with
      hpayoff | hpayoff
    · rw [hpayoff]
      norm_num
    · rw [hpayoff]

/-- The payoff from copying any positive-mass timing action of player `0` is
at least `-1` plus that atom's mass. -/
theorem timingMixedPayoff_update_one_ge_neg_one_add_atom
    (dates : ℕ)
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (action : QuittingFiniteDeadlineTimingAction dates) :
    -1 + (mixed 0 action).toReal ≤
      timingMixedPayoff reward dates
        (Function.update mixed 1 (PMF.pure action)) 1 := by
  let updated := Function.update mixed 1 (PMF.pure action)
  let joint := pmfPi updated
  let floor :
      (Player → QuittingFiniteDeadlineTimingAction dates) → ℝ :=
    fun choices ↦ if choices 0 = action then 0 else -1
  have hmono : Math.Probability.expect joint floor ≤
      Math.Probability.expect joint
        (fun choices ↦ timingPurePayoff reward dates choices 1) := by
    apply Math.ProbabilityMassFunction.expect_mono_on_support
    intro choices hchoices
    have hmass : joint choices ≠ 0 := by
      simpa only [PMF.mem_support_iff] using hchoices
    have honeMass := pmfPi_coord_ne_zero_of_ne_zero
      updated choices hmass 1
    have hone : choices 1 = action := by
      unfold updated at honeMass
      rw [Function.update_self] at honeMass
      by_contra hne
      rw [PMF.pure_apply_of_ne action (choices 1) hne] at honeMass
      exact honeMass rfl
    exact timingPurePayoff_one_ge_matching_floor dates choices action hone
  have hcoord :
      pushforward joint (fun choices ↦ choices 0) = mixed 0 := by
    unfold joint
    rw [pmfPi_push_coord]
    unfold updated
    rw [Function.update_of_ne (by decide : (0 : Player) ≠ 1)]
  have hfloor : Math.Probability.expect joint floor =
      -1 + (mixed 0 action).toReal := by
    calc
      Math.Probability.expect joint floor =
          Math.Probability.expect
            (pushforward joint fun choices ↦ choices 0)
            (fun choice ↦ if choice = action then 0 else -1) := by
              unfold pushforward floor
              exact (Math.Probability.expect_map
                (fun choices ↦ choices 0) joint
                (fun choice ↦ if choice = action then 0 else -1)).symm
      _ = Math.Probability.expect (mixed 0)
          (fun choice ↦ if choice = action then 0 else -1) := by
            rw [hcoord]
      _ = Math.Probability.expect (mixed 0)
          (fun choice ↦ (if choice = action then 1 else 0) - 1) := by
            congr 1
            funext choice
            split_ifs <;> ring
      _ = (mixed 0 action).toReal - 1 := by
            rw [Math.Probability.expect_sub,
              Math.Probability.apply_toReal_eq_expect_indicator,
              Math.Probability.expect_const]
      _ = -1 + (mixed 0 action).toReal := by ring
  rw [hfloor] at hmono
  exact hmono

theorem rootExpectedPayoff_one_of_one_sure_zero_continue
    (root : Player → PMF Bool) (continuation : Payoff Player)
    (hzero : root 0 = PMF.pure false)
    (hone : root 1 = PMF.pure true)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootExpectedPayoff reward continuation root 1 = -1 := by
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  simp [hzero, hone, htwo, hthree, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]

theorem timingMixedPayoff_one_of_one_current_sure_zero_continue
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hzero : pushforward (mixed 0) timingActionCurrent = PMF.pure false)
    (hone : pushforward (mixed 1) timingActionCurrent = PMF.pure true)
    (htwo : pushforward (mixed 2) timingActionCurrent = PMF.pure false)
    (hthree : pushforward (mixed 3) timingActionCurrent = PMF.pure false) :
    timingMixedPayoff reward (dates + 1) mixed 1 = -1 := by
  rw [timingMixedPayoff_bellman reward]
  exact rootExpectedPayoff_one_of_one_sure_zero_continue
    _ _ hzero hone htwo hthree

/-- Player `1` also cannot stop surely at the current date in a
positive-deadline mixed Nash law. The decisive deviation copies one
positive-mass timing atom of player `0`. -/
theorem one_currentMass_lt_one
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    (mixed 1 (some (0 : Fin (dates + 1)))).toReal < 1 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  by_contra hnot
  have hle : (mixed 1 (some (0 : Fin (dates + 1)))).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal
      (PMF.apply_ne_top (mixed 1) (some (0 : Fin (dates + 1))))
      (by norm_num)).2 (PMF.coe_le_one _ _)
  have honeMass :
      (mixed 1 (some (0 : Fin (dates + 1)))).toReal = 1 :=
    le_antisymm hle (le_of_not_gt hnot)
  have honeCurrent :
      pushforward (mixed 1) timingActionCurrent = PMF.pure true := by
    apply Math.PMFProduct.eq_pure_true_of_true_toReal_eq_one
    rw [timingActionCurrent_pushforward_true]
    have hzero :
        (some ⟨0, Nat.zero_lt_succ dates⟩ :
          QuittingFiniteDeadlineTimingAction (dates + 1)) =
          some (0 : Fin (dates + 1)) := by
      congr
    rw [hzero, honeMass]
  have htwo := dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree := dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hgainNever :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 0 none
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_never_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree,
    timingMixedPayoff_zero_of_one_current_sure
      dates mixed honeCurrent htwo hthree] at hgainNever
  have hpNonneg : 0 ≤
      (pushforward (mixed 0) timingActionCurrent true).toReal :=
    ENNReal.toReal_nonneg
  have hpZero :
      (pushforward (mixed 0) timingActionCurrent true).toReal = 0 := by
    linarith
  have hzeroCurrent :
      pushforward (mixed 0) timingActionCurrent = PMF.pure false :=
    Math.PMFProduct.eq_pure_false_of_true_toReal_eq_zero _ hpZero
  obtain ⟨action, hactionSupport⟩ := (mixed 0).support_nonempty
  have haction : mixed 0 action ≠ 0 := by
    simpa only [PMF.mem_support_iff] using hactionSupport
  have hactionPos : 0 < (mixed 0 action).toReal :=
    ENNReal.toReal_pos haction (PMF.apply_ne_top (mixed 0) action)
  have hgainAction :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash 1 action
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_one_of_one_current_sure_zero_continue
      dates mixed hzeroCurrent honeCurrent htwo hthree] at hgainAction
  have hlower := timingMixedPayoff_update_one_ge_neg_one_add_atom
    (dates + 1) mixed action
  linarith

/-- Every coordinate has positive current-Continue mass in a
positive-deadline Nash law. -/
theorem all_currentContinue_ne_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed) :
    ∀ who, pushforward (mixed who) timingActionCurrent false ≠ 0 := by
  intro who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · exact timingActionCurrent_false_ne_zero_of_lt_one _
      (zero_currentMass_lt_one dates mixed hnash)
  · exact timingActionCurrent_false_ne_zero_of_lt_one _
      (one_currentMass_lt_one dates mixed hnash)
  · rw [dummyTwo_currentLaw_eq_pure_false dates mixed hnash]
    simp
  · rw [dummyThree_currentLaw_eq_pure_false dates mixed hnash]
    simp

/-! ## Exact active-root identification -/

theorem rootEndpointDifference_zero_formula
    (dates : ℕ) (root : Player → PMF Bool)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootEndpointDifference reward (valueAfter dates) root 0 =
      (1 - (root 1 true).toReal) / 2 -
        ((root 1 true).toReal +
          (1 - (root 1 true).toReal) * zeroValue dates) := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [htwo, hthree, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

theorem rootEndpointDifference_one_formula
    (dates : ℕ) (root : Player → PMF Bool)
    (htwo : root 2 = PMF.pure false)
    (hthree : root 3 = PMF.pure false) :
    quittingRootEndpointDifference reward (valueAfter dates) root 1 =
      (-1 + (root 0 true).toReal) -
        (-(root 0 true).toReal +
          (1 - (root 0 true).toReal) * oneValue dates) := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
  simp [htwo, hthree, valueAfter, reward, quittingRootPayoff,
    quittingQuitters, Math.Probability.expect_eq_sum]
  rw [Math.PMFProduct.pmfBool_false_toReal]
  ring

/-- A timing Nash law with the displayed conditioned-tail payoff has
nonpositive current endpoint difference at every coordinate. -/
theorem currentRoot_endpointDifference_nonpos
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates)
    (who : Player) :
    quittingRootEndpointDifference reward (valueAfter dates)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who ≤ 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgain :=
    ((quittingFiniteDeadlineTimingGame reward
      (dates + 1)).isNash_iff_gains_nonpos mixed).mp hnash who
        (some (0 : Fin (dates + 1)))
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_eq_quitPayoff,
    timingMixedPayoff_bellman reward] at hgain
  change quittingRootQuitPayoff reward
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who -
    quittingRootSuccessorPayoff reward
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who ≤ 0
    at hgain
  rw [htailPayoff,
    quittingRootQuitPayoff_sub_successorPayoff] at hgain
  have hcontinue := all_currentContinue_ne_zero dates mixed hnash who
  have hcontinuePos : 0 <
      (pushforward (mixed who) timingActionCurrent false).toReal :=
    ENNReal.toReal_pos hcontinue
      (PMF.apply_ne_top (pushforward (mixed who) timingActionCurrent) false)
  rw [mul_comm] at hgain
  exact nonpos_of_mul_nonpos_left hgain hcontinuePos

/-- Positive mass on the current timing atom pins the corresponding endpoint
difference to zero. -/
theorem currentRoot_endpointDifference_eq_zero_of_current_ne_zero
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates)
    (who : Player)
    (hcurrent : mixed who (some (0 : Fin (dates + 1))) ≠ 0) :
    quittingRootEndpointDifference reward (valueAfter dates)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who = 0 := by
  letI : Finite (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (player : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward
        (dates + 1)).Strategy player) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  have hgain := KernelGame.mixedGain_eq_zero_of_mem_support
    (quittingFiniteDeadlineTimingGame reward (dates + 1)) mixed hnash who
      (some (0 : Fin (dates + 1))) hcurrent
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
    timingMixedPayoff_update_current_eq_quitPayoff,
    timingMixedPayoff_bellman reward] at hgain
  change quittingRootQuitPayoff reward
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who -
    quittingRootSuccessorPayoff reward
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player)
      (fun player ↦ pushforward (mixed player) timingActionCurrent) who = 0
    at hgain
  rw [htailPayoff,
    quittingRootQuitPayoff_sub_successorPayoff] at hgain
  have hcontinue := all_currentContinue_ne_zero dates mixed hnash who
  have hcontinuePos : 0 <
      (pushforward (mixed who) timingActionCurrent false).toReal :=
    ENNReal.toReal_pos hcontinue
      (PMF.apply_ne_top (pushforward (mixed who) timingActionCurrent) false)
  exact (mul_eq_zero.mp hgain).resolve_left hcontinuePos.ne'

/-- The active player `0` has positive current mass once the conditioned tail
has the displayed shorter-game payoff. -/
theorem zero_current_ne_zero_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    mixed 0 (some (0 : Fin (dates + 1))) ≠ 0 := by
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hdiffZero := currentRoot_endpointDifference_nonpos
    dates mixed hnash htailPayoff 0
  by_contra hzero
  have hpZero : (root 0 true).toReal = 0 := by
    unfold root
    rw [timingActionCurrent_pushforward_true_zero, hzero]
    rfl
  have hdiffOneFormula := rootEndpointDifference_one_formula
    dates root htwo hthree
  rw [hpZero] at hdiffOneFormula
  by_cases hone : mixed 1 (some (0 : Fin (dates + 1))) = 0
  · have hqZero : (root 1 true).toReal = 0 := by
      unfold root
      rw [timingActionCurrent_pushforward_true_zero, hone]
      rfl
    have hdiffZeroFormula := rootEndpointDifference_zero_formula
      dates root htwo hthree
    rw [hqZero] at hdiffZeroFormula
    have hvalue := zeroValue_lt_half dates
    linarith
  · have hdiffOne :=
      currentRoot_endpointDifference_eq_zero_of_current_ne_zero
        dates mixed hnash htailPayoff 1 hone
    have hvalue := oneValue_gt_neg_one dates
    linarith

/-- Player `1`'s current mass is then positive as well. -/
theorem one_current_ne_zero_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    mixed 1 (some (0 : Fin (dates + 1))) ≠ 0 := by
  have hzero := zero_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hdiffZero :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 0 hzero
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hformula := rootEndpointDifference_zero_formula
    dates root htwo hthree
  by_contra hone
  have hqZero : (root 1 true).toReal = 0 := by
    unfold root
    rw [timingActionCurrent_pushforward_true_zero, hone]
    rfl
  rw [hqZero] at hformula
  have hvalue := zeroValue_lt_half dates
  linarith

/-- The current Boolean root of any Nash law with the unique shorter tail is
exactly the displayed backward-induction root. -/
theorem currentRoot_eq_rootBefore_of_tailPayoff
    (dates : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction (dates + 1)))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      (dates + 1)).mixedExtension.IsNash mixed)
    (htailPayoff :
      (fun player ↦ timingMixedPayoff reward dates
        (fun other ↦ timingLawTail (mixed other)) player) =
        valueAfter dates) :
    (fun player ↦ pushforward (mixed player) timingActionCurrent) =
      rootBefore dates := by
  let root : Player → PMF Bool := fun player ↦
    pushforward (mixed player) timingActionCurrent
  have htwo : root 2 = PMF.pure false :=
    dummyTwo_currentLaw_eq_pure_false dates mixed hnash
  have hthree : root 3 = PMF.pure false :=
    dummyThree_currentLaw_eq_pure_false dates mixed hnash
  have hzero := zero_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hone := one_current_ne_zero_of_tailPayoff
    dates mixed hnash htailPayoff
  have hdiffZero :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 0 hzero
  have hdiffOne :=
    currentRoot_endpointDifference_eq_zero_of_current_ne_zero
      dates mixed hnash htailPayoff 1 hone
  have hformulaZero := rootEndpointDifference_zero_formula
    dates root htwo hthree
  have hformulaOne := rootEndpointDifference_one_formula
    dates root htwo hthree
  have hp : (root 0 true).toReal = zeroHazard dates := by
    rw [zeroHazard_eq_indifference]
    have hden : 0 < 2 + oneValue dates := by
      have := oneValue_gt_neg_one dates
      linarith
    apply (eq_div_iff hden.ne').2
    nlinarith
  have hq : (root 1 true).toReal = oneHazard dates := by
    rw [oneHazard_eq_indifference]
    have hden : 0 < 3 / 2 - zeroValue dates := by
      have := zeroValue_lt_half dates
      linarith
    apply (eq_div_iff hden.ne').2
    nlinarith
  funext who
  have hcases : who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
    fin_cases who <;> simp
  rcases hcases with rfl | rfl | rfl | rfl
  · apply pmfBool_eq_of_true_toReal_eq
    rw [hp, rootBefore_zero_true_toReal]
  · apply pmfBool_eq_of_true_toReal_eq
    rw [hq, rootBefore_one_true_toReal]
  · change root 2 = rootBefore dates 2
    rw [htwo, rootBefore_two]
  · change root 3 = rootBefore dates 3
    rw [hthree, rootBefore_three]

/-! ## Backward induction and exact uniqueness -/

/-- Every Nash law of the finite timing game is unique and has the displayed
backward-induction payoff. -/
theorem timingNash_unique_and_payoff :
    ∀ (dates : ℕ)
      (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates)),
      (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
          mixed →
        (fun who ↦ timingMixedPayoff reward dates mixed who) = valueAfter dates ∧
        ∀ other : Player →
            PMF (QuittingFiniteDeadlineTimingAction dates),
          (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
              other →
            other = mixed := by
  intro dates
  induction dates with
  | zero =>
      intro mixed _hnash
      constructor
      · funext who
        rw [timingMixedPayoff_zero]
        fin_cases who <;> simp [valueAfter]
      · intro other _hother
        funext who
        calc
          other who = (PMF.pure none :
              PMF (QuittingFiniteDeadlineTimingAction 0)) :=
            Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
          _ = mixed who :=
            (Math.ProbabilityMassFunction.eq_pure_of_subsingleton
              (mixed who) none).symm
  | succ dates ih =>
      intro mixed hnash
      let tails : Player →
          PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
        timingLawTail (mixed who)
      have hcontinue := all_currentContinue_ne_zero dates mixed hnash
      have htailNash :
          (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
            tails := by
        exact timingLawTail_isNash_of_isNash_of_positiveContinue reward dates mixed hnash hcontinue
      have htailResult := ih tails htailNash
      have htailPayoff :
          (fun who ↦ timingMixedPayoff reward dates tails who) = valueAfter dates :=
        htailResult.1
      have hroot := currentRoot_eq_rootBefore_of_tailPayoff
        dates mixed hnash htailPayoff
      constructor
      · funext who
        rw [timingMixedPayoff_bellman reward]
        change quittingRootSuccessorPayoff reward
          (fun player ↦ timingMixedPayoff reward dates tails player)
          (fun player ↦ pushforward (mixed player) timingActionCurrent) who =
            valueAfter (dates + 1) who
        rw [htailPayoff, hroot]
        exact (congrFun (valueAfter_succ_eq_successor dates) who).symm
      · intro other hother
        let otherTails : Player →
            PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
          timingLawTail (other who)
        have hotherContinue := all_currentContinue_ne_zero dates other hother
        have hotherTailNash :
            (quittingFiniteDeadlineTimingGame reward dates).mixedExtension.IsNash
              otherTails := by
          exact timingLawTail_isNash_of_isNash_of_positiveContinue reward
            dates other hother hotherContinue
        have hotherTailResult := ih otherTails hotherTailNash
        have hotherTailPayoff :
            (fun who ↦ timingMixedPayoff reward dates otherTails who) =
              valueAfter dates := hotherTailResult.1
        have hotherRoot := currentRoot_eq_rootBefore_of_tailPayoff
          dates other hother hotherTailPayoff
        have htails : otherTails = tails :=
          htailResult.2 otherTails hotherTailNash
        have hroots :
            (fun who ↦ pushforward (other who) timingActionCurrent) =
              (fun who ↦ pushforward (mixed who) timingActionCurrent) :=
          hotherRoot.trans hroot.symm
        funext who
        apply timingLaw_eq_of_current_tail_eq
        · exact congrFun hroots who
        · exact congrFun htails who
        · exact hotherContinue who
        · exact hcontinue who

/-- The concrete hard Fin4 timing game has exactly one mixed Nash law at
every finite deadline, including deadline zero. -/
theorem existsUnique_finiteDeadlineTimingNash (deadline : ℕ) :
    ∃! mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward
        deadline).mixedExtension.IsNash mixed := by
  letI (who : Player) : Finite
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI (who : Player) : Nonempty
      ((quittingFiniteDeadlineTimingGame reward deadline).Strategy who) := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  letI : Finite
      (quittingFiniteDeadlineTimingGame reward deadline).Outcome := by
    unfold quittingFiniteDeadlineTimingGame KernelGame.ofPureEU
    infer_instance
  obtain ⟨mixed, hnash⟩ :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixed_nash_exists
  refine ⟨mixed, hnash, ?_⟩
  intro other hother
  exact (timingNash_unique_and_payoff deadline mixed hnash).2 other hother

/-- The unique timing Nash law has the displayed backward-induction payoff. -/
theorem finiteDeadlineTimingNash_payoff_eq_valueAfter
    (deadline : ℕ)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    (fun who ↦ timingMixedPayoff reward deadline mixed who) =
      valueAfter deadline :=
  (timingNash_unique_and_payoff deadline mixed hnash).1

/-- The explicit hard-deadline behavior chain is its displayed current root
followed by the shorter hard-deadline chain. -/
theorem hardDeadlineProfile_succ (dates : ℕ) :
    hardDeadlineProfile (dates + 1) =
      quittingRootThenContinuationProfile reward (rootBefore dates)
        (hardDeadlineProfile dates) := by
  funext who time history
  cases time with
  | zero =>
      simp [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile, hardDeadlineRoots]
  | succ time =>
      simp only [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile,
        quittingRootThenContinuationProfile]
      simp only [Nat.zero_add]
      change hardDeadlineRoots (dates + 1) (time + 1) who =
        hardDeadlineRoots dates time who
      by_cases htime : time < dates
      · simp [hardDeadlineRoots, htime]
      · have hle : dates ≤ time := Nat.le_of_not_gt htime
        simp [hardDeadlineRoots, htime]

/-- Every Nash law of the finite hard table realizes the explicit
hard-deadline behavioral profile, not merely the same normal-form payoff. -/
theorem finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile :
    ∀ (deadline : ℕ)
      (mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline)),
      (quittingFiniteDeadlineTimingGame reward
        deadline).mixedExtension.IsNash mixed →
        quittingFiniteDeadlineTimingProfile reward deadline mixed =
          hardDeadlineProfile deadline := by
  intro deadline
  induction deadline with
  | zero =>
      intro mixed _hnash
      funext who time history
      have hlaw : mixed who =
          (PMF.pure none :
            PMF (QuittingFiniteDeadlineTimingAction 0)) :=
        Math.ProbabilityMassFunction.eq_pure_of_subsingleton _ none
      unfold quittingFiniteDeadlineTimingProfile
        quittingCompactStoppingLawProfile
        quittingStoppingLawBehaviorStrategy
      dsimp only
      rw [hlaw]
      simp only [quittingFiniteDeadlineTimingLaw,
        Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
      rw [PMF.pure_map]
      simp only [hardDeadlineProfile, quittingInfinitePathProfile,
        quittingRootSequenceProfile, hardDeadlineRoots]
      change (Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard
        (PMF.pure (none : Option ℕ))).toBoolean time = PMF.pure false
      apply Math.ProbabilityMassFunction.eq_pure_false_of_apply_true_toReal_eq_zero
      simp [
        Math.Probability.DiscreteHazard.StoppingLaw.toScalarHazard,
        Math.Probability.DiscreteHazard.StoppingLaw.finiteMass,
        Math.Probability.DiscreteHazard.StoppingLaw.survival,
        Math.Probability.DiscreteHazard.ScalarHazard.toBoolean]
  | succ dates ih =>
      intro mixed hnash
      let tails : Player →
          PMF (QuittingFiniteDeadlineTimingAction dates) := fun who ↦
        timingLawTail (mixed who)
      have hcontinue := all_currentContinue_ne_zero dates mixed hnash
      have htailNash :
          (quittingFiniteDeadlineTimingGame reward
            dates).mixedExtension.IsNash tails :=
        timingLawTail_isNash_of_isNash_of_positiveContinue reward dates mixed hnash hcontinue
      have htailPayoff :=
        finiteDeadlineTimingNash_payoff_eq_valueAfter
          dates tails htailNash
      have hroot := currentRoot_eq_rootBefore_of_tailPayoff
        dates mixed hnash htailPayoff
      calc
        quittingFiniteDeadlineTimingProfile reward (dates + 1) mixed =
            quittingRootThenContinuationProfile reward
              (quittingProfileRoot reward
                (quittingFiniteDeadlineTimingProfile reward
                  (dates + 1) mixed))
              (quittingAllContinueProfileSpine reward
                (quittingFiniteDeadlineTimingProfile reward
                  (dates + 1) mixed) 1) :=
          finiteDeadlineTimingProfile_eq_rootThen_spine reward
            (dates + 1) mixed
        _ = quittingRootThenContinuationProfile reward (rootBefore dates)
              (quittingFiniteDeadlineTimingProfile reward dates tails) := by
          rw [finiteDeadlineTimingProfile_root_eq_current reward dates mixed,
            hroot,
            finiteDeadlineTimingProfile_spine_one_eq_tail
              reward dates mixed hcontinue]
        _ = quittingRootThenContinuationProfile reward (rootBefore dates)
              (hardDeadlineProfile dates) := by
          rw [ih tails htailNash]
        _ = hardDeadlineProfile (dates + 1) :=
          (hardDeadlineProfile_succ dates).symm

/-- The unique Nash law, strengthened with its exact behavioral
realization. -/
theorem existsUnique_finiteDeadlineTimingNash_realizing_hardDeadlineProfile
    (deadline : ℕ) :
    ∃! mixed : Player →
        PMF (QuittingFiniteDeadlineTimingAction deadline),
      (quittingFiniteDeadlineTimingGame reward
          deadline).mixedExtension.IsNash mixed ∧
        quittingFiniteDeadlineTimingProfile reward deadline mixed =
          hardDeadlineProfile deadline := by
  obtain ⟨mixed, hnash, hunique⟩ :=
    existsUnique_finiteDeadlineTimingNash deadline
  refine ⟨mixed, ⟨hnash,
    finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash⟩, ?_⟩
  intro other hother
  exact hunique other hother.1

/-- A canonical representative of the unique hard-deadline timing Nash law. -/
noncomputable def hardDeadlineTimingNashLaw (deadline : ℕ) :
    Player → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
  Classical.choose (existsUnique_finiteDeadlineTimingNash deadline)

theorem hardDeadlineTimingNashLaw_isNash (deadline : ℕ) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
      (hardDeadlineTimingNashLaw deadline) :=
  Classical.choose_spec
    (existsUnique_finiteDeadlineTimingNash deadline) |>.1

theorem hardDeadlineTimingNashLaw_profile_eq (deadline : ℕ) :
    quittingFiniteDeadlineTimingProfile reward deadline
        (hardDeadlineTimingNashLaw deadline) =
      hardDeadlineProfile deadline :=
  finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile deadline
    (hardDeadlineTimingNashLaw deadline)
    (hardDeadlineTimingNashLaw_isNash deadline)

/-- Every positive-deadline timing Nash law has exactly the packet's
unrestricted behavioral debt at player `0`. -/
theorem finiteDeadlineTimingNash_debt_zero_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    quittingTerminalDeviationDebt reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) 0 =
      hardDeadlineDebt deadline := by
  rw [finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash,
    hardDeadlineProfile_debt_zero_eq,
    oneNeverMass_div_two_eq_hardDeadlineDebt deadline hdeadline]

/-- Every positive-deadline timing Nash law has exact unrestricted semantic
exploitability `D_N`, independently of how an existence theorem selected it. -/
theorem finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)) =
      hardDeadlineDebt deadline := by
  rw [finiteDeadlineTimingNash_profile_eq_hardDeadlineProfile
      deadline mixed hnash,
    hardDeadlineProfile_exploitability_eq_hardDeadlineDebt
      deadline hdeadline]

/-- The hard-table timing Nash family has a selection-independent strict
quarter barrier at every positive deadline. -/
theorem quarter_lt_finiteDeadlineTimingNash_exploitability
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : Player →
      PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hnash : (quittingFiniteDeadlineTimingGame reward
      deadline).mixedExtension.IsNash mixed) :
    1 / 4 < quittingTerminalSemanticExploitability
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed)) := by
  rw [finiteDeadlineTimingNash_exploitability_eq_hardDeadlineDebt
    deadline hdeadline mixed hnash]
  exact hardDeadlineDebt_gt_quarter deadline hdeadline

end FinFourHardDeadlineTimingNashBarrier
end GameTheory
