/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau
import UniformEquilibrium.Quitting.Classification.Existence.UniformPayoffTerminalSemanticCarrier
import UniformEquilibrium.Quitting.Root.OneDateNeverNashDebt
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingCanonical
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Zero-penalty failure of passive-padding target retraction

The strict positivity of the fresh-player penalty in canonical passive
padding is necessary.  For a two-player singleton-reward table, adding one
fresh player with zero penalty creates the uniform payoff `(1, 1, 0)`, even
though `(1, 1)` is not a uniform payoff of the old game.

This is a single sharp boundary table.  It makes no claim about arbitrary
zero-penalty padding or arbitrary larger-player games.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct StochasticGame

/-- The old two-player table pays one exactly to a unique quitter. -/
def passivePaddingZeroPenaltyOldReward
    (terminal : {S : Finset (Fin 2) // S.Nonempty}) : Payoff (Fin 2) :=
  fun who =>
    if terminal.1.card = 1 then
      if who ∈ terminal.1 then 1 else 0
    else 0

/-- The canonical upper endpoint of the boundary table, written literally. -/
def passivePaddingZeroPenaltyUpper : Payoff (Fin 2) := fun _ => 1

/-- One fresh player Quits surely at date zero; both old players Continue. -/
def passivePaddingZeroPenaltyRoot : (Fin 2 ⊕ Unit) → PMF Bool
  | .inl _ => PMF.pure false
  | .inr _ => PMF.pure true

/-- The deterministic action underlying the zero-penalty root. -/
def passivePaddingZeroPenaltyAction : (Fin 2 ⊕ Unit) → Bool
  | .inl _ => false
  | .inr _ => true

private theorem passivePaddingZeroPenaltyRoot_eq_pure :
    passivePaddingZeroPenaltyRoot =
      fun player => PMF.pure (passivePaddingZeroPenaltyAction player) := by
  funext player
  cases player <;> rfl

private theorem passivePaddingZeroPenaltyAction_quitters :
    quittingQuitters passivePaddingZeroPenaltyAction = {.inr ()} := by
  ext player
  cases player with
  | inl old => simp [quittingQuitters, passivePaddingZeroPenaltyAction]
  | inr fresh =>
      cases fresh
      simp [quittingQuitters, passivePaddingZeroPenaltyAction]

/-- The padded zero-penalty boundary table. -/
def passivePaddingZeroPenaltyReward :
    {S : Finset (Fin 2 ⊕ Unit) // S.Nonempty} → Payoff (Fin 2 ⊕ Unit) :=
  quittingPassivePaddingReward passivePaddingZeroPenaltyOldReward
    passivePaddingZeroPenaltyUpper 0

/-- The sure fresh Quit followed by Never. -/
def passivePaddingZeroPenaltyProfile :
    (quittingGame passivePaddingZeroPenaltyReward).BehaviorProfile :=
  quittingOneDateThenNeverProfile passivePaddingZeroPenaltyReward
    passivePaddingZeroPenaltyRoot

/-- The old target which zero-penalty padding spuriously creates. -/
def passivePaddingZeroPenaltyOldTarget : Payoff (Fin 2) := fun _ => 1

/-- Its padded extension has a zero fresh coordinate. -/
def passivePaddingZeroPenaltyPaddedTarget : Payoff (Fin 2 ⊕ Unit)
  | .inl _ => 1
  | .inr _ => 0

private theorem quittingRootExpectedPayoff_passivePaddingZeroPenaltyRoot
    (tail : Payoff (Fin 2 ⊕ Unit)) (player : Fin 2 ⊕ Unit) :
    quittingRootExpectedPayoff passivePaddingZeroPenaltyReward tail
        passivePaddingZeroPenaltyRoot player =
      passivePaddingZeroPenaltyPaddedTarget player := by
  unfold quittingRootExpectedPayoff
  rw [passivePaddingZeroPenaltyRoot_eq_pure, pmfPi_pure, expect_pure]
  have hnonempty :
      (quittingQuitters passivePaddingZeroPenaltyAction).Nonempty := by
    rw [passivePaddingZeroPenaltyAction_quitters]
    exact Finset.singleton_nonempty _
  rw [show quittingRootPayoff passivePaddingZeroPenaltyReward tail
      passivePaddingZeroPenaltyAction player =
        passivePaddingZeroPenaltyReward
          ⟨quittingQuitters passivePaddingZeroPenaltyAction, hnonempty⟩
          player by simp [quittingRootPayoff, hnonempty]]
  cases player with
  | inl old =>
      simp [passivePaddingZeroPenaltyReward,
        quittingPassivePaddingReward,
        passivePaddingZeroPenaltyUpper,
        passivePaddingZeroPenaltyPaddedTarget,
        quittingPassivePaddingOldPart,
        passivePaddingZeroPenaltyAction_quitters]
  | inr fresh =>
      cases fresh
      simp [passivePaddingZeroPenaltyReward,
        quittingPassivePaddingReward,
        passivePaddingZeroPenaltyPaddedTarget,
        quittingPassivePaddingOldPart,
        passivePaddingZeroPenaltyAction_quitters]

private theorem passivePaddingZeroPenaltyReward_le_target
    (outcome : QuittingTerminalOutcome (Fin 2 ⊕ Unit))
    (player : Fin 2 ⊕ Unit) :
    quittingTerminalOutcomeReward passivePaddingZeroPenaltyReward outcome player ≤
      passivePaddingZeroPenaltyPaddedTarget player := by
  cases outcome with
  | none =>
      cases player <;>
        simp [quittingTerminalOutcomeReward,
          passivePaddingZeroPenaltyPaddedTarget]
  | some terminal =>
      cases player with
      | inl old =>
          simp only [quittingTerminalOutcomeReward]
          unfold passivePaddingZeroPenaltyReward
            quittingPassivePaddingReward
          split
          · simp only [passivePaddingZeroPenaltyOldReward,
              passivePaddingZeroPenaltyPaddedTarget]
            by_cases hcard :
                (quittingPassivePaddingOldPart terminal.1).card = 1
            · by_cases hmem : old ∈
                  quittingPassivePaddingOldPart terminal.1 <;>
                simp [hcard, hmem]
            · simp [hcard]
          · simp [passivePaddingZeroPenaltyUpper,
              passivePaddingZeroPenaltyPaddedTarget]
      | inr fresh =>
          cases fresh
          simp [quittingTerminalOutcomeReward,
            passivePaddingZeroPenaltyReward,
            quittingPassivePaddingReward,
            passivePaddingZeroPenaltyPaddedTarget]
private theorem passivePaddingZeroPenaltyOldReward_sum_le_one
    (terminal : QuittingTerminalOutcome (Fin 2)) :
    (∑ who, quittingTerminalOutcomeReward
      passivePaddingZeroPenaltyOldReward terminal who) ≤ 1 := by
  cases terminal with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
      by_cases hcard : terminal.1.card = 1
      · simp [quittingTerminalOutcomeReward,
          passivePaddingZeroPenaltyOldReward, hcard]
      · simp [quittingTerminalOutcomeReward,
          passivePaddingZeroPenaltyOldReward, hcard]

/-- Every old terminal reward moment has coordinate sum at most one. -/
theorem sum_passivePaddingZeroPenaltyOldRewardMoment_le_one
    (mass : QuittingTerminalOutcome (Fin 2) → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome (Fin 2))) :
    (∑ who, quittingTerminalRewardMoment
      passivePaddingZeroPenaltyOldReward mass who) ≤ 1 := by
  rw [show (∑ who, quittingTerminalRewardMoment
      passivePaddingZeroPenaltyOldReward mass who) =
      ∑ outcome, mass outcome *
        (∑ who, quittingTerminalOutcomeReward
          passivePaddingZeroPenaltyOldReward outcome who) by
    simp only [quittingTerminalRewardMoment, Finset.mul_sum]
    exact Finset.sum_comm]
  calc
    (∑ outcome, mass outcome *
        (∑ who, quittingTerminalOutcomeReward
          passivePaddingZeroPenaltyOldReward outcome who)) ≤
      ∑ outcome, mass outcome * 1 := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left
          (passivePaddingZeroPenaltyOldReward_sum_le_one outcome)
          (hmass.1 outcome)
    _ = 1 := by simpa using hmass.2

/-- The vector `(1, 1)` is not an old uniform-equilibrium payoff. -/
theorem not_isUniformEquilibriumPayoff_passivePaddingZeroPenaltyOldTarget :
    ¬(quittingGame passivePaddingZeroPenaltyOldReward).IsUniformEquilibriumPayoff
      none passivePaddingZeroPenaltyOldTarget := by
  intro huniform
  have hcarrier :=
    diagonal_mem_terminalSemanticCarrier_of_isUniformEquilibriumPayoff
      passivePaddingZeroPenaltyOldReward
      passivePaddingZeroPenaltyOldTarget huniform
  have hmoment :=
    quittingTerminalSemanticCarrier_prescribed_mem_rewardMomentSet
      passivePaddingZeroPenaltyOldReward
      (passivePaddingZeroPenaltyOldTarget,
        passivePaddingZeroPenaltyOldTarget) hcarrier
  obtain ⟨mass, hmass, hmassTarget⟩ := hmoment
  have hle := sum_passivePaddingZeroPenaltyOldRewardMoment_le_one mass hmass
  rw [hmassTarget] at hle
  norm_num [passivePaddingZeroPenaltyOldTarget] at hle

/-- The sure fresh Quit pays `(1, 1, 0)` exactly. -/
theorem quittingTerminalPayoff_passivePaddingZeroPenaltyProfile :
    quittingTerminalPayoff passivePaddingZeroPenaltyReward
        passivePaddingZeroPenaltyProfile =
      passivePaddingZeroPenaltyPaddedTarget := by
  funext player
  unfold passivePaddingZeroPenaltyProfile
    quittingOneDateThenNeverProfile
  rw [quittingTerminalPayoff_rootThenContinuation_eq]
  change quittingRootExpectedPayoff passivePaddingZeroPenaltyReward
    (fun who => quittingTerminalPayoff passivePaddingZeroPenaltyReward
      (quittingAlwaysContinueProfile passivePaddingZeroPenaltyReward) who)
    passivePaddingZeroPenaltyRoot player = _
  exact quittingRootExpectedPayoff_passivePaddingZeroPenaltyRoot _ player

/-- The sure fresh Quit is an exact terminal Nash profile at zero penalty. -/
theorem passivePaddingZeroPenaltyProfile_isExactTerminalNash :
    (quittingGame passivePaddingZeroPenaltyReward).IsεAsymptoticNash
      (quittingTerminalPayoff passivePaddingZeroPenaltyReward) 0
      passivePaddingZeroPenaltyProfile := by
  intro player deviation
  have hdeviation :=
    quittingTerminalPayoff_update_le_continuationBestResponseValue
      passivePaddingZeroPenaltyReward passivePaddingZeroPenaltyProfile
      player deviation
  have hcap :=
    quittingContinuationBestResponseValue_le_of_terminalOutcomeReward_le
      passivePaddingZeroPenaltyProfile player
      (passivePaddingZeroPenaltyPaddedTarget player)
      (fun outcome => passivePaddingZeroPenaltyReward_le_target outcome player)
  rw [quittingTerminalPayoff_passivePaddingZeroPenaltyProfile]
  simpa using hdeviation.trans hcap

/-- The padded target `(1, 1, 0)` is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_passivePaddingZeroPenaltyPaddedTarget :
    (quittingGame passivePaddingZeroPenaltyReward).IsUniformEquilibriumPayoff
      none passivePaddingZeroPenaltyPaddedTarget := by
  have huniform :=
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
      passivePaddingZeroPenaltyReward passivePaddingZeroPenaltyProfile
      passivePaddingZeroPenaltyProfile_isExactTerminalNash
  rwa [quittingTerminalPayoff_passivePaddingZeroPenaltyProfile] at huniform

/-- At zero penalty, the padded uniform target restricts to a non-uniform old
target.  This is the literal failure excluded by the strict-positive-penalty
hypothesis in passive-padding target retraction. -/
theorem passivePaddingZeroPenalty_uniformTargetRestriction_failure :
    (quittingGame passivePaddingZeroPenaltyReward).IsUniformEquilibriumPayoff
        none passivePaddingZeroPenaltyPaddedTarget ∧
      (∀ old, passivePaddingZeroPenaltyPaddedTarget (.inl old) =
        passivePaddingZeroPenaltyOldTarget old) ∧
      ¬(quittingGame passivePaddingZeroPenaltyOldReward).IsUniformEquilibriumPayoff
        none passivePaddingZeroPenaltyOldTarget := by
  exact ⟨isUniformEquilibriumPayoff_passivePaddingZeroPenaltyPaddedTarget,
    fun _ => rfl,
    not_isUniformEquilibriumPayoff_passivePaddingZeroPenaltyOldTarget⟩

end GameTheory
