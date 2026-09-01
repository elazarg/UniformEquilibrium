/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.PassivePlayerPaddingRetraction
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Fixed-target retraction for canonical passive-player padding

The canonical quiet lift extends an old target by zero on the fresh block.
Conversely, quantitative projection restricts every padded uniform target to
an old uniform target, while fresh Never deviations force every fresh target
coordinate to be zero.  Thus the uniform-payoff target set is identified
exactly, without assuming target attainment by one profile.

These results concern the canonical padded reward only.  They do not reduce an
arbitrary larger-player reward table and do not prove a new finite-cardinality
case.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {I J : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]

/-- Extend an old target by literal zero on the fresh coordinates. -/
def quittingPassivePaddingTarget (target : Payoff I) : Payoff (I ⊕ J) :=
  Sum.elim target (fun _ ↦ 0)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] theorem quittingPassivePaddingTarget_inl
    (target : Payoff I) (who : I) :
    quittingPassivePaddingTarget (J := J) target (.inl who) = target who := by
  rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] theorem quittingPassivePaddingTarget_inr
    (target : Payoff I) (fresh : J) :
    quittingPassivePaddingTarget (J := J) target (.inr fresh) = 0 := by
  rfl

/-- An accepted old target lifts to its literal zero extension for the
canonical passive padding. -/
theorem isUniformEquilibriumPayoff_passivePaddingTarget
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 ≤ penalty) (target : Payoff I)
    (htarget : (quittingGame reward).IsUniformEquilibriumPayoff none target) :
    (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsUniformEquilibriumPayoff none
        (quittingPassivePaddingTarget (J := J) target) := by
  obtain ⟨certificate⟩ :=
    exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
      reward target htarget
  apply QuittingTerminalTargetAcceptanceCertificate.isUniformEquilibriumPayoff
  refine ⟨?_⟩
  intro error herror
  obtain ⟨profile, hnash, hclose⟩ := certificate.terminalProfile error herror
  refine ⟨quittingPassivePaddingQuietProfile (J := J) reward penalty profile,
    isεAsymptoticNash_passivePaddingQuietProfile
      (J := J) reward hpenalty herror.le profile hnash, ?_⟩
  intro player
  cases player with
  | inl who =>
      simpa [quittingPassivePaddingTarget,
        quittingTerminalPayoff_passivePaddingQuietProfile_old_eq]
        using hclose who
  | inr fresh =>
      simp [quittingPassivePaddingTarget,
        quittingTerminalPayoff_passivePaddingQuietProfile_fresh_eq_zero]
      exact herror

/-- Every fresh coordinate of a canonical padded uniform target is zero. -/
theorem isUniformEquilibriumPayoff_passivePadding_fresh_eq_zero
    [Nonempty I]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 ≤ penalty) (target : Payoff (I ⊕ J))
    (htarget : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsUniformEquilibriumPayoff none target) :
    ∀ fresh : J, target (.inr fresh) = 0 := by
  obtain ⟨certificate⟩ :=
    exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)
      target htarget
  intro fresh
  rcases lt_trichotomy (target (.inr fresh)) 0 with hnegative | hzero | hpositive
  · let error := -target (.inr fresh) / 3
    have herror : 0 < error := by
      dsimp only [error]
      linarith
    obtain ⟨profile, hnash, hclose⟩ :=
      certificate.terminalProfile error herror
    have hnever := hnash (.inr fresh)
      (quittingPureTimeBehaviorStrategy
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty)
        (.inr fresh) none)
    rw [quittingTerminalPayoff_update_passivePadding_fresh_never_eq_zero]
      at hnever
    have hcloseFresh := abs_lt.mp (hclose (.inr fresh))
    dsimp only [error] at hnever hcloseFresh
    linarith
  · exact hzero
  · let error := target (.inr fresh) / 2
    have herror : 0 < error := by
      dsimp only [error]
      linarith
    obtain ⟨profile, _hnash, hclose⟩ :=
      certificate.terminalProfile error herror
    have hpayoff := quittingTerminalPayoff_passivePadding_fresh_nonpos
      (J := J) reward (quittingPassivePaddingUpperEndpoint reward)
      hpenalty profile fresh
    have hcloseFresh := abs_lt.mp (hclose (.inr fresh))
    dsimp only [error] at hcloseFresh
    linarith

/-- Restricting the old coordinates of a canonical padded uniform target
produces an old uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_restrict_passivePadding
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) (target : Payoff (I ⊕ J))
    (htarget : (quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsUniformEquilibriumPayoff none target) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun who ↦ target (.inl who)) := by
  obtain ⟨certificate⟩ :=
    exists_quittingTerminalTargetAcceptanceCertificate_of_isUniformEquilibriumPayoff
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty)
      target htarget
  apply QuittingTerminalTargetAcceptanceCertificate.isUniformEquilibriumPayoff
  refine ⟨?_⟩
  intro error herror
  let factor := quittingPassivePaddingRetractionFactor
    (J := J) reward penalty
  have hfactor : 0 < factor :=
    quittingPassivePaddingRetractionFactor_pos
      (J := J) reward hpenalty
  let paddedError := factor * (error / 2)
  have hpaddedError : 0 < paddedError := by
    dsimp only [paddedError]
    positivity
  obtain ⟨profile, hnash, hclose⟩ :=
    certificate.terminalProfile paddedError hpaddedError
  refine ⟨quittingPassivePaddingProjectProfile reward profile, ?_, ?_⟩
  · have hproject := isεAsymptoticNash_project_passivePadding
      (J := J) reward hpenalty hpaddedError.le profile hnash
    have hratio : paddedError / factor = error / 2 := by
      dsimp only [paddedError]
      field_simp
    rw [hratio] at hproject
    exact hproject.mono (by linarith)
  · intro who
    have hproject := terminalTargetError_project_passivePadding
      (J := J) reward hpenalty profile hnash target
      (fun old ↦ (hclose (.inl old)).le)
    have hratio : paddedError / factor = error / 2 := by
      dsimp only [paddedError]
      field_simp
    rw [hratio] at hproject
    exact (hproject who).trans_lt (by linarith)

/-- Exact fixed-target characterization for canonical passive padding. -/
theorem isUniformEquilibriumPayoff_passivePadding_iff
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) (target : Payoff (I ⊕ J)) :
    ((quittingGame
      (quittingPassivePaddingReward (J := J) reward
        (quittingPassivePaddingUpperEndpoint reward) penalty))
      |>.IsUniformEquilibriumPayoff none target) ↔
      (quittingGame reward).IsUniformEquilibriumPayoff none
          (fun who ↦ target (.inl who)) ∧
        ∀ fresh : J, target (.inr fresh) = 0 := by
  constructor
  · intro htarget
    exact ⟨isUniformEquilibriumPayoff_restrict_passivePadding
      (J := J) reward hpenalty target htarget,
      isUniformEquilibriumPayoff_passivePadding_fresh_eq_zero
        (J := J) reward hpenalty.le target htarget⟩
  · rintro ⟨hold, hfresh⟩
    have hlift := isUniformEquilibriumPayoff_passivePaddingTarget
      (J := J) reward hpenalty.le (fun who ↦ target (.inl who)) hold
    have heq : quittingPassivePaddingTarget (J := J)
        (fun who ↦ target (.inl who)) = target := by
      funext player
      cases player with
      | inl who => rfl
      | inr fresh => simpa using (hfresh fresh).symm
    rwa [heq] at hlift

/-- The canonical padded uniform-payoff target set is exactly the image of
the old target set under zero extension. -/
theorem uniformEquilibriumPayoffSet_passivePadding_eq_image
    [Nonempty I] [Nonempty J]
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    {penalty : ℝ} (hpenalty : 0 < penalty) :
    {target : Payoff (I ⊕ J) |
      (quittingGame
        (quittingPassivePaddingReward (J := J) reward
          (quittingPassivePaddingUpperEndpoint reward) penalty))
        |>.IsUniformEquilibriumPayoff none target} =
      quittingPassivePaddingTarget (J := J) ''
        {target : Payoff I |
          (quittingGame reward).IsUniformEquilibriumPayoff none target} := by
  ext target
  rw [Set.mem_setOf_eq, isUniformEquilibriumPayoff_passivePadding_iff
    (J := J) reward hpenalty, Set.mem_image]
  constructor
  · rintro ⟨hold, hfresh⟩
    refine ⟨fun who ↦ target (.inl who), hold, ?_⟩
    funext player
    cases player with
    | inl who => rfl
    | inr fresh => simpa using (hfresh fresh).symm
  · rintro ⟨oldTarget, hold, rfl⟩
    exact ⟨hold, fun fresh ↦ by rfl⟩

end GameTheory
