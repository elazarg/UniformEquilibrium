/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FinFourRationalFiniteClockChildUpperCompleteness
import UniformEquilibrium.Quitting.Terminal.FiniteMenuFullProfileApproximation
import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueSource
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-!
# Actual child sources for the rational Fin4 child-only search

Finite stopping laws of the deleted three-player game are lifted by the
canonical deleted-player Never profile. Their actual parent stopping laws form
the real Fin4 finite-clock source used by residual-floor approximation. The
masked real maximum is proved equal to the literal unrestricted terminal
exploitability of the original child profile.

This connects an actual child uniform-equilibrium payoff to finite discovery
by the child-only rational checker. The reward table is arbitrary and need not
be normalized.
-/

noncomputable section

namespace GameTheory

open Math.ProbabilityMassFunction

namespace FinFourRationalFiniteClockChildProducer

open FinFourRationalFiniteClockProfileCompleteness
open FinFourRationalFiniteClockChildUpperCompleteness

/-- Actual Fin4 stopping laws obtained by taking the complete laws of the
canonical Never lift of a supplied deleted-child law profile. -/
def liftedChildStoppingLaws (reward : RationalFinFourRewardCode)
    (owner : Fin 4)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ)) :
    Fin 4 → PMF (Option ℕ) :=
  quittingBehaviorStoppingLaws reward.realReward
    (quittingLiftDeletedProfile reward.realReward (fun player => player = owner)
      (quittingStoppingLawProfile
        (quittingDeleteReward reward.realReward (fun player => player = owner))
        laws))

theorem liftedChildStoppingLaws_owner
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ)) :
    liftedChildStoppingLaws reward owner laws owner = PMF.pure none := by
  unfold liftedChildStoppingLaws quittingBehaviorStoppingLaws
  exact quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
    reward.realReward (fun player => player = owner)
    (quittingStoppingLawProfile
      (quittingDeleteReward reward.realReward (fun player => player = owner))
      laws) rfl

theorem liftedChildStoppingLaws_survivor
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (who : {who : Fin 4 // who ≠ owner}) :
    liftedChildStoppingLaws reward owner laws who.1 = laws who := by
  unfold liftedChildStoppingLaws quittingBehaviorStoppingLaws
  rw [quittingBehaviorStoppingLaw_liftDeletedProfile reward.realReward
    (fun player => player = owner)
    (quittingStoppingLawProfile
      (quittingDeleteReward reward.realReward (fun player => player = owner))
      laws) who]
  exact quittingBehaviorStoppingLaw_stoppingLawProfile
    (quittingDeleteReward reward.realReward (fun player => player = owner))
    laws who

theorem liftedChildStoppingLaws_finite
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (clock : ℕ)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clock (laws who)) :
    ∀ player, IsFiniteClockStoppingLaw clock
      (liftedChildStoppingLaws reward owner laws player) := by
  intro player
  by_cases hplayer : player = owner
  · subst player
    rw [liftedChildStoppingLaws_owner]
    exact isFiniteClockStoppingLaw_pure_never clock
  · let who : {who : Fin 4 // who ≠ owner} := ⟨player, hplayer⟩
    rw [liftedChildStoppingLaws_survivor reward owner laws who]
    exact hlaws who

/-- Real Fin4 source obtained from actual finite-clock child laws and their
canonical Never lift. -/
def RealFiniteClockProfile.ofDeletedChildStoppingLaws
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clock (laws who)) :
    RealFiniteClockProfile reward :=
  RealFiniteClockProfile.ofStoppingLaws (reward := reward) clock hclock
    (liftedChildStoppingLaws reward owner laws)
    (liftedChildStoppingLaws_finite reward owner clock laws hlaws)

/-- The real source produced from child laws has an exactly pure-Never owner
coordinate, not merely a limiting one. -/
theorem RealFiniteClockProfile.ofDeletedChildStoppingLaws_owner_zero
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clock (laws who))
    (atom : FiniteClockAtom clock)
    (hatom : atom ≠ none) :
    (RealFiniteClockProfile.ofDeletedChildStoppingLaws
      reward owner clock hclock laws hlaws).weight owner atom = 0 := by
  change finiteClockLawCoordinates clock
    (liftedChildStoppingLaws reward owner laws owner) atom = 0
  rw [liftedChildStoppingLaws_owner]
  unfold finiteClockLawCoordinates finiteClockEncodeLaw toVector
  rw [PMF.pure_map]
  rw [stoppingTimeToFiniteClockAtom_none]
  rw [PMF.pure_apply_of_ne none atom hatom]
  rfl

/-- The real masked maximum of the canonical Never extension is exactly the
literal terminal exploitability of the supplied deleted-child laws. -/
theorem realChildExploitability_ofDeletedChildStoppingLaws_eq
    (reward : RationalFinFourRewardCode) (owner : Fin 4)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clock (laws who)) :
    let source := RealFiniteClockProfile.ofDeletedChildStoppingLaws
      reward owner clock hclock laws hlaws
    realChildExploitability reward source.clockBound owner source.weight =
      quittingTerminalExploitability
        (quittingDeleteReward reward.realReward (fun player => player = owner))
        (quittingStoppingLawProfile
          (quittingDeleteReward reward.realReward
            (fun player => player = owner)) laws) := by
  dsimp only
  let childReward :=
    quittingDeleteReward reward.realReward (fun player => player = owner)
  let child := quittingStoppingLawProfile childReward laws
  let lifted := quittingLiftDeletedProfile reward.realReward
    (fun player => player = owner) child
  let parentLaws := liftedChildStoppingLaws reward owner laws
  let source := RealFiniteClockProfile.ofDeletedChildStoppingLaws
    reward owner clock hclock laws hlaws
  have hsourceProfile : source.toBehaviorProfile =
      quittingStoppingLawProfile reward.realReward parentLaws := by
    exact RealFiniteClockProfile.toBehaviorProfile_ofStoppingLaws
      reward clock hclock parentLaws
        (liftedChildStoppingLaws_finite reward owner clock laws hlaws)
  have hsame : quittingBehaviorStoppingLaws reward.realReward
      source.toBehaviorProfile =
        quittingBehaviorStoppingLaws reward.realReward lifted := by
    rw [hsourceProfile,
      quittingBehaviorStoppingLaws_stoppingLawProfile]
    rfl
  have hgap (who : {who : Fin 4 // who ≠ owner}) :
      max 0
          (realCap reward source.clockBound source.weight who.1 -
            realPayoff reward source.clockBound source.weight who.1) =
        max 0
          (quittingContinuationBestResponseValue childReward child who -
            quittingTerminalPayoff childReward child who) := by
    rw [realCap_eq_continuationBestResponseValue reward source.clockBound
        source.weight source.weight_simplex source.auxiliary_eq_zero who.1,
      realPayoff_eq_terminalPayoff reward source.clockBound source.weight
        source.weight_simplex who.1]
    change max 0
        (quittingBehaviorDeviationPayoffCap reward.realReward
            source.toBehaviorProfile who.1 -
          quittingTerminalPayoff reward.realReward
            source.toBehaviorProfile who.1) = _
    rw [quittingBehaviorDeviationPayoffCap_eq_of_behaviorStoppingLaws_eq
        reward.realReward source.toBehaviorProfile lifted hsame who.1,
      quittingTerminalPayoff_eq_of_behaviorStoppingLaws_eq
        reward.realReward source.toBehaviorProfile lifted hsame who.1,
      quittingBehaviorDeviationDebt_liftDeletedProfile
        reward.realReward (fun player => player = owner) child who]
    rfl
  have hchildNonneg : 0 ≤ quittingTerminalExploitability childReward child :=
    quittingTerminalExploitability_nonneg childReward child
  unfold realChildExploitability quittingTerminalExploitability
    QuittingBoundaryHolonomy.finitePlayerMax
  apply le_antisymm
  · obtain ⟨player, -, hplayer⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty fun player : Fin 4 =>
        if player = owner then 0 else
          max 0
            (realCap reward source.clockBound source.weight player -
              realPayoff reward source.clockBound source.weight player)
    rw [hplayer]
    by_cases howner : player = owner
    · subst player
      rw [ite_eq_left rfl]
      exact hchildNonneg
    · let who : {who : Fin 4 // who ≠ owner} := ⟨player, howner⟩
      rw [ite_eq_right howner, hgap who]
      exact Finset.le_sup'
        (fun candidate : {who : Fin 4 // who ≠ owner} =>
          max 0
            (quittingContinuationBestResponseValue childReward child candidate -
              quittingTerminalPayoff childReward child candidate))
        (Finset.mem_univ who)
  · apply Finset.sup'_le Finset.univ_nonempty
    intro who _
    rw [← hgap who]
    simpa only [ite_eq_right who.2] using
      (Finset.le_sup'
        (fun player : Fin 4 =>
          if player = owner then 0 else
            max 0
              (realCap reward source.clockBound source.weight player -
                realPayoff reward source.clockBound source.weight player))
        (Finset.mem_univ who.1))

/-- A strict actual finite-clock child upper bound is discovered by the
existing rational Fin4 enumeration while retaining the appended Never owner. -/
theorem exists_checkedChildCandidateAt_of_finiteClockDeletedStoppingLaws
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (clock : ℕ) (hclock : 0 < clock)
    (laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ))
    (hlaws : ∀ who, IsFiniteClockStoppingLaw clock (laws who))
    (hbelow : quittingTerminalExploitability
      (quittingDeleteReward reward.realReward (fun player => player = owner))
      (quittingStoppingLawProfile
        (quittingDeleteReward reward.realReward
          (fun player => player = owner)) laws) < (target : ℝ)) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt
          reward owner target stage = some code ∧
        code.clockBound = clock ∧
        ∀ atom, code.mass owner atom = if atom = none then 1 else 0 := by
  let source := RealFiniteClockProfile.ofDeletedChildStoppingLaws
    reward owner clock hclock laws hlaws
  have hpure : ∀ atom, atom ≠ none → source.weight owner atom = 0 := by
    exact RealFiniteClockProfile.ofDeletedChildStoppingLaws_owner_zero
      reward owner clock hclock laws hlaws
  have hsourceBelow : realChildExploitability reward source.clockBound owner
      source.weight < (target : ℝ) := by
    rw [realChildExploitability_ofDeletedChildStoppingLaws_eq
      reward owner clock hclock laws hlaws]
    exact hbelow
  simpa only [source, RealFiniteClockProfile.ofDeletedChildStoppingLaws,
    RealFiniteClockProfile.ofStoppingLaws] using
      exists_checkedChildCandidateAt_of_realFiniteClockProfile
        reward owner target source hpure hsourceBelow

/-- A supplied uniform-equilibrium payoff of the actual deleted child makes
the child-only rational search terminate at every positive rational threshold.
The intermediate finite menu is chosen with positive clock bound. -/
theorem exists_checkedChildCandidateAt_of_childUniformEquilibriumPayoff
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (htarget : 0 < target)
    (childTarget : Payoff {who : Fin 4 // who ≠ owner})
    (hchildTarget :
      (quittingGame
        (quittingDeleteReward reward.realReward
          (fun player => player = owner))).IsUniformEquilibriumPayoff
        none childTarget) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt
          reward owner target stage = some code ∧
        0 < code.clockBound ∧
        ∀ atom, code.mass owner atom = if atom = none then 1 else 0 := by
  let childReward :=
    quittingDeleteReward reward.realReward (fun player => player = owner)
  have htargetReal : 0 < (target : ℝ) := by
    exact_mod_cast htarget
  obtain ⟨deadline, hdeadline, mixed, hexploit, _⟩ :=
    (isUniformEquilibriumPayoff_iff_finiteMenu_fullCap_target_approximation
      childReward childTarget).mp hchildTarget
        (target : ℝ) htargetReal 1
  have hclock : 0 < deadline := by omega
  let laws : {who : Fin 4 // who ≠ owner} → PMF (Option ℕ) :=
    fun who => (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF
  have hlaws : ∀ who, IsFiniteClockStoppingLaw deadline (laws who) := by
    intro who
    exact isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who)
  have hprofile : quittingFiniteDeadlineTimingProfile
      childReward deadline mixed =
        quittingStoppingLawProfile childReward laws := by
    apply finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    intro who
    rfl
  have hbelow : quittingTerminalExploitability childReward
      (quittingStoppingLawProfile childReward laws) < (target : ℝ) := by
    rw [← hprofile]
    exact hexploit
  obtain ⟨stage, code, hstage, hcodeClock, hpure⟩ :=
    exists_checkedChildCandidateAt_of_finiteClockDeletedStoppingLaws
      reward owner target deadline hclock laws hlaws hbelow
  have hcodeClockPos : 0 < code.clockBound := by
    simpa only [hcodeClock] using hclock
  exact ⟨stage, code, hstage, hcodeClockPos, hpure⟩

/-- For every rational Fin4 reward table and owner, the literal child-only
rational search terminates at every positive rational threshold. This uses the
checked uniform-equilibrium existence theorem for the three-player deleted
game; no reward normalization is required. -/
theorem exists_checkedChildCandidateAt
    (reward : RationalFinFourRewardCode) (owner : Fin 4) (target : ℚ)
    (htarget : 0 < target) :
    ∃ stage code,
      RationalFinFourFiniteClockProfileCode.checkedChildCandidateAt
          reward owner target stage = some code ∧
        0 < code.clockBound ∧
        ∀ atom, code.mass owner atom = if atom = none then 1 else 0 := by
  have hchildCard :
      Fintype.card {who : Fin 4 // who ≠ owner} = 3 :=
    card_quittingDeletedPlayer_eq_three_of_card_eq_four owner rfl
  obtain ⟨childTarget, hchildTarget⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three hchildCard
      (quittingDeleteReward reward.realReward
        (fun player => player = owner))
  exact exists_checkedChildCandidateAt_of_childUniformEquilibriumPayoff
    reward owner target htarget childTarget hchildTarget

end FinFourRationalFiniteClockChildProducer

end GameTheory
