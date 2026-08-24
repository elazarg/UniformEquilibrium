/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.TwoCycleUniqueSharedHelper

/-!
# Standard-Q return from a unique common helper

In the choice-invariant shared-helper chamber, the two hard rows are helped
by one outside label and are nonpositive at the other outside label.  Full
standard Q forces a positive entry in the common helper's own row.  If that
entry comes from a hard label, it closes a positive two-cycle.  If it comes
from the remaining outside label, standard Q in that label's row closes
either a positive two-cycle or a positive three-cycle through a hard label.

This is a genuine incidence contraction on the actual normalized singleton
matrix.  It does not provide the uniform-over-background inequalities of a
positive quitting influence, and it does not supply the nonsingleton rows of
an odd blocker core.
-/

noncomputable section

namespace GameTheory

open Finset Math.LinearProgramming QuittingLCPClassification
open Math.FiniteSerialRelation
open QuittingSureSetOwnerRepair

/-- The owner label strictly raises the receiver's normalized singleton
payoff. -/
def NormalizedSoloStrictlyHelps
    {player : Type} [Fintype player] [DecidableEq player]
    (reward : {S : Finset player // S.Nonempty} → Payoff player)
    (owner receiver : player) : Prop :=
  0 < normalizedSoloMatrix reward receiver owner

/-- A positive return cycle of length two or three through the unique common
helper. -/
def HasFinFourUniqueSharedHelperPositiveReturnCycle
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
    {players : Finset (Fin 4)}
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) : Prop :=
  Nonempty (RootedTwoCycle (NormalizedSoloStrictlyHelps reward)
      unique.crossing.firstHelper) ∨
    Nonempty (RootedThreeCycle (NormalizedSoloStrictlyHelps reward)
      unique.crossing.firstHelper)

namespace FinFourHardCardTwoUniqueSharedHelper

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {residual : FinFourQuantitativeFullSupportHardResidual reward bound}
variable {players : Finset (Fin 4)}

private theorem label_cases
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players)
    (who : Fin 4) :
    who = unique.crossing.first ∨
      who = unique.crossing.second ∨
      who = unique.crossing.firstHelper ∨
      who = unique.other := by
  by_cases hinside : who ∈ players
  · have hpair : who = unique.crossing.first ∨
        who = unique.crossing.second := by
      rw [unique.crossing.players_eq] at hinside
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hinside
    rcases hpair with hfirst | hsecond
    · exact Or.inl hfirst
    · exact Or.inr (Or.inl hsecond)
  · have houtside : who ∈ playersᶜ := by
      simpa only [Finset.mem_compl] using hinside
    rw [unique.complement_eq] at houtside
    have hpair : who = unique.crossing.firstHelper ∨
        who = unique.other := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using houtside
    rcases hpair with hhelper | hother
    · exact Or.inr (Or.inr (Or.inl hhelper))
    · exact Or.inr (Or.inr (Or.inr hother))

private theorem first_ne_helper
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) :
    unique.crossing.first ≠ unique.crossing.firstHelper := by
  intro heq
  apply unique.crossing.firstHelper_outside
  have hfirst : unique.crossing.first ∈ players := by
    have hiff := congrArg
      (fun selected : Finset (Fin 4) ↦ unique.crossing.first ∈ selected)
      unique.crossing.players_eq
    exact hiff.mpr (by simp)
  exact heq ▸ hfirst

private theorem second_ne_helper
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) :
    unique.crossing.second ≠ unique.crossing.firstHelper := by
  intro heq
  apply unique.crossing.firstHelper_outside
  have hsecond : unique.crossing.second ∈ players := by
    have hiff := congrArg
      (fun selected : Finset (Fin 4) ↦ unique.crossing.second ∈ selected)
      unique.crossing.players_eq
    exact hiff.mpr (by simp)
  exact heq ▸ hsecond

private theorem other_ne_first
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) :
    unique.other ≠ unique.crossing.first := by
  intro heq
  apply unique.other_outside
  have hfirst : unique.crossing.first ∈ players := by
    have hiff := congrArg
      (fun selected : Finset (Fin 4) ↦ unique.crossing.first ∈ selected)
      unique.crossing.players_eq
    exact hiff.mpr (by simp)
  exact heq.symm ▸ hfirst

private theorem other_ne_second
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) :
    unique.other ≠ unique.crossing.second := by
  intro heq
  apply unique.other_outside
  have hsecond : unique.crossing.second ∈ players := by
    have hiff := congrArg
      (fun selected : Finset (Fin 4) ↦ unique.crossing.second ∈ selected)
      unique.crossing.players_eq
    exact hiff.mpr (by simp)
  exact heq.symm ▸ hsecond

/-- **Standard-Q return contraction.**  The unique common helper lies on a
strictly positive normalized-solo cycle of length two or three. -/
theorem hasPositiveReturnCycle
    (unique : FinFourHardCardTwoUniqueSharedHelper residual players) :
    HasFinFourUniqueSharedHelperPositiveReturnCycle unique := by
  let matrix := principalMatrix (normalizedSoloMatrix reward) Finset.univ
  have hstandard : IsStandardQMatrix matrix := by
    exact residual.residualHardClass.fullPrincipal_standardQ
      residual.normalCore_eq_univ
  have positiveOwner (receiver : Fin 4) :
      ∃ owner : Fin 4, 0 < normalizedSoloMatrix reward receiver owner := by
    obtain ⟨owner, hpositive⟩ :=
      exists_positive_entry_in_row_of_standardQ matrix hstandard
        ⟨receiver, Finset.mem_univ receiver⟩
    exact ⟨owner.1, by simpa [matrix, principalMatrix] using hpositive⟩
  have hcommonSecond :
      0 < normalizedSoloMatrix reward unique.crossing.second
        unique.crossing.firstHelper := by
    rw [unique.helpers_eq]
    exact unique.crossing.second_helped
  obtain ⟨owner, howner⟩ := positiveOwner unique.crossing.firstHelper
  rcases label_cases unique owner with hfirst | hsecond | hhelper | hother
  · left
    rw [hfirst] at howner
    exact ⟨{
      next := unique.crossing.first
      next_ne_root := first_ne_helper unique
      forward := unique.crossing.first_helped
      backward := howner }⟩
  · left
    rw [hsecond] at howner
    exact ⟨{
      next := unique.crossing.second
      next_ne_root := second_ne_helper unique
      forward := hcommonSecond
      backward := howner }⟩
  · rw [hhelper, normalizedSoloMatrix_diagonal] at howner
    linarith
  · rw [hother] at howner
    obtain ⟨returnOwner, hreturn⟩ := positiveOwner unique.other
    rcases label_cases unique returnOwner with
      hreturnFirst | hreturnSecond | hreturnHelper | hreturnOther
    · right
      rw [hreturnFirst] at hreturn
      exact ⟨{
        first := unique.crossing.first
        second := unique.other
        first_ne_root := first_ne_helper unique
        second_ne_root := unique.other_ne_helper
        second_ne_first := other_ne_first unique
        first_edge := unique.crossing.first_helped
        second_edge := hreturn
        closing_edge := howner }⟩
    · right
      rw [hreturnSecond] at hreturn
      exact ⟨{
        first := unique.crossing.second
        second := unique.other
        first_ne_root := second_ne_helper unique
        second_ne_root := unique.other_ne_helper
        second_ne_first := other_ne_second unique
        first_edge := hcommonSecond
        second_edge := hreturn
        closing_edge := howner }⟩
    · left
      rw [hreturnHelper] at hreturn
      exact ⟨{
        next := unique.other
        next_ne_root := unique.other_ne_helper
        forward := hreturn
        backward := howner }⟩
    · rw [hreturnOther, normalizedSoloMatrix_diagonal] at hreturn
      linarith

end FinFourHardCardTwoUniqueSharedHelper

namespace FinFourQuantitativeFullSupportHardResidual

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}

/-- Source-facing rooted-two-next dispatch with the rigid common-helper arm
contracted to a positive return cycle in the actual singleton table. -/
theorem rootedTwoNext_positiveReturnCycle_or_ownerLeaveCollisionChain_or_hardHelperJoin
    (residual : FinFourQuantitativeFullSupportHardResidual reward bound)
    (certificate : QuittingImmediateSingletonCollision reward
      residual.witness.terminalGap)
    (geometry : RootedTwoCycle
      (QuittingSoloPreempts reward residual.witness.terminalGap)
      certificate.owner)
    (marker_eq : certificate.collider = geometry.next) :
    (∃ unique : FinFourHardCardTwoUniqueSharedHelper residual
        {certificate.owner, certificate.collider},
      HasFinFourUniqueSharedHelperPositiveReturnCycle unique) ∨
      ∃ crossing : FinFourHardCardTwoCrossing residual
          {certificate.owner, certificate.collider},
        ((∃ chain :
              FinFourRootedTwoNextOwnerLeaveCollisionChain residual certificate,
            chain.spectator = crossing.firstHelper ∨
              chain.spectator = crossing.secondHelper) ∨
          ∃ helper,
            (helper = crossing.firstHelper ∨
              helper = crossing.secondHelper) ∧
            helper ∉
              ({certificate.owner, certificate.collider} : Finset (Fin 4)) ∧
            quittingSetReward reward
                  ({certificate.owner, certificate.collider} : Finset (Fin 4))
                  helper + residual.witness.terminalGap ≤
              quittingSetReward reward
                (insert helper {certificate.owner, certificate.collider})
                helper) := by
  obtain ⟨crossing, hunique | hchainOrJoin⟩ :=
    residual.rootedTwoNext_uniqueSharedHelper_or_ownerLeaveCollisionChain_or_hardHelperJoin
      certificate geometry marker_eq
  · left
    obtain ⟨unique⟩ := hunique
    exact ⟨unique, unique.hasPositiveReturnCycle⟩
  · exact Or.inr ⟨crossing, hchainOrJoin⟩

end FinFourQuantitativeFullSupportHardResidual

end GameTheory
