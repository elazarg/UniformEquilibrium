/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.InfiniteRun

/-!
# Essential APS depends only on singleton terminal payoffs

The essential-APS language uses a quitting reward table only through its
singleton terminal payoff vectors. This file makes that extensionality
literal. It does not identify the full quitting games: collision payoffs and
all other nonsingleton terminal data may differ.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type}

/-- Two complete quitting reward tables have the same singleton terminal
payoff vectors. No equality is required at nonsingleton coalitions. -/
def HaveSameQuittingSingletonRewards
    (first second : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ quitter, quittingSoloReward first quitter = quittingSoloReward second quitter

namespace HaveSameQuittingSingletonRewards

variable {first second : {S : Finset ι // S.Nonempty} → Payoff ι}
variable (hsame : GameTheory.HaveSameQuittingSingletonRewards first second)

include hsame

theorem soloReward (quitter : ι) :
    quittingSoloReward first quitter = quittingSoloReward second quitter :=
  hsame quitter

theorem soloBaseline :
    quittingSoloBaseline first = quittingSoloBaseline second := by
  funext who
  exact congrFun (hsame who) who

theorem fleschSuccessor_iff (owner successor : ι) :
    QuittingFleschSuccessor first owner successor ↔
      QuittingFleschSuccessor second owner successor := by
  simp only [QuittingFleschSuccessor]
  rw [hsame successor, hsame owner]

theorem essentialAPSViable_iff (value : Payoff ι) :
    QuittingEssentialAPSViable first value ↔
      QuittingEssentialAPSViable second value := by
  unfold QuittingEssentialAPSViable
  rw [hsame.soloBaseline]

theorem essentialAPSTerminal_eq (owner : ι) :
    quittingEssentialAPSTerminal first owner =
      quittingEssentialAPSTerminal second owner := by
  ext value
  simp only [quittingEssentialAPSTerminal, Set.mem_setOf_eq]
  rw [hsame owner, hsame.essentialAPSViable_iff]

theorem essentialAPSPrefix_eq
    (owner : ι) (family : Set (Payoff ι)) :
    quittingEssentialAPSPrefix first owner family =
      quittingEssentialAPSPrefix second owner family := by
  ext value
  simp only [quittingEssentialAPSPrefix, Set.mem_setOf_eq]
  rw [hsame.essentialAPSViable_iff, hsame owner]

theorem segmentEssentialAPSPrefix_eq
    (owner : ι) (family : Set (Payoff ι)) :
    quittingSegmentEssentialAPSPrefix first owner family =
      quittingSegmentEssentialAPSPrefix second owner family := by
  ext value
  simp only [quittingSegmentEssentialAPSPrefix, Set.mem_setOf_eq]
  rw [hsame.essentialAPSViable_iff, hsame owner]

theorem essentialAPSSuccessorSet_eq
    (family : ι → Set (Payoff ι)) (owner : ι) :
    quittingEssentialAPSSuccessorSet first family owner =
      quittingEssentialAPSSuccessorSet second family owner := by
  ext value
  simp only [mem_quittingEssentialAPSSuccessorSet_iff]
  constructor
  · rintro ⟨successor, hedge, hvalue⟩
    exact ⟨successor, (hsame.fleschSuccessor_iff owner successor).mp hedge, hvalue⟩
  · rintro ⟨successor, hedge, hvalue⟩
    exact ⟨successor, (hsame.fleschSuccessor_iff owner successor).mpr hedge, hvalue⟩

theorem essentialAPSOwnerStep_eq
    (family : ι → Set (Payoff ι)) (owner : ι) :
    quittingEssentialAPSOwnerStep first family owner =
      quittingEssentialAPSOwnerStep second family owner := by
  rw [quittingEssentialAPSOwnerStep_eq_prefix,
    quittingEssentialAPSOwnerStep_eq_prefix,
    hsame.essentialAPSSuccessorSet_eq family owner,
    hsame.essentialAPSPrefix_eq owner]

theorem essentialAPSOperator_eq (family : ι → Set (Payoff ι)) :
    quittingEssentialAPSOperator first family =
      quittingEssentialAPSOperator second family := by
  funext owner
  exact hsame.essentialAPSOwnerStep_eq family owner

theorem essentialAPSRestrictedOperator_eq
    (carrier family : ι → Set (Payoff ι)) :
    quittingEssentialAPSRestrictedOperator first carrier family =
      quittingEssentialAPSRestrictedOperator second carrier family := by
  funext owner
  unfold quittingEssentialAPSRestrictedOperator
  rw [hsame.essentialAPSOperator_eq family]

theorem essentialAPSSubinvariantWithin_iff
    (carrier family : ι → Set (Payoff ι)) :
    IsQuittingEssentialAPSSubinvariantWithin first carrier family ↔
      IsQuittingEssentialAPSSubinvariantWithin second carrier family := by
  unfold IsQuittingEssentialAPSSubinvariantWithin
  rw [hsame.essentialAPSRestrictedOperator_eq carrier family]

theorem essentialAPSGreatestFamily_eq (carrier : ι → Set (Payoff ι)) :
    quittingEssentialAPSGreatestFamily first carrier =
      quittingEssentialAPSGreatestFamily second carrier := by
  funext owner
  ext value
  simp only [quittingEssentialAPSGreatestFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨family, hfamily, hvalue⟩
    exact ⟨family,
      (hsame.essentialAPSSubinvariantWithin_iff carrier family).mp hfamily,
      hvalue⟩
  · rintro ⟨family, hfamily, hvalue⟩
    exact ⟨family,
      (hsame.essentialAPSSubinvariantWithin_iff carrier family).mpr hfamily,
      hvalue⟩

theorem essentialAPSInfiniteRun_iff
    (family : ι → Set (Payoff ι)) (owner : ℕ → ι)
    (initial : Payoff ι) (mass : ℕ → ℝ) (value : ℕ → Payoff ι) :
    IsQuittingEssentialAPSInfiniteRun first family owner initial mass value ↔
      IsQuittingEssentialAPSInfiniteRun second family owner initial mass value := by
  unfold IsQuittingEssentialAPSInfiniteRun
  constructor
  · rintro ⟨hinitial, hmem, harc⟩
    refine ⟨hinitial, hmem, fun time ↦ ⟨(harc time).1, ?_⟩⟩
    simpa only [hsame (owner time)] using (harc time).2
  · rintro ⟨hinitial, hmem, harc⟩
    refine ⟨hinitial, hmem, fun time ↦ ⟨(harc time).1, ?_⟩⟩
    simpa only [hsame (owner time)] using (harc time).2

end HaveSameQuittingSingletonRewards

end GameTheory
