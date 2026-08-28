/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import Research.Quitting.FinFourSameStageEndpointMonodromy
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.VanishingDebtAtomAlternative
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# Paid nonsingleton maximum-toggle cycles

This file selects one table-level maximum positive membership toggle at each
Fin4 coalition.  Starting from a nonsingleton coalition, the resulting fixed
finite orbit either reaches a singleton or closes on a simple nonsingleton
cycle.  The cycle can then be copied over any family of actual profiles at
one marked date.  Its edges are sibling comparisons, not chronological
transitions.

The literal profile layer records exact payoff gains, exact mover-debt
subtraction, spectator recharge, and the existing stopping-law atom dispatch.
No return chronology, recursive descent, or uniform-equilibrium consumer is
asserted.
-/

noncomputable section

namespace GameTheory

open Filter MathUE.FiniteBooleanEndpointOrbit
open MathUE.FinFourCoalitionCycle
open QuittingSureSetOwnerRepair

abbrev FinFourNonsingletonCoalition :=
  QuittingNonsingletonCoalition (Fin 4)

/-! ## Fixed table-level maximum toggle -/

/-- The largest positive membership-toggle gain at one Fin4 coalition. -/
def quittingMaximumPositiveToggleGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who ↦
    max 0 (quittingPureToggleGain reward coalition who)

/-- A deterministic, table-level maximizer of positive toggle gain. -/
def quittingMaximumPositiveTogglePlayer
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) : Fin 4 :=
  Classical.choose <| Finset.exists_mem_eq_sup' Finset.univ_nonempty fun who ↦
    max 0 (quittingPureToggleGain reward coalition who)

theorem quittingMaximumPositiveTogglePlayer_spec
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) :
    max 0 (quittingPureToggleGain reward coalition
        (quittingMaximumPositiveTogglePlayer reward coalition)) =
      quittingMaximumPositiveToggleGain reward coalition := by
  exact (Classical.choose_spec <|
    Finset.exists_mem_eq_sup' Finset.univ_nonempty fun who ↦
      max 0 (quittingPureToggleGain reward coalition who)).2.symm

/-- The fixed successor toggles the selected maximizing player. -/
def quittingMaximumPositiveToggleNext
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) : Finset (Fin 4) :=
  quittingToggleCoalition coalition
    (quittingMaximumPositiveTogglePlayer reward coalition)

/-- The selected toggle is exactly the standard prescribed-endpoint routing
at its displayed target action. -/
theorem quittingMaximumPositiveToggleNext_eq_routed
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) :
    quittingMaximumPositiveToggleNext reward coalition =
      quittingPureEndpointRoutedCoalition coalition
        (quittingMaximumPositiveTogglePlayer reward coalition)
        (quittingCoalitionAction
          (quittingMaximumPositiveToggleNext reward coalition)
          (quittingMaximumPositiveTogglePlayer reward coalition)) := by
  unfold quittingMaximumPositiveToggleNext
  by_cases hmem : quittingMaximumPositiveTogglePlayer reward coalition ∈
      coalition
  · rw [quittingToggleCoalition_of_mem hmem]
    simp [quittingPureEndpointRoutedCoalition, quittingCoalitionAction, hmem]
  · rw [quittingToggleCoalition_of_notMem hmem]
    simp [quittingPureEndpointRoutedCoalition, quittingCoalitionAction, hmem]

/-- Pure nonsingleton debt is the positive part of the corresponding static
toggle gain.  The nonsingleton hypothesis removes the only tail-exposing
singleton-leave boundary. -/
theorem quittingTerminalSemanticDebt_pureNonsingleton_eq_max_zero_toggleGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : FinFourNonsingletonCoalition) (who : Fin 4) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingStationaryProfile reward
            (quittingPureSetRoot coalition.1))) who =
      max 0 (quittingPureToggleGain reward coalition.1 who) := by
  rw [quittingTerminalSemanticDebt_pureSetRoot_eq]
  by_cases hwho : who ∈ coalition.1
  · have herase : (coalition.1.erase who).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hcard := coalition.2
      have hcardOne : coalition.1.card = 1 := by
        rw [← Finset.card_erase_add_one hwho, hempty]
        simp
      omega
    rw [Finset.insert_eq_self.mpr hwho,
      quittingPureToggleGain, quittingToggleCoalition_of_mem hwho]
    by_cases hle : quittingSetReward reward (coalition.1.erase who) who ≤
        quittingSetReward reward coalition.1 who
    · rw [max_eq_left hle, max_eq_left (sub_nonpos.mpr hle)]
      ring
    · have hle' : quittingSetReward reward coalition.1 who ≤
          quittingSetReward reward (coalition.1.erase who) who :=
        le_of_not_ge hle
      rw [max_eq_right hle', max_eq_right (sub_nonneg.mpr hle')]
  · rw [Finset.erase_eq_of_notMem hwho,
      quittingPureToggleGain, quittingToggleCoalition_of_notMem hwho]
    by_cases hle : quittingSetReward reward (insert who coalition.1) who ≤
        quittingSetReward reward coalition.1 who
    · rw [max_eq_right hle, max_eq_left (sub_nonpos.mpr hle)]
      ring
    · have hle' : quittingSetReward reward coalition.1 who ≤
          quittingSetReward reward (insert who coalition.1) who :=
        le_of_not_ge hle
      rw [max_eq_left hle', max_eq_right (sub_nonneg.mpr hle')]

/-- Global positive minimum debt forces the selected table toggle to gain at
least one quarter of that minimum. -/
theorem minimumDebt_div_four_le_maximumPositiveToggleGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (coalition : FinFourNonsingletonCoalition) :
    quittingTerminalSemanticDebtSum minimum / 4 ≤
      quittingMaximumPositiveToggleGain reward coalition.1 := by
  let candidate := quittingTerminalSemanticPair reward
    (quittingStationaryProfile reward (quittingPureSetRoot coalition.1))
  have hcandidate : candidate ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have hlower := hminimum candidate hcandidate
  have hdebt : quittingTerminalSemanticDebtSum candidate =
      ∑ who, max 0 (quittingPureToggleGain reward coalition.1 who) := by
    unfold quittingTerminalSemanticDebtSum
    apply Finset.sum_congr rfl
    intro who _
    exact quittingTerminalSemanticDebt_pureNonsingleton_eq_max_zero_toggleGain
      reward coalition who
  have hsum : (∑ who, max 0
        (quittingPureToggleGain reward coalition.1 who)) ≤
      4 * quittingMaximumPositiveToggleGain reward coalition.1 := by
    unfold quittingMaximumPositiveToggleGain
    calc
      (∑ who, max 0 (quittingPureToggleGain reward coalition.1 who)) ≤
          ∑ _who : Fin 4,
            quittingMaximumPositiveToggleGain reward coalition.1 := by
        apply Finset.sum_le_sum
        intro who _
        change max 0 (quittingPureToggleGain reward coalition.1 who) ≤
          Finset.univ.sup' Finset.univ_nonempty fun player ↦
            max 0 (quittingPureToggleGain reward coalition.1 player)
        exact Finset.le_sup'
          (fun player : Fin 4 ↦
            max 0 (quittingPureToggleGain reward coalition.1 player))
          (Finset.mem_univ who)
      _ = 4 * quittingMaximumPositiveToggleGain reward coalition.1 := by
        simp
  rw [hdebt] at hlower
  linarith

theorem minimumDebt_div_four_le_selectedToggleGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (coalition : FinFourNonsingletonCoalition) :
    quittingTerminalSemanticDebtSum minimum / 4 ≤
      quittingPureToggleGain reward coalition.1
        (quittingMaximumPositiveTogglePlayer reward coalition.1) := by
  have hfloor := minimumDebt_div_four_le_maximumPositiveToggleGain
    reward minimum hminimum coalition
  have hmaxPos : 0 < quittingMaximumPositiveToggleGain reward coalition.1 :=
    (div_pos hpositive (by norm_num)).trans_le hfloor
  rw [← quittingMaximumPositiveTogglePlayer_spec] at hmaxPos hfloor
  have htogglePos : 0 < quittingPureToggleGain reward coalition.1
      (quittingMaximumPositiveTogglePlayer reward coalition.1) := by
    by_contra hnot
    have htoggleNonpos : quittingPureToggleGain reward coalition.1
        (quittingMaximumPositiveTogglePlayer reward coalition.1) ≤ 0 :=
      le_of_not_gt hnot
    rw [max_eq_left htoggleNonpos] at hmaxPos
    exact (lt_irrefl 0) hmaxPos
  rw [max_eq_right htogglePos.le] at hfloor
  exact hfloor

/-- The selected table toggle has its literal static gain at every declared
continuation payoff.  Nonsingletonity prevents the Continue endpoint from
falling through to the tail. -/
theorem quittingRootSuccessorPayoff_maximumPositiveToggle_eq_toggleGain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (tail : Payoff (Fin 4)) (source : FinFourNonsingletonCoalition) :
    let mover := quittingMaximumPositiveTogglePlayer reward source.1
    quittingRootSuccessorPayoff reward tail
          (Function.update (quittingPureSetRoot source.1) mover
            (PMF.pure (quittingCoalitionAction
              (quittingMaximumPositiveToggleNext reward source.1) mover))) mover -
        quittingRootSuccessorPayoff reward tail
          (quittingPureSetRoot source.1) mover =
      quittingPureToggleGain reward source.1 mover := by
  dsimp only
  unfold quittingMaximumPositiveToggleNext quittingPureToggleGain
  by_cases hmem : quittingMaximumPositiveTogglePlayer reward source.1 ∈ source.1
  · have herase : (source.1.erase
        (quittingMaximumPositiveTogglePlayer reward source.1)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hcardOne : source.1.card = 1 := by
        rw [← Finset.card_erase_add_one hmem, hempty]
        simp
      have hnonsingleton := source.2
      omega
    rw [quittingToggleCoalition_of_mem hmem]
    change quittingRootExpectedPayoff reward tail
          (Function.update (quittingPureSetRoot source.1) _ _) _ -
        quittingRootSuccessorPayoff reward tail (quittingPureSetRoot source.1) _ = _
    rw [quittingRootExpectedPayoff_update_eq_endpointMix,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty
        tail source.1 _ herase,
      quittingRootQuitPayoff_pureSetRoot_eq_insert]
    simp [quittingCoalitionAction, quittingSetAction, quittingPureSetRoot,
      hmem, Finset.insert_eq_self.mpr hmem]
  · rw [quittingToggleCoalition_of_notMem hmem]
    change quittingRootExpectedPayoff reward tail
          (Function.update (quittingPureSetRoot source.1) _ _) _ -
        quittingRootSuccessorPayoff reward tail (quittingPureSetRoot source.1) _ = _
    rw [quittingRootExpectedPayoff_update_eq_endpointMix,
      quittingRootSuccessorPayoff_eq_endpointMix,
      quittingRootQuitPayoff_pureSetRoot_eq_insert,
      quittingRootContinuePayoff_pureSetRoot_eq_erase_of_nonempty]
    · simp [quittingCoalitionAction, quittingSetAction, quittingPureSetRoot, hmem]
    · simpa [Finset.erase_eq_of_notMem hmem] using
        (Finset.card_pos.mp (lt_trans Nat.zero_lt_one source.2))

/-! ## Fixed finite dispatch -/

/-- The selected maximum toggle reaches a singleton. -/
structure FinFourMaximumToggleSingletonRoute
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source : FinFourNonsingletonCoalition) where
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  terminal_card : terminal.val.card = 1
  terminal_eq : terminal.val =
    quittingMaximumPositiveToggleNext reward source.1

/-- One selected maximum toggle stays in the nonsingleton state space. -/
structure FinFourMaximumNonsingletonToggleEdge
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source target : FinFourNonsingletonCoalition) where
  target_eq : target.1 = quittingMaximumPositiveToggleNext reward source.1

/-- Every nonsingleton coalition has exactly the fixed selected successor,
classified by whether that successor is a singleton. -/
theorem finFourMaximumToggle_dispatch
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (source : FinFourNonsingletonCoalition) :
    Nonempty (FinFourMaximumToggleSingletonRoute reward source) ∨
      ∃ target, Nonempty
        (FinFourMaximumNonsingletonToggleEdge reward source target) := by
  let routed := quittingMaximumPositiveToggleNext reward source.1
  have hrouted : routed.Nonempty := by
    unfold routed quittingMaximumPositiveToggleNext
    by_cases hwho : quittingMaximumPositiveTogglePlayer reward source.1 ∈ source.1
    · rw [quittingToggleCoalition_of_mem hwho]
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hcardOne : source.1.card = 1 := by
        rw [← Finset.card_erase_add_one hwho, hempty]
        simp
      have hnonsingleton := source.2
      omega
    · rw [quittingToggleCoalition_of_notMem hwho]
      exact Finset.insert_nonempty _ _
  have hcard : routed.card = 1 ∨ 1 < routed.card := by
    have hpositive : 0 < routed.card := Finset.card_pos.mpr hrouted
    omega
  rcases hcard with hsingleton | hnonsingleton
  · left
    exact ⟨⟨⟨routed, hrouted⟩, hsingleton, rfl⟩⟩
  · right
    let target : FinFourNonsingletonCoalition := ⟨routed, hnonsingleton⟩
    exact ⟨target, ⟨⟨rfl⟩⟩⟩

/-- The fixed maximum-toggle orbit either first reaches a singleton or has a
simple closed nonsingleton segment. -/
theorem exists_finFourMaximumToggle_terminalOrbit_or_closedSegment
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (start : FinFourNonsingletonCoalition) :
    Nonempty (DispatchedOrbit
      (fun source ↦ Nonempty (FinFourMaximumToggleSingletonRoute reward source))
      (fun source target ↦ Nonempty
        (FinFourMaximumNonsingletonToggleEdge reward source target)) start) ∨
      Nonempty (DispatchedClosedSegment
        (fun source ↦ Nonempty (FinFourMaximumToggleSingletonRoute reward source))
        (fun source target ↦ Nonempty
          (FinFourMaximumNonsingletonToggleEdge reward source target)) start) := by
  apply exists_dispatchedOrbit_terminal_or_closedSegment
  intro source
  exact finFourMaximumToggle_dispatch reward source

/-! ## Literal profile realization of one fixed edge -/

/-- The actual sibling profile displaying a fixed nonsingleton coalition at
one marked date of a supplied complete behavioral profile. -/
def quittingMaximumToggleSiblingProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (coalition : FinFourNonsingletonCoalition) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootCoalitionProfile reward profile stage coalition

/-- The complete target strategy on one maximum-toggle sibling edge. -/
def quittingMaximumToggleTargetStrategy
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source target : FinFourNonsingletonCoalition)
    (_edge : FinFourMaximumNonsingletonToggleEdge reward source target) :
    (quittingGame reward).BehaviorStrategy
      (quittingMaximumPositiveTogglePlayer reward source.1) :=
  (quittingMaximumToggleSiblingProfile reward profile stage target)
    (quittingMaximumPositiveTogglePlayer reward source.1)

/-- The selected target is the literal one-date action edit of the selected
source sibling. -/
theorem quittingMaximumToggleSiblingProfile_target_eq_literalOneDateProfile
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source target : FinFourNonsingletonCoalition)
    (edge : FinFourMaximumNonsingletonToggleEdge reward source target) :
    quittingMaximumToggleSiblingProfile reward profile stage target =
      quittingLiteralOneDateProfile reward
        (quittingMaximumToggleSiblingProfile reward profile stage source)
        (quittingMaximumPositiveTogglePlayer reward source.1)
        stage
        (quittingCoalitionAction target.1
          (quittingMaximumPositiveTogglePlayer reward source.1)) := by
  symm
  unfold quittingLiteralOneDateProfile
    quittingMaximumToggleSiblingProfile
    quittingLiteralPureRootCoalitionProfile
    quittingPureRootOfCoalition
  apply quittingLiteralPureRootProfile_update_eq_routed
  have haction :
      quittingCoalitionAction target.1
          (quittingMaximumPositiveTogglePlayer reward source.1) =
        quittingCoalitionAction
          (quittingMaximumPositiveToggleNext reward source.1)
          (quittingMaximumPositiveTogglePlayer reward source.1) := by
    rw [edge.target_eq]
  rw [haction]
  exact edge.target_eq.trans
    (quittingMaximumPositiveToggleNext_eq_routed reward source.1)

/-- A fixed table edge is literally a unilateral update between complete
same-date sibling profiles. -/
theorem quittingMaximumToggleSiblingProfile_target_eq_update
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source target : FinFourNonsingletonCoalition)
    (edge : FinFourMaximumNonsingletonToggleEdge reward source target) :
    quittingMaximumToggleSiblingProfile reward profile stage target =
      Function.update
        (quittingMaximumToggleSiblingProfile reward profile stage source)
        (quittingMaximumPositiveTogglePlayer reward source.1)
        (quittingMaximumToggleTargetStrategy reward profile stage source target edge) := by
  unfold quittingMaximumToggleTargetStrategy
  rw [quittingMaximumToggleSiblingProfile_target_eq_literalOneDateProfile
    reward profile stage source target edge]
  simp only [quittingLiteralOneDateProfile, Function.update_self]

/-- Every sibling is literally the supplied source away from its one marked
date. -/
theorem quittingMaximumToggleSiblingProfile_at_of_ne
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage time : ℕ)
    (coalition : FinFourNonsingletonCoalition) (htime : time ≠ stage)
    (player : Fin 4) :
    quittingMaximumToggleSiblingProfile reward profile stage coalition player time =
      profile player time := by
  funext history
  exact congrFun
    (quittingLiteralOneDateOverride_of_ne (profile player) stage time _ htime)
    history

/-- Every sibling has the same reached live mass as the supplied profile. -/
theorem quittingMaximumToggleSiblingProfile_liveMass_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (coalition : FinFourNonsingletonCoalition) :
    quittingLiveMass reward
        (quittingMaximumToggleSiblingProfile reward profile stage coalition)
        stage = quittingLiveMass reward profile stage :=
  quittingLiveMass_literalPureRootProfile_eq reward profile stage _

/-- Every sibling has the exact common complete post-date spine. -/
theorem quittingMaximumToggleSiblingProfile_postDateSpine_eq
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (coalition : FinFourNonsingletonCoalition) :
    quittingAllContinueProfileSpine reward
        (quittingMaximumToggleSiblingProfile reward profile stage coalition)
        (stage + 1) =
      quittingAllContinueProfileSpine reward profile (stage + 1) := by
  apply quittingAllContinueProfileSpine_eq_of_eq_from
  intro who time history htime
  have hne : time ≠ stage := by omega
  exact congrFun
    (quittingMaximumToggleSiblingProfile_at_of_ne reward profile stage time
      coalition hne who) history

/-- Exact payoff gain on a selected table edge. -/
theorem quittingMaximumToggleSiblingProfile_gain_eq_liveMass_mul
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source target : FinFourNonsingletonCoalition)
    (edge : FinFourMaximumNonsingletonToggleEdge reward source target) :
    let mover := quittingMaximumPositiveTogglePlayer reward source.1
    quittingTerminalPayoff reward
          (quittingMaximumToggleSiblingProfile reward profile stage target) mover -
        quittingTerminalPayoff reward
          (quittingMaximumToggleSiblingProfile reward profile stage source) mover =
      quittingLiveMass reward profile stage *
        quittingPureToggleGain reward source.1 mover := by
  dsimp only
  rw [quittingMaximumToggleSiblingProfile_target_eq_literalOneDateProfile
    reward profile stage source target edge]
  have hgain :=
    quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
      reward
        (quittingMaximumToggleSiblingProfile reward profile stage source)
        (quittingMaximumPositiveTogglePlayer reward source.1) stage
        (quittingCoalitionAction target.1
          (quittingMaximumPositiveTogglePlayer reward source.1))
  rw [quittingMaximumToggleSiblingProfile_liveMass_eq] at hgain
  rw [show quittingProfileLiveRoot reward
      (quittingMaximumToggleSiblingProfile reward profile stage source) stage =
        quittingPureSetRoot source.1 by
    exact quittingProfileLiveRoot_literalPureRootProfile_self
      reward profile stage _] at hgain
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward
      (quittingMaximumToggleSiblingProfile reward profile stage source)
      (stage + 1))).1
  have hrootGain :=
    quittingRootSuccessorPayoff_maximumPositiveToggle_eq_toggleGain
      reward tail source
  rw [← edge.target_eq] at hrootGain
  change _ = quittingLiveMass reward profile stage * _ at hgain
  rw [hrootGain] at hgain
  exact hgain

/-- The mover's unrestricted whole-profile debt falls by exactly its actual
payoff gain on a sibling edge. -/
theorem quittingMaximumToggleSiblingProfile_moverDebt_eq_sub_gain
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (source target : FinFourNonsingletonCoalition)
    (edge : FinFourMaximumNonsingletonToggleEdge reward source target) :
    let mover := quittingMaximumPositiveTogglePlayer reward source.1
    let sourceProfile :=
      quittingMaximumToggleSiblingProfile reward profile stage source
    let targetProfile :=
      quittingMaximumToggleSiblingProfile reward profile stage target
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward targetProfile) mover =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward sourceProfile) mover -
        (quittingTerminalPayoff reward targetProfile mover -
          quittingTerminalPayoff reward sourceProfile mover) := by
  dsimp only
  rw [quittingMaximumToggleSiblingProfile_target_eq_literalOneDateProfile
    reward profile stage source target edge]
  exact quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    reward _ _ stage _

/-! ## Closed-segment accessors and Fin4 period -/

namespace FinFourMaximumToggleClosedSegment

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {start : FinFourNonsingletonCoalition}

abbrev Trace
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {start : FinFourNonsingletonCoalition} := DispatchedClosedSegment
  (fun source ↦ Nonempty (FinFourMaximumToggleSingletonRoute reward source))
  (fun source target ↦ Nonempty
    (FinFourMaximumNonsingletonToggleEdge reward source target)) start

/-- The selected table edge at one offset of the simple closed segment. -/
theorem edge (trace : Trace (reward := reward) (start := start))
    (offset : Fin trace.segment.segment.period) :
    FinFourMaximumNonsingletonToggleEdge reward
      (trace.orbit (trace.segment.segment.start + offset))
      (trace.orbit (trace.segment.segment.start + offset + 1)) :=
  Classical.choice (trace.offset_edge offset)

/-- The literal sibling at a natural offset from the closed segment's base. -/
def profileAt (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage offset : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingMaximumToggleSiblingProfile reward profile stage
    (trace.orbit (trace.segment.segment.start + offset))

/-- The mover label of a selected cycle edge. -/
def moverAt (trace : Trace (reward := reward) (start := start))
    (offset : Fin trace.segment.segment.period) : Fin 4 :=
  quittingMaximumPositiveTogglePlayer reward
    (trace.orbit (trace.segment.segment.start + offset)).1

/-- The actual mover payoff gain at one sibling edge. -/
def gainAt (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) : ℝ :=
  quittingTerminalPayoff reward (profileAt trace profile stage (offset + 1))
      (moverAt trace offset) -
    quittingTerminalPayoff reward (profileAt trace profile stage offset)
      (moverAt trace offset)

/-- The complete sibling profile returns literally after one cycle. -/
theorem profileAt_period_eq_zero
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    profileAt trace profile stage trace.segment.segment.period =
      profileAt trace profile stage 0 := by
  apply congrArg (quittingMaximumToggleSiblingProfile reward profile stage)
  simpa only [profileAt, Nat.add_zero] using trace.segment.segment.closes

/-- Each selected cycle edge is literally one complete-strategy update. -/
theorem profileAt_succ_eq_update
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) :
    profileAt trace profile stage (offset + 1) =
      Function.update (profileAt trace profile stage offset)
        (moverAt trace offset)
        ((profileAt trace profile stage (offset + 1))
          (moverAt trace offset)) := by
  exact quittingMaximumToggleSiblingProfile_target_eq_update reward profile stage
    _ _ (edge trace offset)

/-- The selected cycle gain is the common reached live mass times the fixed
table toggle gain. -/
theorem gainAt_eq_liveMass_mul
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) :
    gainAt trace profile stage offset =
      quittingLiveMass reward profile stage *
        quittingPureToggleGain reward
          (trace.orbit (trace.segment.segment.start + offset)).1
          (moverAt trace offset) := by
  exact quittingMaximumToggleSiblingProfile_gain_eq_liveMass_mul
    reward profile stage _ _ (edge trace offset)

/-- The mover's exact whole-profile debt subtraction on one cycle edge. -/
theorem moverDebt_succ_eq_sub_gain
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (profileAt trace profile stage (offset + 1)))
        (moverAt trace offset) =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profileAt trace profile stage offset))
          (moverAt trace offset) -
        gainAt trace profile stage offset := by
  exact quittingMaximumToggleSiblingProfile_moverDebt_eq_sub_gain
    reward profile stage _ _ (edge trace offset)

/-- Every edge of the fixed maximum-toggle cycle has the sharp actual paid
floor `lambda * D_* / 4`. -/
theorem gainAt_floor
    (trace : Trace (reward := reward) (start := start))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (lambda : ℝ) (_hlambda : 0 < lambda)
    (hlive : lambda ≤ quittingLiveMass reward profile stage)
    (offset : Fin trace.segment.segment.period) :
    lambda * quittingTerminalSemanticDebtSum minimum / 4 ≤
      gainAt trace profile stage offset := by
  rw [gainAt_eq_liveMass_mul trace]
  have htoggle := minimumDebt_div_four_le_selectedToggleGain reward minimum
    hminimum hpositive
      (trace.orbit (trace.segment.segment.start + offset))
  have hminimumNonneg := hpositive.le
  have hliveScaled := mul_le_mul hlive htoggle
    (div_nonneg hminimumNonneg (by norm_num))
    (quittingLiveMass_nonneg reward profile stage)
  simpa only [moverAt, div_eq_mul_inv, mul_assoc] using (show
    lambda * (quittingTerminalSemanticDebtSum minimum / 4) ≤
      quittingLiveMass reward profile stage *
        quittingPureToggleGain reward
          (trace.orbit (trace.segment.segment.start + offset)).1
          (quittingMaximumPositiveTogglePlayer reward
            (trace.orbit (trace.segment.segment.start + offset)).1) from
    hliveScaled)

private theorem eq_of_toggle_toggle_eq
    (coalition : Finset (Fin 4)) (first second : Fin 4)
    (hreturn : quittingToggleCoalition
      (quittingToggleCoalition coalition first) second = coalition) :
    second = first := by
  by_contra hne
  have hmembership := congrArg (fun target ↦ first ∈ target) hreturn
  by_cases hfirst : first ∈ coalition <;>
    by_cases hsecond : second ∈ coalition <;>
      simp [quittingToggleCoalition, hfirst, hsecond, hne] at hmembership
  all_goals exact hne hmembership.symm

/-- The selected maximum-toggle cycle cannot have period two: the same
undirected toggle would have to have strictly positive gain in both
directions. -/
theorem period_ne_two
    (trace : Trace (reward := reward) (start := start))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    trace.segment.segment.period ≠ 2 := by
  intro hperiod
  let zero : Fin trace.segment.segment.period := ⟨0, by omega⟩
  let one : Fin trace.segment.segment.period := ⟨1, by omega⟩
  let first := edge trace zero
  let second := edge trace one
  have hclose : trace.orbit (trace.segment.segment.start + 2) =
      trace.orbit trace.segment.segment.start := by
    simpa [hperiod] using trace.segment.segment.closes
  have first' : FinFourMaximumNonsingletonToggleEdge reward
      (trace.orbit trace.segment.segment.start)
      (trace.orbit (trace.segment.segment.start + 1)) := by
    simpa [zero] using first
  have second' : FinFourMaximumNonsingletonToggleEdge reward
      (trace.orbit (trace.segment.segment.start + 1))
      (trace.orbit trace.segment.segment.start) := by
    rw [← hclose]
    simpa [one] using second
  have hfirstToggle :
      (trace.orbit (trace.segment.segment.start + 1)).1 =
        quittingToggleCoalition
          (trace.orbit trace.segment.segment.start).1
          (quittingMaximumPositiveTogglePlayer reward
            (trace.orbit trace.segment.segment.start).1) := by
    simpa only [quittingMaximumPositiveToggleNext] using first'.target_eq
  have hsecondToggle :
      (trace.orbit trace.segment.segment.start).1 =
        quittingToggleCoalition
          (trace.orbit (trace.segment.segment.start + 1)).1
          (quittingMaximumPositiveTogglePlayer reward
            (trace.orbit (trace.segment.segment.start + 1)).1) := by
    simpa only [quittingMaximumPositiveToggleNext] using second'.target_eq
  have hreturn : quittingToggleCoalition
      (quittingToggleCoalition
        (trace.orbit trace.segment.segment.start).1
        (quittingMaximumPositiveTogglePlayer reward
          (trace.orbit trace.segment.segment.start).1))
      (quittingMaximumPositiveTogglePlayer reward
        (trace.orbit (trace.segment.segment.start + 1)).1) =
      (trace.orbit trace.segment.segment.start).1 := by
    rw [← hfirstToggle, ← hsecondToggle]
  have hmover : quittingMaximumPositiveTogglePlayer reward
      (trace.orbit (trace.segment.segment.start + 1)).1 =
        quittingMaximumPositiveTogglePlayer reward
          (trace.orbit trace.segment.segment.start).1 :=
    eq_of_toggle_toggle_eq _ _ _ hreturn
  have hfirst := minimumDebt_div_four_le_selectedToggleGain reward minimum
    hminimum hpositive (trace.orbit trace.segment.segment.start)
  have hsecond := minimumDebt_div_four_le_selectedToggleGain reward minimum
    hminimum hpositive (trace.orbit (trace.segment.segment.start + 1))
  have hfirstGain : 0 < quittingPureToggleGain reward
      (trace.orbit trace.segment.segment.start).1
        (quittingMaximumPositiveTogglePlayer reward
          (trace.orbit trace.segment.segment.start).1) :=
    (div_pos hpositive (by norm_num)).trans_le hfirst
  have hsecondGain : 0 < quittingPureToggleGain reward
      (trace.orbit (trace.segment.segment.start + 1)).1
        (quittingMaximumPositiveTogglePlayer reward
          (trace.orbit (trace.segment.segment.start + 1)).1) :=
    (div_pos hpositive (by norm_num)).trans_le hsecond
  unfold quittingPureToggleGain at hfirstGain hsecondGain
  rw [← hfirstToggle] at hfirstGain
  rw [← hsecondToggle, hmover] at hsecondGain
  linarith

private def cycleNext (period : ℕ) (hperiod : 0 < period)
    (offset : Fin period) : Fin period :=
  ⟨(offset + 1) % period, Nat.mod_lt _ hperiod⟩

private theorem orbit_cycleNext_eq
    (trace : Trace (reward := reward) (start := start))
    (offset : Fin trace.segment.segment.period) :
    trace.orbit (trace.segment.segment.start +
        (cycleNext trace.segment.segment.period
          trace.segment.segment.period_pos offset : Fin _)) =
      trace.orbit (trace.segment.segment.start + offset + 1) := by
  unfold cycleNext
  change trace.orbit (trace.segment.segment.start +
      ((offset.val + 1) % trace.segment.segment.period)) =
    trace.orbit (trace.segment.segment.start + offset.val + 1)
  by_cases hlt : offset.val + 1 < trace.segment.segment.period
  · apply congrArg trace.orbit
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · have heq : offset.val + 1 = trace.segment.segment.period := by omega
    simpa [heq, Nat.add_assoc] using trace.segment.segment.closes.symm

private theorem oneCoordinateAdjacent_of_toggle
    (source target : FinFourNonsingletonCoalition) (who : Fin 4)
    (htarget : target.1 = quittingToggleCoalition source.1 who) :
    oneCoordinateAdjacent (coalitionCodeEquiv.symm source)
      (coalitionCodeEquiv.symm target) := by
  unfold oneCoordinateAdjacent
  rw [coalitionSet_equiv_symm, coalitionSet_equiv_symm, htarget]
  by_cases hwho : who ∈ source.1
  · rw [quittingToggleCoalition_of_mem hwho]
    have hleft : source.1 \ source.1.erase who = {who} := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [hwho]
      · simp [hplayer]
    have hright : source.1.erase who \ source.1 = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.erase_subset _ _)
    rw [hleft, hright]
    simp
  · rw [quittingToggleCoalition_of_notMem hwho]
    have hleft : source.1 \ insert who source.1 = ∅ :=
      Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_insert _ _)
    have hright : insert who source.1 \ source.1 = {who} := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [hwho]
      · simp [hplayer]
    rw [hleft, hright]
    simp

private def traceCode
    (trace : Trace (reward := reward) (start := start))
    (offset : Fin trace.segment.segment.period) : CoalitionCode :=
  coalitionCodeEquiv.symm
    (trace.orbit (trace.segment.segment.start + offset))

private theorem traceCode_injective
    (trace : Trace (reward := reward) (start := start)) :
    Function.Injective (traceCode trace) := by
  intro first second heq
  apply trace.segment.offset_injective
  have hcoalition := congrArg coalitionCodeEquiv heq
  simpa [traceCode] using hcoalition

private theorem traceCode_adjacent
    (trace : Trace (reward := reward) (start := start))
    (offset : Fin trace.segment.segment.period) :
    oneCoordinateAdjacent (traceCode trace offset)
      (traceCode trace
        (cycleNext trace.segment.segment.period
          trace.segment.segment.period_pos offset)) := by
  let selected := edge trace offset
  have hnext := orbit_cycleNext_eq trace offset
  apply oneCoordinateAdjacent_of_toggle _ _ (moverAt trace offset)
  have htarget := selected.target_eq
  change (trace.orbit (trace.segment.segment.start + offset + 1)).1 =
    quittingToggleCoalition
      (trace.orbit (trace.segment.segment.start + offset)).1
      (moverAt trace offset) at htarget
  rw [← htarget]
  exact congrArg Subtype.val hnext

private def orderedCycle
    (trace : Trace (reward := reward) (start := start)) :
    OrderedBooleanCycle where
  period := trace.segment.segment.period
  period_pos := trace.segment.segment.period_pos
  vertex := traceCode trace
  vertex_injective := traceCode_injective trace
  adjacent := by
    intro offset
    simpa [cycleNext, cycleNext'] using traceCode_adjacent trace offset

private theorem orderedBooleanCycle_period_even
    (cycle : OrderedBooleanCycle) : Even cycle.period := by
  let triples : Finset (Fin cycle.period) :=
    Finset.univ.filter fun offset ↦ isTriple (cycle.vertex offset)
  let others : Finset (Fin cycle.period) :=
    Finset.univ.filter fun offset ↦ ¬isTriple (cycle.vertex offset)
  have hcard : triples.card = others.card := by
    apply Finset.card_bijective
      (cycleNext' cycle.period cycle.period_pos)
      (cycleNext'_bijective cycle.period cycle.period_pos)
    intro offset
    simp only [triples, others, Finset.mem_filter, Finset.mem_univ, true_and]
    exact adjacent_triple_xor _ _ (cycle.adjacent offset)
  have hdisjoint : Disjoint triples others := by
    apply Finset.disjoint_left.2
    intro offset htriple hother
    exact (Finset.mem_filter.1 hother).2 (Finset.mem_filter.1 htriple).2
  have hunion : triples ∪ others = Finset.univ := by
    ext offset
    simp only [triples, others, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  have hsum : triples.card + others.card = cycle.period := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
    simp
  exact ⟨triples.card, by omega⟩

theorem period_even
    (trace : Trace (reward := reward) (start := start)) :
    Even trace.segment.segment.period :=
  orderedBooleanCycle_period_even (orderedCycle trace)

theorem period_le_eight
    (trace : Trace (reward := reward) (start := start)) :
    trace.segment.segment.period ≤ 8 :=
  orderedBooleanCycle_card_le_eight (orderedCycle trace)

/-- Exact Fin4 cycle-length classification for the selected paid orbit. -/
theorem period_eq_four_or_six_or_eight
    (trace : Trace (reward := reward) (start := start))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    trace.segment.segment.period = 4 ∨
      trace.segment.segment.period = 6 ∨
        trace.segment.segment.period = 8 := by
  obtain ⟨half, hhalf⟩ := period_even trace
  have hpos := trace.segment.segment.period_pos
  have hbound := period_le_eight trace
  have hnotTwo := period_ne_two trace minimum hminimum hpositive
  omega

end FinFourMaximumToggleClosedSegment

/-! ## Paid singleton terminal orbit -/

namespace FinFourMaximumToggleTerminalOrbit

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {start : FinFourNonsingletonCoalition}

abbrev Trace
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {start : FinFourNonsingletonCoalition} := DispatchedOrbit
  (fun source ↦ Nonempty (FinFourMaximumToggleSingletonRoute reward source))
  (fun source target ↦ Nonempty
    (FinFourMaximumNonsingletonToggleEdge reward source target)) start

def sourceCoalition
    (trace : Trace (reward := reward) (start := start)) :
    FinFourNonsingletonCoalition :=
  trace.orbit trace.terminal_time

def route (trace : Trace (reward := reward) (start := start)) :
    FinFourMaximumToggleSingletonRoute reward (sourceCoalition trace) :=
  Classical.choice trace.terminal_at

def mover (trace : Trace (reward := reward) (start := start)) : Fin 4 :=
  quittingMaximumPositiveTogglePlayer reward (sourceCoalition trace).1

def action (trace : Trace (reward := reward) (start := start)) : Bool :=
  quittingCoalitionAction (route trace).terminal.val (mover trace)

theorem terminal_eq_routed
    (trace : Trace (reward := reward) (start := start)) :
    (route trace).terminal.val = quittingPureEndpointRoutedCoalition
      (sourceCoalition trace).1 (mover trace) (action trace) := by
  rw [(route trace).terminal_eq]
  simpa only [mover, action, (route trace).terminal_eq] using
    quittingMaximumPositiveToggleNext_eq_routed reward
      (sourceCoalition trace).1

def sourceProfile (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingMaximumToggleSiblingProfile reward profile stage
    (sourceCoalition trace)

def targetProfile (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPureRootProfile reward profile stage
    (quittingCoalitionAction (route trace).terminal.val)

theorem targetProfile_eq_literalOneDateProfile
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    targetProfile trace profile stage =
      quittingLiteralOneDateProfile reward (sourceProfile trace profile stage)
        (mover trace) stage (action trace) := by
  symm
  unfold quittingLiteralOneDateProfile sourceProfile targetProfile
    quittingMaximumToggleSiblingProfile
    quittingLiteralPureRootCoalitionProfile
    quittingPureRootOfCoalition
  apply quittingLiteralPureRootProfile_update_eq_routed
  exact terminal_eq_routed trace

theorem targetProfile_eq_update
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    targetProfile trace profile stage =
      Function.update (sourceProfile trace profile stage) (mover trace)
        (targetProfile trace profile stage (mover trace)) := by
  rw [targetProfile_eq_literalOneDateProfile trace]
  simp only [quittingLiteralOneDateProfile, Function.update_self]

def gain (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) : ℝ :=
  quittingTerminalPayoff reward (targetProfile trace profile stage) (mover trace) -
    quittingTerminalPayoff reward (sourceProfile trace profile stage) (mover trace)

theorem gain_eq_liveMass_mul_toggleGain
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    gain trace profile stage = quittingLiveMass reward profile stage *
      quittingPureToggleGain reward (sourceCoalition trace).1 (mover trace) := by
  unfold gain
  rw [targetProfile_eq_literalOneDateProfile trace]
  have hgain :=
    quittingTerminalPayoff_literalOneDateProfile_gain_eq_liveMass_mul_defect
    reward (sourceProfile trace profile stage) (mover trace) stage (action trace)
  have hlive : quittingLiveMass reward (sourceProfile trace profile stage) stage =
      quittingLiveMass reward profile stage := by
    exact quittingMaximumToggleSiblingProfile_liveMass_eq reward profile stage _
  rw [hlive] at hgain
  have hroot : quittingProfileLiveRoot reward
      (sourceProfile trace profile stage) stage =
      quittingPureSetRoot (sourceCoalition trace).1 := by
    exact quittingProfileLiveRoot_literalPureRootProfile_self reward profile stage _
  rw [hroot] at hgain
  have haction : action trace = quittingCoalitionAction
      (quittingMaximumPositiveToggleNext reward (sourceCoalition trace).1)
      (mover trace) := by
    unfold action mover
    rw [(route trace).terminal_eq]
  rw [haction] at hgain
  let tail := (quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward
      (sourceProfile trace profile stage) (stage + 1))).1
  have hrootGain :=
    quittingRootSuccessorPayoff_maximumPositiveToggle_eq_toggleGain
      reward tail (sourceCoalition trace)
  have hrootGain' :
      quittingRootSuccessorPayoff reward tail
            (Function.update (quittingPureSetRoot (sourceCoalition trace).1)
              (mover trace)
              (PMF.pure (quittingCoalitionAction
                (quittingMaximumPositiveToggleNext reward
                  (sourceCoalition trace).1) (mover trace))))
            (mover trace) -
          quittingRootSuccessorPayoff reward tail
            (quittingPureSetRoot (sourceCoalition trace).1) (mover trace) =
        quittingPureToggleGain reward (sourceCoalition trace).1
          (mover trace) := by
    simpa only [mover] using hrootGain
  change _ = quittingLiveMass reward profile stage * _ at hgain
  rw [hrootGain'] at hgain
  rw [haction]
  exact hgain

theorem gain_floor
    (trace : Trace (reward := reward) (start := start))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (lambda : ℝ) (_hlambda : 0 < lambda)
    (hlive : lambda ≤ quittingLiveMass reward profile stage) :
    lambda * quittingTerminalSemanticDebtSum minimum / 4 ≤
      gain trace profile stage := by
  rw [gain_eq_liveMass_mul_toggleGain trace]
  have htoggle := minimumDebt_div_four_le_selectedToggleGain reward minimum
    hminimum hpositive (sourceCoalition trace)
  have hliveScaled := mul_le_mul hlive htoggle
    (div_nonneg hpositive.le (by norm_num))
    (quittingLiveMass_nonneg reward profile stage)
  simpa only [mover, div_eq_mul_inv, mul_assoc] using (show
    lambda * (quittingTerminalSemanticDebtSum minimum / 4) ≤
      quittingLiveMass reward profile stage *
        quittingPureToggleGain reward (sourceCoalition trace).1
          (quittingMaximumPositiveTogglePlayer reward
            (sourceCoalition trace).1) from hliveScaled)

/-- The singleton toggle lowers the mover's unrestricted whole-profile debt
by exactly its actual payoff gain. -/
theorem moverDebt_eq_sub_gain
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (targetProfile trace profile stage)) (mover trace) =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (sourceProfile trace profile stage)) (mover trace) -
        gain trace profile stage := by
  unfold gain
  rw [targetProfile_eq_literalOneDateProfile trace]
  exact quittingTerminalSemanticDebt_literalOneDateProfile_eq_sub_gain
    reward _ _ stage _

theorem targetStageMass_eq_liveMass
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingStageCoalitionMass reward (targetProfile trace profile stage) stage
        (route trace).terminal = quittingLiveMass reward profile stage := by
  unfold targetProfile
  rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
    quittingLiveMass_literalPureRootProfile_eq,
    quittingProfileLiveRoot_literalPureRootProfile_self,
    quittingRootCoalitionMass_pureCoalitionAction_eq_one, mul_one]

theorem targetProfile_postDateSpine_eq
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    quittingAllContinueProfileSpine reward (targetProfile trace profile stage)
        (stage + 1) =
      quittingAllContinueProfileSpine reward profile (stage + 1) := by
  apply quittingAllContinueProfileSpine_eq_of_eq_from
  intro who time history htime
  have hne : time ≠ stage := by omega
  exact congrFun
    (quittingLiteralOneDateOverride_of_ne (profile who) stage time _ hne)
    history

end FinFourMaximumToggleTerminalOrbit

/-! ## Generic Fin4 spectator recharge -/

/-- Literal finite sibling-cycle data sufficient for the spectator ledger.
The profiles are complete behavioral profiles; no chronological relation
between successive entries is assumed. -/
structure FinFourLiteralSiblingCycle
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) where
  period : ℕ
  period_pos : 0 < period
  profile : ℕ → (quittingGame reward).BehaviorProfile
  mover : Fin period → Fin 4
  closes : profile period = profile 0
  target_eq_update : ∀ offset : Fin period,
    profile (offset + 1) = Function.update (profile offset) (mover offset)
      (profile (offset + 1) (mover offset))

namespace FinFourLiteralSiblingCycle

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

def gain (cycle : FinFourLiteralSiblingCycle reward)
    (offset : Fin cycle.period) : ℝ :=
  quittingTerminalPayoff reward (cycle.profile (offset + 1))
      (cycle.mover offset) -
    quittingTerminalPayoff reward (cycle.profile offset) (cycle.mover offset)

def debtChange (cycle : FinFourLiteralSiblingCycle reward)
    (offset : Fin cycle.period) (who : Fin 4) : ℝ :=
  quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (cycle.profile (offset + 1))) who -
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward (cycle.profile offset)) who

theorem mover_debtChange_eq_neg_gain
    (cycle : FinFourLiteralSiblingCycle reward)
    (offset : Fin cycle.period) :
    cycle.debtChange offset (cycle.mover offset) = -cycle.gain offset := by
  unfold debtChange gain
  rw [cycle.target_eq_update offset]
  -- The general update identity is strategy-level and independent of how the
  -- target strategy was generated.  Use continuation-value invariance
  -- directly to avoid assigning a fictitious marked date to this ledger.
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  change
    (quittingContinuationBestResponseValue reward
          (Function.update (cycle.profile offset) (cycle.mover offset)
            (cycle.profile (offset + 1) (cycle.mover offset)))
          (cycle.mover offset) -
        quittingTerminalPayoff reward
          (Function.update (cycle.profile offset) (cycle.mover offset)
            (cycle.profile (offset + 1) (cycle.mover offset)))
          (cycle.mover offset)) -
      (quittingContinuationBestResponseValue reward (cycle.profile offset)
          (cycle.mover offset) -
        quittingTerminalPayoff reward (cycle.profile offset)
          (cycle.mover offset)) = _
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- One spectator-edge pair absorbs at least one third of the common mover
gain floor.  This is the exact Fin4 averaging constant. -/
theorem exists_spectator_debtRise
    (cycle : FinFourLiteralSiblingCycle reward)
    (gainFloor : ℝ) (hgain : ∀ offset, gainFloor ≤ cycle.gain offset) :
    ∃ offset : Fin cycle.period, ∃ observer : Fin 4,
      observer ≠ cycle.mover offset ∧
        gainFloor / 3 ≤ cycle.debtChange offset observer := by
  letI : Nonempty (Fin cycle.period) := ⟨⟨0, cycle.period_pos⟩⟩
  have htotal : ∑ offset : Fin cycle.period,
      ∑ observer ∈ Finset.univ.erase (cycle.mover offset),
        cycle.debtChange offset observer =
      ∑ offset : Fin cycle.period, cycle.gain offset := by
    have htelescopes : ∑ offset : Fin cycle.period,
        ∑ who : Fin 4, cycle.debtChange offset who = 0 := by
      unfold debtChange
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero
      intro who _
      let debtAt (time : ℕ) := quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (cycle.profile time)) who
      change (∑ offset : Fin cycle.period,
        (debtAt (offset + 1) - debtAt offset)) = 0
      rw [Fin.sum_univ_eq_sum_range
        (fun offset ↦ debtAt (offset + 1) - debtAt offset) cycle.period]
      rw [Finset.sum_range_sub]
      have hcloseDebt : debtAt cycle.period = debtAt 0 := by
        dsimp only [debtAt]
        rw [cycle.closes]
      rw [hcloseDebt]
      ring
    calc
      (∑ offset : Fin cycle.period,
          ∑ observer ∈ Finset.univ.erase (cycle.mover offset),
            cycle.debtChange offset observer) =
          ∑ offset : Fin cycle.period,
            ((∑ who : Fin 4, cycle.debtChange offset who) -
              cycle.debtChange offset (cycle.mover offset)) := by
        apply Finset.sum_congr rfl
        intro offset _
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (cycle.mover offset))]
        ring
      _ = ∑ offset : Fin cycle.period,
          ((∑ who : Fin 4, cycle.debtChange offset who) +
            cycle.gain offset) := by
        apply Finset.sum_congr rfl
        intro offset _
        rw [cycle.mover_debtChange_eq_neg_gain]
        ring
      _ = ∑ offset : Fin cycle.period, cycle.gain offset := by
        rw [Finset.sum_add_distrib, htelescopes, zero_add]
  have hlower : cycle.period * gainFloor ≤
      ∑ offset : Fin cycle.period, cycle.gain offset := by
    calc
      (cycle.period : ℝ) * gainFloor =
          ∑ _offset : Fin cycle.period, gainFloor := by simp
      _ ≤ ∑ offset : Fin cycle.period, cycle.gain offset :=
        Finset.sum_le_sum fun offset _ ↦ hgain offset
  by_contra hnone
  push Not at hnone
  have hstrict : ∑ offset : Fin cycle.period,
      ∑ observer ∈ Finset.univ.erase (cycle.mover offset),
        cycle.debtChange offset observer <
      cycle.period * gainFloor := by
    have hcard : ∀ offset : Fin cycle.period,
        (Finset.univ.erase (cycle.mover offset)).card = 3 := by
      intro offset
      simp
    have hinner : ∀ offset : Fin cycle.period,
        (∑ observer ∈ Finset.univ.erase (cycle.mover offset),
            cycle.debtChange offset observer) < 3 * (gainFloor / 3) := by
      intro offset
      have hnonempty : (Finset.univ.erase (cycle.mover offset)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        have hcardZero := congrArg Finset.card hempty
        rw [hcard offset] at hcardZero
        simp at hcardZero
      calc
        (∑ observer ∈ Finset.univ.erase (cycle.mover offset),
            cycle.debtChange offset observer) <
            ∑ _observer ∈ Finset.univ.erase (cycle.mover offset),
              gainFloor / 3 :=
          Finset.sum_lt_sum_of_nonempty hnonempty fun observer hobserver ↦
            hnone offset observer (Finset.mem_erase.1 hobserver).1
        _ = 3 * (gainFloor / 3) := by rw [Finset.sum_const, hcard offset]; norm_num
    calc
      (∑ offset : Fin cycle.period,
          ∑ observer ∈ Finset.univ.erase (cycle.mover offset),
            cycle.debtChange offset observer) <
          ∑ _offset : Fin cycle.period, 3 * (gainFloor / 3) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun offset _ ↦
          hinner offset
      _ = (cycle.period : ℝ) * (3 * (gainFloor / 3)) := by simp
      _ = cycle.period * gainFloor := by ring
  rw [htotal] at hstrict
  exact (not_lt_of_ge hlower) hstrict

end FinFourLiteralSiblingCycle

namespace FinFourMaximumToggleClosedSegment

variable
  {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {start : FinFourNonsingletonCoalition}

/-- Forget the table orbit to the exact complete-profile sibling ledger at
one supplied source row and date. -/
def toLiteralSiblingCycle
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ) :
    FinFourLiteralSiblingCycle reward where
  period := trace.segment.segment.period
  period_pos := trace.segment.segment.period_pos
  profile := profileAt trace profile stage
  mover := moverAt trace
  closes := profileAt_period_eq_zero trace profile stage
  target_eq_update := profileAt_succ_eq_update trace profile stage

@[simp] theorem toLiteralSiblingCycle_gain
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) :
    (toLiteralSiblingCycle trace profile stage).gain offset =
      gainAt trace profile stage offset := rfl

@[simp] theorem toLiteralSiblingCycle_debtChange
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) (who : Fin 4) :
    (toLiteralSiblingCycle trace profile stage).debtChange offset who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profileAt trace profile stage (offset + 1))) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profileAt trace profile stage offset)) who := rfl

/-- The fixed maximum-toggle cycle produces a positive spectator rise on
every supplied same-date realization. -/
theorem exists_spectatorDebtRise
    (trace : Trace (reward := reward) (start := start))
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (hlive : lambda ≤ quittingLiveMass reward profile stage) :
    ∃ offset : Fin trace.segment.segment.period, ∃ observer : Fin 4,
      observer ≠ moverAt trace offset ∧
        lambda * quittingTerminalSemanticDebtSum minimum / 12 ≤
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (profileAt trace profile stage (offset + 1))) observer -
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward
                (profileAt trace profile stage offset)) observer := by
  have hdispatch :=
    (toLiteralSiblingCycle trace profile stage).exists_spectator_debtRise
      (lambda * quittingTerminalSemanticDebtSum minimum / 4)
      (gainAt_floor trace minimum hminimum hpositive profile stage lambda
        hlambda hlive)
  obtain ⟨offset, observer, hobserver, hrise⟩ := hdispatch
  exact ⟨offset, observer, hobserver, by
    rw [toLiteralSiblingCycle_debtChange] at hrise
    nlinarith⟩

/-- The checked stopping-law atom alternative attached to one selected
spectator-rise edge. -/
theorem hasVanishingDebtAtomAlternative
    (trace : Trace (reward := reward) (start := start))
    (profile : (quittingGame reward).BehaviorProfile) (stage : ℕ)
    (offset : Fin trace.segment.segment.period) (observer : Fin 4)
    (charge error : ℝ) (hcharge : 0 < charge) (herror : 0 < error)
    (herrorLe : error ≤ charge / 8)
    (hrise : charge ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profileAt trace profile stage (offset + 1))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (profileAt trace profile stage offset)) observer) :
    HasQuittingStoppingLawVanishingDebtAtomAlternative reward
      (profileAt trace profile stage offset) (moverAt trace offset) observer
      ((profileAt trace profile stage (offset + 1)) (moverAt trace offset))
      (7 * charge / 8) error := by
  rw [profileAt_succ_eq_update trace profile stage offset] at hrise
  exact hasVanishingDebtAtomAlternative_of_endpointDebtRise reward
    (profileAt trace profile stage offset) (moverAt trace offset) observer
    ((profileAt trace profile stage (offset + 1)) (moverAt trace offset))
    charge error hcharge herror herrorLe hrise

end FinFourMaximumToggleClosedSegment

end GameTheory
