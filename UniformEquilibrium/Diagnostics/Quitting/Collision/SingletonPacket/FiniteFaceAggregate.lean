/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.FiniteDispatch
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.ReachableSimpleCycle

/-!
# Finite sign-face aggregate for a crossed four-player packet

This module packages the rate-free collision residual for an arbitrarily
labelled ordered support pair.  One orientation is feasible exactly when its
owner defect lies on one of three finite faces: a negative defect with all
rate-zero rows nonpositive, a positive defect with all rate-one rows
nonpositive, or a zero defect satisfying the finite sign/cross-product
criterion.

For a `Fin 4` counterexample packet, both orientations fail.  Negative faces
therefore expose packet-certified rate-zero outsider joins, positive faces
whose opposite owner defect is nonnegative expose rate-one outsider joins,
and zero faces expose literal failures of the finite affine criterion.  The
same aggregate retains the crossed singleton labels and their independent
owner/preemption screen.

Positive join defects anchor the already checked reachable simple strict
toggle cycle.  The cycle remains a static reward-table object; no behavioral
or chronological compiler is claimed here.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}

/-- Pair-minus-blocker-singleton payoff defect of the collision owner. -/
def quittingSupportPairOwnerDefect
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner blocker : iota) : Real :=
  quittingSetReward reward ({owner, blocker} : Finset iota) owner -
    quittingSetReward reward ({blocker} : Finset iota) owner

/-- A positive rate-zero outsider join defect. -/
def HasPositiveCollisionLowerSpectatorDefect
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner blocker : iota) : Prop :=
  ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
    quittingSetReward reward ({blocker} : Finset iota) spectator <
      quittingSetReward reward ({spectator, blocker} : Finset iota) spectator

/-- A positive rate-one outsider join defect. -/
def HasPositiveCollisionUpperSpectatorDefect
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner blocker : iota) : Prop :=
  ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
    quittingSetReward reward ({owner, blocker} : Finset iota) spectator <
      quittingSetReward reward
        ({owner, spectator, blocker} : Finset iota) spectator

/-- The completely finite condition for one ordered collision orientation. -/
def QuittingCollisionFiniteOrientationCriterion
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (owner blocker : iota) : Prop :=
  (quittingSupportPairOwnerDefect reward owner blocker < 0 ∧
      ∀ index : QuittingCollisionConstraintPlayer owner,
        quittingCollisionConstraintLower reward owner blocker index <= 0) ∨
    (0 < quittingSupportPairOwnerDefect reward owner blocker ∧
      ∀ index : QuittingCollisionConstraintPlayer owner,
        quittingCollisionConstraintUpper reward owner blocker index <= 0) ∨
    (quittingSupportPairOwnerDefect reward owner blocker = 0 ∧
      Math.FiniteAffineIntervalCriterion
        (quittingCollisionConstraintLower reward owner blocker)
        (quittingCollisionConstraintUpper reward owner blocker))

/-- One ordered collision orientation works exactly when its finite sign-face
criterion holds.  No real rate remains in the right-hand side. -/
theorem exists_quittingCollisionRepairWorks_iff_finiteOrientationCriterion
    (reward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    {owner blocker : iota} (hne : owner ≠ blocker) :
    (∃ (rate : Real) (hrate0 : 0 <= rate) (hrate1 : rate <= 1),
      QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1) ↔
      QuittingCollisionFiniteOrientationCriterion reward owner blocker := by
  let pairValue :=
    quittingSetReward reward ({owner, blocker} : Finset iota) owner
  let singletonValue :=
    quittingSetReward reward ({blocker} : Finset iota) owner
  rcases lt_trichotomy pairValue singletonValue with hlt | heq | hgt
  · rw [exists_quittingCollisionRepairWorks_iff_lower_of_owner_lt
      reward hne hlt]
    have hdefect : pairValue - singletonValue < 0 := by linarith
    constructor
    · intro hlower
      exact Or.inl ⟨by simpa [quittingSupportPairOwnerDefect,
        pairValue, singletonValue] using hdefect, hlower⟩
    · intro hcriterion
      rcases hcriterion with hnegative | hpositive | hzero
      · exact hnegative.2
      · exfalso
        have := hpositive.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith
      · exfalso
        have := hzero.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith
  · have heq' : singletonValue = pairValue := heq.symm
    rw [exists_quittingCollisionRepairWorks_iff_finiteCriterion_of_owner_eq
      reward hne heq']
    have hdefect : pairValue - singletonValue = 0 := by linarith
    constructor
    · intro hcriterion
      exact Or.inr (Or.inr ⟨by simpa [quittingSupportPairOwnerDefect,
        pairValue, singletonValue] using hdefect, hcriterion⟩)
    · intro hcriterion
      rcases hcriterion with hnegative | hpositive | hzero
      · exfalso
        have := hnegative.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith
      · exfalso
        have := hpositive.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith
      · exact hzero.2
  · rw [exists_quittingCollisionRepairWorks_iff_upper_of_owner_lt
      reward hne hgt]
    have hdefect : 0 < pairValue - singletonValue := by linarith
    constructor
    · intro hupper
      exact Or.inr (Or.inl ⟨by simpa [quittingSupportPairOwnerDefect,
        pairValue, singletonValue] using hdefect, hupper⟩)
    · intro hcriterion
      rcases hcriterion with hnegative | hpositive | hzero
      · exfalso
        have := hnegative.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith
      · exact hpositive.2
      · exfalso
        have := hzero.1
        unfold quittingSupportPairOwnerDefect at this
        dsimp only [pairValue, singletonValue] at hdefect
        linarith

namespace QuittingTerminalExploitabilityWitness

/-- An owner-indifference face fails the finite affine criterion in a terminal
counterexample. -/
theorem not_finiteCollisionCriterion_of_ownerDefect_eq_zero
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner blocker : iota} (hne : owner ≠ blocker)
    (heq : quittingSupportPairOwnerDefect reward owner blocker = 0) :
    ¬Math.FiniteAffineIntervalCriterion
      (quittingCollisionConstraintLower reward owner blocker)
      (quittingCollisionConstraintUpper reward owner blocker) := by
  intro hcriterion
  have horientation :
      QuittingCollisionFiniteOrientationCriterion reward owner blocker :=
    Or.inr (Or.inr ⟨heq, hcriterion⟩)
  obtain ⟨rate, hrate0, hrate1, hworks⟩ :=
    (exists_quittingCollisionRepairWorks_iff_finiteOrientationCriterion
      reward hne).2 horientation
  exact witness.not_quittingCollisionRepairWorks
    owner blocker rate hrate0 hrate1 hworks

/-- Reusable rate-free residual for an arbitrarily labelled ordered support
pair in a four-player counterexample packet.  The record itself is generic;
the cardinality-four assumption enters in its producer below. -/
structure CrossedSupportTwoFiniteResidual
    (gameReward : {S : Finset iota // S.Nonempty} -> Payoff iota)
    (witness : QuittingTerminalExploitabilityWitness gameReward)
    (packet : QuittingNormalizedSingletonSourcePacket gameReward)
    (first second : iota) where
  support_eq : packet.support = {first, second}
  labels_ne : first ≠ second
  left : iota
  right : iota
  outside_eq : packet.supportᶜ = {left, right}
  outsiders_ne : left ≠ right
  left_crossed :
    gameReward (quittingSingletonTerminal first) left <
        gameReward (quittingSingletonTerminal left) left ∧
      gameReward (quittingSingletonTerminal left) left <
        gameReward (quittingSingletonTerminal second) left
  right_crossed :
    gameReward (quittingSingletonTerminal second) right <
        gameReward (quittingSingletonTerminal right) right ∧
      gameReward (quittingSingletonTerminal right) right <
        gameReward (quittingSingletonTerminal first) right
  owner_preemption_screen :
    (witness.terminalGap <= -quittingSoloReward gameReward first first ∨
        QuittingSoloPreempts gameReward witness.terminalGap first left) ∧
      (witness.terminalGap <= -quittingSoloReward gameReward second second ∨
        QuittingSoloPreempts gameReward witness.terminalGap second right)
  first_negative :
    quittingSupportPairOwnerDefect gameReward first second < 0 ->
      HasPositiveCollisionLowerSpectatorDefect gameReward first second
  second_negative :
    quittingSupportPairOwnerDefect gameReward second first < 0 ->
      HasPositiveCollisionLowerSpectatorDefect gameReward second first
  first_positive :
    0 < quittingSupportPairOwnerDefect gameReward first second ->
      0 <= quittingSupportPairOwnerDefect gameReward second first ->
      HasPositiveCollisionUpperSpectatorDefect gameReward first second
  second_positive :
    0 < quittingSupportPairOwnerDefect gameReward second first ->
      0 <= quittingSupportPairOwnerDefect gameReward first second ->
      HasPositiveCollisionUpperSpectatorDefect gameReward second first
  first_zero :
    quittingSupportPairOwnerDefect gameReward first second = 0 ->
      ¬Math.FiniteAffineIntervalCriterion
        (quittingCollisionConstraintLower gameReward first second)
        (quittingCollisionConstraintUpper gameReward first second)
  second_zero :
    quittingSupportPairOwnerDefect gameReward second first = 0 ->
      ¬Math.FiniteAffineIntervalCriterion
        (quittingCollisionConstraintLower gameReward second first)
        (quittingCollisionConstraintUpper gameReward second first)

namespace CrossedSupportTwoFiniteResidual

/-- Swapping the two support labels swaps the two crossed outsiders and all
finite sign-face fields. -/
def swap
    {gameReward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {witness : QuittingTerminalExploitabilityWitness gameReward}
    {packet : QuittingNormalizedSingletonSourcePacket gameReward}
    {first second : iota}
    (residual : CrossedSupportTwoFiniteResidual
      gameReward witness packet first second) :
    CrossedSupportTwoFiniteResidual
      gameReward witness packet second first where
  support_eq := by simpa only [Finset.pair_comm] using residual.support_eq
  labels_ne := residual.labels_ne.symm
  left := residual.right
  right := residual.left
  outside_eq := by simpa only [Finset.pair_comm] using residual.outside_eq
  outsiders_ne := residual.outsiders_ne.symm
  left_crossed := residual.right_crossed
  right_crossed := residual.left_crossed
  owner_preemption_screen := residual.owner_preemption_screen.symm
  first_negative := residual.second_negative
  second_negative := residual.first_negative
  first_positive := residual.second_positive
  second_positive := residual.first_positive
  first_zero := residual.second_zero
  second_zero := residual.first_zero

@[simp] theorem swap_swap
    {gameReward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    {witness : QuittingTerminalExploitabilityWitness gameReward}
    {packet : QuittingNormalizedSingletonSourcePacket gameReward}
    {first second : iota}
    (residual : CrossedSupportTwoFiniteResidual
      gameReward witness packet first second) :
    residual.swap.swap = residual := by
  cases residual
  rfl

end CrossedSupportTwoFiniteResidual

/-- Backward-compatible name for the canonical four-player specialization. -/
abbrev FinFourCrossedSupportTwoFiniteResidual
    (gameReward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness gameReward)
    (packet : QuittingNormalizedSingletonSourcePacket gameReward)
    (first second : Fin 4) :=
  CrossedSupportTwoFiniteResidual gameReward witness packet first second

/-- **Crossed support-two finite aggregate on an arbitrary four-element player
type.**  The result is symmetric in the ordered support labels and covers
every strict and equality face without a remaining real-rate quantifier. -/
theorem nonempty_crossedSupportTwoFiniteResidual_of_card_eq_four
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hcard : Fintype.card iota = 4)
    {first second : iota} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    Nonempty (CrossedSupportTwoFiniteResidual
      reward witness packet first second) := by
  obtain ⟨left, right, hleftOutside, hrightOutside, hlr, hleftBad, hleftHelped,
      hrightBad, hrightHelped⟩ :=
    witness.exists_crossedSpectators_of_support_eq_pair
      packet hne hsupport
  have hpairSubset : ({left, right} : Finset iota) ⊆ packet.supportᶜ := by
    intro who hwho
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl
    · simpa only [Finset.mem_compl] using hleftOutside
    · simpa only [Finset.mem_compl] using hrightOutside
  have hcomplCard : packet.supportᶜ.card = 2 := by
    rw [Finset.card_compl, hsupport, Finset.card_pair hne, hcard]
  have hpairCard : ({left, right} : Finset iota).card = 2 :=
    Finset.card_pair hlr
  have houtside : packet.supportᶜ = ({left, right} : Finset iota) := by
    symm
    apply Finset.eq_of_subset_of_card_le hpairSubset
    rw [hpairCard, hcomplCard]
  obtain ⟨hfirstMass, hsecondMass⟩ :=
    packet.mass_pos_of_support_eq_pair hsupport
  have hsupportSwap : packet.support = {second, first} := by
    simpa only [Finset.pair_comm] using hsupport
  have houtsideSwap : packet.supportᶜ = {right, left} := by
    simpa only [Finset.pair_comm] using houtside
  have hscreen :
      (witness.terminalGap ≤ -quittingSoloReward reward first first ∨
          QuittingSoloPreempts reward witness.terminalGap first left) ∧
        (witness.terminalGap ≤ -quittingSoloReward reward second second ∨
          QuittingSoloPreempts reward witness.terminalGap second right) := ⟨
    witness.terminalGap_le_negSolo_or_remaining_preempts_of_support_eq_pair
      packet hne hsupport houtside hrightHelped,
    witness.terminalGap_le_negSolo_or_remaining_preempts_of_support_eq_pair
      packet hne.symm hsupportSwap houtsideSwap hleftHelped⟩
  refine ⟨{
    support_eq := hsupport
    labels_ne := hne
    left := left
    right := right
    outside_eq := houtside
    outsiders_ne := hlr
    left_crossed := ⟨hleftBad, hleftHelped⟩
    right_crossed := ⟨hrightBad, hrightHelped⟩
    owner_preemption_screen := hscreen
    first_negative := ?_
    second_negative := ?_
    first_positive := ?_
    second_positive := ?_
    first_zero := ?_
    second_zero := ?_ }⟩
  · intro hdefect
    have hlt : quittingSetReward reward ({first, second} : Finset iota) first <
        quittingSetReward reward ({second} : Finset iota) first := by
      unfold quittingSupportPairOwnerDefect at hdefect
      linarith
    simpa only [HasPositiveCollisionLowerSpectatorDefect] using
      (witness.exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
        packet hne hsecondMass hlt)
  · intro hdefect
    have hlt : quittingSetReward reward ({second, first} : Finset iota) second <
        quittingSetReward reward ({first} : Finset iota) second := by
      unfold quittingSupportPairOwnerDefect at hdefect
      linarith
    simpa only [HasPositiveCollisionLowerSpectatorDefect] using
      (witness.exists_spectator_lowerCollisionDefect_pos_of_ownerPair_lt
        packet hne.symm hfirstMass hlt)
  · intro hfirst hsecond
    have hlt : quittingSetReward reward ({second} : Finset iota) first <
        quittingSetReward reward ({first, second} : Finset iota) first := by
      unfold quittingSupportPairOwnerDefect at hfirst
      linarith
    have hblocker : quittingSetReward reward ({first} : Finset iota) second <=
        quittingSetReward reward ({first, second} : Finset iota) second := by
      unfold quittingSupportPairOwnerDefect at hsecond
      have hsecond' : 0 <=
          quittingSetReward reward ({first, second} : Finset iota) second -
            quittingSetReward reward ({first} : Finset iota) second := by
        simpa only [Finset.pair_comm] using hsecond
      linarith
    simpa only [HasPositiveCollisionUpperSpectatorDefect] using
      (witness.exists_spectator_upperCollisionDefect_pos_of_owner_lt
        hne hlt hblocker)
  · intro hsecond hfirst
    have hlt : quittingSetReward reward ({first} : Finset iota) second <
        quittingSetReward reward ({second, first} : Finset iota) second := by
      unfold quittingSupportPairOwnerDefect at hsecond
      linarith
    have hblocker : quittingSetReward reward ({second} : Finset iota) first <=
        quittingSetReward reward ({second, first} : Finset iota) first := by
      unfold quittingSupportPairOwnerDefect at hfirst
      have hfirst' : 0 <=
          quittingSetReward reward ({second, first} : Finset iota) first -
            quittingSetReward reward ({second} : Finset iota) first := by
        simpa only [Finset.pair_comm] using hfirst
      linarith
    simpa only [HasPositiveCollisionUpperSpectatorDefect] using
      (witness.exists_spectator_upperCollisionDefect_pos_of_owner_lt
        hne.symm hlt hblocker)
  · exact witness.not_finiteCollisionCriterion_of_ownerDefect_eq_zero hne
  · exact witness.not_finiteCollisionCriterion_of_ownerDefect_eq_zero hne.symm

/-- Canonical `Fin 4` specialization of the relabeling-invariant aggregate. -/
theorem nonempty_finFourCrossedSupportTwoFiniteResidual
    {reward : {S : Finset (Fin 4) // S.Nonempty} -> Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second : Fin 4} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    Nonempty (FinFourCrossedSupportTwoFiniteResidual
      reward witness packet first second) :=
  nonempty_crossedSupportTwoFiniteResidual_of_card_eq_four
    witness packet (by simp) hne hsupport

/-- A rate-zero join defect anchors a reachable simple strict-toggle cycle at
the joined blocker--spectator coalition. -/
theorem exists_reachableStrictToggleSimpleCycle_of_lowerSpectatorDefect
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card iota = 4)
    {owner blocker : iota}
    (hdefect : HasPositiveCollisionLowerSpectatorDefect
      reward owner blocker) :
    ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
      quittingSetReward reward ({blocker} : Finset iota) spectator <
        quittingSetReward reward ({spectator, blocker} : Finset iota) spectator ∧
      Nonempty (witness.ReachableStrictToggleSimpleCycle
        ({spectator, blocker} : Finset iota)) := by
  obtain ⟨spectator, hso, hsb, hjoin⟩ := hdefect
  exact ⟨spectator, hso, hsb, hjoin,
    witness.exists_reachableStrictToggleSimpleCycle hcard {spectator, blocker}⟩

/-- A rate-one join defect anchors a reachable simple strict-toggle cycle at
the joined owner--blocker--spectator coalition. -/
theorem exists_reachableStrictToggleSimpleCycle_of_upperSpectatorDefect
    {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hcard : Fintype.card iota = 4)
    {owner blocker : iota}
    (hdefect : HasPositiveCollisionUpperSpectatorDefect
      reward owner blocker) :
    ∃ spectator, spectator ≠ owner ∧ spectator ≠ blocker ∧
      quittingSetReward reward ({owner, blocker} : Finset iota) spectator <
        quittingSetReward reward
          ({owner, spectator, blocker} : Finset iota) spectator ∧
      Nonempty (witness.ReachableStrictToggleSimpleCycle
        ({owner, spectator, blocker} : Finset iota)) := by
  obtain ⟨spectator, hso, hsb, hjoin⟩ := hdefect
  exact ⟨spectator, hso, hsb, hjoin,
    witness.exists_reachableStrictToggleSimpleCycle
      hcard {owner, spectator, blocker}⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
