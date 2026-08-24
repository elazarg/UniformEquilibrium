/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteBinaryBlockEquilibrium
import UniformEquilibrium.Quitting.Stationary.TogglePotential

/-!
# Block-triangular influence certificates for quitting games

A polarity switch reverses the binary action of selected players.  If the
switched terminal-payoff game has increasing differences within each block
and later blocks do not affect earlier action gains, the finite block theorem
produces a pure action profile.  Undoing the switch gives a quitting sure-exit
set and hence a uniform-equilibrium payoff.

This file consumes a supplied block certificate.  In particular, it does not
yet derive that certificate from signed directed-cycle balance of the raw
coalition influences.
-/

noncomputable section

namespace GameTheory

open MathUE
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Reverse the Quit/Continue coordinates in `switched`. -/
def quittingPolaritySwitch (switched actionOne : Finset ι) : Finset ι :=
  (actionOne \ switched) ∪ (switched \ actionOne)

omit [Fintype ι] in
@[simp] theorem mem_quittingPolaritySwitch {switched actionOne : Finset ι}
    {who : ι} :
    who ∈ quittingPolaritySwitch switched actionOne ↔
      (who ∈ actionOne ∧ who ∉ switched) ∨
        (who ∈ switched ∧ who ∉ actionOne) := by
  simp [quittingPolaritySwitch]

omit [Fintype ι] in
theorem quittingPolaritySwitch_insert_of_notMem
    {switched actionOne : Finset ι} {who : ι} (hwho : who ∉ switched) :
    quittingPolaritySwitch switched (insert who actionOne) =
      insert who (quittingPolaritySwitch switched actionOne) := by
  ext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPolaritySwitch, hwho]
  · simp [quittingPolaritySwitch, hplayer]

omit [Fintype ι] in
theorem quittingPolaritySwitch_erase_of_notMem
    {switched actionOne : Finset ι} {who : ι} (hwho : who ∉ switched) :
    quittingPolaritySwitch switched (actionOne.erase who) =
      (quittingPolaritySwitch switched actionOne).erase who := by
  ext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPolaritySwitch, hwho]
  · simp [quittingPolaritySwitch, hplayer]

omit [Fintype ι] in
theorem quittingPolaritySwitch_insert_of_mem
    {switched actionOne : Finset ι} {who : ι} (hwho : who ∈ switched) :
    quittingPolaritySwitch switched (insert who actionOne) =
      (quittingPolaritySwitch switched actionOne).erase who := by
  ext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPolaritySwitch, hwho]
  · simp [quittingPolaritySwitch, hplayer]

omit [Fintype ι] in
theorem quittingPolaritySwitch_erase_of_mem
    {switched actionOne : Finset ι} {who : ι} (hwho : who ∈ switched) :
    quittingPolaritySwitch switched (actionOne.erase who) =
      insert who (quittingPolaritySwitch switched actionOne) := by
  ext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingPolaritySwitch, hwho]
  · simp [quittingPolaritySwitch, hplayer]

/-- Terminal payoff of the original coalition represented by the switched
binary action coordinates. -/
def quittingSwitchedSetPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (switched : Finset ι) (who : ι) (actionOne : Finset ι) : ℝ :=
  quittingSetReward reward (quittingPolaritySwitch switched actionOne) who

/-- Finite block data after one coordinatewise polarity switch.  This is the
exact downstream certificate expected from an SCC/condensation construction;
it does not package the desired sure-exit set. -/
structure QuittingInfluenceBlockCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  switched : Finset ι
  triangular : BinaryBlockTriangularCertificate
    (quittingSwitchedSetPayoff reward switched)

omit [Fintype ι] in
private theorem isQuittingSureExitSet_of_switched_stable
    {switched actionOne : Finset ι}
    (hstable : IsBinaryGainStable
      (quittingSwitchedSetPayoff reward switched) actionOne) :
    IsQuittingSureExitSet reward
      (quittingPolaritySwitch switched actionOne) := by
  let exit := quittingPolaritySwitch switched actionOne
  constructor
  · intro member hmember
    have hmembership :=
      (mem_quittingPolaritySwitch (switched := switched)
        (actionOne := actionOne)).mp hmember
    by_cases hswitch : member ∈ switched
    · have hnotAction : member ∉ actionOne := by
        rcases hmembership with hmembership | hmembership
        · exact (hmembership.2 hswitch).elim
        · exact hmembership.2
      have hg := hstable member
      rw [if_neg hnotAction] at hg
      unfold binaryJoinGain quittingSwitchedSetPayoff at hg
      rw [quittingPolaritySwitch_insert_of_mem hswitch,
        quittingPolaritySwitch_erase_of_mem hswitch] at hg
      simpa [exit, Finset.insert_eq_self.mpr hmember] using hg
    · have haction : member ∈ actionOne := by
        rcases hmembership with hmembership | hmembership
        · exact hmembership.1
        · exact (hswitch hmembership.1).elim
      have hg := hstable member
      rw [if_pos haction] at hg
      unfold binaryJoinGain quittingSwitchedSetPayoff at hg
      rw [quittingPolaritySwitch_insert_of_notMem hswitch,
        quittingPolaritySwitch_erase_of_notMem hswitch] at hg
      simpa [exit, Finset.insert_eq_self.mpr hmember] using hg
  · intro outsider houtside
    have hnotMembership :
        outsider ∉ quittingPolaritySwitch switched actionOne := houtside
    by_cases hswitch : outsider ∈ switched
    · have haction : outsider ∈ actionOne := by
        by_contra hnotAction
        exact hnotMembership
          ((mem_quittingPolaritySwitch (switched := switched)
            (actionOne := actionOne)).mpr (Or.inr ⟨hswitch, hnotAction⟩))
      have hg := hstable outsider
      rw [if_pos haction] at hg
      unfold binaryJoinGain quittingSwitchedSetPayoff at hg
      rw [quittingPolaritySwitch_insert_of_mem hswitch,
        quittingPolaritySwitch_erase_of_mem hswitch] at hg
      simpa [exit, Finset.erase_eq_of_notMem houtside] using hg
    · have hnotAction : outsider ∉ actionOne := by
        intro haction
        exact hnotMembership
          ((mem_quittingPolaritySwitch (switched := switched)
            (actionOne := actionOne)).mpr (Or.inl ⟨haction, hswitch⟩))
      have hg := hstable outsider
      rw [if_neg hnotAction] at hg
      unfold binaryJoinGain quittingSwitchedSetPayoff at hg
      rw [quittingPolaritySwitch_insert_of_notMem hswitch,
        quittingPolaritySwitch_erase_of_notMem hswitch] at hg
      simpa [exit, Finset.erase_eq_of_notMem houtside] using hg

/-- A supplied block-triangular signed-influence certificate produces a
literal quitting sure-exit coalition. -/
theorem exists_isQuittingSureExitSet_of_influenceBlockCertificate
    (certificate : QuittingInfluenceBlockCertificate reward) :
    ∃ S, IsQuittingSureExitSet reward S := by
  obtain ⟨actionOne, hstable⟩ := certificate.triangular.exists_isBinaryGainStable
  exact ⟨quittingPolaritySwitch certificate.switched actionOne,
    isQuittingSureExitSet_of_switched_stable hstable⟩

/-- The same certificate feeds the existing unrestricted-behavior semantic
consumer. -/
theorem quittingGame_exists_uniformPayoff_of_influenceBlockCertificate
    (certificate : QuittingInfluenceBlockCertificate reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨S, hS⟩ :=
    exists_isQuittingSureExitSet_of_influenceBlockCertificate certificate
  exact ⟨quittingSetReward reward S,
    isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hS⟩

end GameTheory
