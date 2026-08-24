/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.SignedInfluenceCycleBalance

/-!
# Sharp regressions for cycle-balanced signed quitting influences

Two exact three-player tables test the boundary of the SCC theorem.  The first
has an acyclic signed influence graph, admits the sure-exit coalition `{0, 2}`,
and admits no single global polarity switch.  The second is the directed odd
negative cycle and has no sure-exit coalition.
-/

noncomputable section

namespace GameTheory
namespace SignedInfluenceCycleBalanceRegression

open Math
open Math.DirectedTransport
open MathUE
open QuittingSureSetOwnerRepair

/-! ## An acyclic table outside the global-polarity class -/

namespace Acyclic

abbrev Player := Fin 3

def setPayoff (S : Finset Player) (who : Player) : ℝ :=
  if who ∈ S then
    if who = 0 then 1
    else if who = 1 then 1 - 2 * if (0 : Player) ∈ S then 1 else 0
    else 1 + (if (0 : Player) ∈ S then 1 else 0) +
      if (1 : Player) ∈ S then 1 else 0
  else 0

def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who => setPayoff S.1 who

@[simp] theorem quittingSetReward_eq (S : Finset Player) (who : Player) :
    quittingSetReward reward S who = setPayoff S who := by
  by_cases hS : S.Nonempty
  · simp [quittingSetReward, reward, hS]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [quittingSetReward, setPayoff]

theorem pairInfluence_zero_one (S : Finset Player)
    (hzero : (0 : Player) ∉ S) (hone : (1 : Player) ∉ S) :
    quittingPairInfluence reward 0 1 S = -2 := by
  simp [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
    reward, setPayoff, hzero, hone]

theorem pairInfluence_zero_two (S : Finset Player)
    (hzero : (0 : Player) ∉ S) (htwo : (2 : Player) ∉ S) :
    quittingPairInfluence reward 0 2 S = 1 := by
  simp [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
    reward, setPayoff, hzero, htwo]

theorem pairInfluence_one_two (S : Finset Player)
    (hone : (1 : Player) ∉ S) (htwo : (2 : Player) ∉ S) :
    quittingPairInfluence reward 1 2 S = 1 := by
  simp [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
    reward, setPayoff, hone, htwo]

theorem pairInfluence_absent
    {other who : Player} (hne : other ≠ who)
    (hnotZeroOne : ¬(other = 0 ∧ who = 1))
    (hnotZeroTwo : ¬(other = 0 ∧ who = 2))
    (hnotOneTwo : ¬(other = 1 ∧ who = 2))
    (S : Finset Player) (hother : other ∉ S) (hwho : who ∉ S) :
    quittingPairInfluence reward other who S = 0 := by
  fin_cases other <;> fin_cases who <;>
    simp_all [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
      reward, setPayoff]

theorem positive_zero_two : IsPositiveQuittingInfluence reward 0 2 := by
  refine ⟨fun S hzero htwo => by
    rw [pairInfluence_zero_two S hzero htwo]
    norm_num, ?_⟩
  exact ⟨∅, by simp, by simp, by rw [pairInfluence_zero_two] <;> norm_num⟩

theorem positive_one_two : IsPositiveQuittingInfluence reward 1 2 := by
  refine ⟨fun S hone htwo => by
    rw [pairInfluence_one_two S hone htwo]
    norm_num, ?_⟩
  exact ⟨∅, by simp, by simp, by rw [pairInfluence_one_two] <;> norm_num⟩

theorem negative_zero_one : IsNegativeQuittingInfluence reward 0 1 := by
  refine ⟨fun S hzero hone => by
    rw [pairInfluence_zero_one S hzero hone]
    norm_num, ?_⟩
  exact ⟨∅, by simp, by simp, by rw [pairInfluence_zero_one] <;> norm_num⟩

theorem signConsistent : SignConsistentQuittingInfluence reward := by
  intro other who hne
  fin_cases other <;> fin_cases who
  all_goals try { exact (hne rfl).elim }
  · exact Or.inr (Or.inl negative_zero_one)
  · exact Or.inl positive_zero_two
  · exact Or.inr (Or.inr fun S hother hwho =>
      pairInfluence_absent (by decide) (by decide) (by decide) (by decide)
        S hother hwho)
  · exact Or.inl positive_one_two
  · exact Or.inr (Or.inr fun S hother hwho =>
      pairInfluence_absent (by decide) (by decide) (by decide) (by decide)
        S hother hwho)
  · exact Or.inr (Or.inr fun S hother hwho =>
      pairInfluence_absent (by decide) (by decide) (by decide) (by decide)
        S hother hwho)

private theorem nonabsent_classification
    {other who : Player} (hne : other ≠ who)
    (hedge : IsPositiveQuittingInfluence reward other who ∨
      IsNegativeQuittingInfluence reward other who) :
    (other = 0 ∧ who = 1) ∨ (other = 0 ∧ who = 2) ∨
      (other = 1 ∧ who = 2) := by
  by_contra hnot
  have hnotZeroOne : ¬(other = 0 ∧ who = 1) :=
    fun h => hnot (Or.inl h)
  have hnotZeroTwo : ¬(other = 0 ∧ who = 2) :=
    fun h => hnot (Or.inr (Or.inl h))
  have hnotOneTwo : ¬(other = 1 ∧ who = 2) :=
    fun h => hnot (Or.inr (Or.inr h))
  have habsent := pairInfluence_absent hne hnotZeroOne hnotZeroTwo hnotOneTwo
  rcases hedge with hpositive | hnegative
  · obtain ⟨S, hother, hwho, hstrict⟩ := hpositive.2
    rw [habsent S hother hwho] at hstrict
    norm_num at hstrict
  · obtain ⟨S, hother, hwho, hstrict⟩ := hnegative.2
    rw [habsent S hother hwho] at hstrict
    norm_num at hstrict

theorem influenceEdge_source_lt_target
    (edge : QuittingInfluenceEdge reward) :
    edge.1.1.val < edge.1.2.val := by
  rcases nonabsent_classification edge.2.1 edge.2.2 with
      ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩
  · rw [hsource, htarget]
    norm_num
  · rw [hsource, htarget]
    norm_num
  · rw [hsource, htarget]
    norm_num

theorem influenceWalk_source_le_target {start finish : Player}
    (walk : (quittingInfluenceGraph reward).Walk start finish) :
    start.val ≤ finish.val := by
  induction walk with
  | nil => exact le_rfl
  | concat walk edge legal ih =>
      calc
        start.val ≤ _ := ih
        _ = edge.1.1.val := congrArg Fin.val legal.symm
        _ ≤ edge.1.2.val := (influenceEdge_source_lt_target edge).le

theorem influenceWalk_source_lt_target_of_pos {start finish : Player}
    (walk : (quittingInfluenceGraph reward).Walk start finish)
    (hpositive : 0 < walk.length) :
    start.val < finish.val := by
  cases walk with
  | nil => simp at hpositive
  | concat walk edge legal =>
      calc
        start.val ≤ _ := influenceWalk_source_le_target walk
        _ = edge.1.1.val := congrArg Fin.val legal.symm
        _ < edge.1.2.val := influenceEdge_source_lt_target edge

theorem everyDirectedInfluenceCyclePositive :
    EveryDirectedInfluenceCyclePositive reward := by
  intro base cycle hsimple
  exact (lt_irrefl base.val
    (influenceWalk_source_lt_target_of_pos cycle hsimple.1)).elim

/-- A single switch set whose endpoints agree on positive edges and disagree
on negative edges. -/
def HasGlobalPolarity : Prop :=
  ∃ switched : Finset Player,
    (0 ∈ switched ↔ 1 ∉ switched) ∧
      (0 ∈ switched ↔ 2 ∈ switched) ∧
        (1 ∈ switched ↔ 2 ∈ switched)

theorem not_hasGlobalPolarity : ¬HasGlobalPolarity := by
  rintro ⟨switched, hzeroOne, hzeroTwo, honeTwo⟩
  by_cases hzero : (0 : Player) ∈ switched
  · have hnotOne : (1 : Player) ∉ switched := hzeroOne.mp hzero
    have htwo : (2 : Player) ∈ switched := hzeroTwo.mp hzero
    exact hnotOne (honeTwo.mpr htwo)
  · have hone : (1 : Player) ∈ switched := by
      by_contra hnotOne
      exact hzero (hzeroOne.mpr hnotOne)
    have htwo : (2 : Player) ∈ switched := honeTwo.mp hone
    exact hzero (hzeroTwo.mpr htwo)

theorem sureExit_zero_two :
    IsQuittingSureExitSet reward ({0, 2} : Finset Player) := by
  constructor
  · intro member hmember
    fin_cases member <;>
      simp_all [reward, setPayoff]
  · intro outsider houtside
    fin_cases outsider <;>
      simp_all [reward, setPayoff]

end Acyclic

/-! ## The odd directed negative cycle -/

namespace OddNegativeCycle

abbrev Player := Fin 3

def succ (who : Player) : Player :=
  if who = 0 then 1 else if who = 1 then 2 else 0

def setPayoff (S : Finset Player) (who : Player) : ℝ :=
  if who ∈ S then if succ who ∈ S then -1 else 1 else 0

def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun S who => setPayoff S.1 who

@[simp] theorem quittingSetReward_eq (S : Finset Player) (who : Player) :
    quittingSetReward reward S who = setPayoff S who := by
  by_cases hS : S.Nonempty
  · simp [quittingSetReward, reward, hS]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [quittingSetReward, setPayoff]

@[simp] theorem succ_zero : succ 0 = 1 := by simp [succ]

@[simp] theorem succ_one : succ 1 = 2 := by simp [succ]

@[simp] theorem succ_two : succ 2 = 0 := by simp [succ]

theorem pairInfluence_successor (who : Player) (S : Finset Player)
    (hsucc : succ who ∉ S) (hwho : who ∉ S) :
    quittingPairInfluence reward (succ who) who S = -2 := by
  fin_cases who <;>
    simp_all [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
      reward, setPayoff] <;> norm_num

theorem pairInfluence_absent
    {other who : Player} (hne : other ≠ who) (hnotSucc : other ≠ succ who)
    (S : Finset Player) (hother : other ∉ S) (hwho : who ∉ S) :
    quittingPairInfluence reward other who S = 0 := by
  fin_cases other <;> fin_cases who <;>
    simp_all [quittingPairInfluence, quittingMembershipGain, binaryJoinGain,
      reward, setPayoff]

theorem negative_successor (who : Player) :
    IsNegativeQuittingInfluence reward (succ who) who := by
  refine ⟨fun S hsucc hwho => by
    rw [pairInfluence_successor who S hsucc hwho]
    norm_num, ?_⟩
  exact ⟨∅, by simp, by simp, by rw [pairInfluence_successor] <;> norm_num⟩

theorem signConsistent : SignConsistentQuittingInfluence reward := by
  intro other who hne
  by_cases hsucc : other = succ who
  · subst other
    exact Or.inr (Or.inl (negative_successor who))
  · exact Or.inr (Or.inr fun S hother hwho =>
      pairInfluence_absent hne hsucc S hother hwho)

theorem membership_iff_successor_notMem
    {S : Finset Player} (hS : IsQuittingSureExitSet reward S)
    (who : Player) :
    who ∈ S ↔ succ who ∉ S := by
  constructor
  · intro hwho hsucc
    have hmember := hS.1 who hwho
    have hne : succ who ≠ who := by
      fin_cases who <;> decide
    rw [quittingSetReward_eq, quittingSetReward_eq] at hmember
    simp [setPayoff, hwho, hsucc] at hmember
    norm_num at hmember
  · intro hsucc
    by_contra hwho
    have houtsider := hS.2 who hwho
    have hne : succ who ≠ who := by
      fin_cases who <;> decide
    rw [quittingSetReward_eq, quittingSetReward_eq] at houtsider
    simp [setPayoff, hwho, hsucc, hne] at houtsider
    norm_num at houtsider

theorem no_sureExitSet : ¬∃ S, IsQuittingSureExitSet reward S := by
  rintro ⟨S, hS⟩
  have hzero := membership_iff_successor_notMem hS (0 : Player)
  have hone := membership_iff_successor_notMem hS (1 : Player)
  have htwo := membership_iff_successor_notMem hS (2 : Player)
  simp only [succ_zero, succ_one, succ_two] at hzero hone htwo
  by_cases hz : (0 : Player) ∈ S
  · have hnOne : (1 : Player) ∉ S := hzero.mp hz
    have ht : (2 : Player) ∈ S := by
      by_contra hnTwo
      exact hnOne (hone.mpr hnTwo)
    exact (htwo.mp ht) hz
  · have hOne : (1 : Player) ∈ S := by
      by_contra hnOne
      exact hz (hzero.mpr hnOne)
    have hnTwo : (2 : Player) ∉ S := hone.mp hOne
    exact hnTwo (htwo.mpr hz)

theorem exists_negativeSimpleInfluenceCycle :
    ∃ (base : Player)
      (cycle : (quittingInfluenceGraph reward).Walk base base),
      Math.AdditiveTransport.IsSimpleCycle cycle ∧
        walkLabel quittingInfluenceLabel cycle = -1 :=
  exists_negativeSimpleInfluenceCycle_of_no_sureExitSet
    signConsistent no_sureExitSet

end OddNegativeCycle

end SignedInfluenceCycleBalanceRegression
end GameTheory

end
