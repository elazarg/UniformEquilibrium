/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ForwardExactCapTailFlow
import UniformEquilibrium.Quitting.Punishment.SingletonCapBindingCollision

/-!
# Forward-tail consequences of singleton-cap binding collisions

The generic finite-cap probe and collision sign theorems now live in
`UniformEquilibrium.Quitting.Punishment.SingletonCapBindingCollision`.
This Research module retains only their consequences for a supplied forward
exact-cap tail.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Consequences for the binding face of a forward exact-cap ray -/

namespace QuittingForwardExactCapTail

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Membership in the binding face is exactly a vanishing cap defect. -/
theorem mem_bindingFinset_iff_capDefect_eq_zero
    (tail : QuittingForwardExactCapTail reward) (who : ι) :
    who ∈ tail.bindingFinset ↔
      quittingSingletonCapDefect reward tail.capLimit who = 0 := by
  rw [bindingFinset, Finset.mem_filter, quittingSingletonCapDefect,
    sub_eq_zero]
  simp only [Finset.mem_univ, true_and]

/-- With a unique all-Continue root at the limiting cap, every binding
coordinate has another binding coordinate that strictly gains by joining
it. -/
theorem exists_binding_collisionGain_pos_of_unique_allContinue
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    {owner : ι} (howner : owner ∈ tail.bindingFinset) :
    ∃ other ∈ tail.bindingFinset, other ≠ owner ∧
      0 < quittingSingletonCollisionGain reward owner other := by
  obtain ⟨other, hne, hdefect, hgain⟩ :=
    exists_quittingSingletonCollisionGain_pos_of_unique_allContinue
      reward tail.capLimit tail.singleton_le_capLimit hunique owner
      ((tail.mem_bindingFinset_iff_capDefect_eq_zero owner).1 howner)
  exact ⟨other, (tail.mem_bindingFinset_iff_capDefect_eq_zero other).2 hdefect,
    hne, hgain⟩

/-- **The binding face is never a singleton** under a unique all-Continue
root at the limiting cap. -/
theorem bindingFinset_card_ne_one_of_unique_allContinue
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    tail.bindingFinset.card ≠ 1 := by
  intro hcard
  obtain ⟨owner, hsingleton⟩ := Finset.card_eq_one.1 hcard
  have howner : owner ∈ tail.bindingFinset := by
    rw [hsingleton]
    exact Finset.mem_singleton_self owner
  obtain ⟨other, hother, hne, -⟩ :=
    tail.exists_binding_collisionGain_pos_of_unique_allContinue hunique howner
  rw [hsingleton, Finset.mem_singleton] at hother
  exact hne hother

/-- **On a binding pair each coordinate strictly gains by joining the
other.**  This is the sign fact the finite-cap face computation consumes. -/
theorem quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two
    (tail : QuittingForwardExactCapTail reward)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.capLimit 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hcard : tail.bindingFinset.card = 2)
    {owner other : ι} (howner : owner ∈ tail.bindingFinset)
    (hother : other ∈ tail.bindingFinset) (hne : other ≠ owner) :
    0 < quittingSingletonCollisionGain reward owner other := by
  classical
  obtain ⟨witness, hwitness, hwitnessNe, hgain⟩ :=
    tail.exists_binding_collisionGain_pos_of_unique_allContinue hunique howner
  have hwitnessEq : witness = other := by
    by_contra hdifferent
    have hsubset : ({owner, other, witness} : Finset ι) ⊆ tail.bindingFinset := by
      intro player hplayer
      simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
      rcases hplayer with hcase | hcase | hcase
      · exact hcase ▸ howner
      · exact hcase ▸ hother
      · exact hcase ▸ hwitness
    have hthree : ({owner, other, witness} : Finset ι).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push Not
          exact ⟨Ne.symm hne, Ne.symm hwitnessNe⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact fun heq ↦ hdifferent heq.symm),
        Finset.card_singleton]
    have hle := Finset.card_le_card hsubset
    omega
  exact hwitnessEq ▸ hgain

end QuittingForwardExactCapTail

end GameTheory
