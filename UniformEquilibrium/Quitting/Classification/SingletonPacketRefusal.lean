/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.AnalyticWaist

/-!
# Conditional refusal for normalized singleton packets

A normalized singleton source packet supplies a probability distribution on
singleton exits. Conditioning its singleton delivery on one owner not being
selected gives a refusal value. The identities below split the mixture at
that owner and express refusal gain exactly in terms of the owner's packet
surplus.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Singleton delivery to `who`, conditioned on the selected singleton owner
being different from `owner`.  The definition is used only when
`mass owner < 1`. -/
def quittingSingletonRefusalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) (owner who : ι) : ℝ :=
  (∑ other ∈ (Finset.univ.erase owner : Finset ι),
      mass other * reward (quittingSingletonTerminal other) who) /
    (1 - mass owner)

namespace QuittingNormalizedSingletonSourcePacket

/-- A packet mass is at most one. -/
theorem mass_le_one
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    packet.mass owner ≤ 1 := by
  rw [← packet.mass_sum]
  exact single_le_sum (fun other _ ↦ packet.mass_nonneg other)
    (mem_univ owner)

/-- Split the singleton mixture into the owner's atom and all other atoms. -/
theorem singletonMixture_eq_owner_add_erase
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (owner who : ι) :
    quittingSingletonMixture reward packet.mass who =
      packet.mass owner * reward (quittingSingletonTerminal owner) who +
        ∑ other ∈ (Finset.univ.erase owner : Finset ι),
          packet.mass other * reward (quittingSingletonTerminal other) who := by
  unfold quittingSingletonMixture
  rw [← sum_erase_add _ _ (mem_univ owner)]
  ac_rfl

/-- If an atom has full mass, the singleton mixture is exactly its reward
vector. -/
theorem singletonMixture_eq_singleton_of_mass_eq_one
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (hmass : packet.mass owner = 1) (who : ι) :
    quittingSingletonMixture reward packet.mass who =
      reward (quittingSingletonTerminal owner) who := by
  have heraseMass :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι), packet.mass other = 0 := by
    have hsplit := sum_erase_add
      (s := (Finset.univ : Finset ι)) (f := packet.mass)
      (a := owner) (mem_univ owner)
    rw [packet.mass_sum, hmass] at hsplit
    linarith
  have hzero : ∀ other ∈ (Finset.univ.erase owner : Finset ι),
      packet.mass other = 0 := by
    intro other hother
    apply le_antisymm
    · have hle : packet.mass other ≤
          ∑ player ∈ (Finset.univ.erase owner : Finset ι),
            packet.mass player :=
        single_le_sum (fun player _ ↦ packet.mass_nonneg player) hother
      simpa [heraseMass] using hle
    · exact packet.mass_nonneg other
  have hweightedZero :
      ∑ other ∈ (Finset.univ.erase owner : Finset ι),
        packet.mass other * reward (quittingSingletonTerminal other) who = 0 := by
    apply sum_eq_zero
    intro other hother
    rw [hzero other hother, zero_mul]
  rw [packet.singletonMixture_eq_owner_add_erase owner who, hmass]
  rw [hweightedZero]
  ring

/-- For a non-full atom, the singleton mixture is the affine combination of
its singleton reward and its conditional refusal value. -/
theorem singletonMixture_eq_mass_mul_add_refusal
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (hmass : packet.mass owner < 1) (who : ι) :
    quittingSingletonMixture reward packet.mass who =
      packet.mass owner * reward (quittingSingletonTerminal owner) who +
        (1 - packet.mass owner) *
          quittingSingletonRefusalValue reward packet.mass owner who := by
  rw [packet.singletonMixture_eq_owner_add_erase owner who]
  unfold quittingSingletonRefusalValue
  rw [mul_comm (1 - packet.mass owner),
    div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt hmass))]

/-- Exact refusal amplification on a pinned active atom.  The gain from
refusing relative to the original singleton mixture is its source surplus
multiplied by the odds of the refused atom. -/
theorem refusal_sub_mixture_eq_mass_div_mul_surplus
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (howner : 0 < packet.mass owner)
    (hmass : packet.mass owner < 1) :
    quittingSingletonRefusalValue reward packet.mass owner owner -
        quittingSingletonMixture reward packet.mass owner =
      packet.mass owner / (1 - packet.mass owner) *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by
  have hpinned := packet.positive_mass_pins_target owner howner
  rw [packet.singletonMixture_eq_owner_add_erase owner owner, hpinned]
  unfold quittingSingletonRefusalValue
  field_simp [sub_ne_zero.mpr (ne_of_gt hmass)]
  ring

end QuittingNormalizedSingletonSourcePacket

end GameTheory
