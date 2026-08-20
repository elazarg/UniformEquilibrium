/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SingletonPacketRefusal

/-!
# Support graph of a normalized singleton packet

Every supported owner in a nonsingleton normalized packet weakly prefers the
singleton exit of some other supported owner to its pinned target. Choosing
successors produces a finite directed support graph. A strict refusal edge
can be joined to a recurrent weak-preference class as a supported lasso.

These packet-local facts do not require a counterexample regime. They do not
by themselves supply outsider inequalities or an equilibrium compiler.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingNormalizedSingletonSourcePacket

/-- The finite support of the packet's normalized singleton mass. -/
def support (packet : QuittingNormalizedSingletonSourcePacket reward) : Finset ι :=
  Finset.univ.filter fun owner => 0 < packet.mass owner

@[simp] theorem mem_support_iff
    (packet : QuittingNormalizedSingletonSourcePacket reward) (owner : ι) :
    owner ∈ packet.support ↔ 0 < packet.mass owner := by
  simp [support]

/-- Mass vanishes away from the positive support. -/
theorem mass_eq_zero_of_notMem_support
    (packet : QuittingNormalizedSingletonSourcePacket reward) {owner : ι}
    (howner : owner ∉ packet.support) :
    packet.mass owner = 0 := by
  have hnot : ¬ 0 < packet.mass owner := by
    simpa [mem_support_iff] using howner
  exact le_antisymm (le_of_not_gt hnot) (packet.mass_nonneg owner)

/-- The positive support retains all of the normalized mass. -/
theorem sum_support_mass
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    ∑ owner ∈ packet.support, packet.mass owner = 1 := by
  rw [← packet.mass_sum]
  apply Finset.sum_subset (Finset.subset_univ packet.support)
  intro owner _ howner
  exact packet.mass_eq_zero_of_notMem_support howner

/-- The support is nonempty because its nonnegative masses sum to one. -/
theorem support_nonempty
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    packet.support.Nonempty := by
  by_contra hempty
  have hsum := packet.sum_support_mass
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
  simp at hsum

/-- Restricting a weighted singleton row to the positive support changes
nothing. -/
theorem sum_support_mul_singletonReward
    (packet : QuittingNormalizedSingletonSourcePacket reward) (who : ι) :
    ∑ owner ∈ packet.support,
        packet.mass owner * reward (quittingSingletonTerminal owner) who =
      quittingSingletonMixture reward packet.mass who := by
  unfold quittingSingletonMixture
  apply Finset.sum_subset (Finset.subset_univ packet.support)
  intro owner _ howner
  rw [packet.mass_eq_zero_of_notMem_support howner, zero_mul]

/-- Every supported row of a nonsingleton packet has a distinct supported
successor whose singleton outcome weakly beats that row's pinned target. -/
theorem exists_nonnegative_offDiagonal_on_support
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    ∃ other ∈ packet.support, other ≠ owner ∧
      packet.target owner ≤
        reward (quittingSingletonTerminal other) owner := by
  have hownerMass : 0 < packet.mass owner :=
    (packet.mem_support_iff owner).mp howner
  have hpinned := packet.positive_mass_pins_target owner hownerMass
  have herase : (packet.support.erase owner).Nonempty :=
    hsupport.erase_nonempty
  have hweighted :
      ∑ other ∈ packet.support.erase owner,
          packet.mass other * packet.target owner ≤
        ∑ other ∈ packet.support.erase owner,
          packet.mass other *
            reward (quittingSingletonTerminal other) owner := by
    have hmix := packet.mix_ge_target owner
    rw [← packet.sum_support_mul_singletonReward owner] at hmix
    have hmassSplit := Finset.sum_erase_add
      (s := packet.support) (f := packet.mass) howner
    have hrewardSplit := Finset.sum_erase_add
      (s := packet.support)
      (f := fun other => packet.mass other *
        reward (quittingSingletonTerminal other) owner) howner
    have hmassSum := packet.sum_support_mass
    rw [hmassSum] at hmassSplit
    rw [← hpinned] at hrewardSplit
    rw [← Finset.sum_mul]
    have htargetSplit :
        packet.target owner =
          (∑ other ∈ packet.support.erase owner, packet.mass other) *
              packet.target owner +
            packet.mass owner * packet.target owner := by
      rw [← add_mul, hmassSplit, one_mul]
    calc
      (∑ other ∈ packet.support.erase owner, packet.mass other) *
            packet.target owner =
          packet.target owner - packet.mass owner * packet.target owner := by
            linarith
      _ ≤ (∑ other ∈ packet.support,
              packet.mass other *
                reward (quittingSingletonTerminal other) owner) -
            packet.mass owner * packet.target owner :=
          sub_le_sub_right hmix _
      _ = ∑ other ∈ packet.support.erase owner,
            packet.mass other *
              reward (quittingSingletonTerminal other) owner := by
          linarith
  obtain ⟨other, hother, hle⟩ :=
    Finset.exists_le_of_sum_le herase hweighted
  have hotherSupport : other ∈ packet.support :=
    Finset.mem_of_mem_erase hother
  have hotherNe : other ≠ owner := Finset.ne_of_mem_erase hother
  have hotherMass : 0 < packet.mass other :=
    (packet.mem_support_iff other).mp hotherSupport
  refine ⟨other, hotherSupport, hotherNe, ?_⟩
  exact le_of_mul_le_mul_left hle hotherMass

/-- Packet support is either a singleton or carries the successor relation
needed to choose a weak directed support cycle.  The pointwise form avoids
installing an arbitrary choice as canonical packet data. -/
theorem support_singleton_or_successors
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    (∃ owner, packet.support = {owner}) ∨
      ∀ owner ∈ packet.support,
        ∃ other ∈ packet.support, other ≠ owner ∧
          packet.target owner ≤
            reward (quittingSingletonTerminal other) owner := by
  by_cases hs : packet.support.Nontrivial
  · exact Or.inr fun owner howner =>
      packet.exists_nonnegative_offDiagonal_on_support
        hs howner
  · obtain ⟨owner, howner⟩ := packet.support_nonempty
    refine Or.inl ⟨owner, Finset.ext fun other => ?_⟩
    constructor
    · intro hother
      have : other = owner := by
        by_contra hne
        exact hs ⟨other, hother, owner, howner, hne⟩
      simp [this]
    · intro heq
      have hother : other = owner := by simpa using heq
      rw [hother]
      exact howner

/-- A chosen weak-preference successor on a nontrivial packet support.  The
definition is deliberately local to the packet graph; no strategic meaning
is assigned to the arbitrary choice. -/
noncomputable def weakPreferenceSuccessor
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) (owner : ι) : ι :=
  if howner : owner ∈ packet.support then
    Classical.choose
      (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)
  else packet.support_nonempty.choose

theorem weakPreferenceSuccessor_mem
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) (owner : ι) :
    packet.weakPreferenceSuccessor hsupport owner ∈ packet.support := by
  by_cases howner : owner ∈ packet.support
  · simp only [weakPreferenceSuccessor, dif_pos howner]
    exact (Classical.choose_spec
      (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).1
  · simp only [weakPreferenceSuccessor, dif_neg howner]
    exact packet.support_nonempty.choose_spec

theorem weakPreferenceSuccessor_ne
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    packet.weakPreferenceSuccessor hsupport owner ≠ owner := by
  simp only [weakPreferenceSuccessor, dif_pos howner]
  exact (Classical.choose_spec
    (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).2.1

theorem target_le_weakPreferenceSuccessor_reward
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    {owner : ι} (howner : owner ∈ packet.support) :
    packet.target owner ≤ reward
      (quittingSingletonTerminal
        (packet.weakPreferenceSuccessor hsupport owner)) owner := by
  simp only [weakPreferenceSuccessor, dif_pos howner]
  exact (Classical.choose_spec
    (packet.exists_nonnegative_offDiagonal_on_support hsupport howner)).2.2

/-- A closed weak-preference orbit can be extracted from any supported seed,
not only from an arbitrary canonical support point. -/
theorem exists_weakPreferenceClosedOrbit_from
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial)
    (seed : ι) (hseed : seed ∈ packet.support) :
    ∃ start stop : ℕ, start < stop ∧
      let successor := packet.weakPreferenceSuccessor hsupport
      (successor^[start]) seed = (successor^[stop]) seed ∧
      (∀ time,
        (successor^[time]) seed ∈ packet.support ∧
        successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        packet.target ((successor^[time]) seed) ≤
          reward (quittingSingletonTerminal
            (successor ((successor^[time]) seed)))
            ((successor^[time]) seed)) := by
  let successor := packet.weakPreferenceSuccessor hsupport
  have horbitMem : ∀ time, (successor^[time]) seed ∈ packet.support := by
    intro time
    induction time with
    | zero => exact hseed
    | succ time ih =>
        rw [Function.iterate_succ_apply']
        exact packet.weakPreferenceSuccessor_mem hsupport _
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun time : ℕ => (successor^[time]) seed)
  have hedge : ∀ time,
      successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        packet.target ((successor^[time]) seed) ≤
          reward (quittingSingletonTerminal
            (successor ((successor^[time]) seed)))
            ((successor^[time]) seed) := by
    intro time
    exact ⟨packet.weakPreferenceSuccessor_ne hsupport (horbitMem time),
      packet.target_le_weakPreferenceSuccessor_reward hsupport
        (horbitMem time)⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨first, second, hlt, heq, ?_⟩
    intro time
    exact ⟨horbitMem time, hedge time⟩
  · refine ⟨second, first, hgt, heq.symm, ?_⟩
    intro time
    exact ⟨horbitMem time, hedge time⟩

/-- A nonsingleton packet support contains a finite closed orbit of weak
singleton preferences.  The returned interval is a closed directed walk;
one may erase repetitions to obtain a simple directed cycle.  Keeping the
orbit form avoids adding a separate finite-graph representation merely for
this consequence. -/
theorem exists_weakPreferenceClosedOrbit
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hsupport : packet.support.Nontrivial) :
    ∃ start stop : ℕ, start < stop ∧
      let successor := packet.weakPreferenceSuccessor hsupport
      let seed := packet.support_nonempty.choose
      (successor^[start]) seed = (successor^[stop]) seed ∧
      (∀ time,
        (successor^[time]) seed ∈ packet.support ∧
        successor ((successor^[time]) seed) ≠ (successor^[time]) seed ∧
        packet.target ((successor^[time]) seed) ≤
          reward (quittingSingletonTerminal
            (successor ((successor^[time]) seed)))
            ((successor^[time]) seed)) := by
  let seed := packet.support_nonempty.choose
  exact packet.exists_weakPreferenceClosedOrbit_from hsupport seed
    packet.support_nonempty.choose_spec

/-- The conditional refusal value is bounded above by one literal singleton
reward at a distinct positive-mass atom. -/
theorem exists_supported_refusal_le_singletonReward
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {owner : ι} (howner : owner ∈ packet.support)
    (hmass : packet.mass owner < 1) :
    ∃ other ∈ packet.support, other ≠ owner ∧
      quittingSingletonRefusalValue reward packet.mass owner owner ≤
        reward (quittingSingletonTerminal other) owner := by
  have hsumMass :
      ∑ other ∈ packet.support.erase owner, packet.mass other =
        1 - packet.mass owner := by
    have hsplit := Finset.sum_erase_add
      (s := packet.support) (f := packet.mass) howner
    rw [packet.sum_support_mass] at hsplit
    linarith
  have heraseNonempty : (packet.support.erase owner).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsumMass
    simp at hsumMass
    linarith
  have hsumReward :
      ∑ other ∈ packet.support.erase owner,
          packet.mass other * reward (quittingSingletonTerminal other) owner =
        ∑ other ∈ (Finset.univ.erase owner : Finset ι),
          packet.mass other * reward (quittingSingletonTerminal other) owner := by
    apply Finset.sum_subset
    · intro other hother
      simp only [Finset.mem_erase] at hother ⊢
      exact ⟨hother.1, Finset.mem_univ other⟩
    · intro other _ hother
      have hnotSupport : other ∉ packet.support := by
        intro hsupport
        exact hother (Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp ‹other ∈ Finset.univ.erase owner›).1,
            hsupport⟩)
      rw [packet.mass_eq_zero_of_notMem_support hnotSupport, zero_mul]
  have haverage :
      ∑ other ∈ packet.support.erase owner,
          packet.mass other *
            quittingSingletonRefusalValue reward packet.mass owner owner =
        ∑ other ∈ packet.support.erase owner,
          packet.mass other * reward (quittingSingletonTerminal other) owner := by
    have hdenom : 1 - packet.mass owner ≠ 0 :=
      ne_of_gt (sub_pos.mpr hmass)
    rw [← Finset.sum_mul, hsumMass, hsumReward]
    unfold quittingSingletonRefusalValue
    field_simp [hdenom]
  obtain ⟨other, hother, hle⟩ :=
    Finset.exists_le_of_sum_le heraseNonempty haverage.le
  have hotherSupport : other ∈ packet.support :=
    Finset.mem_of_mem_erase hother
  have hotherNe : other ≠ owner := Finset.ne_of_mem_erase hother
  have hotherMass : 0 < packet.mass other :=
    (packet.mem_support_iff other).mp hotherSupport
  refine ⟨other, hotherSupport, hotherNe, ?_⟩
  exact le_of_mul_le_mul_left hle hotherMass

end QuittingNormalizedSingletonSourcePacket

/-- A strict supported singleton edge feeding a recurrent weak-preference
class.  The strict entrance need not itself lie on the recurrent cycle. -/
structure QuittingStrictSupportedPreferenceLasso
    (packet : QuittingNormalizedSingletonSourcePacket reward) where
  entrance : ι
  first : ι
  entrance_mem : entrance ∈ packet.support
  first_mem : first ∈ packet.support
  first_ne : first ≠ entrance
  target_lt_mixture :
    packet.target entrance <
      quittingSingletonMixture reward packet.mass entrance
  mixture_lt_refusal :
    quittingSingletonMixture reward packet.mass entrance <
      quittingSingletonRefusalValue reward packet.mass entrance entrance
  refusal_le_first :
    quittingSingletonRefusalValue reward packet.mass entrance entrance ≤
      reward (quittingSingletonTerminal first) entrance
  support_nontrivial : packet.support.Nontrivial
  cycleStart : ℕ
  cycleStop : ℕ
  cycleStart_lt_cycleStop : cycleStart < cycleStop
  recurrent_closed :
    let successor := packet.weakPreferenceSuccessor support_nontrivial
    (successor^[cycleStart]) first = (successor^[cycleStop]) first
  recurrent_weak :
    let successor := packet.weakPreferenceSuccessor support_nontrivial
    ∀ time,
      (successor^[time]) first ∈ packet.support ∧
      successor ((successor^[time]) first) ≠ (successor^[time]) first ∧
      packet.target ((successor^[time]) first) ≤
        reward (quittingSingletonTerminal
          (successor ((successor^[time]) first)))
          ((successor^[time]) first)

end GameTheory
