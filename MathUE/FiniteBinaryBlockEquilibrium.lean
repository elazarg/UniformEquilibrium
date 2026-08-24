/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
# Pure equilibria in block-triangular binary games

This file proves a finite, game-independent equilibrium lemma.  A binary
game has increasing differences among players on the same natural-numbered
block.  Players in later blocks have no effect on the action gain of players
in earlier blocks.  Solving the blocks from first to last then produces a
pure equilibrium.

The result is stated directly in terms of the gain from changing action zero
to action one.  It does not assume or produce a potential.
-/

noncomputable section

namespace MathUE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Gain to `who` from choosing action one rather than action zero, with the
other action-one players recorded by `S`.  Membership of `who` in `S` is
ignored by the `insert`/`erase` normalization. -/
def binaryJoinGain (payoff : ι → Finset ι → ℝ) (who : ι)
    (S : Finset ι) : ℝ :=
  payoff who (insert who S) - payoff who (S.erase who)

omit [Fintype ι] in
@[simp] theorem binaryJoinGain_insert_self
    (payoff : ι → Finset ι → ℝ) (who : ι) (S : Finset ι) :
    binaryJoinGain payoff who (insert who S) =
      binaryJoinGain payoff who S := by
  simp [binaryJoinGain]

/-- The action-one coalition is a pure equilibrium, written using normalized
join gains. -/
def IsBinaryGainStable (payoff : ι → Finset ι → ℝ) (S : Finset ι) : Prop :=
  ∀ who,
    if who ∈ S then 0 ≤ binaryJoinGain payoff who S
    else binaryJoinGain payoff who S ≤ 0

/-- Global increasing differences in a finite binary game. -/
def HasBinaryIncreasingDifferences
    (payoff : ι → Finset ι → ℝ) : Prop :=
  ∀ {who other S}, who ≠ other →
    binaryJoinGain payoff who S ≤
      binaryJoinGain payoff who (insert other S)

/-- Increasing differences within blocks and exact invariance from later
blocks to earlier blocks. -/
structure BinaryBlockTriangularCertificate
    (payoff : ι → Finset ι → ℝ) where
  level : ι → ℕ
  within : ∀ {who other S}, who ≠ other → level who = level other →
    binaryJoinGain payoff who S ≤
      binaryJoinGain payoff who (insert other S)
  future : ∀ {who other S}, level who < level other →
    binaryJoinGain payoff who (insert other S) =
      binaryJoinGain payoff who S

namespace BinaryBlockTriangularCertificate

variable {payoff : ι → Finset ι → ℝ}

omit [Fintype ι] in
private theorem joinGain_union_eq_of_future
    (certificate : BinaryBlockTriangularCertificate payoff)
    {who : ι} {S T : Finset ι}
    (hfuture : ∀ other ∈ T, certificate.level who < certificate.level other) :
    binaryJoinGain payoff who (S ∪ T) = binaryJoinGain payoff who S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert other T hnotMem ih =>
      rw [Finset.union_insert, certificate.future (hfuture other (by simp))]
      exact ih fun player hplayer => hfuture player (by simp [hplayer])

private theorem exists_stable_on_block
    (certificate : BinaryBlockTriangularCertificate payoff)
    {block outside : Finset ι} {rank : ℕ}
    (hblock : ∀ who, who ∈ block ↔ certificate.level who = rank)
    (hdisjoint : Disjoint outside block) :
    ∃ selected ⊆ block, ∀ who ∈ block,
      if who ∈ selected then
        0 ≤ binaryJoinGain payoff who (outside ∪ selected)
      else
        binaryJoinGain payoff who (outside ∪ selected) ≤ 0 := by
  classical
  let admissible : Finset (Finset ι) :=
    block.powerset.filter fun selected =>
      ∀ who ∈ selected,
        0 < binaryJoinGain payoff who (outside ∪ selected)
  have hempty : (∅ : Finset ι) ∈ admissible := by
    simp [admissible]
  obtain ⟨selected, hselected, hmax⟩ :=
    Finset.exists_max_image admissible Finset.card ⟨∅, hempty⟩
  have hsubset : selected ⊆ block := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hselected).1
  have hpositive : ∀ who ∈ selected,
      0 < binaryJoinGain payoff who (outside ∪ selected) :=
    (Finset.mem_filter.mp hselected).2
  refine ⟨selected, hsubset, fun who hwho => ?_⟩
  by_cases hmem : who ∈ selected
  · rw [if_pos hmem]
    exact (hpositive who hmem).le
  · rw [if_neg hmem]
    by_contra hnot
    have hgain : 0 < binaryJoinGain payoff who (outside ∪ selected) :=
      lt_of_not_ge hnot
    have hwhoOutside : who ∉ outside := by
      intro hmemOutside
      exact Finset.disjoint_left.mp hdisjoint hmemOutside hwho
    have hinsert : insert who selected ∈ admissible := by
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_powerset.mpr (Finset.insert_subset hwho hsubset)
      · intro player hplayer
        rw [Finset.mem_insert] at hplayer
        rcases hplayer with rfl | hplayer
        · simpa [Finset.union_insert, hwhoOutside, hmem] using hgain
        · have hne : player ≠ who := by
            intro heq
            exact hmem (heq ▸ hplayer)
          have hlevel : certificate.level player = certificate.level who := by
            rw [(hblock player).mp (hsubset hplayer), (hblock who).mp hwho]
          have hmono := certificate.within hne hlevel
            (S := outside ∪ selected)
          have hstrict := (hpositive player hplayer).trans_le hmono
          simpa [Finset.union_insert] using hstrict
    have hcard := hmax (insert who selected) hinsert
    rw [Finset.card_insert_of_notMem hmem] at hcard
    omega

/-- A block-triangular binary game has a pure equilibrium. -/
theorem exists_isBinaryGainStable
    (certificate : BinaryBlockTriangularCertificate payoff) :
    ∃ S, IsBinaryGainStable payoff S := by
  classical
  let below (rank : ℕ) : Finset ι :=
    Finset.univ.filter fun who => certificate.level who < rank
  have hpartial : ∀ rank, ∃ S, S ⊆ below rank ∧
      ∀ who ∈ below rank,
        if who ∈ S then 0 ≤ binaryJoinGain payoff who S
        else binaryJoinGain payoff who S ≤ 0 := by
    intro rank
    induction rank with
    | zero =>
        refine ⟨∅, by simp [below], ?_⟩
        simp [below]
    | succ rank ih =>
        obtain ⟨outside, houtside, hstable⟩ := ih
        let block : Finset ι :=
          Finset.univ.filter fun who => certificate.level who = rank
        have hblock : ∀ who, who ∈ block ↔ certificate.level who = rank := by
          intro who
          simp [block]
        have hdisjoint : Disjoint outside block := by
          rw [Finset.disjoint_left]
          intro who hwhoOutside hwhoBlock
          have hlt : certificate.level who < rank := by
            exact Finset.mem_filter.mp (houtside hwhoOutside) |>.2
          have heq : certificate.level who = rank := (hblock who).mp hwhoBlock
          omega
        obtain ⟨selected, hselected, hblockStable⟩ :=
          certificate.exists_stable_on_block hblock hdisjoint
        refine ⟨outside ∪ selected, ?_, ?_⟩
        · intro who hwho
          rw [Finset.mem_union] at hwho
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ who, by
            rcases hwho with hwho | hwho
            · have := Finset.mem_filter.mp (houtside hwho) |>.2
              omega
            · have := (hblock who).mp (hselected hwho)
              omega⟩
        · intro who hwhoBelow
          have hlevel : certificate.level who < rank + 1 := by
            exact Finset.mem_filter.mp hwhoBelow |>.2
          rcases Nat.lt_succ_iff_lt_or_eq.mp hlevel with hlt | heq
          · have hwhoOld : who ∈ below rank := by
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ who, hlt⟩
            have hwhoNotSelected : who ∉ selected := by
              intro hmem
              have := (hblock who).mp (hselected hmem)
              omega
            have hgainEq : binaryJoinGain payoff who (outside ∪ selected) =
                binaryJoinGain payoff who outside := by
              apply certificate.joinGain_union_eq_of_future
              intro other hother
              have hotherLevel := (hblock other).mp (hselected hother)
              omega
            simpa [Finset.mem_union, hwhoNotSelected, hgainEq] using
              hstable who hwhoOld
          · have hwhoBlock : who ∈ block := (hblock who).mpr heq
            have hwhoNotOutside : who ∉ outside := by
              intro hmem
              have := Finset.mem_filter.mp (houtside hmem) |>.2
              omega
            simpa [Finset.mem_union, hwhoNotOutside] using
              hblockStable who hwhoBlock
  let topRank := Finset.univ.sup certificate.level + 1
  obtain ⟨S, -, hstable⟩ := hpartial topRank
  refine ⟨S, fun who => ?_⟩
  have hlevel : certificate.level who < topRank := by
    unfold topRank
    exact Nat.lt_succ_of_le
      (Finset.le_sup (f := certificate.level) (Finset.mem_univ who))
  exact hstable who (Finset.mem_filter.mpr ⟨Finset.mem_univ who, hlevel⟩)

/-- The one-block special case: every finite binary game with increasing
differences has a pure equilibrium. -/
theorem exists_isBinaryGainStable_of_increasingDifferences
    (hincreasing : HasBinaryIncreasingDifferences payoff) :
    ∃ S, IsBinaryGainStable payoff S := by
  let certificate : BinaryBlockTriangularCertificate payoff :=
    { level := fun _ => 0
      within := fun hne _ => hincreasing hne
      future := by
        intro who other S hlt
        omega }
  exact certificate.exists_isBinaryGainStable

end BinaryBlockTriangularCertificate

end MathUE
