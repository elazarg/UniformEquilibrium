/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteBinaryBlockEquilibrium
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure equilibria from blockwise weighted potentials

A finite binary game has a pure equilibrium when later blocks do not affect
earlier action gains and every block admits a positive weighted potential,
with the actions in earlier blocks held fixed.  This is the potential-game
analogue of the increasing-differences block theorem.
-/

noncomputable section

namespace MathUE

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A triangular decomposition whose individual blocks have positive
weighted exact potentials, for every fixed choice on earlier blocks. -/
structure BinaryBlockWeightedPotentialCertificate
    (payoff : ι → Finset ι → ℝ) where
  level : ι → ℕ
  future : ∀ {who other S}, level who < level other →
    binaryJoinGain payoff who (insert other S) =
      binaryJoinGain payoff who S
  potential : ℕ → Finset ι → Finset ι → ℝ
  weight : ι → ℝ
  weight_pos : ∀ who, 0 < weight who
  potential_insert : ∀ {rank outside selected who},
    (∀ player ∈ outside, level player < rank) →
    (∀ player ∈ selected, level player = rank) →
    level who = rank → who ∉ selected →
    potential rank outside (insert who selected) -
        potential rank outside selected =
      weight who * binaryJoinGain payoff who (outside ∪ selected)

namespace BinaryBlockWeightedPotentialCertificate

variable {payoff : ι → Finset ι → ℝ}

omit [Fintype ι] in
private theorem joinGain_union_eq_of_future
    (certificate : BinaryBlockWeightedPotentialCertificate payoff)
    {who : ι} {S T : Finset ι}
    (hfuture : ∀ other ∈ T, certificate.level who < certificate.level other) :
    binaryJoinGain payoff who (S ∪ T) = binaryJoinGain payoff who S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert other T hnotMem ih =>
      rw [Finset.union_insert, certificate.future (hfuture other (by simp))]
      exact ih fun player hplayer => hfuture player (by simp [hplayer])

omit [Fintype ι] in
private theorem exists_stable_on_block
    (certificate : BinaryBlockWeightedPotentialCertificate payoff)
    {block outside : Finset ι} {rank : ℕ}
    (hblock : ∀ who, who ∈ block ↔ certificate.level who = rank)
    (houtsideLevel : ∀ player ∈ outside, certificate.level player < rank)
    (hdisjoint : Disjoint outside block) :
    ∃ selected ⊆ block, ∀ who ∈ block,
      if who ∈ selected then
        0 ≤ binaryJoinGain payoff who (outside ∪ selected)
      else
        binaryJoinGain payoff who (outside ∪ selected) ≤ 0 := by
  classical
  obtain ⟨selected, hselected, hmax⟩ :=
    Finset.exists_max_image block.powerset
      (certificate.potential rank outside) ⟨∅, by simp⟩
  have hsubset : selected ⊆ block := Finset.mem_powerset.mp hselected
  have hselectedLevel : ∀ player ∈ selected,
      certificate.level player = rank := by
    intro player hplayer
    exact (hblock player).mp (hsubset hplayer)
  refine ⟨selected, hsubset, fun who hwho => ?_⟩
  by_cases hmem : who ∈ selected
  · rw [if_pos hmem]
    by_contra hnot
    have hwhoErase : who ∉ selected.erase who := by simp
    have hlevel : certificate.level who = rank := (hblock who).mp hwho
    have hpotential := certificate.potential_insert
      (rank := rank) (outside := outside) (selected := selected.erase who)
      houtsideLevel (fun player hplayer =>
        hselectedLevel player (Finset.mem_of_mem_erase hplayer))
      hlevel hwhoErase
    have hinsert : insert who (selected.erase who) = selected :=
      Finset.insert_erase hmem
    rw [hinsert] at hpotential
    have hwhoOutside : who ∉ outside := by
      intro hmemOutside
      exact Finset.disjoint_left.mp hdisjoint hmemOutside hwho
    have hcoalition : insert who (outside ∪ selected.erase who) =
        outside ∪ selected := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [hmem]
      · simp [hplayer]
    have hgain : binaryJoinGain payoff who
        (outside ∪ selected.erase who) =
          binaryJoinGain payoff who (outside ∪ selected) := by
      rw [← hcoalition, binaryJoinGain_insert_self]
    rw [hgain] at hpotential
    have hstrict : certificate.potential rank outside (selected.erase who) >
        certificate.potential rank outside selected := by
      have hweight := certificate.weight_pos who
      nlinarith
    have heraseMem : selected.erase who ∈ block.powerset := by
      exact Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsubset)
    exact (not_lt_of_ge (hmax _ heraseMem)) hstrict
  · rw [if_neg hmem]
    by_contra hnot
    have hlevel : certificate.level who = rank := (hblock who).mp hwho
    have hpotential := certificate.potential_insert
      (rank := rank) (outside := outside) (selected := selected)
      houtsideLevel hselectedLevel hlevel hmem
    have hgain : 0 < binaryJoinGain payoff who (outside ∪ selected) :=
      lt_of_not_ge hnot
    have hstrict : certificate.potential rank outside selected <
        certificate.potential rank outside (insert who selected) := by
      have hweight := certificate.weight_pos who
      nlinarith
    have hinsertMem : insert who selected ∈ block.powerset := by
      exact Finset.mem_powerset.mpr (Finset.insert_subset hwho hsubset)
    exact (not_lt_of_ge (hmax _ hinsertMem)) hstrict

/-- A finite block-triangular binary game with a positive weighted potential
on every block has a pure equilibrium. -/
theorem exists_isBinaryGainStable
    (certificate : BinaryBlockWeightedPotentialCertificate payoff) :
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
          certificate.exists_stable_on_block hblock
            (fun player hplayer =>
              Finset.mem_filter.mp (houtside hplayer) |>.2)
            hdisjoint
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

end BinaryBlockWeightedPotentialCertificate

/-! ## Affine gains with blockwise symmetrizing weights -/

/-- The weighted quadratic potential for one binary block, with the actions
in all earlier blocks held fixed in `outside`.  The factor `1 / 2` removes
the double counting of unordered pairs. -/
def binaryAffineBlockPotential
    (bias : ι → ℝ) (coefficient : ι → ι → ℝ) (weight : ι → ℝ)
    (outside selected : Finset ι) : ℝ :=
  (∑ who ∈ selected,
      weight who * (bias who + ∑ other ∈ outside, coefficient who other)) +
    (1 / 2 : ℝ) *
      ∑ who ∈ selected,
        ∑ other ∈ selected.erase who,
          weight who * coefficient who other

omit [Fintype ι] in
theorem binaryAffineBlockPotential_insert
    (bias : ι → ℝ) (coefficient : ι → ι → ℝ) (weight : ι → ℝ)
    {outside selected : Finset ι} {who : ι}
    (_hwhoOutside : who ∉ outside)
    (hwho : who ∉ selected)
    (hdisjoint : Disjoint outside selected)
    (hsymmetric : ∀ other ∈ selected,
      weight who * coefficient who other =
        weight other * coefficient other who) :
    binaryAffineBlockPotential bias coefficient weight outside
          (insert who selected) -
        binaryAffineBlockPotential bias coefficient weight outside selected =
      weight who *
        (bias who + ∑ other ∈ outside ∪ selected, coefficient who other) := by
  classical
  simp only [binaryAffineBlockPotential, Finset.sum_insert hwho]
  have hne : ∀ other ∈ selected, other ≠ who := by
    intro other hother heq
    exact hwho (heq ▸ hother)
  simp_rw [Finset.erase_insert_eq_erase]
  simp_rw [Finset.erase_eq_of_notMem hwho]
  have hinner : ∀ other ∈ selected,
      ∑ player ∈ (insert who selected).erase other,
          weight other * coefficient other player =
        weight other * coefficient other who +
          ∑ player ∈ selected.erase other,
            weight other * coefficient other player := by
    intro other hother
    have herase : (insert who selected).erase other =
        insert who (selected.erase other) := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp only [Finset.mem_erase, Finset.mem_insert, true_or, iff_true]
        exact ⟨Ne.symm (hne other hother), trivial⟩
      · simp [hplayer]
    rw [herase, Finset.sum_insert]
    exact fun hmem => hwho (Finset.mem_of_mem_erase hmem)
  have hinnerSum :
      (∑ other ∈ selected,
        ∑ player ∈ (insert who selected).erase other,
          weight other * coefficient other player) =
        ∑ other ∈ selected,
          (weight other * coefficient other who +
            ∑ player ∈ selected.erase other,
              weight other * coefficient other player) := by
    apply Finset.sum_congr rfl
    intro other hother
    exact hinner other hother
  rw [hinnerSum]
  have hsymSum :
      (∑ other ∈ selected, weight other * coefficient other who) =
        ∑ other ∈ selected, weight who * coefficient who other := by
    apply Finset.sum_congr rfl
    intro other hother
    exact (hsymmetric other hother).symm
  rw [Finset.sum_add_distrib, hsymSum]
  rw [Finset.sum_union]
  · rw [Finset.mul_sum]
    simp only [← Finset.mul_sum]
    ring
  · exact hdisjoint

/-- Raw affine binary-game data, triangular by `level` and positively
symmetrized on every level block. -/
structure BinaryAffineBlockWeightedCertificate
    (payoff : ι → Finset ι → ℝ) where
  level : ι → ℕ
  bias : ι → ℝ
  coefficient : ι → ι → ℝ
  weight : ι → ℝ
  weight_pos : ∀ who, 0 < weight who
  joinGain_eq : ∀ who S,
    binaryJoinGain payoff who S =
      bias who + ∑ other ∈ S.erase who, coefficient who other
  future_coefficient_zero : ∀ {who other}, level who < level other →
    coefficient who other = 0
  within_symmetry : ∀ {who other}, who ≠ other → level who = level other →
    weight who * coefficient who other =
      weight other * coefficient other who

namespace BinaryAffineBlockWeightedCertificate

variable {payoff : ι → Finset ι → ℝ}

/-- Affine triangular data with symmetrizing weights produce the blockwise
weighted-potential certificate. -/
def toBlockWeightedPotentialCertificate
    (certificate : BinaryAffineBlockWeightedCertificate payoff) :
    BinaryBlockWeightedPotentialCertificate payoff where
  level := certificate.level
  future := by
    intro who other S hlevel
    have hne : who ≠ other := fun heq => by subst other; omega
    rw [certificate.joinGain_eq, certificate.joinGain_eq]
    by_cases hother : other ∈ S
    · rw [Finset.insert_eq_self.mpr hother]
    · have herase : (insert other S).erase who =
          insert other (S.erase who) := by
        ext player
        by_cases hplayer : player = who
        · subst player
          simp [hne]
        · simp [hplayer]
      rw [herase, Finset.sum_insert]
      · rw [certificate.future_coefficient_zero hlevel]
        ring
      · simp [hother, Ne.symm hne]
  potential := fun _ outside selected =>
    binaryAffineBlockPotential certificate.bias certificate.coefficient
      certificate.weight outside selected
  weight := certificate.weight
  weight_pos := certificate.weight_pos
  potential_insert := by
    intro rank outside selected who houtside hselected hwhoLevel hwho
    have hwhoOutside : who ∉ outside := by
      intro hmem
      have := houtside who hmem
      omega
    have hdisjoint : Disjoint outside selected := by
      rw [Finset.disjoint_left]
      intro player hplayerOutside hplayerSelected
      have hlower := houtside player hplayerOutside
      have hequal := hselected player hplayerSelected
      omega
    have hsymmetry : ∀ other ∈ selected,
        certificate.weight who * certificate.coefficient who other =
          certificate.weight other * certificate.coefficient other who := by
      intro other hother
      have hne : who ≠ other := by
        intro heq
        subst other
        exact hwho hother
      exact certificate.within_symmetry hne
        (hwhoLevel.trans (hselected other hother).symm)
    rw [binaryAffineBlockPotential_insert certificate.bias
      certificate.coefficient certificate.weight hwhoOutside hwho hdisjoint
      hsymmetry]
    rw [certificate.joinGain_eq]
    have herase : (outside ∪ selected).erase who = outside ∪ selected := by
      rw [Finset.erase_eq_of_notMem]
      simp [hwhoOutside, hwho]
    rw [herase]

/-- Every finite binary game with affine triangular gains and positive
blockwise symmetrizing weights has a pure equilibrium. -/
theorem exists_isBinaryGainStable
    (certificate : BinaryAffineBlockWeightedCertificate payoff) :
    ∃ S, IsBinaryGainStable payoff S :=
  certificate.toBlockWeightedPotentialCertificate.exists_isBinaryGainStable

end BinaryAffineBlockWeightedCertificate


end MathUE
