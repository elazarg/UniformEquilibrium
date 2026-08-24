/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Simplex

/-!
# Target-mass ledgers for finite coalition laws

This file records the game-independent counting argument behind target-coalition
forcing.  A law includes an empty outcome, which can represent nonabsorption.
Target-member security and outsider-incidence bounds force mass onto the exact
target.  No strategic or independence claim is made here.
-/

namespace Math.Probability

noncomputable section

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- A finite coalition law, including an empty outcome. -/
abbrev CoalitionOutcome (Player : Type) := Option {S : Finset Player // S.Nonempty}

/-- The coalition carried by an outcome; `none` carries the empty coalition. -/
def CoalitionOutcome.coalition : CoalitionOutcome Player → Finset Player
  | none => ∅
  | some terminal => terminal.1

/-- Mass of a coalition event under a finite outcome law. -/
def coalitionEventMass
    (mass : CoalitionOutcome Player → ℝ) (event : Finset Player → Prop)
    [DecidablePred event] : ℝ :=
  ∑ outcome, if event outcome.coalition then mass outcome else 0

/-- Mass of one exact coalition. -/
def exactCoalitionMass
    (mass : CoalitionOutcome Player → ℝ) (target : Finset Player) : ℝ :=
  coalitionEventMass mass (fun coalition => coalition = target)

/-- Mass of outcomes containing a target and a displayed outsider. -/
def targetOutsiderIncidenceMass
    (mass : CoalitionOutcome Player → ℝ)
    (target : Finset Player) (outsider : Player) : ℝ :=
  coalitionEventMass mass
    (fun coalition => target ⊆ coalition ∧ outsider ∈ coalition)

/-- Expected indicator that a target member belongs to the realized coalition. -/
def coalitionMemberMass
    (mass : CoalitionOutcome Player → ℝ) (member : Player) : ℝ :=
  coalitionEventMass mass (fun coalition => member ∈ coalition)

theorem exactCoalitionMass_nonneg
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : ∀ outcome, 0 ≤ mass outcome) (target : Finset Player) :
    0 ≤ exactCoalitionMass mass target := by
  unfold exactCoalitionMass coalitionEventMass
  exact Finset.sum_nonneg fun outcome _ => by
    split_ifs
    · exact hmass outcome
    · exact le_rfl

theorem exactCoalitionMass_add_le_one_of_ne
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player))
    {first second : Finset Player} (hne : first ≠ second) :
    exactCoalitionMass mass first + exactCoalitionMass mass second ≤ 1 := by
  unfold exactCoalitionMass coalitionEventMass
  rw [← Finset.sum_add_distrib, ← hmass.2]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hfirst : outcome.coalition = first
  · rw [if_pos hfirst, if_neg (fun hsecond => hne (hfirst.symm.trans hsecond))]
    simp
  · rw [if_neg hfirst]
    split_ifs <;> simp [hmass.1 outcome]

omit [DecidableEq Player] in
theorem coalitionEventMass_nonneg
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : ∀ outcome, 0 ≤ mass outcome) (event : Finset Player → Prop)
    [DecidablePred event] :
    0 ≤ coalitionEventMass mass event := by
  unfold coalitionEventMass
  exact Finset.sum_nonneg fun outcome _ => by
    split_ifs
    · exact hmass outcome
    · exact le_rfl

omit [Fintype Player] in
private theorem target_member_count_le
    (target coalition : Finset Player) (htarget : target.Nonempty) :
    (∑ member ∈ target, if member ∈ coalition then (1 : ℝ) else 0) ≤
      (target.card : ℝ) - 1 + if target ⊆ coalition then 1 else 0 := by
  by_cases hsubset : target ⊆ coalition
  · rw [if_pos hsubset]
    calc
      (∑ member ∈ target,
          if member ∈ coalition then (1 : ℝ) else 0) =
          ∑ _member ∈ target, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro member hmember
        rw [if_pos (hsubset hmember)]
      _ = (target.card : ℝ) := by simp
      _ = (target.card : ℝ) - 1 + 1 := by ring
      _ ≤ (target.card : ℝ) - 1 + 1 := le_rfl
  · rw [if_neg hsubset]
    rw [Finset.not_subset] at hsubset
    obtain ⟨missing, hmissingTarget, hmissingCoalition⟩ := hsubset
    have hsumErase :
        (∑ member ∈ target, if member ∈ coalition then (1 : ℝ) else 0) =
          ∑ member ∈ target.erase missing,
            if member ∈ coalition then (1 : ℝ) else 0 := by
      rw [← Finset.add_sum_erase target
        (fun member => if member ∈ coalition then (1 : ℝ) else 0)
        hmissingTarget]
      simp [hmissingCoalition]
    rw [hsumErase]
    calc
      (∑ member ∈ target.erase missing,
          if member ∈ coalition then (1 : ℝ) else 0) ≤
          ∑ _member ∈ target.erase missing, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro member _
        split_ifs <;> norm_num
      _ = (target.card : ℝ) - 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [Finset.card_erase_of_mem hmissingTarget]
        rw [Nat.cast_sub (Finset.one_le_card.mpr htarget)]
        norm_num
      _ ≤ (target.card : ℝ) - 1 + 0 := by simp

private theorem sum_memberMass_le_card_sub_one_add_containingMass
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player))
    (target : Finset Player) (htarget : target.Nonempty) :
    (∑ member ∈ target, coalitionMemberMass mass member) ≤
      (target.card : ℝ) - 1 +
        coalitionEventMass mass (fun coalition => target ⊆ coalition) := by
  unfold coalitionMemberMass coalitionEventMass
  rw [Finset.sum_comm]
  have hpoint (outcome : CoalitionOutcome Player) :
      (∑ member ∈ target,
          if member ∈ outcome.coalition then mass outcome else 0) ≤
        mass outcome * ((target.card : ℝ) - 1) +
          if target ⊆ outcome.coalition then mass outcome else 0 := by
    have hcount := target_member_count_le target outcome.coalition htarget
    have hscaled := mul_le_mul_of_nonneg_left hcount (hmass.1 outcome)
    calc
      (∑ member ∈ target,
          if member ∈ outcome.coalition then mass outcome else 0) =
          mass outcome *
            ∑ member ∈ target,
              if member ∈ outcome.coalition then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro member _
        split_ifs <;> simp
      _ ≤ mass outcome * ((target.card : ℝ) - 1) +
          mass outcome * (if target ⊆ outcome.coalition then 1 else 0) := by
        simpa [mul_add] using hscaled
      _ = mass outcome * ((target.card : ℝ) - 1) +
          if target ⊆ outcome.coalition then mass outcome else 0 := by
        split_ifs <;> simp
  calc
    (∑ outcome, ∑ member ∈ target,
        if member ∈ outcome.coalition then mass outcome else 0) ≤
        ∑ outcome, (mass outcome * ((target.card : ℝ) - 1) +
          if target ⊆ outcome.coalition then mass outcome else 0) := by
      exact Finset.sum_le_sum fun outcome _ => hpoint outcome
    _ = (target.card : ℝ) - 1 +
        ∑ outcome, if target ⊆ outcome.coalition then mass outcome else 0 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass.2, one_mul]

private theorem containingMass_le_exact_add_sum_outsiderIncidence
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player))
    (target : Finset Player) :
    coalitionEventMass mass (fun coalition => target ⊆ coalition) ≤
      exactCoalitionMass mass target +
        ∑ outsider ∈ Finset.univ \ target,
          targetOutsiderIncidenceMass mass target outsider := by
  unfold exactCoalitionMass targetOutsiderIncidenceMass
  simp only [coalitionEventMass]
  have hswap :
      (∑ outsider ∈ Finset.univ \ target,
          ∑ outcome,
            if target ⊆ outcome.coalition ∧ outsider ∈ outcome.coalition then
              mass outcome else 0) =
        ∑ outcome, ∑ outsider ∈ Finset.univ \ target,
          if target ⊆ outcome.coalition ∧ outsider ∈ outcome.coalition then
            mass outcome else 0 := by
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hcontains : target ⊆ outcome.coalition
  · rw [if_pos hcontains]
    by_cases heq : outcome.coalition = target
    · rw [if_pos heq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun outsider _ => by
        split_ifs
        · exact hmass.1 outcome
        · exact le_rfl)
    · rw [if_neg heq]
      have hproper : target ⊂ outcome.coalition :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hcontains, Ne.symm heq⟩
      obtain ⟨outsider, houtCoalition, houtTarget⟩ :=
        Finset.exists_of_ssubset hproper
      have houtComp : outsider ∈ Finset.univ \ target := by
        simp [houtTarget]
      calc
        mass outcome =
            if target ⊆ outcome.coalition ∧ outsider ∈ outcome.coalition then
              mass outcome else 0 := by simp [hcontains, houtCoalition]
        _ ≤ ∑ outsider ∈ Finset.univ \ target,
            if target ⊆ outcome.coalition ∧ outsider ∈ outcome.coalition then
              mass outcome else 0 := by
          exact Finset.single_le_sum
            (s := Finset.univ \ target)
            (f := fun other =>
              if target ⊆ outcome.coalition ∧ other ∈ outcome.coalition then
                mass outcome else 0)
            (fun other _ => by
              split_ifs
              · exact hmass.1 outcome
              · exact le_rfl)
            houtComp
        _ ≤ 0 + ∑ outsider ∈ Finset.univ \ target,
            if target ⊆ outcome.coalition ∧ outsider ∈ outcome.coalition then
              mass outcome else 0 := by simp
  · rw [if_neg hcontains]
    exact add_nonneg (by
      split_ifs
      · exact hmass.1 outcome
      · exact le_rfl) (Finset.sum_nonneg fun outsider _ => by
        split_ifs
        · exact hmass.1 outcome
        · exact le_rfl)

/-- Target security and uniform outsider-incidence control force exact target mass.

The law may charge the empty outcome.  No independence or realizability assumption is
used. -/
theorem exactCoalitionMass_ge_of_memberSecurity_of_outsiderIncidence
    {mass : CoalitionOutcome Player → ℝ}
    (hmass : mass ∈ stdSimplex ℝ (CoalitionOutcome Player))
    (target : Finset Player) (htarget : target.Nonempty)
    {epsilon incidenceBound : ℝ}
    (hsecurity : ∀ member ∈ target,
      1 - epsilon ≤ coalitionMemberMass mass member)
    (hincidence : ∀ outsider ∉ target,
      targetOutsiderIncidenceMass mass target outsider ≤ incidenceBound) :
    1 - (target.card : ℝ) * epsilon -
        ((Finset.univ \ target).card : ℝ) * incidenceBound ≤
      exactCoalitionMass mass target := by
  have hsecuritySum :
      (target.card : ℝ) * (1 - epsilon) ≤
        ∑ member ∈ target, coalitionMemberMass mass member := by
    calc
      (target.card : ℝ) * (1 - epsilon) =
          ∑ _member ∈ target, (1 - epsilon) := by simp; ring
      _ ≤ ∑ member ∈ target, coalitionMemberMass mass member := by
        exact Finset.sum_le_sum fun member hmember => hsecurity member hmember
  have htargetContaining :=
    sum_memberMass_le_card_sub_one_add_containingMass hmass target htarget
  have hunion :=
    containingMass_le_exact_add_sum_outsiderIncidence hmass target
  have hincidenceSum :
      (∑ outsider ∈ Finset.univ \ target,
        targetOutsiderIncidenceMass mass target outsider) ≤
        ((Finset.univ \ target).card : ℝ) * incidenceBound := by
    calc
      (∑ outsider ∈ Finset.univ \ target,
          targetOutsiderIncidenceMass mass target outsider) ≤
          ∑ _outsider ∈ Finset.univ \ target, incidenceBound := by
        apply Finset.sum_le_sum
        intro outsider hout
        exact hincidence outsider (by simpa using hout)
      _ = ((Finset.univ \ target).card : ℝ) * incidenceBound := by simp
  linarith

end

end Math.Probability
