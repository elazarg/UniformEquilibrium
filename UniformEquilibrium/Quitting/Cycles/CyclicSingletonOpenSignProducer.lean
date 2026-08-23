/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FinitePowerSumRoot
import UniformEquilibrium.Quitting.Cycles.CyclicSingletonTailProducer

/-!
# Open-sign cyclic singleton producer

A cyclically invariant normalized singleton matrix whose first forward envy is
negative, whose later forward envies are nonnegative, and whose total forward
envy is positive admits an equal-hazard balanced singleton cycle.  The survival
factor is a root of the associated finite power sum.  Solo levels and all
nonsingleton rewards remain unrestricted.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

/-- A finite tail of the sequence `coefficient`, starting at `start` and
stopping just before `stop`. -/
def finiteCyclicSingletonTail
    (coefficient : ℕ → ℝ) (stop start : ℕ) (survival : ℝ) : ℝ :=
  ∑ offset ∈ Finset.range (stop - start),
    coefficient (start + offset) * survival ^ offset

theorem finiteCyclicSingletonTail_eq_zero_of_le
    (coefficient : ℕ → ℝ) (survival : ℝ) {stop start : ℕ}
    (h : stop ≤ start) :
    finiteCyclicSingletonTail coefficient stop start survival = 0 := by
  simp [finiteCyclicSingletonTail, Nat.sub_eq_zero_of_le h]

/-- Head-tail recursion for a finite power tail. -/
theorem finiteCyclicSingletonTail_recursion
    (coefficient : ℕ → ℝ) (survival : ℝ) {stop start : ℕ}
    (h : start < stop) :
    finiteCyclicSingletonTail coefficient stop start survival =
      coefficient start + survival *
        finiteCyclicSingletonTail coefficient stop (start + 1) survival := by
  unfold finiteCyclicSingletonTail
  have hsub : stop - start = (stop - (start + 1)) + 1 := by omega
  rw [hsub, Finset.sum_range_succ']
  simp only [add_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro offset hoffset
  rw [show start + (offset + 1) = start + 1 + offset by omega, pow_succ']
  ring

variable {extra : ℕ}

/-- Extend cyclic coefficients by zero outside their finite player range. -/
def cyclicSingletonGammaNat (gamma : Fin (extra + 2) → ℝ) (index : ℕ) : ℝ :=
  if hindex : index < extra + 2 then gamma ⟨index, hindex⟩ else 0

@[simp] theorem cyclicSingletonGammaNat_apply
    (gamma : Fin (extra + 2) → ℝ) (index : Fin (extra + 2)) :
    cyclicSingletonGammaNat gamma index.val = gamma index := by
  simp [cyclicSingletonGammaNat, index.isLt]

/-- Polynomial coefficients `gamma₁,…,gamma_(n-1)`, with the constant
coefficient equal to the first forward envy. -/
def cyclicSingletonPowerCoefficient
    (gamma : Fin (extra + 2) → ℝ) (index : Fin (extra + 1)) : ℝ :=
  gamma ⟨index.val + 1, by omega⟩

/-- The balance polynomial `gamma₁ + gamma₂ s + ⋯`. -/
def cyclicSingletonBalancePolynomial
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ) : ℝ :=
  Math.finitePowerSum (cyclicSingletonPowerCoefficient gamma) survival

/-- Closed cyclic tails.  Offset zero is pinned to zero; every positive offset
uses the ordinary finite tail through the last forward envy. -/
def cyclicSingletonTail
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ)
    (offset : Fin (extra + 2)) : ℝ :=
  if offset.val = 0 then 0 else
    finiteCyclicSingletonTail (cyclicSingletonGammaNat gamma)
      (extra + 2) offset.val survival

@[simp] theorem cyclicSingletonTail_zero
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ) :
    cyclicSingletonTail gamma survival 0 = 0 := by
  simp [cyclicSingletonTail]

theorem cyclicSingletonTail_one_eq_balancePolynomial
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ) :
    cyclicSingletonTail gamma survival ⟨1, by omega⟩ =
      cyclicSingletonBalancePolynomial gamma survival := by
  rw [cyclicSingletonTail, if_neg (by norm_num)]
  unfold finiteCyclicSingletonTail cyclicSingletonBalancePolynomial
    Math.finitePowerSum cyclicSingletonPowerCoefficient
  rw [show extra + 2 - 1 = extra + 1 by omega]
  rw [← Fin.sum_univ_eq_sum_range
    (fun index ↦ cyclicSingletonGammaNat gamma (1 + index) * survival ^ index)
    (extra + 1)]
  apply Fintype.sum_congr
  intro index
  have hlt : 1 + index.val < extra + 2 := by omega
  simp only [cyclicSingletonGammaNat, hlt, dif_pos]
  congr 2
  apply Fin.ext
  simp [Nat.add_comm]

theorem finRotate_sub_eq_finRotate_sub
    (phase who : Fin (extra + 2)) :
    finRotate (extra + 2) phase - who =
      finRotate (extra + 2) (phase - who) := by
  rw [finRotate_apply, finRotate_apply]
  abel

theorem cyclicSingletonTail_recurrence
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ)
    (hgammaZero : gamma 0 = 0)
    (hbalance : cyclicSingletonBalancePolynomial gamma survival = 0)
    (offset : Fin (extra + 2)) :
    cyclicSingletonTail gamma survival offset = gamma offset +
      survival * cyclicSingletonTail gamma survival
        (finRotate (extra + 2) offset) := by
  by_cases hoffset : offset.val = 0
  · have hoffsetZero : offset = 0 := Fin.ext hoffset
    subst offset
    rw [cyclicSingletonTail_zero, hgammaZero]
    simp only [zero_add]
    have hrotate : finRotate (extra + 2) (0 : Fin (extra + 2)) =
        ⟨1, by omega⟩ := by
      apply Fin.ext
      norm_num [finRotate_apply]
    rw [hrotate, cyclicSingletonTail_one_eq_balancePolynomial, hbalance, mul_zero]
  · rw [cyclicSingletonTail, if_neg hoffset]
    by_cases hlast : offset.val + 1 = extra + 2
    · have hrotateZero : finRotate (extra + 2) offset = 0 := by
        apply Fin.ext
        rw [Math.val_finRotate]
        simp [hlast]
      rw [hrotateZero, cyclicSingletonTail_zero, mul_zero, add_zero]
      have htail := finiteCyclicSingletonTail_recursion
        (cyclicSingletonGammaNat gamma) survival offset.isLt
      rw [htail]
      have hstop : extra + 2 ≤ offset.val + 1 := by omega
      rw [finiteCyclicSingletonTail_eq_zero_of_le _ _ hstop, mul_zero, add_zero]
      exact cyclicSingletonGammaNat_apply gamma offset
    · have hsuccLt : offset.val + 1 < extra + 2 := by omega
      have hrotateVal : (finRotate (extra + 2) offset).val = offset.val + 1 := by
        rw [Math.val_finRotate, Nat.mod_eq_of_lt hsuccLt]
      rw [cyclicSingletonTail, if_neg (by omega :
        (finRotate (extra + 2) offset).val ≠ 0)]
      rw [hrotateVal]
      have htail := finiteCyclicSingletonTail_recursion
        (cyclicSingletonGammaNat gamma) survival offset.isLt
      rw [htail, cyclicSingletonGammaNat_apply gamma offset]

/-- Cyclic invariance of the raw normalized singleton matrix. -/
def IsQuittingCyclicSingletonMatrix
    (reward : {S : Finset (Fin (extra + 2)) // S.Nonempty} →
      Payoff (Fin (extra + 2)))
    (gamma : Fin (extra + 2) → ℝ) : Prop :=
  ∀ who phase, quittingSingletonMatrix reward who phase = gamma (phase - who)

/-- Raw equal-hazard balance and floor criterion for the canonical equivariant
one-owner-per-player schedule. -/
def QuittingCyclicSingletonEqualHazardCriterion
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ) : Prop :=
  cyclicSingletonBalancePolynomial gamma survival = 0 ∧
    ∀ offset, 0 ≤ cyclicSingletonTail gamma survival offset

/-- Existence of the canonical equivariant tail input at a prescribed
survival factor.  This is the exact finite input consumed by
`CyclicSingletonTailData.certificate`. -/
def HasQuittingCanonicalEqualHazardTailData
    (reward : {S : Finset (Fin (extra + 2)) // S.Nonempty} →
      Payoff (Fin (extra + 2)))
    (gamma : Fin (extra + 2) → ℝ) (survival : ℝ) : Prop :=
  ∃ data : CyclicSingletonTailData reward,
    data.survival = survival ∧
      data.tail = cyclicSingletonTail gamma survival

/-- **Raw equal-hazard criterion.**  For a cyclic normalized singleton
matrix and `0 < survival < 1`, the canonical equivariant tail input exists
if and only if the balance polynomial vanishes and every closed tail is
nonnegative. -/
theorem hasQuittingCanonicalEqualHazardTailData_iff
    {reward : {S : Finset (Fin (extra + 2)) // S.Nonempty} →
      Payoff (Fin (extra + 2))}
    {gamma : Fin (extra + 2) → ℝ} {survival : ℝ}
    (hcyclic : IsQuittingCyclicSingletonMatrix reward gamma)
    (hgammaZero : gamma 0 = 0) (hsurvivalZero : 0 < survival)
    (hsurvivalOne : survival < 1) :
    HasQuittingCanonicalEqualHazardTailData reward gamma survival ↔
      QuittingCyclicSingletonEqualHazardCriterion gamma survival := by
  constructor
  · rintro ⟨data, hdataSurvival, hdataTail⟩
    have hrecurrence := data.recurrence (0 : Fin (extra + 2)) (0 : Fin (extra + 2))
    rw [hdataTail, hdataSurvival, hcyclic, sub_self, hgammaZero,
      cyclicSingletonTail_zero] at hrecurrence
    have hrotate : finRotate (extra + 2) (0 : Fin (extra + 2)) =
        ⟨1, by omega⟩ := by
      apply Fin.ext
      norm_num [finRotate_apply]
    simp only [sub_zero] at hrecurrence
    rw [hrotate, cyclicSingletonTail_one_eq_balancePolynomial] at hrecurrence
    simp only [zero_add] at hrecurrence
    refine ⟨?_, ?_⟩
    · exact (mul_eq_zero.mp hrecurrence.symm).resolve_left hsurvivalZero.ne'
    · intro offset
      rw [← hdataTail]
      exact data.tail_nonneg offset
  · rintro ⟨hbalance, htailNonneg⟩
    let data : CyclicSingletonTailData reward := {
      survival := survival
      tail := cyclicSingletonTail gamma survival
      survival_pos := hsurvivalZero
      survival_lt_one := hsurvivalOne
      tail_zero := cyclicSingletonTail_zero gamma survival
      tail_nonneg := htailNonneg
      recurrence := by
        intro phase who
        rw [hcyclic, finRotate_sub_eq_finRotate_sub]
        exact cyclicSingletonTail_recurrence gamma survival hgammaZero hbalance
          (phase - who)
    }
    exact ⟨data, rfl, rfl⟩

/-- Open-sign input class for the cyclic singleton producer. -/
structure QuittingCyclicSingletonOpenSignData
    (reward : {S : Finset (Fin (extra + 2)) // S.Nonempty} →
      Payoff (Fin (extra + 2))) where
  gamma : Fin (extra + 2) → ℝ
  cyclic : IsQuittingCyclicSingletonMatrix reward gamma
  gamma_zero : gamma 0 = 0
  first_neg : gamma ⟨1, by omega⟩ < 0
  later_nonneg : ∀ index : Fin (extra + 2), 2 ≤ index.val → 0 ≤ gamma index
  total_pos : 0 < ∑ index : Fin (extra + 1),
    cyclicSingletonPowerCoefficient gamma index

namespace QuittingCyclicSingletonOpenSignData

variable {reward : {S : Finset (Fin (extra + 2)) // S.Nonempty} →
  Payoff (Fin (extra + 2))}

/-- The balance polynomial has a root strictly between zero and one. -/
theorem exists_balance_root (data : QuittingCyclicSingletonOpenSignData reward) :
    ∃ survival ∈ Set.Ioo (0 : ℝ) 1,
      cyclicSingletonBalancePolynomial data.gamma survival = 0 := by
  exact Math.exists_finitePowerSum_root_mem_Ioo
    (cyclicSingletonPowerCoefficient data.gamma) data.first_neg data.total_pos

private theorem powerCoefficient_nonneg_of_ne_zero
    (data : QuittingCyclicSingletonOpenSignData reward)
    (index : Fin (extra + 1)) (hindex : index ≠ 0) :
    0 ≤ cyclicSingletonPowerCoefficient data.gamma index := by
  apply data.later_nonneg
  change 2 ≤ index.val + 1
  have hval : index.val ≠ 0 := by
    intro hzero
    apply hindex
    exact Fin.ext hzero
  omega

private theorem exists_positive_powerCoefficient
    (data : QuittingCyclicSingletonOpenSignData reward) :
    ∃ index : Fin (extra + 1), index ≠ 0 ∧
      0 < cyclicSingletonPowerCoefficient data.gamma index := by
  let coefficient := cyclicSingletonPowerCoefficient data.gamma
  have hzero : coefficient 0 < 0 := data.first_neg
  have hsumErase : 0 < ∑ index ∈ (Finset.univ.erase 0), coefficient index := by
    have hsplit := Finset.sum_erase_add (s := Finset.univ)
      (f := coefficient) (Finset.mem_univ (0 : Fin (extra + 1)))
    have htotal := data.total_pos
    change 0 < ∑ index, coefficient index at htotal
    rw [← hsplit] at htotal
    linarith
  have hnonneg : ∀ index ∈ (Finset.univ.erase 0), 0 ≤ coefficient index := by
    intro index hindex
    exact data.powerCoefficient_nonneg_of_ne_zero index
      (Finset.ne_of_mem_erase hindex)
  rw [Finset.sum_pos_iff_of_nonneg hnonneg] at hsumErase
  obtain ⟨index, hindex, hpositive⟩ := hsumErase
  exact ⟨index, Finset.ne_of_mem_erase hindex, hpositive⟩

/-- Under the open-sign hypotheses, the balance polynomial is strictly
increasing on the positive half-line.  Thus the root used by the cyclic
producer is intrinsic rather than an artifact of classical choice. -/
theorem strictMonoOn_balancePolynomial_pos
    (data : QuittingCyclicSingletonOpenSignData reward) :
    StrictMonoOn (cyclicSingletonBalancePolynomial data.gamma)
      (Set.Ioi (0 : ℝ)) := by
  intro first hfirst second hsecond hlt
  unfold cyclicSingletonBalancePolynomial Math.finitePowerSum
  apply Finset.sum_lt_sum
  · intro index _
    by_cases hindex : index = 0
    · subst index
      simp
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hfirst.le hlt.le index.val)
        (data.powerCoefficient_nonneg_of_ne_zero index hindex)
  · obtain ⟨index, hindex, hcoefficient⟩ :=
      data.exists_positive_powerCoefficient
    refine ⟨index, Finset.mem_univ index, ?_⟩
    exact mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hlt hfirst.le (by
        intro hzero
        apply hindex
        exact Fin.ext hzero)) hcoefficient

/-- The open-sign balance equation has exactly one root in `(0,1)`. -/
theorem existsUnique_balance_root
    (data : QuittingCyclicSingletonOpenSignData reward) :
    ∃! survival : ℝ, survival ∈ Set.Ioo (0 : ℝ) 1 ∧
      cyclicSingletonBalancePolynomial data.gamma survival = 0 := by
  obtain ⟨survival, hsurvival, hroot⟩ := data.exists_balance_root
  refine ⟨survival, ⟨hsurvival, hroot⟩, ?_⟩
  intro other hother
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := data.strictMonoOn_balancePolynomial_pos
      hother.1.1 hsurvival.1 hlt
    rw [hroot, hother.2] at this
    exact (lt_irrefl 0 this).elim
  · have := data.strictMonoOn_balancePolynomial_pos
      hsurvival.1 hother.1.1 hgt
    rw [hroot, hother.2] at this
    exact (lt_irrefl 0 this).elim

private theorem tail_nonneg_at_root
    (data : QuittingCyclicSingletonOpenSignData reward)
    {survival : ℝ} (hsurvival : 0 ≤ survival)
    (hroot : cyclicSingletonBalancePolynomial data.gamma survival = 0)
    (offset : Fin (extra + 2)) :
    0 ≤ cyclicSingletonTail data.gamma survival offset := by
  by_cases hoffsetZero : offset.val = 0
  · rw [cyclicSingletonTail, if_pos hoffsetZero]
  by_cases hoffsetOne : offset.val = 1
  · have hoffset : offset = ⟨1, by omega⟩ := Fin.ext hoffsetOne
    rw [hoffset]
    rw [cyclicSingletonTail_one_eq_balancePolynomial, hroot]
  · rw [cyclicSingletonTail, if_neg hoffsetZero]
    apply Finset.sum_nonneg
    intro index hindex
    apply mul_nonneg
    · have hindexLt : offset.val + index < extra + 2 := by
        have hrange := Finset.mem_range.mp hindex
        omega
      rw [cyclicSingletonGammaNat, dif_pos hindexLt]
      apply data.later_nonneg
      change 2 ≤ offset.val + index
      omega
    · positivity

/-- If the last forward envy is positive, every tail beginning at offset at
least two is strictly positive.  This sharpens the nonnegativity used by the
open-sign producer and does not require the balance equation. -/
theorem tail_pos_of_two_le_of_last_pos
    (data : QuittingCyclicSingletonOpenSignData reward)
    {survival : ℝ} (hsurvival : 0 < survival)
    (hlast : 0 < data.gamma ⟨extra + 1, by omega⟩)
    (offset : Fin (extra + 2)) (hoffset : 2 ≤ offset.val) :
    0 < cyclicSingletonTail data.gamma survival offset := by
  have hoffsetZero : offset.val ≠ 0 := by omega
  rw [cyclicSingletonTail, if_neg hoffsetZero]
  have hnonneg : ∀ index ∈ Finset.range (extra + 2 - offset.val),
      0 ≤ cyclicSingletonGammaNat data.gamma (offset.val + index) *
        survival ^ index := by
    intro index hindex
    apply mul_nonneg
    · have hindexLt : offset.val + index < extra + 2 := by
        have hrange := Finset.mem_range.mp hindex
        omega
      rw [cyclicSingletonGammaNat, dif_pos hindexLt]
      apply data.later_nonneg
      change 2 ≤ offset.val + index
      omega
    · positivity
  unfold finiteCyclicSingletonTail
  rw [Finset.sum_pos_iff_of_nonneg hnonneg]
  let lastOffset := extra + 2 - offset.val - 1
  have hlength : 0 < extra + 2 - offset.val := Nat.sub_pos_of_lt offset.isLt
  have hlastOffset : lastOffset < extra + 2 - offset.val := by
    dsimp [lastOffset]
    omega
  refine ⟨lastOffset, Finset.mem_range.mpr hlastOffset, ?_⟩
  have hsum : offset.val + lastOffset = extra + 1 := by
    dsimp [lastOffset]
    omega
  have hindexLt : offset.val + lastOffset < extra + 2 := by omega
  rw [cyclicSingletonGammaNat, dif_pos hindexLt]
  have hfin : (⟨offset.val + lastOffset, hindexLt⟩ : Fin (extra + 2)) =
      ⟨extra + 1, by omega⟩ := by
    apply Fin.ext
    exact hsum
  rw [hfin]
  exact mul_pos hlast (pow_pos hsurvival _)

/-- At a balanced open-sign root with positive last envy, the canonical tail
vanishes at exactly offsets zero and one. -/
theorem tail_eq_zero_iff_offset_zero_or_one
    (data : QuittingCyclicSingletonOpenSignData reward)
    {survival : ℝ} (hsurvival : 0 < survival)
    (hroot : cyclicSingletonBalancePolynomial data.gamma survival = 0)
    (hlast : 0 < data.gamma ⟨extra + 1, by omega⟩)
    (offset : Fin (extra + 2)) :
    cyclicSingletonTail data.gamma survival offset = 0 ↔
      offset.val = 0 ∨ offset.val = 1 := by
  constructor
  · intro hzero
    by_contra hnot
    simp only [not_or] at hnot
    have htwo : 2 ≤ offset.val := by omega
    have hpositive := data.tail_pos_of_two_le_of_last_pos
      hsurvival hlast offset htwo
    linarith
  · rintro (hzero | hone)
    · have hoffset : offset = 0 := Fin.ext hzero
      subst offset
      exact cyclicSingletonTail_zero data.gamma survival
    · have hoffset : offset = ⟨1, by omega⟩ := Fin.ext hone
      rw [hoffset]
      exact cyclicSingletonTail_one_eq_balancePolynomial data.gamma survival |>.trans hroot

/-- With positive last envy, the canonical cyclic continuation equals a
player's solo level at exactly the owner's phase and the immediately following
relative offset. -/
theorem coarse_eq_solo_iff_relativeOffset_zero_or_one
    (data : QuittingCyclicSingletonOpenSignData reward)
    {survival : ℝ} (hsurvival : 0 < survival)
    (hsurvivalOne : survival < 1)
    (hroot : cyclicSingletonBalancePolynomial data.gamma survival = 0)
    (hlast : 0 < data.gamma ⟨extra + 1, by omega⟩)
    (phase who : Fin (extra + 2)) :
    quittingSoloReward reward who who + (1 - survival) *
        cyclicSingletonTail data.gamma survival (phase - who) =
        quittingSoloReward reward who who ↔
      (phase - who).val = 0 ∨ (phase - who).val = 1 := by
  constructor
  · intro heq
    have hmul : (1 - survival) *
        cyclicSingletonTail data.gamma survival (phase - who) = 0 := by
      linarith
    have htail := (mul_eq_zero.mp hmul).resolve_left (by
      linarith [hsurvivalOne])
    exact (data.tail_eq_zero_iff_offset_zero_or_one
      hsurvival hroot hlast (phase - who)).mp htail
  · intro hoffset
    have htail := (data.tail_eq_zero_iff_offset_zero_or_one
      hsurvival hroot hlast (phase - who)).mpr hoffset
    rw [htail, mul_zero, add_zero]

/-- Root-selected cyclic tail data for the raw reward table. -/
def tailData (data : QuittingCyclicSingletonOpenSignData reward) :
    CyclicSingletonTailData reward := by
  let survival := data.exists_balance_root.choose
  have hsurvival := data.exists_balance_root.choose_spec
  exact {
    survival := survival
    tail := cyclicSingletonTail data.gamma survival
    survival_pos := hsurvival.1.1
    survival_lt_one := hsurvival.1.2
    tail_zero := cyclicSingletonTail_zero data.gamma survival
    tail_nonneg := data.tail_nonneg_at_root hsurvival.1.1.le hsurvival.2
    recurrence := by
      intro phase who
      rw [data.cyclic]
      rw [finRotate_sub_eq_finRotate_sub]
      exact cyclicSingletonTail_recurrence data.gamma survival data.gamma_zero
        hsurvival.2 (phase - who)
  }

/-- Direct unrestricted-behavior uniform-equilibrium consumer for the open
cyclic singleton class. -/
theorem isUniformEquilibriumPayoff
    (data : QuittingCyclicSingletonOpenSignData reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (data.tailData.coarse 0) :=
  data.tailData.isUniformEquilibriumPayoff (by omega)

end QuittingCyclicSingletonOpenSignData

end GameTheory
