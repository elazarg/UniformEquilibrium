import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget

/-! # Auxiliary-prefix debt contraction under nonconcentrated payoff exclusion -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A nonconcentrated exclusion weight yields one below-singleton auxiliary
coordinate. -/
theorem exists_auxiliary_below_singleton_of_nonconcentratedWeight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (weight : ι → ℝ)
    {beta : ℝ} (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightMax : ∀ who, weight who ≤ beta)
    (hexclusion : ∑ who, weight who *
      (pair.1 who - reward (quittingSingletonTerminal who) who) ≤ 0) :
    ∃ who, pair.2 who -
        (quittingTerminalSemanticDebtSum pair -
          (1 - beta) * quittingTerminalSemanticDebtSum pair / 2) ≤
      reward (quittingSingletonTerminal who) who -
        (1 - beta) * quittingTerminalSemanticDebtSum pair / 2 := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := (1 - beta) * total / 2
  have hdebt : ∀ who, 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have hweightedDebt : (∑ who, weight who *
      quittingTerminalSemanticDebt pair who) ≤ beta * total := by
    unfold total quittingTerminalSemanticDebtSum
    calc
      _ ≤ ∑ who, beta * quittingTerminalSemanticDebt pair who :=
        Finset.sum_le_sum fun who _ =>
          mul_le_mul_of_nonneg_right (hweightMax who) (hdebt who)
      _ = _ := by rw [← Finset.mul_sum]
  by_contra hall
  push Not at hall
  have hpoint : ∀ who, -paid <
      pair.1 who - reward (quittingSingletonTerminal who) who +
        quittingTerminalSemanticDebt pair who - (total - paid) := by
    intro who
    dsimp only [quittingTerminalSemanticDebt]
    have h := hall who
    dsimp only [paid, total] at h ⊢
    linarith
  have hsumNe : (∑ who, weight who) ≠ 0 := by rw [hweightSum]; norm_num
  obtain ⟨positive, hpositiveMem, hpositiveNe⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hsumNe
  have hpositive : 0 < weight positive := lt_of_le_of_ne
    (hweight positive) (Ne.symm hpositiveNe)
  have hstrict : (∑ who, weight who * (-paid)) <
      ∑ who, weight who *
        (pair.1 who - reward (quittingSingletonTerminal who) who +
          quittingTerminalSemanticDebt pair who - (total - paid)) := by
    exact Finset.sum_lt_sum (fun who _ =>
      mul_le_mul_of_nonneg_left (hpoint who).le (hweight who))
        ⟨positive, hpositiveMem,
          mul_lt_mul_of_pos_left (hpoint positive) hpositive⟩
  have hupper : (∑ who, weight who *
      (pair.1 who - reward (quittingSingletonTerminal who) who +
        quittingTerminalSemanticDebt pair who - (total - paid))) ≤ -paid := by
    have hidentity : (∑ who, weight who *
        (pair.1 who - reward (quittingSingletonTerminal who) who +
          quittingTerminalSemanticDebt pair who - (total - paid))) =
        (∑ who, weight who *
          (pair.1 who - reward (quittingSingletonTerminal who) who)) +
        (∑ who, weight who * quittingTerminalSemanticDebt pair who) -
          (total - paid) := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, ← Finset.sum_mul, hweightSum, one_mul, one_mul]
    rw [hidentity]
    dsimp only [paid]
    linarith
  have hleft : (∑ who, weight who * (-paid)) = -paid := by
    rw [← Finset.sum_mul, hweightSum, one_mul]
  rw [hleft] at hstrict
  exact (not_lt_of_ge hupper) hstrict

/-- The exact auxiliary root selected under a nonconcentrated exclusion
weight absorbs at the scale of the current total debt. -/
theorem nonconcentratedWeight_exactAuxiliaryPrefix_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (weight : ι → ℝ) {M beta : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hbeta : beta < 1)
    (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightMax : ∀ who, weight who ≤ beta)
    (hexclusion : ∑ who, weight who *
      (pair.1 who - reward (quittingSingletonTerminal who) who) ≤ 0)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun _ => quittingTerminalSemanticDebtSum pair -
        (1 - beta) * quittingTerminalSemanticDebtSum pair / 2) 0 root) :
    (1 - beta) * quittingTerminalSemanticDebtSum pair /
        (4 * M + (1 - beta) * quittingTerminalSemanticDebtSum pair) ≤
      quittingRootAbsorptionMass root := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := (1 - beta) * total / 2
  let auxiliary : Payoff ι := pair.2 - fun _ => total - paid
  have hpaid : 0 < paid := by dsimp only [paid, total]; positivity
  obtain ⟨who, hbelow⟩ :=
    exists_auxiliary_below_singleton_of_nonconcentratedWeight
      reward pair weight hpair hweight hweightSum hweightMax hexclusion
  have hbelow' : auxiliary who ≤
      reward (quittingSingletonTerminal who) who - paid := by
    simpa [auxiliary, paid, total] using hbelow
  have habsorption := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward auxiliary root who hpaid hreward hbelow'
      (by simpa [auxiliary, paid, total] using hnash)
  convert habsorption using 1
  dsimp only [paid, total]
  field_simp
  ring

/-- One exact auxiliary-Nash prefix under a nonconcentrated exclusion
weight has the reciprocal-scale debt drop. -/
theorem nonconcentratedWeight_exactAuxiliaryPrefix_debtDrop
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (weight : ι → ℝ) {M beta : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hpositive : 0 < quittingTerminalSemanticDebtSum pair)
    (hbeta : beta < 1)
    (hweight : ∀ who, 0 ≤ weight who)
    (hweightSum : ∑ who, weight who = 1)
    (hweightMax : ∀ who, weight who ≤ beta)
    (hexclusion : ∑ who, weight who *
      (pair.1 who - reward (quittingSingletonTerminal who) who) ≤ 0)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun _ => quittingTerminalSemanticDebtSum pair -
        (1 - beta) * quittingTerminalSemanticDebtSum pair / 2) 0 root) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) ≤
      quittingTerminalSemanticDebtSum pair -
        (1 - beta) ^ 2 * quittingTerminalSemanticDebtSum pair ^ 2 /
          (8 * M + 2 * (1 - beta) *
            quittingTerminalSemanticDebtSum pair) := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := (1 - beta) * total / 2
  let shift := total - paid
  let auxiliary : Payoff ι := pair.2 - fun _ => shift
  have hpaid : 0 < paid := by dsimp only [paid]; positivity
  obtain ⟨who, hbelow⟩ :=
    exists_auxiliary_below_singleton_of_nonconcentratedWeight
      reward pair weight hpair hweight hweightSum hweightMax hexclusion
  have hbelow' : auxiliary who ≤
      reward (quittingSingletonTerminal who) who - paid := by
    simpa [auxiliary, shift, paid, total] using hbelow
  have habsorption := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward auxiliary root who hpaid hreward hbelow'
      (by simpa [auxiliary, shift, paid, total] using hnash)
  have hshift : 0 ≤ shift := by
    dsimp only [shift, paid]
    have hbetaNonneg : 0 ≤ beta := by
      have hpositiveWeight : ∃ who, 0 < weight who := by
        by_contra hall
        push Not at hall
        have hzero : ∀ who, weight who = 0 := fun who =>
          le_antisymm (hall who) (hweight who)
        simp [hzero] at hweightSum
      obtain ⟨who, hwho⟩ := hpositiveWeight
      exact (hwho.le.trans (hweightMax who))
    dsimp only [total]
    nlinarith
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair shift root hshift
  have hzero :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward auxiliary root).mp
        (by simpa [auxiliary, shift, paid, total] using hnash)
  have hspend : paid ^ 2 / (2 * M + paid) ≤
      quittingRootAbsorptionMass root * paid := by
    calc
      paid ^ 2 / (2 * M + paid) =
          (paid / (2 * M + paid)) * paid := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right habsorption hpaid.le
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hdenom : 0 < 2 * M + paid := by positivity
  have hrewrite : paid ^ 2 / (2 * M + paid) =
      (1 - beta) ^ 2 * total ^ 2 /
        (8 * M + 2 * (1 - beta) * total) := by
    have hdenomEq : 8 * M + 2 * (1 - beta) * total =
        4 * (2 * M + paid) := by dsimp only [paid]; ring
    rw [hdenomEq]
    dsimp only [paid]
    field_simp [ne_of_gt hdenom]
    ring
  dsimp only [auxiliary] at hzero
  rw [hzero, add_zero] at hbudget
  dsimp only [shift] at hbudget
  dsimp only [total] at hrewrite ⊢
  rw [← hrewrite]
  nlinarith

end GameTheory
