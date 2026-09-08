import UniformEquilibrium.Quitting.Terminal.GroupExclusionExactPrefixStep

/-! # Approximate auxiliary-prefix debt contraction under group exclusion -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A sufficiently accurate approximate auxiliary root retains one quarter of
the exact group-exclusion debt gain. -/
theorem nonconcentratedWeight_approximateAuxiliaryPrefix_debtDrop
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
    (htotal : quittingRootTotalNashDefect reward
      (pair.2 - fun _ => quittingTerminalSemanticDebtSum pair -
        (1 - beta) * quittingTerminalSemanticDebtSum pair / 2) root ≤
      (1 - beta) ^ 2 * quittingTerminalSemanticDebtSum pair ^ 2 /
        (32 * M + 8 * (1 - beta) * quittingTerminalSemanticDebtSum pair)) :
    (1 - beta) * quittingTerminalSemanticDebtSum pair /
        (8 * M + 2 * (1 - beta) * quittingTerminalSemanticDebtSum pair) ≤
      quittingRootAbsorptionMass root ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) ≤
      quittingTerminalSemanticDebtSum pair -
        (1 - beta) ^ 2 * quittingTerminalSemanticDebtSum pair ^ 2 /
          (32 * M + 8 * (1 - beta) *
            quittingTerminalSemanticDebtSum pair) := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := (1 - beta) * total / 2
  let shift := total - paid
  let auxiliary : Payoff ι := pair.2 - fun _ => shift
  obtain ⟨who, hbelow⟩ :=
    exists_auxiliary_below_singleton_of_nonconcentratedWeight
      reward pair weight hpair hweight hweightSum hweightMax hexclusion
  have hpositiveWeight : ∃ player, 0 < weight player := by
    have hsumNe : (∑ player, weight player) ≠ 0 := by
      rw [hweightSum]
      norm_num
    obtain ⟨player, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumNe
    exact ⟨player, lt_of_le_of_ne (hweight player) (Ne.symm hne)⟩
  have hbetaNonneg : 0 ≤ beta := by
    obtain ⟨player, hplayer⟩ := hpositiveWeight
    exact hplayer.le.trans (hweightMax player)
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hrho : 0 < 1 - beta := by linarith
  have hrhoLeOne : 1 - beta ≤ 1 := by linarith
  have hpaid : 0 < paid := by
    dsimp only [paid, total]
    positivity
  have hpaidLeTotal : paid ≤ total := by
    dsimp only [paid]
    nlinarith
  have hshift : 0 ≤ shift := by
    dsimp only [shift]
    linarith
  have hbelow' : auxiliary who ≤
      reward (quittingSingletonTerminal who) who - paid := by
    simpa [auxiliary, shift, paid, total] using hbelow
  have hdenom : 0 < 2 * M + paid := by positivity
  have haccuracyEq :
      (1 - beta) ^ 2 * total ^ 2 /
          (32 * M + 8 * (1 - beta) * total) =
        paid ^ 2 / (4 * (2 * M + paid)) := by
    have hdenomEq : 32 * M + 8 * (1 - beta) * total =
        16 * (2 * M + paid) := by
      dsimp only [paid]
      ring
    rw [hdenomEq]
    dsimp only [paid]
    field_simp [hdenom.ne']
    ring
  have htotal' : quittingRootTotalNashDefect reward auxiliary root ≤
      paid ^ 2 / (4 * (2 * M + paid)) := by
    simpa [auxiliary, shift, paid, total, haccuracyEq] using htotal
  have hcoordinateLeTotal : quittingRootCoordinateNashDefect
      reward auxiliary root who ≤
        quittingRootTotalNashDefect reward auxiliary root := by
    unfold quittingRootTotalNashDefect
    exact Finset.single_le_sum
      (fun player _ => quittingRootCoordinateNashDefect_nonneg
        reward auxiliary root player) (Finset.mem_univ who)
  have haccuracyLeQuarter : paid ^ 2 / (4 * (2 * M + paid)) ≤ paid / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (2 * M + paid))).2
    nlinarith
  have hcoordinate : quittingRootCoordinateNashDefect
      reward auxiliary root who ≤ paid / 4 :=
    hcoordinateLeTotal.trans (htotal'.trans haccuracyLeQuarter)
  have habsorption := belowSingleton_approximateRoot_absorptionMass_lowerBound
    reward auxiliary root who hpaid hreward hbelow' hcoordinate
  have habsorption' : (1 - beta) * total /
      (8 * M + 2 * (1 - beta) * total) ≤
        quittingRootAbsorptionMass root := by
    have hnumerator : (1 - beta) * total = 2 * paid := by
      dsimp only [paid]
      ring
    have hdenominator : 8 * M + 2 * (1 - beta) * total =
        4 * (2 * M + paid) := by
      dsimp only [paid]
      ring
    rw [hnumerator, hdenominator]
    calc
      2 * paid / (4 * (2 * M + paid)) =
          paid / (2 * (2 * M + paid)) := by
        field_simp [hdenom.ne']
        ring
      _ ≤ _ := habsorption
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair shift root hshift
  have hspend : paid ^ 2 / (2 * (2 * M + paid)) ≤
      quittingRootAbsorptionMass root * paid := by
    have habsorptionPaid := mul_le_mul_of_nonneg_right habsorption hpaid.le
    calc
      paid ^ 2 / (2 * (2 * M + paid)) =
          (paid / (2 * (2 * M + paid))) * paid := by ring
      _ ≤ _ := habsorptionPaid
  have hnet : paid ^ 2 / (4 * (2 * M + paid)) =
      paid ^ 2 / (2 * (2 * M + paid)) -
        paid ^ 2 / (4 * (2 * M + paid)) := by
    field_simp [hdenom.ne']
    ring
  dsimp only [auxiliary] at htotal'
  dsimp only [shift] at hbudget
  constructor
  · simpa only [total] using habsorption'
  · rw [haccuracyEq]
    dsimp only [total] at hbudget ⊢
    rw [hnet]
    linarith

end GameTheory
