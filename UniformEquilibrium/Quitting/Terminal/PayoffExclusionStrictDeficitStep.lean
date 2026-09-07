import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDefectBudget

/-! # Auxiliary-prefix contraction from a strict singleton deficit -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One exact auxiliary-Nash prefix step under the strict singleton-deficit
witness. The output is the literal semantic prefix of the supplied pair. -/
theorem strictDeficit_exactAuxiliaryPrefix_absorption_and_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdeficit : pair.1 who ≤
      reward (quittingSingletonTerminal who) who - gap)
    (hnash : IsεQuittingRootNash reward
      (pair.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair -
          min (quittingTerminalSemanticDebtSum pair) (gap / 2)) 0 root) :
    gap / (4 * M + gap) ≤ quittingRootAbsorptionMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        quittingTerminalSemanticDebtSum pair -
          gap / (4 * M + gap) *
            min (quittingTerminalSemanticDebtSum pair) (gap / 2) := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := min total (gap / 2)
  let shift := total - paid
  let auxiliary : Payoff ι := pair.2 - fun _ => shift
  have hdebtNonneg : ∀ player, 0 ≤ quittingTerminalSemanticDebt pair player :=
    fun player => quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair player
  have htotalNonneg : 0 ≤ total := by
    unfold total quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ => hdebtNonneg player
  have hcoordinateLe : quittingTerminalSemanticDebt pair who ≤ total := by
    unfold total quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum (fun player _ => hdebtNonneg player)
      (Finset.mem_univ who)
  have hpaidLeTotal : paid ≤ total := min_le_left _ _
  have hshiftNonneg : 0 ≤ shift := sub_nonneg.mpr hpaidLeTotal
  have hpaidLeHalf : paid ≤ gap / 2 := min_le_right _ _
  have hauxiliaryGap : auxiliary who ≤
      reward (quittingSingletonTerminal who) who - gap / 2 := by
    change pair.2 who - shift ≤
      reward (quittingSingletonTerminal who) who - gap / 2
    dsimp only [shift, paid]
    dsimp only [quittingTerminalSemanticDebt] at hcoordinateLe
    linarith
  have habsorption := belowSingleton_exactRoot_absorptionMass_lowerBound
    reward auxiliary root who (by positivity : 0 < gap / 2) hreward
      hauxiliaryGap hnash
  have habsorption' : gap / (4 * M + gap) ≤
      quittingRootAbsorptionMass root := by
    convert habsorption using 1
    field_simp
    ring
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair shift root hshiftNonneg
  have hzero :=
    (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward auxiliary root).mp hnash
  have hcoefficient : 0 ≤ paid := le_min htotalNonneg (by linarith)
  have hspend : gap / (4 * M + gap) * paid ≤
      quittingRootAbsorptionMass root * paid :=
    mul_le_mul_of_nonneg_right habsorption' hcoefficient
  dsimp only [auxiliary] at hzero
  dsimp only [shift, paid, total] at hbudget ⊢
  rw [hzero, add_zero] at hbudget
  constructor
  · exact habsorption'
  · linarith

/-- The same strict-deficit step with explicit coordinate and total root
defect budgets. This is the interface consumed by rational root selection. -/
theorem strictDeficit_approximateAuxiliaryPrefix_absorption_and_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (who : ι) {M gap : ℝ} (hgap : 0 < gap)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdeficit : pair.1 who ≤
      reward (quittingSingletonTerminal who) who - gap)
    (hcoordinate :
      quittingRootCoordinateNashDefect reward
        (pair.2 - fun _ =>
          quittingTerminalSemanticDebtSum pair -
            min (quittingTerminalSemanticDebtSum pair) (gap / 2)) root who ≤
        gap / 8)
    (htotal : quittingRootTotalNashDefect reward
      (pair.2 - fun _ =>
        quittingTerminalSemanticDebtSum pair -
          min (quittingTerminalSemanticDebtSum pair) (gap / 2)) root ≤
      gap / (4 * M + gap) *
        min (quittingTerminalSemanticDebtSum pair) (gap / 2) / 4) :
    gap / (2 * (4 * M + gap)) ≤ quittingRootAbsorptionMass root ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPrefix reward root pair) ≤
        quittingTerminalSemanticDebtSum pair -
          gap / (4 * (4 * M + gap)) *
            min (quittingTerminalSemanticDebtSum pair) (gap / 2) := by
  let total := quittingTerminalSemanticDebtSum pair
  let paid := min total (gap / 2)
  let shift := total - paid
  let auxiliary : Payoff ι := pair.2 - fun _ => shift
  have hdebtNonneg : ∀ player, 0 ≤ quittingTerminalSemanticDebt pair player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair
  have htotalNonneg : 0 ≤ total := by
    unfold total quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ => hdebtNonneg player
  have hcoordinateLe : quittingTerminalSemanticDebt pair who ≤ total := by
    unfold total quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum (fun player _ => hdebtNonneg player)
      (Finset.mem_univ who)
  have hpaidLeTotal : paid ≤ total := min_le_left _ _
  have hshiftNonneg : 0 ≤ shift := sub_nonneg.mpr hpaidLeTotal
  have hpaidLeHalf : paid ≤ gap / 2 := min_le_right _ _
  have hpaidNonneg : 0 ≤ paid := le_min htotalNonneg (by linarith)
  have hauxiliaryGap : auxiliary who ≤
      reward (quittingSingletonTerminal who) who - gap / 2 := by
    change pair.2 who - shift ≤
      reward (quittingSingletonTerminal who) who - gap / 2
    dsimp only [shift, paid]
    dsimp only [quittingTerminalSemanticDebt] at hcoordinateLe
    linarith
  have hcoordinateWho :
      quittingRootCoordinateNashDefect reward auxiliary root who ≤
        (gap / 2) / 4 := by
    have h := hcoordinate
    change quittingRootCoordinateNashDefect reward auxiliary root who ≤ gap / 8 at h
    convert h using 1
    ring
  have habsorption := belowSingleton_approximateRoot_absorptionMass_lowerBound
    reward auxiliary root who (by positivity : 0 < gap / 2) hreward
      hauxiliaryGap hcoordinateWho
  have habsorption' : gap / (2 * (4 * M + gap)) ≤
      quittingRootAbsorptionMass root := by
    convert habsorption using 1
    field_simp
    ring
  have hbudget := quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (reward := reward) pair shift root hshiftNonneg
  have htotal' : quittingRootTotalNashDefect reward auxiliary root ≤
      gap / (4 * M + gap) * paid / 4 := by
    simpa [auxiliary, shift, paid, total] using htotal
  have hspend : gap / (2 * (4 * M + gap)) * paid ≤
      quittingRootAbsorptionMass root * paid :=
    mul_le_mul_of_nonneg_right habsorption' hpaidNonneg
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hdenom : 4 * M + gap ≠ 0 := by positivity
  have hcoefficient :
      gap / (2 * (4 * M + gap)) * paid -
          gap / (4 * M + gap) * paid / 4 =
        gap / (4 * (4 * M + gap)) * paid := by
    field_simp [hdenom]
    ring
  dsimp only [shift, paid, total] at hbudget ⊢
  constructor
  · exact habsorption'
  · dsimp only [auxiliary] at htotal'
    linarith

end GameTheory
