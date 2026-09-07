import UniformEquilibrium.Quitting.Terminal.AuxiliaryNashDebt
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.Root.TerminalSemanticDebt

/-! # Total debt budget for approximate auxiliary Nash prefixes -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Summing the coordinate ledgers for a common auxiliary shift charges only
the total root defect and the absorbed fraction of that common shift. -/
theorem quittingTerminalSemanticDebtSum_prefix_le_auxiliaryNashDefect
    (pair : QuittingTerminalSemanticPair ι) (h : ℝ)
    (root : ι → PMF Bool) (hh : 0 ≤ h) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) ≤
      quittingTerminalSemanticDebtSum pair -
          quittingRootAbsorptionMass root *
            (quittingTerminalSemanticDebtSum pair - h) +
        quittingRootTotalNashDefect reward (pair.2 - fun _ => h) root := by
  let shift : Payoff ι := fun _ => h
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who ≤
        quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair who +
          quittingRootCoalitionMass root {who} * h +
            quittingRootCoordinateNashDefect reward (pair.2 - shift) root who := by
    intro who
    simpa [shift] using
      quittingTerminalSemanticDebt_prefix_le_auxiliaryNashDefect
        (reward := reward) pair shift root who hh
  have hsum :
      (∑ who, quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root pair) who) ≤
        ∑ who, (quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair who +
          quittingRootCoalitionMass root {who} * h +
            quittingRootCoordinateNashDefect reward (pair.2 - shift) root who) :=
    Finset.sum_le_sum fun who _ => hcoordinate who
  have hsingleton :=
    QuittingFiniteRootWindow.quittingRootAbsorptionMass_eq_sum_singletonMass_add_collisionMass
      root
  have hcollision := quittingRootCollisionMass_nonneg root
  have hsingletonLe : (∑ who, quittingRootCoalitionMass root {who}) ≤
      quittingRootAbsorptionMass root := by linarith
  have hshift : (∑ who, quittingRootCoalitionMass root {who} * h) ≤
      quittingRootAbsorptionMass root * h := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsingletonLe hh
  have hcontinue : quittingStationaryContinueMass root =
      1 - quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    ring
  unfold quittingTerminalSemanticDebtSum at hsum ⊢
  unfold quittingRootTotalNashDefect
  dsimp only [shift] at hsum ⊢
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hcontinue] at hsum
  linarith

end GameTheory
