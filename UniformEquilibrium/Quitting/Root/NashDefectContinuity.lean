/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction.Simplex
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Root.NashDefect

/-!
# Continuity of one-stage quitting-root absorption and Nash defects

Root absorption is continuous in the product-root simplex. The coordinatewise
and total root defects are continuous jointly in the tail
payoff and finite product-root simplex. This production interface is
independent of terminal-semantic diagnostics.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Root absorption is continuous in simplex coordinates. -/
theorem continuous_quittingRootAbsorptionMass_simplex :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootAbsorptionMass (quittingRootOfSimplex root)) := by
  simp_rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_const.sub
    (continuous_finsetProd _ fun who _ =>
      (continuous_apply false).comp
        (continuous_subtype_val.comp (continuous_apply who)))

/-- One-coordinate Nash defect is jointly continuous in the tail and root. -/
theorem continuous_quittingRootCoordinateNashDefect_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootCoordinateNashDefect reward point.1
        (quittingRootOfSimplex point.2) who) := by
  unfold quittingRootCoordinateNashDefect
  exact ((continuous_quittingRootQuitPayoff_simplex reward who).max
      (continuous_quittingRootContinuePayoff_simplex reward who)).sub
    ((continuous_apply who).comp
      (continuous_quittingRootSuccessorPayoff_simplex reward))

/-- Total Nash defect is jointly continuous in the tail and root. -/
theorem continuous_quittingRootTotalNashDefect_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootTotalNashDefect reward point.1
        (quittingRootOfSimplex point.2)) := by
  unfold quittingRootTotalNashDefect
  exact continuous_finsetSum _ fun who _ =>
    continuous_quittingRootCoordinateNashDefect_simplex reward who

/-- One-coordinate Nash defect is continuous in the tail for a fixed root. -/
theorem continuous_quittingRootCoordinateNashDefect_fixedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    Continuous (fun tail : Payoff ι =>
      quittingRootCoordinateNashDefect reward tail root who) := by
  let simplexRoot : QuittingRootSimplex ι :=
    fun player => stdSimplexEquiv (root player)
  have hroot : quittingRootOfSimplex simplexRoot = root := by
    funext player
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root player)
  have hmap : Continuous (fun tail : Payoff ι => (tail, simplexRoot)) :=
    continuous_id.prodMk continuous_const
  have hcontinuous :=
    (continuous_quittingRootCoordinateNashDefect_simplex reward who).comp hmap
  change Continuous (fun tail : Payoff ι =>
    quittingRootCoordinateNashDefect reward tail
      (quittingRootOfSimplex simplexRoot) who) at hcontinuous
  rw [hroot] at hcontinuous
  exact hcontinuous

/-- Total Nash defect is continuous in the tail for a fixed product root. -/
theorem continuous_quittingRootTotalNashDefect_fixedRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) :
    Continuous (fun tail : Payoff ι =>
      quittingRootTotalNashDefect reward tail root) := by
  unfold quittingRootTotalNashDefect
  exact continuous_finsetSum _ fun who _ =>
    continuous_quittingRootCoordinateNashDefect_fixedRoot reward root who

end GameTheory
