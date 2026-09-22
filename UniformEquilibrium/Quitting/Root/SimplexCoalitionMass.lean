/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Root.Simplex

/-!
# Continuity of root coalition mass in simplex coordinates

Exact coalition mass and total opponent incidence are finite polynomials in a
product root's Boolean simplex coordinates.  Their continuity belongs beside
the low root/simplex conversion rather than in a diagnostic moat module.
-/

noncomputable section

namespace GameTheory

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One-stage absorption, written polynomially in simplex coordinates. -/
def quittingSimplexAbsorptionMass (root : QuittingRootSimplex ι) : ℝ :=
  1 - ∏ who, (root who).weights false

omit [DecidableEq ι] in
/-- Simplex-coordinate absorption agrees with the PMF-root definition. -/
theorem quittingSimplexAbsorptionMass_eq_rootAbsorptionMass
    (root : QuittingRootSimplex ι) :
    quittingSimplexAbsorptionMass root =
      quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
  classical
  unfold quittingSimplexAbsorptionMass quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp

omit [DecidableEq ι] in
/-- Simplex-coordinate absorption is continuous. -/
theorem continuous_quittingSimplexAbsorptionMass :
    Continuous (quittingSimplexAbsorptionMass :
      QuittingRootSimplex ι → ℝ) := by
  classical
  unfold quittingSimplexAbsorptionMass
  exact continuous_const.sub
    (continuous_finsetProd (s := (Finset.univ : Finset ι)) fun who _ =>
      (Convexity.StdSimplex.continuous_weights_apply ℝ false).comp
        (continuous_apply who))

/-- Root coalition mass is continuous in simplex coordinates. -/
theorem continuous_quittingRootCoalitionMass_simplex
    (coalition : Finset ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootCoalitionMass (quittingRootOfSimplex root) coalition) := by
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  apply (continuous_finsetProd _ fun player _ => ?_).mul
    (continuous_finsetProd _ fun player _ => ?_)
  · simp only [quittingRootOfSimplex_apply_toReal]
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ true).comp
      (continuous_apply player)
  · simp only [quittingRootOfSimplex_apply_toReal]
    exact continuous_const.sub
      ((Convexity.StdSimplex.continuous_weights_apply ℝ true).comp
        (continuous_apply player))

/-- Total opponent incidence of a root is continuous in simplex coordinates. -/
theorem continuous_quittingRootTotalOpponentIncidenceMass_simplex
    (owner : ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootTotalOpponentIncidenceMass owner
        (quittingRootOfSimplex root)) := by
  unfold quittingRootTotalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun terminal _ =>
      continuous_quittingRootCoalitionMass_simplex terminal.val

end GameTheory
