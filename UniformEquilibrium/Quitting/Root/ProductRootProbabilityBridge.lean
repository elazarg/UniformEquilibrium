/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallHazardBounds
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Product-root probability bridges

This module identifies the quitting-root masses with the low-level Bernoulli
product expressions owned by `MathUE.PMFProduct`.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Every quit-rate vector belongs to the real unit box. -/
theorem quittingRootQuitRates_mem_unitBox (root : ι → PMF Bool) :
    (fun player => (root player true).toReal) ∈
      Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1 := by
  intro player _
  exact ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_mono ENNReal.one_ne_top
      ((root player).coe_le_one true)⟩

omit [DecidableEq ι] in
/-- Root absorption is the Bernoulli family's non-continuation mass. -/
theorem quittingRootAbsorptionMass_eq_one_sub_continueMass
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      1 - Math.PMFProduct.continueMass
        (fun player => (root player true).toReal) := by
  simp only [Math.PMFProduct.continueMass, quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  exact congrArg (fun total => 1 - total)
    (Finset.prod_congr rfl fun player _ =>
      Math.PMFProduct.pmfBool_false_toReal (root player))

omit [DecidableEq ι] in
/-- A quitting root absorbs with probability at most one. -/
theorem quittingRootAbsorptionMass_le_one (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root ≤ 1 := by
  have := quittingStationaryContinueMass_nonneg root
  unfold quittingRootAbsorptionMass
  linarith

/-- Exact coalition mass agrees with the low-level Bernoulli product mass. -/
theorem quittingRootCoalitionMass_eq_pmfProductCoalitionMass
    (root : ι → PMF Bool) (coalition : Finset ι) :
    quittingRootCoalitionMass root coalition =
      Math.PMFProduct.coalitionMass
        (fun player => (root player true).toReal) coalition := rfl

/-- Total exact-singleton mass agrees with the low-level singleton mass. -/
theorem sum_quittingRootSingletonMass_eq_pmfProductSingletonMass
    (root : ι → PMF Bool) :
    (∑ player, quittingRootCoalitionMass root {player}) =
      Math.PMFProduct.singletonMass
        (fun player => (root player true).toReal) := by
  unfold Math.PMFProduct.singletonMass
  exact Finset.sum_congr rfl fun player _ => rfl

end GameTheory
