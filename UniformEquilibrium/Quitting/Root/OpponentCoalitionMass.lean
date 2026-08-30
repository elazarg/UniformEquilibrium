/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Bool
import MathUE.PMFProduct.CoalitionMass
import UniformEquilibrium.Quitting.Stationary.LiveMass

/-!
# Exact root coalition and opponent-incidence mass

This module owns the elementary exact-coalition coordinates of a product
quitting root.  The full coalition mass records every player's action.  The
opponent-coalition mass omits one distinguished player's action, and the
opponent-incidence mass sums full coalitions carrying a displayed opponent.
These coordinates are reusable independently of any Nash defect, path, or
diagnostic interpretation.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Bernoulli quit-rate family associated with a product root. -/
def quittingRootQuitRates (root : ι → PMF Bool) : ι → ℝ :=
  fun who => (root who true).toReal

/-- Mass of exactly the displayed coalition at one product root. -/
def quittingRootCoalitionMass (root : ι → PMF Bool)
    (coalition : Finset ι) : ℝ :=
  coalitionMass (quittingRootQuitRates root) coalition

/-- Exact product-coalition mass is nonnegative. -/
theorem quittingRootCoalitionMass_nonneg
    (root : ι → PMF Bool) (coalition : Finset ι) :
    0 ≤ quittingRootCoalitionMass root coalition := by
  exact coalitionMass_nonneg (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who => ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one true)) coalition

/-- First-stage mass of coalitions carrying `other`, with `who` retained as a
distinguished label.  For `other = who` the incidence is zero. -/
def quittingRootOpponentIncidenceMass
    (who other : ι) (root : ι → PMF Bool) : ℝ :=
  ∑ terminal ∈ Finset.univ.filter
      (fun terminal : {S : Finset ι // S.Nonempty} =>
        other ∈ terminal.val ∧ other ≠ who),
    quittingRootCoalitionMass root terminal.val

/-- The mass of an exact coalition is bounded by the Quit probability of
every member. -/
theorem quittingRootCoalitionMass_le_quitProbability_of_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked : ι)
    (hmarked : marked ∈ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (root marked true).toReal := by
  apply coalitionMass_le_coordinate_of_mem
      (quittingRootQuitRates root) _ _ hmarked
  · exact fun _ => ENNReal.toReal_nonneg
  · intro who
    exact ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one true)

/-- The mass of an exact coalition is bounded by the Continue probability of
every nonmember. -/
theorem quittingRootCoalitionMass_le_continueProbability_of_not_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked : ι)
    (hmarked : marked ∉ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (root marked false).toReal := by
  have hbound := coalitionMass_le_one_sub_coordinate_of_not_mem
    (quittingRootQuitRates root)
    (fun _ => ENNReal.toReal_nonneg)
    (fun who => ENNReal.toReal_mono ENNReal.one_ne_top
      ((root who).coe_le_one true)) hmarked
  simpa [quittingRootCoalitionMass, quittingRootQuitRates,
    pmfBool_false_toReal] using hbound

/-- The total mass of the nonempty exact coalitions is the one-stage
absorption probability. -/
theorem quittingRootCoalitionMass_sum_nonempty
    (root : ι → PMF Bool) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      quittingRootCoalitionMass root coalition) =
      1 - quittingStationaryContinueMass root := by
  have hcoalition :=
    sum_coalitionMass_nonempty (quittingRootQuitRates root)
  have hcontinue :
      continueMass (quittingRootQuitRates root) =
        quittingStationaryContinueMass root := by
    rw [continueMass, quittingStationaryContinueMass_eq_prod_continueProbability]
    congr 1
    funext who
    change 1 - (root who true).toReal = (root who false).toReal
    exact (pmfBool_false_toReal (root who)).symm
  simpa [quittingRootCoalitionMass, hcontinue] using hcoalition

/-- A positive exact coalition containing `other` contributes its full mass
to the displayed opponent-incidence coordinate. -/
theorem quittingRootCoalitionMass_le_opponentIncidenceMass_of_other_mem
    (root : ι → PMF Bool) (coalition : Finset ι) (marked other : ι)
    (hother : other ∈ coalition)
    (hne : other ≠ marked) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootOpponentIncidenceMass marked other root := by
  let terminal : {S : Finset ι // S.Nonempty} :=
    ⟨coalition, ⟨other, hother⟩⟩
  unfold quittingRootOpponentIncidenceMass
  have hterminal : terminal ∈ Finset.univ.filter
      (fun outcome : {S : Finset ι // S.Nonempty} =>
        other ∈ outcome.val ∧ other ≠ marked) := by
    simp [terminal, hother, hne]
  exact Finset.single_le_sum
    (fun outcome _ => coalitionMass_nonneg
      (quittingRootQuitRates root)
      (fun _ => ENNReal.toReal_nonneg)
      (fun who => ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one true)) outcome.val)
    hterminal

/-- Probability that the opponents' exact Quit coalition is `coalition`.
The intended coalitions are contained in `univ.erase who`. -/
def quittingOpponentCoalitionMass
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) : ℝ :=
  (∏ player ∈ coalition, (root player true).toReal) *
    ∏ player ∈ Finset.univ.erase who \ coalition,
      (root player false).toReal

theorem quittingOpponentCoalitionMass_nonneg
    (root : ι → PMF Bool) (who : ι) (coalition : Finset ι) :
    0 ≤ quittingOpponentCoalitionMass root who coalition := by
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)

end GameTheory
