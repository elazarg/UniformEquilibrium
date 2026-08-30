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

/-- Sum of all displayed opponent-incidence coordinates for one owner.
A coalition containing several opponents is counted once for each such
opponent. -/
def quittingRootTotalOpponentIncidenceMass
    (owner : ι) (root : ι → PMF Bool) : ℝ :=
  ∑ other ∈ Finset.univ.erase owner,
    quittingRootOpponentIncidenceMass owner other root

/-- Total fresh root incidence is nonnegative. -/
theorem quittingRootTotalOpponentIncidenceMass_nonneg
    (owner : ι) (root : ι → PMF Bool) :
    0 ≤ quittingRootTotalOpponentIncidenceMass owner root := by
  unfold quittingRootTotalOpponentIncidenceMass
  exact Finset.sum_nonneg fun other _ =>
    Finset.sum_nonneg fun terminal _ =>
      quittingRootCoalitionMass_nonneg root terminal.val

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

/-- A product root assigns an exact joint action the mass of its quitter
coalition. -/
theorem pmfPi_apply_toReal_eq_quittingRootCoalitionMass_quitters
    (root : ι → PMF Bool) (action : ι → Bool) :
    ((pmfPi root) action).toReal =
      quittingRootCoalitionMass root (quittingQuitters action) := by
  classical
  rw [pmfPi_apply, ENNReal.toReal_prod]
  unfold quittingRootCoalitionMass quittingRootQuitRates coalitionMass
  change (∏ player, (root player (action player)).toReal) =
    (∏ player ∈ quittingQuitters action, (root player true).toReal) *
      ∏ player ∈ Finset.univ \ quittingQuitters action,
        (1 - (root player true).toReal)
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun player ↦ action player = true)]
  congr 1
  · apply Finset.prod_congr
    · ext player
      simp [quittingQuitters]
    · intro player hplayer
      have haction : action player = true := by
        change player ∈ Finset.univ.filter
          (fun owner ↦ action owner = true) at hplayer
        exact (Finset.mem_filter.mp hplayer).2
      rw [haction]
  · apply Finset.prod_congr
    · ext player
      simp [quittingQuitters]
    · intro player hplayer
      have haction : action player ≠ true := by
        intro htrue
        apply (Finset.mem_sdiff.mp hplayer).2
        simp [quittingQuitters, htrue]
      have hfalse : action player = false := by
        cases h : action player <;> simp_all
      rw [hfalse, pmfBool_false_toReal]

/-- A Boolean product root is determined by the masses of all its nonempty
exact quitter coalitions. -/
theorem quittingRoot_eq_of_coalitionMass_eq
    {left right : ι → PMF Bool}
    (hmass : ∀ coalition : {S : Finset ι // S.Nonempty},
      quittingRootCoalitionMass left coalition =
        quittingRootCoalitionMass right coalition) :
    left = right := by
  classical
  have hsum (root : ι → PMF Bool) :
      (∑ coalition : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass root coalition) =
        1 - quittingStationaryContinueMass root := by
    rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))]
    · exact quittingRootCoalitionMass_sum_nonempty root
    · intro coalition
      simp [Finset.nonempty_iff_ne_empty]
  have hcontinue : quittingStationaryContinueMass left =
      quittingStationaryContinueMass right := by
    have hleft := hsum left
    have hright := hsum right
    have heq : (∑ coalition : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass left coalition) =
        ∑ coalition : {S : Finset ι // S.Nonempty},
          quittingRootCoalitionMass right coalition := by
      apply Finset.sum_congr rfl
      intro coalition _
      exact hmass coalition
    linarith
  have hall (coalition : Finset ι) :
      quittingRootCoalitionMass left coalition =
        quittingRootCoalitionMass right coalition := by
    by_cases hcoalition : coalition.Nonempty
    · exact hmass ⟨coalition, hcoalition⟩
    · have hempty : coalition = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcoalition
      subst coalition
      unfold quittingRootCoalitionMass quittingRootQuitRates
      rw [coalitionMass_empty, coalitionMass_empty]
      unfold continueMass
      rw [quittingStationaryContinueMass_eq_prod_continueProbability,
        quittingStationaryContinueMass_eq_prod_continueProbability] at hcontinue
      simpa only [pmfBool_false_toReal] using hcontinue
  funext who
  have hjoint : pmfPi left = pmfPi right := by
    apply PMF.ext
    intro action
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top (pmfPi left) action)
      (PMF.apply_ne_top (pmfPi right) action)).mp
    rw [pmfPi_apply_toReal_eq_quittingRootCoalitionMass_quitters,
      pmfPi_apply_toReal_eq_quittingRootCoalitionMass_quitters]
    exact hall (quittingQuitters action)
  calc
    left who = Math.ProbabilityMassFunction.pushforward
        (pmfPi left) (fun action ↦ action who) :=
      (pmfPi_push_coord left who).symm
    _ = Math.ProbabilityMassFunction.pushforward
        (pmfPi right) (fun action ↦ action who) := by rw [hjoint]
    _ = right who := pmfPi_push_coord right who

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
