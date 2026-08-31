/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.ProductCoalitionSupportCard
import UniformEquilibrium.Diagnostics.Quitting.TwoSureProductRootTailScreen

/-!
# Support consequences of a two-sure product law

This file records literal support statements for the complete terminal law,
including the cardinality alternatives for a four-player product root.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive exact coalitions of a product quitting root. -/
def quittingProductRootCoalitionSupport
    (root : ι → PMF Bool) : Finset (Finset ι) :=
  productCoalitionSupport (quittingRootQuitRates root)

/-- In a four-player product root with two distinct sure quitters, the
positive exact-coalition support has cardinality `1`, `2`, or `4`. -/
theorem quittingProductRootCoalitionSupport_card_eq_one_or_two_or_four
    (root : Fin 4 → PMF Bool) {first second : Fin 4} (hne : first ≠ second)
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1) :
    (quittingProductRootCoalitionSupport root).card = 1 ∨
      (quittingProductRootCoalitionSupport root).card = 2 ∨
      (quittingProductRootCoalitionSupport root).card = 4 := by
  let flexible := productCoalitionFlexibleCoordinates
    (quittingRootQuitRates root)
  have hfirstNot : first ∉ flexible := by
    simp only [flexible, productCoalitionFlexibleCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and, quittingRootQuitRates]
    intro h
    exact h.2 (by rw [hfirst]; norm_num)
  have hsecondNot : second ∉ flexible := by
    simp only [flexible, productCoalitionFlexibleCoordinates,
      Finset.mem_filter, Finset.mem_univ, true_and, quittingRootQuitRates]
    intro h
    exact h.2 (by rw [hsecond]; norm_num)
  have hcardFlexible : flexible.card ≤ 2 := by
    have hpairSubset : ({first, second} : Finset (Fin 4)) ⊆ flexibleᶜ := by
      intro who hwho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
      rw [Finset.mem_compl]
      rcases hwho with rfl | rfl
      · exact hfirstNot
      · exact hsecondNot
    have hpairCard : ({first, second} : Finset (Fin 4)).card = 2 := by
      simp [hne]
    have hcomplementCard : 2 ≤ flexibleᶜ.card := by
      rw [← hpairCard]
      exact Finset.card_le_card hpairSubset
    rw [Finset.card_compl, Fintype.card_fin] at hcomplementCard
    omega
  have hsupportCard : (quittingProductRootCoalitionSupport root).card =
      2 ^ flexible.card := by
    exact card_productCoalitionSupport (quittingRootQuitRates root)
  rw [hsupportCard]
  interval_cases hflex : flexible.card <;> norm_num

/-- A coalition omitting a sure quitter has zero product-root mass. -/
theorem quittingRootCoalitionMass_eq_zero_of_sureQuitter_not_mem
    (root : ι → PMF Bool) {quitter : ι}
    (hsure : (root quitter true).toReal = 1)
    (coalition : Finset ι) (hnot : quitter ∉ coalition) :
    quittingRootCoalitionMass root coalition = 0 := by
  have hle := quittingRootCoalitionMass_le_continueProbability_of_not_mem
    root coalition quitter hnot
  have hnonneg := quittingRootCoalitionMass_nonneg root coalition
  rw [Math.PMFProduct.pmfBool_false_toReal, hsure] at hle
  norm_num at hle
  exact le_antisymm hle hnonneg

/-- Every positive coalition in a terminal law realized by a two-sure product
root contains both fixed sure quitters. -/
theorem terminalLaw_supportedCoalition_contains_twoSureQuitters
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (root : ι → PMF Bool) {first second : ι}
    (hfirst : (root first true).toReal = 1)
    (hsecond : (root second true).toReal = 1)
    (hlaw : ∀ outcome, quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward root) outcome = mu outcome)
    (terminal : {S : Finset ι // S.Nonempty})
    (hsupported : mu (some terminal) ≠ 0) :
    first ∈ terminal.val ∧ second ∈ terminal.val := by
  have hrootLaw : quittingRootCoalitionMass root terminal.val =
      mu (some terminal) := by
    rw [← hlaw]
    exact (productRoot_terminalOutcomeMass_oneDateThenNever_some
      reward root hfirst terminal).symm
  constructor
  · by_contra hnot
    rw [quittingRootCoalitionMass_eq_zero_of_sureQuitter_not_mem
      root hfirst terminal.val hnot] at hrootLaw
    exact hsupported hrootLaw.symm
  · by_contra hnot
    rw [quittingRootCoalitionMass_eq_zero_of_sureQuitter_not_mem
      root hsecond terminal.val hnot] at hrootLaw
    exact hsupported hrootLaw.symm

end GameTheory
