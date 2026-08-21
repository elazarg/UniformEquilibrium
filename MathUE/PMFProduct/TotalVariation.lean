/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Update
import MathUE.ProbabilityMassFunction.TotalVariation

/-!
# Total variation for finite product PMFs

Total-variation identities and expectation bounds for changing one
coordinate of an independent finite product.
-/

noncomputable section

namespace Math
namespace PMFProduct

open Probability ProbabilityMassFunction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Updating one factor of an independent finite product preserves exactly
the total-variation distance between the old and new factors. -/
theorem pmfTV_pmfPi_update_eq
    {A : ι → Type*} [∀ index, Fintype (A index)]
    (marginals : ∀ index, PMF (A index)) (coordinate : ι)
    (oldMarginal newMarginal : PMF (A coordinate)) :
    Probability.pmfTV
        (pmfPi (Function.update marginals coordinate oldMarginal))
        (pmfPi (Function.update marginals coordinate newMarginal)) =
      Probability.pmfTV oldMarginal newMarginal := by
  apply le_antisymm
  · rw [pmfPi_update_bind, pmfPi_update_bind]
    exact Probability.pmfTV_bind_le
      (fun value =>
        pmfPi (Function.update marginals coordinate (PMF.pure value)))
      oldMarginal newMarginal
  · have hmap := Probability.pmfTV_map_le
      (fun sample : ∀ index, A index => sample coordinate)
      (pmfPi (Function.update marginals coordinate oldMarginal))
      (pmfPi (Function.update marginals coordinate newMarginal))
    have hold :
        PMF.map (fun sample : ∀ index, A index => sample coordinate)
            (pmfPi (Function.update marginals coordinate oldMarginal)) =
          oldMarginal := by
      change ProbabilityMassFunction.pushforward
          (pmfPi (Function.update marginals coordinate oldMarginal))
          (fun sample : ∀ index, A index => sample coordinate) = oldMarginal
      rw [pmfPi_push_coord]
      simp
    have hnew :
        PMF.map (fun sample : ∀ index, A index => sample coordinate)
            (pmfPi (Function.update marginals coordinate newMarginal)) =
          newMarginal := by
      change ProbabilityMassFunction.pushforward
          (pmfPi (Function.update marginals coordinate newMarginal))
          (fun sample : ∀ index, A index => sample coordinate) = newMarginal
      rw [pmfPi_push_coord]
      simp
    rwa [hold, hnew] at hmap

/-- Replacing finitely many factors of an independent product changes the
product law by at most the sum of the factorwise total-variation distances. -/
theorem pmfTV_pmfPi_replaceOn_le_sum
    {A : ι → Type*} [∀ index, Fintype (A index)]
    (marginals replacements : ∀ index, PMF (A index)) (coordinates : Finset ι) :
    Probability.pmfTV (pmfPi marginals)
        (pmfPi fun index =>
          if index ∈ coordinates then replacements index else marginals index) ≤
      ∑ index ∈ coordinates,
        Probability.pmfTV (marginals index) (replacements index) := by
  classical
  induction coordinates using Finset.induction_on with
  | empty => simp
  | @insert coordinate coordinates hcoordinate ih =>
      let intermediate : ∀ index, PMF (A index) := fun index =>
        if index ∈ coordinates then replacements index else marginals index
      have hcoordinateIntermediate : intermediate coordinate = marginals coordinate := by
        simp [intermediate, hcoordinate]
      have hfinal :
          (fun index =>
              if index ∈ insert coordinate coordinates then replacements index
              else marginals index) =
            Function.update intermediate coordinate (replacements coordinate) := by
        funext index
        by_cases hindex : index = coordinate
        · subst index
          simp
        · simp [intermediate, hindex]
      calc
        Probability.pmfTV (pmfPi marginals)
            (pmfPi fun index =>
              if index ∈ insert coordinate coordinates then replacements index
              else marginals index) =
            Probability.pmfTV (pmfPi marginals)
              (pmfPi (Function.update intermediate coordinate
                (replacements coordinate))) := by rw [hfinal]
        _ ≤ Probability.pmfTV (pmfPi marginals) (pmfPi intermediate) +
            Probability.pmfTV (pmfPi intermediate)
              (pmfPi (Function.update intermediate coordinate
                (replacements coordinate))) :=
          Probability.pmfTV_triangle _ _ _
        _ = Probability.pmfTV (pmfPi marginals) (pmfPi intermediate) +
            Probability.pmfTV (marginals coordinate)
              (replacements coordinate) := by
          rw [← hcoordinateIntermediate,
            ← pmfTV_pmfPi_update_eq intermediate coordinate
              (intermediate coordinate) (replacements coordinate),
            Function.update_eq_self]
        _ ≤ (∑ index ∈ coordinates,
              Probability.pmfTV (marginals index) (replacements index)) +
            Probability.pmfTV (marginals coordinate)
              (replacements coordinate) := by
          gcongr
        _ = ∑ index ∈ insert coordinate coordinates,
            Probability.pmfTV (marginals index) (replacements index) := by
          rw [Finset.sum_insert hcoordinate]
          ring

/-- Changing one marginal changes the expectation of a bounded observable by
at most twice its bound times the marginal total-variation distance. -/
theorem abs_expect_pmfPi_update_sub_le_two_mul_pmfTV
    {A : ι → Type*} [∀ index, Fintype (A index)]
    (marginals : ∀ index, PMF (A index)) (coordinate : ι)
    (oldMarginal newMarginal : PMF (A coordinate))
    (observable : (∀ index, A index) → ℝ) {bound : ℝ}
    (hbounded : ∀ sample, |observable sample| ≤ bound) :
    |Probability.expect
          (pmfPi (Function.update marginals coordinate oldMarginal)) observable -
        Probability.expect
          (pmfPi (Function.update marginals coordinate newMarginal)) observable| ≤
      (2 * bound) * Probability.pmfTV oldMarginal newMarginal := by
  rw [← pmfTV_pmfPi_update_eq marginals coordinate oldMarginal newMarginal]
  exact Probability.abs_expect_sub_le_two_mul_pmfTV _ _ observable hbounded

end PMFProduct
end Math
