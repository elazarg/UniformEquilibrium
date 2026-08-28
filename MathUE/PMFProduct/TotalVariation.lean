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

/-- The total variation between two finite independent products is at most
the sum of their marginal total variations. -/
theorem pmfTV_pmfPi_le_sum
    {A : ι → Type*} [∀ index, Fintype (A index)]
    (first second : ∀ index, PMF (A index)) :
    Probability.pmfTV (pmfPi first) (pmfPi second) ≤
      ∑ index, Probability.pmfTV (first index) (second index) := by
  simpa using pmfTV_pmfPi_replaceOn_le_sum first second Finset.univ

/-- A bounded observable of a finite independent product is Lipschitz in the
sum of the marginal total variations. -/
theorem abs_expect_pmfPi_sub_le_two_mul_sum_pmfTV
    {A : ι → Type*} [∀ index, Fintype (A index)]
    (first second : ∀ index, PMF (A index))
    (observable : (∀ index, A index) → ℝ) {bound : ℝ}
    (hbound : 0 ≤ bound)
    (hobservable : ∀ sample, |observable sample| ≤ bound) :
    |Probability.expect (pmfPi first) observable -
        Probability.expect (pmfPi second) observable| ≤
      2 * bound *
        ∑ index, Probability.pmfTV (first index) (second index) := by
  calc
    |Probability.expect (pmfPi first) observable -
        Probability.expect (pmfPi second) observable| ≤
        2 * bound * Probability.pmfTV (pmfPi first) (pmfPi second) :=
      Probability.abs_expect_sub_le_two_mul_pmfTV _ _ observable hobservable
    _ ≤ 2 * bound *
          ∑ index, Probability.pmfTV (first index) (second index) :=
      mul_le_mul_of_nonneg_left (pmfTV_pmfPi_le_sum first second)
        (mul_nonneg (by norm_num) hbound)

omit [DecidableEq ι] in
/-- If every marginal has the same law after its operational observation,
then the observed independent product laws are exactly equal. -/
theorem pmfPi_map_coordwise_eq_of_maps_eq
    {A C B : ι → Type*}
    (first : ∀ index, PMF (A index))
    (second : ∀ index, PMF (C index))
    (observeFirst : ∀ index, A index → B index)
    (observeSecond : ∀ index, C index → B index)
    (hmarginal : ∀ index,
      (first index).map (observeFirst index) =
        (second index).map (observeSecond index)) :
    (pmfPi first).map (fun sample index => observeFirst index (sample index)) =
      (pmfPi second).map
        (fun sample index => observeSecond index (sample index)) := by
  change ProbabilityMassFunction.pushforward (pmfPi first)
      (fun sample index => observeFirst index (sample index)) =
    ProbabilityMassFunction.pushforward (pmfPi second)
      (fun sample index => observeSecond index (sample index))
  rw [pmfPi_push_coordwise, pmfPi_push_coordwise]
  congr 1
  funext index
  exact hmarginal index

omit [DecidableEq ι] in
/-- An observable depending only on coordinatewise operational images has
exactly the same expectation under marginally operationally equal product
laws.  This is the source-independent null-direction theorem. -/
theorem expect_pmfPi_coordwise_eq_of_maps_eq
    {A C B : ι → Type*}
    (first : ∀ index, PMF (A index))
    (second : ∀ index, PMF (C index))
    (observeFirst : ∀ index, A index → B index)
    (observeSecond : ∀ index, C index → B index)
    (observable : (∀ index, B index) → ℝ)
    (hmarginal : ∀ index,
      (first index).map (observeFirst index) =
        (second index).map (observeSecond index)) :
    Probability.expect (pmfPi first)
        (fun sample => observable fun index => observeFirst index (sample index)) =
      Probability.expect (pmfPi second)
        (fun sample => observable fun index =>
          observeSecond index (sample index)) := by
  calc
    Probability.expect (pmfPi first)
        (fun sample => observable fun index => observeFirst index (sample index)) =
        Probability.expect
          ((pmfPi first).map
            (fun sample index => observeFirst index (sample index))) observable :=
      (Probability.expect_map _ _ _).symm
    _ = Probability.expect
          ((pmfPi second).map
            (fun sample index => observeSecond index (sample index))) observable := by
      rw [pmfPi_map_coordwise_eq_of_maps_eq first second
        observeFirst observeSecond hmarginal]
    _ = Probability.expect (pmfPi second)
        (fun sample => observable fun index =>
          observeSecond index (sample index)) := Probability.expect_map _ _ _

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
