/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ProbabilityMassFunction

/-!
# Elementary PMF coupling lemmas

This file collects game-independent support and expectation identities used by
finite-clock encodings and semantic couplings.
-/

noncomputable section

namespace Math
namespace ProbabilityMassFunction

open Set

/-- Mapping a PMF by a function that fixes every positive-mass atom leaves it
unchanged. -/
theorem PMF.map_eq_self_of_eq_on_support {α : Type*}
    (law : PMF α) (mapChoice : α → α)
    (hfix : ∀ choice, law choice ≠ 0 → mapChoice choice = choice) :
    law.map mapChoice = law := by
  classical
  apply PMF.ext
  intro choice
  rw [PMF.map_apply, tsum_eq_single choice]
  · by_cases hchoice : law choice = 0
    · simp [hchoice]
    · simp [hfix choice hchoice]
  · intro other hother
    by_cases hmass : law other = 0
    · simp [hmass]
    · simp [hfix other hmass, hother.symm]

/-- Two real observables that agree on the support of a PMF have equal
expectations. -/
theorem expect_eq_of_eq_on_support {Sample : Type*}
    (law : PMF Sample) (first second : Sample → ℝ)
    (heq : ∀ sample, law sample ≠ 0 → first sample = second sample) :
    Probability.expect law first = Probability.expect law second := by
  unfold Probability.expect
  apply tsum_congr
  intro sample
  by_cases hsample : law sample = 0
  · simp [hsample]
  · rw [heq sample hsample]

/-- Coupled bounded observables differ in expectation by at most twice their
common absolute bound times the probability of the bad event. -/
theorem abs_expect_sub_expect_map_le_of_eq_off_event
    {Source Target : Type*} (law : PMF Source) (quotient : Source → Target)
    (sourceValue : Source → ℝ) (targetValue : Target → ℝ)
    (event : Set Source) {bound : ℝ}
    (hsource : ∀ sample, |sourceValue sample| ≤ bound)
    (htarget : ∀ sample, |targetValue sample| ≤ bound)
    (heq : ∀ sample, sample ∉ event →
      sourceValue sample = targetValue (quotient sample)) :
    |Probability.expect law sourceValue -
        Probability.expect (law.map quotient) targetValue| ≤
      2 * bound * (pmfMass law fun sample => sample ∈ event).toReal := by
  have hmap : Probability.expect (law.map quotient) targetValue =
      Probability.expect law
        (fun sample => targetValue (quotient sample)) := by
    simpa [pushforward] using
      expect_pushforward_of_bounded law quotient targetValue htarget
  rw [hmap]
  apply abs_expect_sub_le_mul_pmfMass law sourceValue
    (fun sample => targetValue (quotient sample)) event
    (bound := 2 * bound) (observableBound := bound)
    hsource (fun sample => htarget (quotient sample))
  intro sample
  by_cases hevent : sample ∈ event
  · rw [Set.indicator_of_mem hevent]
    simp only [mul_one]
    calc
      |sourceValue sample - targetValue (quotient sample)| ≤
          |sourceValue sample| + |targetValue (quotient sample)| :=
        abs_sub _ _
      _ ≤ bound + bound := add_le_add (hsource sample)
        (htarget (quotient sample))
      _ = 2 * bound := by ring
  · rw [Set.indicator_of_notMem hevent, mul_zero, heq sample hevent,
      sub_self, abs_zero]

end ProbabilityMassFunction
end Math
