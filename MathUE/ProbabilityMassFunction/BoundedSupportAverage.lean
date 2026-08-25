/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.ProbabilityMassFunction

/-!
# Support atoms bracketing a bounded PMF average

An expectation of a bounded real function under an arbitrary probability
mass function lies between two values attained on its support.  The sample
type need not be finite.  The strict comparison used below is justified by
absolute summability of the weighted bounded functions.
-/

namespace Math
namespace ProbabilityMassFunction

open Probability

variable {Omega : Type*}

/-- A support-wise comparison of bounded functions, strict at one support
atom, gives a strict comparison of their expectations. -/
theorem expect_lt_of_le_on_support_of_bounded
    (mu : PMF Omega) (f g : Omega -> Real) {bound : Real}
    (hf : forall omega, |f omega| <= bound)
    (hg : forall omega, |g omega| <= bound)
    (hle : forall omega, omega ∈ mu.support -> f omega <= g omega)
    (hlt : exists omega, omega ∈ mu.support ∧ f omega < g omega) :
    expect mu f < expect mu g := by
  obtain ⟨omega, homega, hstrict⟩ := hlt
  have hmu : mu omega ≠ 0 := by
    simpa [PMF.mem_support_iff] using homega
  have hweight : 0 < (mu omega).toReal :=
    ENNReal.toReal_pos hmu (PMF.apply_ne_top mu omega)
  have hpointwise : forall point,
      (mu point).toReal * f point <= (mu point).toReal * g point := by
    intro point
    by_cases hpoint : mu point = 0
    · simp [hpoint]
    · exact mul_le_mul_of_nonneg_left
        (hle point (by simpa [PMF.mem_support_iff] using hpoint))
        ENNReal.toReal_nonneg
  have hatom :
      (mu omega).toReal * f omega < (mu omega).toReal * g omega :=
    mul_lt_mul_of_pos_left hstrict hweight
  have hfsum := expect_summable_of_bounded mu f hf
  have hgsum := expect_summable_of_bounded mu g hg
  exact hfsum.tsum_lt_tsum hpointwise hatom hgsum

/-- Some support atom is at least the expectation of a bounded function. -/
theorem exists_mem_support_expect_le
    (mu : PMF Omega) (f : Omega -> Real) {bound : Real}
    (hf : forall omega, |f omega| <= bound) :
    exists omega, omega ∈ mu.support ∧ expect mu f <= f omega := by
  have hexpect : |expect mu f| <= bound := abs_expect_le_of_abs_le mu f hf
  by_contra hnone
  push Not at hnone
  obtain ⟨omega, homega⟩ := mu.support_nonempty
  have hstrict := expect_lt_of_le_on_support_of_bounded
    mu f (fun _ => expect mu f) hf (fun _ => hexpect)
    (fun point hpoint => (hnone point hpoint).le)
    ⟨omega, homega, hnone omega homega⟩
  rw [expect_const] at hstrict
  exact (lt_irrefl _ hstrict)

/-- Some support atom is at most the expectation of a bounded function. -/
theorem exists_mem_support_le_expect
    (mu : PMF Omega) (f : Omega -> Real) {bound : Real}
    (hf : forall omega, |f omega| <= bound) :
    exists omega, omega ∈ mu.support ∧ f omega <= expect mu f := by
  have hexpect : |expect mu f| <= bound := abs_expect_le_of_abs_le mu f hf
  by_contra hnone
  push Not at hnone
  obtain ⟨omega, homega⟩ := mu.support_nonempty
  have hstrict := expect_lt_of_le_on_support_of_bounded
    mu (fun _ => expect mu f) f (fun _ => hexpect) hf
    (fun point hpoint => (hnone point hpoint).le)
    ⟨omega, homega, hnone omega homega⟩
  rw [expect_const] at hstrict
  exact (lt_irrefl _ hstrict)

/-- The difference of two bounded PMF averages is bounded above by a
difference attained at one support atom of each law. -/
theorem exists_support_pair_expect_sub_le_sub
    (mu nu : PMF Omega) (f g : Omega -> Real) {bound : Real}
    (hf : forall omega, |f omega| <= bound)
    (hg : forall omega, |g omega| <= bound) :
    exists first second,
      first ∈ mu.support ∧ second ∈ nu.support ∧
        expect mu f - expect nu g <= f first - g second := by
  obtain ⟨first, hfirst, hfirstValue⟩ :=
    exists_mem_support_expect_le mu f hf
  obtain ⟨second, hsecond, hsecondValue⟩ :=
    exists_mem_support_le_expect nu g hg
  exact ⟨first, second, hfirst, hsecond, sub_le_sub hfirstValue hsecondValue⟩

end ProbabilityMassFunction
end Math
