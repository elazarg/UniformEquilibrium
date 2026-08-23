/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.Bind

/-!
# Restricting a finite product PMF to selected coordinates

An assignment on a finite coordinate subset extends to the ambient product by
using fixed values outside the subset.  When every omitted marginal is the
corresponding point mass, the ambient product law is exactly the pushforward of
the restricted product law.  Bind and real-expectation identities follow.
-/

noncomputable section

namespace Math.PMFProduct

open Math.Probability Math.ProbabilityMassFunction

universe uι uA uβ

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type uA}

/-- Extend an assignment on `players` using `outside` on omitted coordinates. -/
def principalExtend (players : Finset ι) (outside : ∀ i, A i)
    (assignment : ∀ i : players, A i.1) : ∀ i, A i :=
  fun i => if hi : i ∈ players then assignment ⟨i, hi⟩ else outside i

omit [Fintype ι] in
@[simp] theorem principalExtend_apply_mem (players : Finset ι)
    (outside : ∀ i, A i) (assignment : ∀ i : players, A i.1)
    (i : players) :
    principalExtend players outside assignment i.1 = assignment i := by
  simp [principalExtend]

omit [Fintype ι] in
theorem principalExtend_apply_not_mem (players : Finset ι)
    (outside : ∀ i, A i) (assignment : ∀ i : players, A i.1)
    {i : ι} (hi : i ∉ players) :
    principalExtend players outside assignment i = outside i := by
  simp [principalExtend, hi]

omit [Fintype ι] in
theorem principalExtend_injective (players : Finset ι) (outside : ∀ i, A i) :
    Function.Injective (principalExtend players outside) := by
  intro left right heq
  funext i
  simpa using congrFun heq i.1

/-- Restrict a family of ambient marginals to a coordinate subtype. -/
def principalMarginals (sigma : ∀ i, PMF (A i)) (players : Finset ι) :
    ∀ i : players, PMF (A i.1) :=
  fun i => sigma i.1

/-- An ambient finite product whose omitted coordinates are point masses is
the pushforward of the restricted product by fixed-value extension. -/
theorem pmfPi_eq_map_principal
    (sigma : ∀ i, PMF (A i)) (players : Finset ι) (outside : ∀ i, A i)
    (hpure : ∀ i, i ∉ players → sigma i = PMF.pure (outside i)) :
    pmfPi sigma =
      PMF.map (principalExtend players outside)
        (pmfPi (principalMarginals sigma players)) := by
  classical
  ext assignment
  rw [PMF.map_apply, pmfPi_apply]
  by_cases hcompatible : ∀ i, i ∉ players → assignment i = outside i
  · let restricted : ∀ i : players, A i.1 := fun i => assignment i.1
    have hextend : principalExtend players outside restricted = assignment := by
      funext i
      by_cases hi : i ∈ players
      · simp [principalExtend, restricted, hi]
      · simp [principalExtend, hi, hcompatible i hi]
    rw [tsum_eq_single restricted]
    · rw [if_pos hextend.symm, pmfPi_apply]
      have hoff : ∀ i ∈ playersᶜ,
          sigma i (assignment i) = 1 := by
        intro i hi
        have hinot : i ∉ players := by simpa using hi
        rw [hpure i hinot, hcompatible i hinot]
        simp
      calc
        (∏ i, sigma i (assignment i)) =
            (∏ i ∈ players, sigma i (assignment i)) *
              ∏ i ∈ playersᶜ, sigma i (assignment i) := by
          rw [← Finset.prod_union disjoint_compl_right, Finset.union_compl]
        _ = ∏ i ∈ players, sigma i (assignment i) := by
          rw [Finset.prod_eq_one hoff, mul_one]
        _ = ∏ i : players, sigma i.1 (restricted i) := by
          rw [Finset.prod_subtype players (fun _ => Iff.rfl)]
    · intro other hother
      rw [if_neg (fun heq => hother (principalExtend_injective players outside
        (heq.symm.trans hextend.symm)))]
  · push Not at hcompatible
    obtain ⟨i, hi, hne⟩ := hcompatible
    have hfactor : sigma i (assignment i) = 0 := by
      rw [hpure i hi]
      simp [hne]
    have hleft : (∏ j, sigma j (assignment j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hfactor
    rw [hleft]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro restricted
    rw [if_neg]
    intro heq
    have := congrFun heq i
    rw [principalExtend_apply_not_mem players outside restricted hi] at this
    exact hne this

/-- Bind form of `pmfPi_eq_map_principal`. -/
theorem pmfPi_bind_eq_principal
    (sigma : ∀ i, PMF (A i)) (players : Finset ι) (outside : ∀ i, A i)
    (hpure : ∀ i, i ∉ players → sigma i = PMF.pure (outside i))
    (kernel : (∀ i, A i) → PMF β) :
    (pmfPi sigma).bind kernel =
      (pmfPi (principalMarginals sigma players)).bind
        (fun assignment => kernel (principalExtend players outside assignment)) := by
  rw [pmfPi_eq_map_principal sigma players outside hpure]
  exact PMF.bind_map _ _ _

/-- Real-expectation form of `pmfPi_eq_map_principal`. -/
theorem expect_pmfPi_eq_principal
    [∀ i, Finite (A i)]
    (sigma : ∀ i, PMF (A i)) (players : Finset ι) (outside : ∀ i, A i)
    (hpure : ∀ i, i ∉ players → sigma i = PMF.pure (outside i))
    (f : (∀ i, A i) → ℝ) :
    expect (pmfPi sigma) f =
      expect (pmfPi (principalMarginals sigma players))
        (fun assignment => f (principalExtend players outside assignment)) := by
  rw [pmfPi_eq_map_principal sigma players outside hpure]
  exact expect_pushforward _ _ _

end Math.PMFProduct
