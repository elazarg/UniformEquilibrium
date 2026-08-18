/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# The range of a coercive function on an open interval

A one-parameter family of tables often forces its parameter through an
explicit continuous curve on an open interval, and the question is which
parameter values the curve reaches.  When the curve escapes every bound near
both endpoints, the answer is always the same closed ray.

`Math.IsCoerciveOn f a b` packages the escape hypothesis without filters: for
every level `c`, some closed subinterval of `(a, b)` contains all the points
where `f` fails to exceed `c`.  Together with continuity on closed
subintervals this gives two facts.

* The sublevel sets are confined to compact subintervals, so `f` attains a
  least value on `(a, b)`.
* Above that least value `f` takes every value: escape supplies a point where
  `f` is at least the target, continuity supplies the crossing.

So the image of `(a, b)` is exactly the closed ray above the minimum.  Nothing
here needs a formula for `f` — only an explicit blow-up bound at each end,
which is what an algebraic lower bound on a rational curve provides.

## Main definitions

* `Math.IsCoerciveOn` — the escape hypothesis

## Main results

* `Math.exists_isLeast_image_Ioo` — the minimum is attained
* `Math.image_Ioo_subset_Ici` and `Math.Ici_subset_image_Ioo` — the two
  inclusions
* `Math.image_Ioo_eq_Ici_sInf` — the image is the closed ray above its
  infimum
-/

noncomputable section

namespace Math

open Set

/-- **Escape at both ends.**  Every sublevel set of `f` on `(a, b)` is
contained in a closed subinterval of `(a, b)`. -/
def IsCoerciveOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ c : ℝ, ∃ lo hi : ℝ, a < lo ∧ lo ≤ hi ∧ hi < b ∧
    ∀ u ∈ Ioo a b, u ∉ Icc lo hi → c < f u

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **The minimum is attained.**  A coercive function continuous on every
closed subinterval has a least value on the open interval.

Pick any point of the interval and take a subinterval outside which `f`
exceeds the value there, enlarged to contain the point.  Compactness gives a
minimum over that subinterval, and outside it `f` is larger still. -/
theorem exists_isLeast_image_Ioo (hab : a < b)
    (hcont : ∀ lo hi : ℝ, a < lo → hi < b → ContinuousOn f (Icc lo hi))
    (hcoercive : IsCoerciveOn f a b) :
    ∃ u₀ ∈ Ioo a b, ∀ u ∈ Ioo a b, f u₀ ≤ f u := by
  set mid := (a + b) / 2 with hmid
  have hmidmem : mid ∈ Ioo a b := by
    constructor <;> · rw [hmid]; linarith
  obtain ⟨lo, hi, hlo, hlohi, hhi, hout⟩ := hcoercive (f mid)
  set lo' := min lo mid with hlo'
  set hi' := max hi mid with hhi'
  have hlo'pos : a < lo' := lt_min hlo hmidmem.1
  have hhi'lt : hi' < b := max_lt hhi hmidmem.2
  have hlo'le : lo' ≤ hi' := le_trans (min_le_left _ _) (le_trans hlohi (le_max_left _ _))
  have hmidmem' : mid ∈ Icc lo' hi' := ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨u₀, hu₀mem, hu₀min⟩ := (isCompact_Icc (a := lo') (b := hi')).exists_isMinOn
    ⟨mid, hmidmem'⟩ (hcont lo' hi' hlo'pos hhi'lt)
  refine ⟨u₀, ⟨lt_of_lt_of_le hlo'pos hu₀mem.1, lt_of_le_of_lt hu₀mem.2 hhi'lt⟩, ?_⟩
  intro u hu
  by_cases hmem : u ∈ Icc lo' hi'
  · exact hu₀min hmem
  · have hnot : u ∉ Icc lo hi := by
      intro hcontra
      exact hmem ⟨le_trans (min_le_left _ _) hcontra.1,
        le_trans hcontra.2 (le_max_left _ _)⟩
    exact le_trans (hu₀min hmidmem') (hout u hu hnot).le

/-- Every value the function takes is at least the infimum of its image. -/
theorem image_Ioo_subset_Ici (hab : a < b)
    (hcont : ∀ lo hi : ℝ, a < lo → hi < b → ContinuousOn f (Icc lo hi))
    (hcoercive : IsCoerciveOn f a b) :
    IsLeast (f '' Ioo a b) (sInf (f '' Ioo a b)) := by
  obtain ⟨u₀, hu₀, hmin⟩ := exists_isLeast_image_Ioo hab hcont hcoercive
  have hleast : IsLeast (f '' Ioo a b) (f u₀) := by
    refine ⟨⟨u₀, hu₀, rfl⟩, ?_⟩
    rintro x ⟨u, hu, rfl⟩
    exact hmin u hu
  have heq : sInf (f '' Ioo a b) = f u₀ := hleast.csInf_eq
  rw [heq]
  exact hleast

/-- **Every larger value is taken.**  Escape supplies a point past the target
and continuity supplies the crossing between it and any point at or below the
target. -/
theorem Ici_subset_image_Ioo
    (hcont : ∀ lo hi : ℝ, a < lo → hi < b → ContinuousOn f (Icc lo hi))
    (hcoercive : IsCoerciveOn f a b) {u₀ : ℝ} (hu₀ : u₀ ∈ Ioo a b) {y : ℝ}
    (hy : f u₀ ≤ y) : ∃ u ∈ Ioo a b, f u = y := by
  obtain ⟨lo, hi, hlo, hlohi, hhi, hout⟩ := hcoercive y
  have hlt : lo ≤ hi := hlohi
  have hstrict : a < hi := lt_of_lt_of_le hlo hlohi
  set u₁ := (a + lo) / 2 with hu₁
  have hu₁mem : u₁ ∈ Ioo a b := by
    constructor
    · rw [hu₁]; linarith
    · rw [hu₁]; linarith [lt_trans hstrict hhi]
  have hu₁not : u₁ ∉ Icc lo hi := by
    intro hcontra
    have := hcontra.1
    rw [hu₁] at this
    linarith
  have hu₁gt : y < f u₁ := hout u₁ hu₁mem hu₁not
  have hlow : min u₀ u₁ ∈ Ioo a b := by
    rcases min_cases u₀ u₁ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hu₀
    · exact hu₁mem
  have hhigh : max u₀ u₁ ∈ Ioo a b := by
    rcases max_cases u₀ u₁ with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hu₀
    · exact hu₁mem
  have huicc : Set.uIcc u₀ u₁ = Icc (min u₀ u₁) (max u₀ u₁) := rfl
  have hsub : Set.uIcc u₀ u₁ ⊆ Ioo a b := Set.ordConnected_Ioo.uIcc_subset hu₀ hu₁mem
  have hcont' : ContinuousOn f (Set.uIcc u₀ u₁) := by
    rw [huicc]
    exact hcont _ _ hlow.1 hhigh.2
  have hmem : y ∈ Set.uIcc (f u₀) (f u₁) := Set.mem_uIcc.mpr (Or.inl ⟨hy, hu₁gt.le⟩)
  obtain ⟨u, hu, heq⟩ := intermediate_value_uIcc hcont' hmem
  exact ⟨u, hsub hu, heq⟩

/-- **The range of a coercive curve.**  The image of the open interval is
exactly the closed ray above its infimum. -/
theorem image_Ioo_eq_Ici_sInf (hab : a < b)
    (hcont : ∀ lo hi : ℝ, a < lo → hi < b → ContinuousOn f (Icc lo hi))
    (hcoercive : IsCoerciveOn f a b) :
    f '' Ioo a b = Ici (sInf (f '' Ioo a b)) := by
  have hleast := image_Ioo_subset_Ici hab hcont hcoercive
  refine Set.Subset.antisymm (fun x hx ↦ hleast.2 hx) ?_
  intro x hx
  obtain ⟨u₀, hu₀, heq⟩ := hleast.1
  obtain ⟨u, hu, hval⟩ := Ici_subset_image_Ioo hcont hcoercive hu₀ (heq.le.trans hx)
  exact ⟨u, hu, hval⟩

end Math
