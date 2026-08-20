/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.BonferroniProductBounds
import MathUE.PMFProduct.CoalitionMass
import Mathlib.Data.Nat.Choose.Cast

/-!
# Collision mass of an independent Bernoulli family

For finitely many independent Bernoulli events, `collisionMass x` is the
probability that at least two coordinates act.  Its definition is the exact
sum of `coalitionMass x coalition` over coalitions of cardinality at least
two.

The central estimate is

`collisionMass x ≤ choose (card ι) 2 * (1 - continueMass x) ^ 2`.

The proof first bounds collision mass by the order-free pair union bound
`Math.pairMulSum`.  Each coordinate probability is then bounded by total
absorption, yielding the finite-player coefficient.  An explicit algebraic
formula is proved equal to the coalition sum; it is used internally to avoid
introducing any probability model separate from `coalitionMass`.

Collision mass is positive exactly when two distinct coordinates have
positive acting probability. Equivalently, it vanishes exactly when the
positive support has cardinality at most one.
-/

namespace Math.PMFProduct

variable {ι : Type*} [DecidableEq ι]

/-! ## Finite-set algebra -/

/-- Algebraic at-least-two mass on a finite coordinate set. -/
noncomputable def collisionMassFormulaOn (x : ι → ℝ) (s : Finset ι) : ℝ :=
  1 - ∏ i ∈ s, (1 - x i) -
    ∑ i ∈ s, x i * ∏ j ∈ s.erase i, (1 - x j)

/-- Adding one coordinate splits a collision according to whether that
coordinate acts. -/
theorem collisionMassFormulaOn_insert (x : ι → ℝ)
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    collisionMassFormulaOn x (insert a s) =
      (1 - x a) * collisionMassFormulaOn x s +
        x a * (1 - ∏ i ∈ s, (1 - x i)) := by
  simp only [collisionMassFormulaOn, Finset.prod_insert ha,
    Finset.sum_insert ha, Finset.erase_insert_eq_erase,
    Finset.erase_eq_of_notMem ha]
  have hsum :
      (∑ i ∈ s,
          x i * ∏ j ∈ (insert a s).erase i, (1 - x j)) =
        (1 - x a) *
          ∑ i ∈ s, x i * ∏ j ∈ s.erase i, (1 - x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    have herase : (insert a s).erase i = insert a (s.erase i) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_insert]
      aesop
    rw [herase, Finset.prod_insert]
    · ring
    · exact fun hmem => ha (Finset.mem_of_mem_erase hmem)
  rw [hsum]
  ring

/-- At-least-two mass is nonnegative for Bernoulli parameters. -/
theorem collisionMassFormulaOn_nonneg (x : ι → ℝ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    0 ≤ collisionMassFormulaOn x s := by
  induction s using Finset.induction_on with
  | empty => simp [collisionMassFormulaOn]
  | @insert a s ha ih =>
      have ha0 := h0 a (Finset.mem_insert_self a s)
      have ha1 := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, 0 ≤ x i :=
        fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, x i ≤ 1 :=
        fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hprod1 : ∏ i ∈ s, (1 - x i) ≤ 1 :=
        Finset.prod_le_one
          (fun i hi => sub_nonneg.mpr (h1s i hi))
          (fun i hi => by linarith [h0s i hi])
      rw [collisionMassFormulaOn_insert x ha]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr ha1) (ih h0s h1s))
        (mul_nonneg ha0 (sub_nonneg.mpr hprod1))

/-- The exact pair-union bound for at-least-two mass. -/
theorem collisionMassFormulaOn_le_pairMulSum (x : ι → ℝ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    collisionMassFormulaOn x s ≤ Math.pairMulSum x s := by
  induction s using Finset.induction_on with
  | empty => simp [collisionMassFormulaOn]
  | @insert a s ha ih =>
      have ha0 := h0 a (Finset.mem_insert_self a s)
      have ha1 := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, 0 ≤ x i :=
        fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, x i ≤ 1 :=
        fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have hcollision0 := collisionMassFormulaOn_nonneg x s h0s h1s
      have habsorption := Math.one_sub_prod_one_sub_le_sum x s h0s h1s
      rw [collisionMassFormulaOn_insert x ha, Math.pairMulSum_insert x ha]
      calc
        (1 - x a) * collisionMassFormulaOn x s +
              x a * (1 - ∏ i ∈ s, (1 - x i))
            ≤ collisionMassFormulaOn x s +
                x a * (1 - ∏ i ∈ s, (1 - x i)) := by
              gcongr
              nlinarith
        _ ≤ collisionMassFormulaOn x s + x a * ∑ i ∈ s, x i := by
              gcongr
        _ ≤ Math.pairMulSum x s + x a * ∑ i ∈ s, x i := by
              simpa [add_comm] using
                add_le_add_right (ih h0s h1s) (x a * ∑ i ∈ s, x i)

omit [DecidableEq ι] in
/-- Every coordinate probability is bounded by the probability that at
least one coordinate acts. -/
theorem coordinate_le_one_sub_prod_one_sub (x : ι → ℝ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1)
    {a : ι} (ha : a ∈ s) :
    x a ≤ 1 - ∏ i ∈ s, (1 - x i) := by
  classical
  have hfactor : ∏ i ∈ s, (1 - x i) =
      (1 - x a) * ∏ i ∈ s.erase a, (1 - x i) := by
    rw [← Finset.prod_erase_mul _ _ ha]
    ring
  have hprod0 : 0 ≤ ∏ i ∈ s.erase a, (1 - x i) :=
    Finset.prod_nonneg fun i hi =>
      sub_nonneg.mpr (h1 i (Finset.mem_of_mem_erase hi))
  have hprod1 : ∏ i ∈ s.erase a, (1 - x i) ≤ 1 :=
    Finset.prod_le_one
      (fun i hi => sub_nonneg.mpr (h1 i (Finset.mem_of_mem_erase hi)))
      (fun i hi => by linarith [h0 i (Finset.mem_of_mem_erase hi)])
  rw [hfactor]
  nlinarith [h1 a ha]

omit [DecidableEq ι] in
/-- The pair sum is bounded by the number of unordered coordinate pairs
times squared total absorption. -/
theorem pairMulSum_le_choose_mul_one_sub_prod_sq
    (x : ι → ℝ) (s : Finset ι)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    Math.pairMulSum x s ≤
      (s.card.choose 2 : ℝ) * (1 - ∏ i ∈ s, (1 - x i)) ^ 2 := by
  classical
  by_cases hs : s = ∅
  · subst s
    simp
  let absorption := 1 - ∏ i ∈ s, (1 - x i)
  have hprod1 : ∏ i ∈ s, (1 - x i) ≤ 1 :=
    Finset.prod_le_one
      (fun i hi => sub_nonneg.mpr (h1 i hi))
      (fun i hi => by linarith [h0 i hi])
  have habsorption0 : 0 ≤ absorption := sub_nonneg.mpr hprod1
  have hcoordinate : ∀ i ∈ s, x i ≤ absorption := fun i hi =>
    coordinate_le_one_sub_prod_one_sub x s h0 h1 hi
  have hterm : ∀ p ∈ s.offDiag,
      x p.1 * x p.2 ≤ absorption ^ 2 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    simpa [sq] using
      mul_le_mul (hcoordinate p.1 hp.1) (hcoordinate p.2 hp.2.1)
        (h0 p.2 hp.2.1) habsorption0
  have hsum : ∑ p ∈ s.offDiag, x p.1 * x p.2 ≤
      (s.offDiag.card : ℝ) * absorption ^ 2 := by
    calc
      (∑ p ∈ s.offDiag, x p.1 * x p.2) ≤
          ∑ _p ∈ s.offDiag, absorption ^ 2 :=
        Finset.sum_le_sum fun p hp => hterm p hp
      _ = (s.offDiag.card : ℝ) * absorption ^ 2 := by simp
  unfold Math.pairMulSum
  change (∑ p ∈ s.offDiag, x p.1 * x p.2) / 2 ≤
    (s.card.choose 2 : ℝ) * absorption ^ 2
  calc
    (∑ p ∈ s.offDiag, x p.1 * x p.2) / 2 ≤
        ((s.offDiag.card : ℝ) * absorption ^ 2) / 2 := by gcongr
    _ = (s.card.choose 2 : ℝ) * absorption ^ 2 := by
      have hcardPos : 0 < s.card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      have hcardLe : s.card ≤ s.card * s.card := by nlinarith
      rw [Finset.offDiag_card, Nat.cast_sub hcardLe, Nat.cast_mul,
        Nat.cast_choose_two]
      ring

/-! ## Full finite family -/

variable [Fintype ι]

/-- Probability mass of coalitions containing at least two acting
coordinates. -/
noncomputable def collisionMass (x : ι → ℝ) : ℝ :=
  ∑ coalition ∈ Finset.univ.filter
      (fun coalition : Finset ι => 2 ≤ coalition.card),
    coalitionMass x coalition

/-- Exact algebraic formula: absorption minus the singleton masses. -/
theorem collisionMass_eq_one_sub_continueMass_sub_singletonMass
    (x : ι → ℝ) :
    collisionMass x =
      1 - continueMass x -
        ∑ i : ι, x i * ∏ j ∈ Finset.univ.erase i, (1 - x j) := by
  let singles : Finset (Finset ι) :=
    Finset.univ.image fun i : ι => ({i} : Finset ι)
  let collisions : Finset (Finset ι) :=
    Finset.univ.filter fun coalition : Finset ι => 2 ≤ coalition.card
  have hdisjoint : Disjoint singles collisions := by
    rw [Finset.disjoint_left]
    intro coalition hsingle hcollision
    simp only [singles, Finset.mem_image, Finset.mem_univ, true_and] at hsingle
    obtain ⟨i, rfl⟩ := hsingle
    simp [collisions] at hcollision
  have hpartition :
      Finset.univ.erase (∅ : Finset ι) = singles ∪ collisions := by
    ext coalition
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union]
    constructor
    · intro hne
      have hpos : 0 < coalition.card := Finset.card_pos.mpr
        (Finset.nonempty_iff_ne_empty.mpr hne.1)
      by_cases hone : coalition.card = 1
      · left
        obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
        simp [singles]
      · right
        simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    · rintro (hsingle | hcollision)
      · simp only [singles, Finset.mem_image, Finset.mem_univ, true_and]
          at hsingle
        obtain ⟨i, rfl⟩ := hsingle
        simp
      · simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and]
          at hcollision
        exact ⟨fun hempty => by simp [hempty] at hcollision, trivial⟩
  have hsingleSum :
      ∑ coalition ∈ singles, coalitionMass x coalition =
        ∑ i : ι, x i * ∏ j ∈ Finset.univ.erase i, (1 - x j) := by
    rw [show singles =
        Finset.univ.image (fun i : ι => ({i} : Finset ι)) by rfl,
      Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      have hcompl : ({i} : Finset ι)ᶜ = Finset.univ.erase i := by
        ext j
        simp
      simp [coalitionMass, hcompl]
    · intro i _ j _ hij
      simpa using hij
  have htotal := sum_coalitionMass_nonempty x
  rw [hpartition, Finset.sum_union hdisjoint, hsingleSum] at htotal
  unfold collisionMass
  change (∑ coalition ∈ collisions, coalitionMass x coalition) =
    1 - continueMass x -
      ∑ i : ι, x i * ∏ j ∈ Finset.univ.erase i, (1 - x j)
  linarith

/-- Collision mass is nonnegative for Bernoulli parameters. -/
theorem collisionMass_nonneg (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    0 ≤ collisionMass x := by
  rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
  exact collisionMassFormulaOn_nonneg x Finset.univ
    (fun i _ => h0 i) (fun i _ => h1 i)

/-- Two distinct positive Bernoulli parameters force positive collision
mass. -/
theorem collisionMass_pos_of_two_pos (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    {first second : ι} (hne : first ≠ second)
    (hfirst : 0 < x first) (hsecond : 0 < x second) :
    0 < collisionMass x := by
  let support : Finset ι := Finset.univ.filter fun i => 0 < x i
  have hfirstMem : first ∈ support := by simp [support, hfirst]
  have hsecondMem : second ∈ support := by simp [support, hsecond]
  have hcard : 2 ≤ support.card := by
    have hsubset : ({first, second} : Finset ι) ⊆ support := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact hfirstMem
      · exact hsecondMem
    have hpairCard : ({first, second} : Finset ι).card = 2 := by simp [hne]
    rw [← hpairCard]
    exact Finset.card_le_card hsubset
  have hinside : 0 < ∏ i ∈ support, x i :=
    Finset.prod_pos fun i hi => (Finset.mem_filter.mp hi).2
  have houtside : 0 < ∏ i ∈ supportᶜ, (1 - x i) := by
    apply Finset.prod_pos
    intro i hi
    have hnot : i ∉ support := by simpa using hi
    have hzero : x i = 0 := by
      apply le_antisymm
      · exact le_of_not_gt (by simpa [support] using hnot)
      · exact h0 i
    simp [hzero]
  have hcoalition : 0 < coalitionMass x support := by
    unfold coalitionMass
    exact mul_pos hinside houtside
  have hmem : support ∈ Finset.univ.filter
      (fun coalition : Finset ι => 2 ≤ coalition.card) := by
    simp [hcard]
  have hle : coalitionMass x support ≤ collisionMass x := by
    unfold collisionMass
    exact Finset.single_le_sum
      (fun coalition _ => coalitionMass_nonneg x h0 h1 coalition) hmem
  exact hcoalition.trans_le hle

/-- Positive collision mass exposes two distinct positive Bernoulli
parameters. -/
theorem exists_two_pos_of_collisionMass_pos (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1)
    (hcollision : 0 < collisionMass x) :
    ∃ first second, first ≠ second ∧ 0 < x first ∧ 0 < x second := by
  unfold collisionMass at hcollision
  obtain ⟨coalition, hcoalition, hmass⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun candidate _ =>
      coalitionMass_nonneg x h0 h1 candidate).mp hcollision
  have hcard : 1 < coalition.card := by
    have := (Finset.mem_filter.mp hcoalition).2
    omega
  obtain ⟨first, hfirstMem, second, hsecondMem, hne⟩ :=
    Finset.one_lt_card.mp hcard
  have houtside : 0 ≤ ∏ i ∈ coalitionᶜ, (1 - x i) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.mpr (h1 i)
  have hinside : 0 < ∏ i ∈ coalition, x i := by
    unfold coalitionMass at hmass
    nlinarith
  have hpositive : ∀ i ∈ coalition, 0 < x i := by
    intro i hi
    by_contra hnot
    have hzero : x i = 0 := le_antisymm (le_of_not_gt hnot) (h0 i)
    have hproductZero : (∏ j ∈ coalition, x j) = 0 :=
      Finset.prod_eq_zero hi hzero
    rw [hproductZero] at hinside
    exact (lt_irrefl 0) hinside
  exact ⟨first, second, hne, hpositive first hfirstMem,
    hpositive second hsecondMem⟩

/-- Collision mass vanishes exactly when at most one Bernoulli parameter is
positive. -/
theorem collisionMass_eq_zero_iff_atMostOne_pos (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x = 0 ↔
      ∀ first second, 0 < x first → 0 < x second → first = second := by
  constructor
  · intro hzero first second hfirst hsecond
    by_contra hne
    have hpositive := collisionMass_pos_of_two_pos
      x h0 h1 hne hfirst hsecond
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  · intro hatMostOne
    apply le_antisymm
    · exact le_of_not_gt fun hpositive => by
        obtain ⟨first, second, hne, hfirst, hsecond⟩ :=
          exists_two_pos_of_collisionMass_pos x h0 h1 hpositive
        exact hne (hatMostOne first second hfirst hsecond)
    · exact collisionMass_nonneg x h0 h1

/-- Collision mass is at most the order-free sum of pair probabilities. -/
theorem collisionMass_le_pairMulSum (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x ≤ Math.pairMulSum x Finset.univ := by
  rw [collisionMass_eq_one_sub_continueMass_sub_singletonMass]
  exact collisionMassFormulaOn_le_pairMulSum x Finset.univ
    (fun i _ => h0 i) (fun i _ => h1 i)

/-- Collision mass is at most half the squared total acting probability.

This is the pair-union estimate used when all configurations with at least
two acting coordinates are replaced by a common reference configuration. -/
theorem collisionMass_le_sq_sum_div_two (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x ≤ (∑ i, x i) ^ 2 / 2 := by
  calc
    collisionMass x ≤ Math.pairMulSum x Finset.univ :=
      collisionMass_le_pairMulSum x h0 h1
    _ ≤ (∑ i ∈ Finset.univ, x i) ^ 2 / 2 :=
      Math.pairMulSum_le_sq_sum_div_two x Finset.univ
    _ = (∑ i, x i) ^ 2 / 2 := by simp

/-- Finite-player quadratic collision bound. -/
theorem collisionMass_le_choose_card_mul_absorption_sq (x : ι → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    collisionMass x ≤
      (Fintype.card ι).choose 2 * (1 - continueMass x) ^ 2 := by
  calc
    collisionMass x ≤ Math.pairMulSum x Finset.univ :=
      collisionMass_le_pairMulSum x h0 h1
    _ ≤ (Finset.univ.card.choose 2 : ℝ) *
        (1 - ∏ i ∈ Finset.univ, (1 - x i)) ^ 2 :=
      pairMulSum_le_choose_mul_one_sub_prod_sq x Finset.univ
        (fun i _ => h0 i) (fun i _ => h1 i)
    _ = (Fintype.card ι).choose 2 * (1 - continueMass x) ^ 2 := by
      simp [continueMass]

end Math.PMFProduct
