/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import FixedPointTheorems.cubical_sperner_prep
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Fin.Basic

/-!
# Unit-step structure of a top-dimensional cubical grid simplex

A grid simplex in the sense of `simplex` is an injective, coordinatewise
monotone chain of grid vertices whose last vertex exceeds its first by at most
one in every coordinate.  When the chain has as many steps as the cube has
coordinates, these conditions force the chain to be a Kuhn chain: each step
raises exactly one coordinate by exactly one, and the raised coordinates
exhaust the coordinate set.

The development here is purely combinatorial.  It records the total grid
weight of a vertex, shows that the weight increases by exactly one at every
step, extracts the unique raised coordinate of each step, and proves that the
resulting step map is a bijection onto the coordinates.  The inverse map sends
a coordinate to the step at which it is raised, which pins down the value of
every coordinate at every vertex of the chain.
-/

noncomputable section

namespace Math

variable {SC : SpernerCube} {m : ℕ} {I : Fin (m + 1) → SC.G}

/-! ## Elementary chain estimates -/

/-- Coordinatewise monotonicity of a grid simplex chain, in natural-number
form. -/
theorem spernerSimplex_val_le_of_le (hs : simplex SC m I)
    {first second : Fin (m + 1)} (hle : first ≤ second) (who : Fin SC.n) :
    (I first who).1 ≤ (I second who).1 :=
  monotone_1_of_simplex SC I hs first second hle who

/-- Every vertex of a grid simplex chain exceeds every other by at most one in
each coordinate. -/
theorem spernerSimplex_val_le_succ (hs : simplex SC m I)
    (first second : Fin (m + 1)) (who : Fin SC.n) :
    (I first who).1 ≤ (I second who).1 + 1 :=
  le_add_one_of_simplex SC I hs first second who

/-- One step of the chain does not decrease a coordinate. -/
theorem spernerSimplex_step_le (hs : simplex SC m I) (i : Fin m) (who : Fin SC.n) :
    (I i.castSucc who).1 ≤ (I i.succ who).1 :=
  spernerSimplex_val_le_of_le hs (Fin.castSucc_lt_succ (i := i)).le who

/-- One step of the chain raises a coordinate by at most one. -/
theorem spernerSimplex_step_le_add_one (hs : simplex SC m I) (i : Fin m)
    (who : Fin SC.n) :
    (I i.succ who).1 ≤ (I i.castSucc who).1 + 1 :=
  spernerSimplex_val_le_succ hs i.succ i.castSucc who

/-- A coordinatewise monotone injective chain whose last vertex exceeds its
first by at most one in every coordinate is a grid simplex.  This converts the
wrap-around index form of `simplex` into successive-index form. -/
theorem simplex_of_step_le (I : Fin (m + 1) → SC.G)
    (hinjective : Function.Injective I)
    (hstep : ∀ i : Fin m, ∀ who, (I i.castSucc who).1 ≤ (I i.succ who).1)
    (hlast : ∀ who, (I (Fin.last m) who).1 ≤ (I 0 who).1 + 1) :
    simplex SC m I := by
  refine ⟨hinjective, fun i hi who ↦ ⟨?_, hlast who⟩⟩
  have hcast : (Fin.ofNat (m + 1) i) = (⟨i, hi⟩ : Fin m).castSucc := by
    apply Fin.val_injective
    simp [Fin.ofNat_eq_cast, Fin.val_natCast,
      Nat.mod_eq_of_lt (by omega : i < m + 1)]
  have hsucc : (Fin.ofNat (m + 1) (i + 1)) = (⟨i, hi⟩ : Fin m).succ := by
    apply Fin.val_injective
    simp [Fin.ofNat_eq_cast, Fin.val_natCast,
      Nat.mod_eq_of_lt (by omega : i + 1 < m + 1)]
  rw [hcast, hsucc]
  exact hstep ⟨i, hi⟩ who

/-! ## Total grid weight -/

/-- The sum of all grid coordinates of one cubical grid vertex. -/
def spernerVertexWeight (SC : SpernerCube) (vertex : SC.G) : ℕ :=
  ∑ who : Fin SC.n, (vertex who).1

/-- Each step of a grid simplex chain strictly increases the total weight. -/
theorem spernerVertexWeight_lt_of_step (hs : simplex SC m I) (i : Fin m) :
    spernerVertexWeight SC (I i.castSucc) < spernerVertexWeight SC (I i.succ) := by
  have hle : spernerVertexWeight SC (I i.castSucc) ≤
      spernerVertexWeight SC (I i.succ) :=
    Finset.sum_le_sum fun who _ ↦ spernerSimplex_step_le hs i who
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hall : ∀ who ∈ (Finset.univ : Finset (Fin SC.n)),
        (I i.castSucc who).1 = (I i.succ who).1 :=
      (Finset.sum_eq_sum_iff_of_le
        fun who _ ↦ spernerSimplex_step_le hs i who).1 heq
    have hvertex : I i.castSucc = I i.succ := by
      funext who
      exact Fin.val_injective (hall who (Finset.mem_univ who))
    exact (Fin.castSucc_lt_succ (i := i)).ne (hs.1 hvertex)

/-- The total weight is strictly monotone along a grid simplex chain. -/
theorem spernerVertexWeight_strictMono (hs : simplex SC m I) :
    StrictMono fun index ↦ spernerVertexWeight SC (I index) :=
  Fin.strictMono_iff_lt_succ.2 fun i ↦ spernerVertexWeight_lt_of_step hs i

/-- The total weight of the last vertex exceeds that of the first by at most
the number of coordinates. -/
theorem spernerVertexWeight_last_le (hs : simplex SC m I) :
    spernerVertexWeight SC (I (Fin.last m)) ≤
      spernerVertexWeight SC (I 0) + SC.n := by
  have hbound : ∀ who ∈ (Finset.univ : Finset (Fin SC.n)),
      (I (Fin.last m) who).1 ≤ (I 0 who).1 + 1 :=
    fun who _ ↦ last_of_simplex SC I hs who
  calc spernerVertexWeight SC (I (Fin.last m))
      ≤ ∑ who : Fin SC.n, ((I 0 who).1 + 1) := Finset.sum_le_sum hbound
    _ = spernerVertexWeight SC (I 0) + SC.n := by
        simp [spernerVertexWeight, Finset.sum_add_distrib]

/-! ## Strictly monotone natural chains on `Fin (N + 1)` -/

/-- A strictly monotone natural chain grows at least as fast as its index. -/
theorem le_apply_of_strictMono_fin {N : ℕ} {f : Fin (N + 1) → ℕ}
    (hf : StrictMono f) (i : Fin (N + 1)) : f 0 + i.1 ≤ f i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      have hlt : f i.castSucc < f i.succ := hf (Fin.castSucc_lt_succ (i := i))
      have hcast : (i.castSucc : ℕ) = (i : ℕ) := rfl
      have hsucc : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
      omega

/-- A strictly monotone natural chain leaves at least one unit of room for each
remaining step. -/
theorem apply_add_le_last_of_strictMono_fin {N : ℕ} {f : Fin (N + 1) → ℕ}
    (hf : StrictMono f) (i : Fin (N + 1)) :
    f i + (N - i.1) ≤ f (Fin.last N) := by
  induction i using Fin.reverseInduction with
  | last => simp
  | cast i ih =>
      have hlt : f i.castSucc < f i.succ := hf (Fin.castSucc_lt_succ (i := i))
      have hcast : (i.castSucc : ℕ) = (i : ℕ) := rfl
      have hsucc : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
      have hbound : (i : ℕ) < N := i.2
      omega

/-- In a top-dimensional grid simplex chain the total weight is the initial
weight plus the index. -/
theorem spernerVertexWeight_eq (hs : simplex SC m I) (hm : m = SC.n)
    (i : Fin (m + 1)) :
    spernerVertexWeight SC (I i) = spernerVertexWeight SC (I 0) + i.1 := by
  have hmono : StrictMono fun index ↦ spernerVertexWeight SC (I index) :=
    spernerVertexWeight_strictMono hs
  have hlow : spernerVertexWeight SC (I 0) + i.1 ≤ spernerVertexWeight SC (I i) :=
    le_apply_of_strictMono_fin hmono i
  have hhigh : spernerVertexWeight SC (I i) + (m - i.1) ≤
      spernerVertexWeight SC (I (Fin.last m)) :=
    apply_add_le_last_of_strictMono_fin hmono i
  have hlast := spernerVertexWeight_last_le hs
  have hindex : (i : ℕ) ≤ m := Nat.lt_succ_iff.1 i.2
  omega

/-! ## The raised coordinate of a step -/

/-- The coordinates raised by one step of a grid simplex chain. -/
def spernerChainStepSet (I : Fin (m + 1) → SC.G) (i : Fin m) : Finset (Fin SC.n) :=
  Finset.univ.filter fun who ↦ (I i.castSucc who).1 < (I i.succ who).1

@[simp] theorem mem_spernerChainStepSet {i : Fin m} {who : Fin SC.n} :
    who ∈ spernerChainStepSet I i ↔ (I i.castSucc who).1 < (I i.succ who).1 := by
  simp [spernerChainStepSet]

/-- A step raises exactly the coordinates of its step set, and by exactly one. -/
theorem spernerSimplex_step_value (hs : simplex SC m I) (i : Fin m) (who : Fin SC.n) :
    (I i.succ who).1 =
      (I i.castSucc who).1 + (if who ∈ spernerChainStepSet I i then 1 else 0) := by
  by_cases hmem : who ∈ spernerChainStepSet I i
  · rw [if_pos hmem]
    have hlt := mem_spernerChainStepSet.1 hmem
    have hle := spernerSimplex_step_le_add_one hs i who
    omega
  · rw [if_neg hmem]
    rw [mem_spernerChainStepSet] at hmem
    have hle := spernerSimplex_step_le hs i who
    omega

/-- The weight gain across one step is the size of its step set. -/
theorem spernerVertexWeight_succ (hs : simplex SC m I) (i : Fin m) :
    spernerVertexWeight SC (I i.succ) =
      spernerVertexWeight SC (I i.castSucc) + (spernerChainStepSet I i).card := by
  have hsum : ∑ who : Fin SC.n, (I i.succ who).1 =
      ∑ who : Fin SC.n, ((I i.castSucc who).1 +
        (if who ∈ spernerChainStepSet I i then 1 else 0)) :=
    Finset.sum_congr rfl fun who _ ↦ spernerSimplex_step_value hs i who
  have hcount : ∑ who : Fin SC.n,
      (if who ∈ spernerChainStepSet I i then 1 else 0) =
        (spernerChainStepSet I i).card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]
  simpa only [spernerVertexWeight, Finset.sum_add_distrib, hcount] using hsum

/-- In a top-dimensional chain each step raises exactly one coordinate. -/
theorem spernerChainStepSet_card (hs : simplex SC m I) (hm : m = SC.n) (i : Fin m) :
    (spernerChainStepSet I i).card = 1 := by
  have hsucc := spernerVertexWeight_succ hs i
  have hcastVal := spernerVertexWeight_eq hs hm i.castSucc
  have hsuccVal := spernerVertexWeight_eq hs hm i.succ
  have hcast : (i.castSucc : ℕ) = (i : ℕ) := rfl
  have hsuccIndex : (i.succ : ℕ) = (i : ℕ) + 1 := rfl
  omega

/-- The coordinate raised by one step of a top-dimensional grid simplex
chain. -/
def spernerChainStep (hs : simplex SC m I) (hm : m = SC.n) (i : Fin m) : Fin SC.n :=
  (Finset.card_eq_one.1 (spernerChainStepSet_card hs hm i)).choose

theorem spernerChainStepSet_eq_singleton (hs : simplex SC m I) (hm : m = SC.n)
    (i : Fin m) : spernerChainStepSet I i = {spernerChainStep hs hm i} :=
  (Finset.card_eq_one.1 (spernerChainStepSet_card hs hm i)).choose_spec

theorem mem_spernerChainStepSet_iff (hs : simplex SC m I) (hm : m = SC.n)
    (i : Fin m) (who : Fin SC.n) :
    who ∈ spernerChainStepSet I i ↔ who = spernerChainStep hs hm i := by
  rw [spernerChainStepSet_eq_singleton hs hm i, Finset.mem_singleton]

/-- The raised coordinate of a step is raised by exactly one. -/
theorem spernerChainStep_val_succ (hs : simplex SC m I) (hm : m = SC.n) (i : Fin m) :
    (I i.succ (spernerChainStep hs hm i)).1 =
      (I i.castSucc (spernerChainStep hs hm i)).1 + 1 := by
  have hmem : spernerChainStep hs hm i ∈ spernerChainStepSet I i :=
    (mem_spernerChainStepSet_iff hs hm i _).2 rfl
  have hlt := mem_spernerChainStepSet.1 hmem
  have hle := spernerSimplex_step_le_add_one hs i (spernerChainStep hs hm i)
  omega

/-- Every other coordinate is unchanged by the step. -/
theorem spernerChainStep_eq_of_ne (hs : simplex SC m I) (hm : m = SC.n) (i : Fin m)
    {who : Fin SC.n} (hne : who ≠ spernerChainStep hs hm i) :
    I i.succ who = I i.castSucc who := by
  have hnotMem : who ∉ spernerChainStepSet I i := by
    rw [mem_spernerChainStepSet_iff hs hm]
    exact hne
  have hvalue := spernerSimplex_step_value hs i who
  rw [if_neg hnotMem] at hvalue
  exact Fin.val_injective (by omega)

/-! ## The step map is a bijection onto the coordinates -/

/-- Two different steps of a top-dimensional chain raise different
coordinates. -/
theorem spernerChainStep_injective (hs : simplex SC m I) (hm : m = SC.n) :
    Function.Injective (spernerChainStep hs hm) := by
  have hlt : ∀ first second : Fin m, first < second →
      spernerChainStep hs hm first ≠ spernerChainStep hs hm second := by
    intro first second horder heq
    have hfirst := spernerChainStep_val_succ hs hm first
    have hsecond := spernerChainStep_val_succ hs hm second
    rw [← heq] at hsecond
    have hbase : (I 0 (spernerChainStep hs hm first)).1 ≤
        (I first.castSucc (spernerChainStep hs hm first)).1 :=
      spernerSimplex_val_le_of_le hs (Fin.zero_le _) _
    have hmiddle : (I first.succ (spernerChainStep hs hm first)).1 ≤
        (I second.castSucc (spernerChainStep hs hm first)).1 := by
      apply spernerSimplex_val_le_of_le hs
      rw [Fin.le_def]
      have : (first : ℕ) < (second : ℕ) := horder
      simpa [Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE] using this
    have htop : (I second.succ (spernerChainStep hs hm first)).1 ≤
        (I 0 (spernerChainStep hs hm first)).1 + 1 :=
      spernerSimplex_val_le_succ hs second.succ 0 _
    omega
  intro first second heq
  rcases lt_trichotomy first second with horder | horder | horder
  · exact absurd heq (hlt first second horder)
  · exact horder
  · exact absurd heq.symm (hlt second first horder)

/-- Every coordinate is raised at some step of a top-dimensional chain. -/
theorem spernerChainStep_surjective (hs : simplex SC m I) (hm : m = SC.n) :
    Function.Surjective (spernerChainStep hs hm) := by
  have hcard : (Finset.univ.image (spernerChainStep hs hm)).card =
      Fintype.card (Fin SC.n) := by
    rw [Finset.card_image_of_injective _ (spernerChainStep_injective hs hm)]
    simp [hm]
  have himage : Finset.univ.image (spernerChainStep hs hm) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  intro who
  have hmem : who ∈ Finset.univ.image (spernerChainStep hs hm) := by
    rw [himage]
    exact Finset.mem_univ who
  simpa using hmem

/-- The step at which one coordinate is raised. -/
def spernerChainRaiseIndex (hs : simplex SC m I) (hm : m = SC.n)
    (who : Fin SC.n) : Fin m :=
  (spernerChainStep_surjective hs hm who).choose

@[simp] theorem spernerChainStep_raiseIndex (hs : simplex SC m I) (hm : m = SC.n)
    (who : Fin SC.n) :
    spernerChainStep hs hm (spernerChainRaiseIndex hs hm who) = who :=
  (spernerChainStep_surjective hs hm who).choose_spec

/-- Distinct coordinates are raised at distinct steps. -/
theorem spernerChainRaiseIndex_injective (hs : simplex SC m I) (hm : m = SC.n) :
    Function.Injective (spernerChainRaiseIndex hs hm) := by
  intro first second heq
  have hfirst := spernerChainStep_raiseIndex hs hm first
  have hsecond := spernerChainStep_raiseIndex hs hm second
  rw [heq, hsecond] at hfirst
  exact hfirst.symm

/-! ## Coordinate values along the chain -/

/-- Up to and including its raising step, a coordinate keeps its initial
value. -/
theorem spernerChain_val_eq_of_le_raiseIndex (hs : simplex SC m I) (hm : m = SC.n)
    (who : Fin SC.n) {i : Fin (m + 1)}
    (hle : (i : ℕ) ≤ (spernerChainRaiseIndex hs hm who : ℕ)) :
    (I i who).1 = (I 0 who).1 := by
  set raise := spernerChainRaiseIndex hs hm who with hraise
  have hstep : spernerChainStep hs hm raise = who :=
    spernerChainStep_raiseIndex hs hm who
  have hsucc : (I raise.succ who).1 = (I raise.castSucc who).1 + 1 := by
    have := spernerChainStep_val_succ hs hm raise
    rwa [hstep] at this
  have hbase : (I 0 who).1 ≤ (I raise.castSucc who).1 :=
    spernerSimplex_val_le_of_le hs (Fin.zero_le _) who
  have htop : (I raise.succ who).1 ≤ (I 0 who).1 + 1 :=
    spernerSimplex_val_le_succ hs raise.succ 0 who
  have hcastEq : (I raise.castSucc who).1 = (I 0 who).1 := by omega
  have hmono : (I i who).1 ≤ (I raise.castSucc who).1 := by
    apply spernerSimplex_val_le_of_le hs
    rw [Fin.le_def]
    simpa [Fin.castSucc, Fin.castAdd, Fin.castLE] using hle
  have hlower : (I 0 who).1 ≤ (I i who).1 :=
    spernerSimplex_val_le_of_le hs (Fin.zero_le _) who
  omega

/-- After its raising step, a coordinate exceeds its initial value by one. -/
theorem spernerChain_val_eq_of_raiseIndex_lt (hs : simplex SC m I) (hm : m = SC.n)
    (who : Fin SC.n) {i : Fin (m + 1)}
    (hlt : (spernerChainRaiseIndex hs hm who : ℕ) < (i : ℕ)) :
    (I i who).1 = (I 0 who).1 + 1 := by
  set raise := spernerChainRaiseIndex hs hm who with hraise
  have hstep : spernerChainStep hs hm raise = who :=
    spernerChainStep_raiseIndex hs hm who
  have hsucc : (I raise.succ who).1 = (I raise.castSucc who).1 + 1 := by
    have := spernerChainStep_val_succ hs hm raise
    rwa [hstep] at this
  have hbase : (I 0 who).1 ≤ (I raise.castSucc who).1 :=
    spernerSimplex_val_le_of_le hs (Fin.zero_le _) who
  have htop : (I raise.succ who).1 ≤ (I 0 who).1 + 1 :=
    spernerSimplex_val_le_succ hs raise.succ 0 who
  have hmono : (I raise.succ who).1 ≤ (I i who).1 := by
    apply spernerSimplex_val_le_of_le hs
    rw [Fin.le_def]
    have hindex : (raise.succ : ℕ) = (raise : ℕ) + 1 := rfl
    omega
  have hceiling : (I i who).1 ≤ (I 0 who).1 + 1 :=
    spernerSimplex_val_le_succ hs i 0 who
  omega

/-- A coordinate keeps its initial value exactly up to its raising step. -/
theorem spernerChain_val_eq_base_iff (hs : simplex SC m I) (hm : m = SC.n)
    (who : Fin SC.n) (i : Fin (m + 1)) :
    (I i who).1 = (I 0 who).1 ↔
      (i : ℕ) ≤ (spernerChainRaiseIndex hs hm who : ℕ) := by
  constructor
  · intro hvalue
    by_contra hgt
    have hraised :=
      spernerChain_val_eq_of_raiseIndex_lt hs hm who (i := i) (by omega)
    omega
  · exact fun hle ↦ spernerChain_val_eq_of_le_raiseIndex hs hm who hle

end Math
