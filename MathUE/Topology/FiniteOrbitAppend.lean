import MathUE.Topology.ExtendedOrbit

/-! # Finite correspondence orbits with retained subwords

Concatenation retains both original finite words, including their common
endpoint and zero-edge cases. Any real edge cost is exactly additive.
-/

noncomputable section

namespace Math.Topology

/-- Two finite correspondence orbits with a common endpoint concatenate. -/
theorem exists_appendFiniteOrbit_with_embeddings {X : Type*} {F : Correspondence X X}
    {A : Set X} {k l : ℕ} (z : Fin (k + 1) → X) (w : Fin (l + 1) → X)
    (hz : IsFiniteOrbit F z) (hw : IsFiniteOrbit F w)
    (hstitch : z ⟨k, Nat.lt_succ_self k⟩ = w 0)
    (hzA : ∀ i, z i ∈ A) (hwA : ∀ i, w i ∈ A) :
    ∃ c : Fin (k + l + 1) → X, c 0 = z 0 ∧ IsFiniteOrbit F c ∧
      (∀ i, c i ∈ A) ∧ c ⟨k + l, Nat.lt_succ_self (k + l)⟩ =
        w ⟨l, Nat.lt_succ_self l⟩ ∧
      (∀ i : Fin (k + 1), c ⟨i, by omega⟩ = z i) ∧
      (∀ i : Fin (l + 1), c ⟨k + i, by omega⟩ = w i) := by
  let c : Fin (k + l + 1) → X := fun i =>
    if h : (i : ℕ) ≤ k then z ⟨i, by omega⟩ else w ⟨(i : ℕ) - k, by omega⟩
  refine ⟨c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c]
  · intro i
    by_cases hik : (i : ℕ) < k
    · let iz : Fin k := ⟨i, hik⟩
      have hsource : c i.castSucc = z iz.castSucc := by
        dsimp only [c]
        simp only [Fin.val_castSucc]
        rw [dite_eq_left hik.le]
        apply congrArg z
        apply Fin.ext
        rfl
      have htarget : c i.succ = z iz.succ := by
        dsimp only [c]
        simp only [Fin.val_succ]
        rw [dite_eq_left (Nat.succ_le_iff.mpr hik)]
        apply congrArg z
        apply Fin.ext
        rfl
      rw [hsource, htarget]
      exact hz iz
    · have hki : k ≤ (i : ℕ) := Nat.le_of_not_gt hik
      by_cases hieq : (i : ℕ) = k
      · have hl0 : 0 < l := by omega
        let iw : Fin l := ⟨0, hl0⟩
        have hsource : c i.castSucc = z ⟨k, Nat.lt_succ_self k⟩ := by
          dsimp only [c]
          simp only [Fin.val_castSucc]
          rw [dite_eq_left (hieq.le)]
          apply congrArg z
          exact Fin.ext hieq
        have htarget : c i.succ = w iw.succ := by
          dsimp only [c]
          simp only [Fin.val_succ]
          rw [dite_eq_right (by omega)]
          apply congrArg w
          apply Fin.ext
          dsimp only [iw]
          simp only [Fin.val_succ]
          omega
        rw [hsource, htarget, hstitch]
        exact hw iw
      · have hkiStrict : k < (i : ℕ) := hki.lt_of_ne (Ne.symm hieq)
        let iw : Fin l := ⟨(i : ℕ) - k, by omega⟩
        have hsource : c i.castSucc = w iw.castSucc := by
          dsimp only [c]
          simp only [Fin.val_castSucc]
          rw [dite_eq_right (by omega)]
          apply congrArg w
          apply Fin.ext
          rfl
        have htarget : c i.succ = w iw.succ := by
          dsimp only [c]
          simp only [Fin.val_succ]
          rw [dite_eq_right (by omega)]
          apply congrArg w
          apply Fin.ext
          dsimp only [iw]
          simp only [Fin.val_succ]
          omega
        rw [hsource, htarget]
        exact hw iw
  · intro i
    by_cases hi : (i : ℕ) ≤ k
    · simpa only [c, dite_eq_left hi] using hzA ⟨i, by omega⟩
    · simpa only [c, dite_eq_right hi] using hwA ⟨(i : ℕ) - k, by omega⟩
  · by_cases hl : l = 0
    · subst l
      simpa [c] using hstitch
    · have hl0 : 0 < l := Nat.pos_of_ne_zero hl
      dsimp only [c]
      rw [dite_eq_right (by omega)]
      apply congrArg w
      apply Fin.ext
      simp
  · intro i
    dsimp only [c]
    rw [dite_eq_left (Nat.le_of_lt_succ i.isLt)]
  · intro i
    by_cases hi : (i : ℕ) = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simpa only [Fin.val_zero, Nat.add_zero, c, dite_eq_left le_rfl] using hstitch
    · dsimp only [c]
      rw [dite_eq_right (by omega)]
      apply congrArg w
      apply Fin.ext
      simp

/-- Signed edge costs add exactly when both original subwords are retained.
Neither positivity of the cost nor an orbit hypothesis is needed. -/
theorem finiteOrbitVariationWith_append_of_embeddings {X : Type*} {k l : ℕ}
    (cost : X → X → ℝ)
    (z : Fin (k + 1) → X) (w : Fin (l + 1) → X)
    (c : Fin (k + l + 1) → X)
    (hleft : ∀ i : Fin (k + 1), c ⟨i, by omega⟩ = z i)
    (hright : ∀ i : Fin (l + 1), c ⟨k + i, by omega⟩ = w i) :
    finiteOrbitVariationWith cost c =
      finiteOrbitVariationWith cost z + finiteOrbitVariationWith cost w := by
  rw [finiteOrbitVariationWith, Fin.sum_univ_add]
  change (∑ i : Fin k, cost (c (i.castAdd l).castSucc) (c (i.castAdd l).succ)) +
      (∑ i : Fin l, cost (c (i.natAdd k).castSucc) (c (i.natAdd k).succ)) =
    (∑ i : Fin k, cost (z i.castSucc) (z i.succ)) +
      ∑ i : Fin l, cost (w i.castSucc) (w i.succ)
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change cost (c ⟨(i.castSucc : ℕ), by omega⟩)
        (c ⟨(i.succ : ℕ), by omega⟩) = cost (z i.castSucc) (z i.succ)
    rw [hleft i.castSucc, hleft i.succ]
  · apply Finset.sum_congr rfl
    intro i _
    change cost (c ⟨k + (i.castSucc : ℕ), by omega⟩)
        (c ⟨k + (i.succ : ℕ), by omega⟩) = cost (w i.castSucc) (w i.succ)
    rw [hright i.castSucc, hright i.succ]

end Math.Topology
