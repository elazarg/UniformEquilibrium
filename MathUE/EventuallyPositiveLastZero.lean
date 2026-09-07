import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # The last zero of an eventually positive sequence -/

namespace Math

open Filter

/-- A nonnegative real sequence which is eventually positive and vanishes
at least once has a last zero. -/
theorem exists_last_zero_of_eventually_positive
    (value : ℕ → ℝ) (hnonneg : ∀ depth, 0 ≤ value depth)
    (heventually : ∀ᶠ depth in atTop, 0 < value depth)
    (hexists : ∃ depth, value depth = 0) :
    ∃ last, value last = 0 ∧ ∀ depth, last < depth → 0 < value depth := by
  rw [eventually_atTop] at heventually
  obtain ⟨cutoff, hcutoff⟩ := heventually
  let zeros := (Finset.range cutoff).filter fun depth => value depth = 0
  have hzeroBefore : ∀ {depth}, value depth = 0 → depth < cutoff := by
    intro depth hzero
    by_contra hnotLt
    have hpositive := hcutoff depth (by omega)
    linarith
  have hzerosNonempty : zeros.Nonempty := by
    obtain ⟨depth, hdepth⟩ := hexists
    exact ⟨depth, by simp [zeros, hzeroBefore hdepth, hdepth]⟩
  let last := zeros.max' hzerosNonempty
  refine ⟨last, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (zeros.max'_mem hzerosNonempty)).2
  · intro depth hlast
    by_cases hzero : value depth = 0
    · have hdepthMem : depth ∈ zeros := by
        simp [zeros, hzeroBefore hzero, hzero]
      have hle := Finset.le_max' zeros depth hdepthMem
      exact False.elim (by omega)
    · exact lt_of_le_of_ne (hnonneg depth) (Ne.symm hzero)

end Math
