import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-! # A common positive parameter for finitely many strict inequalities -/

noncomputable section
namespace Math

open Filter

variable {ι : Type} [Fintype ι]

theorem exists_pos_lt_one_forall_mem_Ioo_of_continuousAt
    (f : ι → ℝ → ℝ) (lower upper : ι → ℝ)
    (hcontinuous : ∀ i, ContinuousAt (f i) 0)
    (hzero : ∀ i, f i 0 ∈ Set.Ioo (lower i) (upper i)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ∀ i, f i t ∈ Set.Ioo (lower i) (upper i) := by
  let sequence : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hsequence : Tendsto sequence atTop (nhds 0) := by
    simpa [sequence] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0))
  have heventually : ∀ᶠ n in atTop,
      ∀ i, f i (sequence n) ∈ Set.Ioo (lower i) (upper i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hcontinuous i).tendsto.comp hsequence).eventually
      (isOpen_Ioo.mem_nhds (hzero i))
  obtain ⟨n, hn, hone⟩ :=
    (heventually.and (eventually_ge_atTop (1 : ℕ))).exists
  refine ⟨sequence n, ?_, ?_, hn⟩
  · dsimp only [sequence]
    exact one_div_pos.mpr (by positivity)
  · dsimp only [sequence]
    rw [div_lt_one]
    · have : (1 : ℕ) < n + 1 := by omega
      exact_mod_cast this
    · positivity

end Math
