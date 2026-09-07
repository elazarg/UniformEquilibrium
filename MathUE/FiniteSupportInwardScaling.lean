import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sequences

/-! # Finite-support inward scaling on the closed cube -/

noncomputable section

namespace Math

open Filter

variable {ι : Type} [Fintype ι]

/-- Strict positivity of finitely many continuous tests on the positive
support persists after a common inward scaling that removes every upper-cube
boundary coordinate without changing the positive support. -/
theorem exists_inwardScale_preserving_positiveSupport_tests
    (q : ι → ℝ) (hq0 : ∀ player, 0 ≤ q player)
    (hq1 : ∀ player, q player ≤ 1)
    (test : ι → (ι → ℝ) → ℝ)
    (hcontinuous : ∀ player, ContinuousAt (test player) q)
    (hpositive : ∀ player, 0 < q player → 0 < test player q) :
    ∃ inward : ι → ℝ,
      (∀ player, 0 ≤ inward player) ∧
      (∀ player, inward player < 1) ∧
      (∀ player, 0 < inward player ↔ 0 < q player) ∧
      ∀ player, 0 < inward player → 0 < test player inward := by
  let scale : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  let inwardSequence : ℕ → ι → ℝ :=
    fun n player => scale n * q player
  have hscale : Tendsto scale atTop (nhds 1) := by
    have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [scale] using tendsto_const_nhds.sub hzero
  have hinward : Tendsto inwardSequence atTop (nhds q) := by
    rw [tendsto_pi_nhds]
    intro player
    simpa [inwardSequence] using hscale.mul_const (q player)
  have heventually : ∀ᶠ n in atTop, ∀ player,
      0 < q player → 0 < test player (inwardSequence n) := by
    apply Filter.eventually_all.mpr
    intro player
    by_cases hq : 0 < q player
    · exact ((hcontinuous player).tendsto.comp hinward).eventually
        (Ioi_mem_nhds (hpositive player hq)) |>.mono fun _ h => fun _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hq h).elim
  obtain ⟨n, htests, hn⟩ :=
    (heventually.and (eventually_ge_atTop (1 : ℕ))).exists
  have hscalePos : 0 < scale n := by
    dsimp only [scale]
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdenom : 0 < (n : ℝ) + 1 := by positivity
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hdenom]
      linarith
    have hfracStrict : 1 / ((n : ℝ) + 1) < 1 := by
      rw [div_lt_one hdenom]
      linarith
    linarith
  have hscaleLt : scale n < 1 := by
    dsimp only [scale]
    exact sub_lt_self 1 (by positivity)
  refine ⟨inwardSequence n, ?_, ?_, ?_, ?_⟩
  · intro player
    exact mul_nonneg hscalePos.le (hq0 player)
  · intro player
    nlinarith [hq0 player, hq1 player]
  · intro player
    simp only [inwardSequence]
    exact mul_pos_iff_of_pos_left hscalePos
  · intro player hplayer
    exact htests player
      ((mul_pos_iff_of_pos_left hscalePos).mp hplayer)

end Math
