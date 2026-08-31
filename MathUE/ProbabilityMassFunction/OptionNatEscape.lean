import MathUE.ProbabilityMassFunction.GeneralTotalVariation

/-!
# Escape of probability mass on `Option Nat`

If every fixed finite atom of a sequence of stopping laws vanishes and the
cemetery masses converge, then the overlap with any fixed law converges to
the overlap of the two cemetery masses.  This statement is purely about
countable probability mass functions.
-/

noncomputable section

open Filter Topology

namespace Math
namespace Probability

/-- Vanishing finite coordinates leave only the limiting common mass at
`none` in the overlap with a fixed law. -/
theorem pmfGeneralTV_tendsto_one_sub_min_of_finiteCoordinates_tendsto_zero
    (laws : ℕ → PMF (Option ℕ)) (fixed : PMF (Option ℕ)) (neverLimit : ℝ)
    (hfinite : ∀ time : ℕ,
      Tendsto (fun index => (laws index (some time)).toReal) atTop (𝓝 0))
    (hnever : Tendsto (fun index => (laws index none).toReal) atTop
      (𝓝 neverLimit)) :
    Tendsto (fun index => pmfGeneralTV (laws index) fixed) atTop
      (𝓝 (1 - min neverLimit (fixed none).toReal)) := by
  let limitingOverlap : Option ℕ → ℝ
    | none => min neverLimit (fixed none).toReal
    | some _ => 0
  have hoverlap : ∀ state : Option ℕ,
      Tendsto
        (fun index => min (laws index state).toReal (fixed state).toReal)
        atTop (𝓝 (limitingOverlap state)) := by
    intro state
    cases state with
    | none =>
        exact hnever.min tendsto_const_nhds
    | some time =>
        have hfixed :
            Tendsto (fun _ : ℕ => (fixed (some time)).toReal) atTop
              (𝓝 (fixed (some time)).toReal) := tendsto_const_nhds
        simpa [limitingOverlap, min_eq_left ENNReal.toReal_nonneg] using
          (hfinite time).min hfixed
  have hsum : Summable (fun state : Option ℕ => (fixed state).toReal) :=
    pmf_toReal_summable fixed
  have htendsto := tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun index state =>
      min (laws index state).toReal (fixed state).toReal)
    (g := limitingOverlap)
    (bound := fun state => (fixed state).toReal)
    hsum hoverlap
    (Eventually.of_forall fun _ state => by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact min_le_right _ _
      · exact le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hlimitingTsum :
      ∑' state : Option ℕ, limitingOverlap state =
        min neverLimit (fixed none).toReal := by
    rw [tsum_eq_single none]
    intro state hstate
    cases state with
    | none => exact (hstate rfl).elim
    | some time => simp [limitingOverlap]
  unfold pmfGeneralTV
  simpa [hlimitingTsum] using tendsto_const_nhds.sub htendsto

/-- If every law has zero cemetery mass and every fixed finite coordinate
vanishes, its general total variation from every fixed law tends to one. -/
theorem pmfGeneralTV_tendsto_one_of_finiteCoordinates_tendsto_zero_of_never_eq_zero
    (laws : ℕ → PMF (Option ℕ)) (fixed : PMF (Option ℕ))
    (hfinite : ∀ time : ℕ,
      Tendsto (fun index => (laws index (some time)).toReal) atTop (𝓝 0))
    (hnever : ∀ index, (laws index none).toReal = 0) :
    Tendsto (fun index => pmfGeneralTV (laws index) fixed) atTop (𝓝 1) := by
  have hneverTendsto :
      Tendsto (fun index => (laws index none).toReal) atTop (𝓝 0) := by
    simpa only [hnever] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa using
    pmfGeneralTV_tendsto_one_sub_min_of_finiteCoordinates_tendsto_zero
      laws fixed 0 hfinite hneverTendsto

end Probability
end Math
