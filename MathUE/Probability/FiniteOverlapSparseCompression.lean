import MathUE.Probability.FiniteOverlapSparseMaximizer

/-! # Finite overlapping-event feasibility reduces to two-supported clocks -/

noncomputable section

namespace Math
namespace Probability

open DiscreteHazard.StoppingLaw

/-- Compression applies to the supplied canonical stopping laws themselves,
on their fixed finite menu of dates and literal Never. The first overlap mass
is unchanged, while the second may increase; both are not asserted unchanged. -/
theorem exists_twoSupported_canonicalOverlap_compression_on_dates
    (dates : Finset ℕ) (first second third : PMF (Option ℕ))
    (hfirst : first.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)))
    (hsecond : second.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)))
    (hthird : third.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ))) :
    ∃ nextFirst nextSecond nextThird : PMF (Option ℕ),
      nextFirst.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      nextSecond.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      nextThird.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      nextFirst.support.ncard ≤ 2 ∧ nextSecond.support.ncard ≤ 2 ∧
      nextThird.support.ncard ≤ 2 ∧
      equalFirstSecondBeforeThirdMass nextFirst nextSecond nextThird =
        equalFirstSecondBeforeThirdMass first second third ∧
      equalFirstThirdBeforeSecondMass first second third ≤
        equalFirstThirdBeforeSecondMass nextFirst nextSecond nextThird := by
  classical
  let embedding : dates ↪o ℕ := OrderEmbedding.subtype _
  have hrange : Set.range (Option.map embedding) =
      (↑(insert none (dates.image some)) : Set (Option ℕ)) := by
    ext choice
    constructor
    · rintro ⟨source, rfl⟩
      cases source with
      | none => simp
      | some time => simp [embedding, time.property]
    · intro hchoice
      rcases Finset.mem_insert.mp hchoice with rfl | hchoice
      · exact ⟨none, rfl⟩
      · obtain ⟨time, htime, rfl⟩ := Finset.mem_image.mp hchoice
        exact ⟨some ⟨time, htime⟩, rfl⟩
  rw [← hrange] at hfirst hsecond hthird ⊢
  obtain ⟨sourceFirst, rfl⟩ :=
    exists_law_map_dateEmbedding_of_support_subset embedding first hfirst
  obtain ⟨sourceSecond, rfl⟩ :=
    exists_law_map_dateEmbedding_of_support_subset embedding second hsecond
  obtain ⟨sourceThird, rfl⟩ :=
    exists_law_map_dateEmbedding_of_support_subset embedding third hthird
  obtain ⟨nextFirst, nextSecond, nextThird, hcFirst, hcSecond, hcThird, heq, hle⟩ :=
    exists_three_twoSupported_pmf_preserving_first_improving_second
      finiteOverlapFirstKernel (fun i j k => finiteOverlapFirstKernel i k j)
      sourceFirst sourceSecond sourceThird
  have hsupport (law : PMF (Option dates)) :
      (law.map (Option.map embedding)).support ⊆ Set.range (Option.map embedding) := by
    rw [PMF.support_map]
    exact Set.image_subset_range _ _
  refine ⟨nextFirst.map (Option.map embedding), nextSecond.map (Option.map embedding),
    nextThird.map (Option.map embedding), hsupport nextFirst, hsupport nextSecond,
    hsupport nextThird, (support_ncard_map_dateEmbedding embedding nextFirst).trans_le hcFirst,
    (support_ncard_map_dateEmbedding embedding nextSecond).trans_le hcSecond,
    (support_ncard_map_dateEmbedding embedding nextThird).trans_le hcThird, ?_, ?_⟩
  · simpa only [equalFirstSecondBeforeThirdMass_map_dateEmbedding,
      finiteOverlapFirstMass] using heq
  · simpa only [equalFirstThirdBeforeSecondMass_map_dateEmbedding,
      finiteOverlapSecondMass] using hle

/-- Simultaneous lower thresholds for the two canonical overlap events are
feasible on a finite date menu exactly when feasible with two-supported
independent marginals. There is no constraint on the signs of the thresholds. -/
theorem canonicalOverlap_threshold_feasible_iff_twoSupported
    (dates : Finset ℕ) (lowerFirst lowerSecond : ℝ) :
    (∃ first second third : PMF (Option ℕ),
      first.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      second.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      third.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      lowerFirst ≤ equalFirstSecondBeforeThirdMass first second third ∧
      lowerSecond ≤ equalFirstThirdBeforeSecondMass first second third) ↔
    ∃ first second third : PMF (Option ℕ),
      first.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      second.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      third.support ⊆ (↑(insert none (dates.image some)) : Set (Option ℕ)) ∧
      first.support.ncard ≤ 2 ∧ second.support.ncard ≤ 2 ∧ third.support.ncard ≤ 2 ∧
      lowerFirst ≤ equalFirstSecondBeforeThirdMass first second third ∧
      lowerSecond ≤ equalFirstThirdBeforeSecondMass first second third := by
  constructor
  · rintro ⟨first, second, third, hfirst, hsecond, hthird, hA, hB⟩
    obtain ⟨nextFirst, nextSecond, nextThird, hnFirst, hnSecond, hnThird,
      hcFirst, hcSecond, hcThird, heq, hle⟩ :=
      exists_twoSupported_canonicalOverlap_compression_on_dates
        dates first second third hfirst hsecond hthird
    exact ⟨nextFirst, nextSecond, nextThird, hnFirst, hnSecond, hnThird,
      hcFirst, hcSecond, hcThird, heq.symm ▸ hA, hB.trans hle⟩
  · rintro ⟨first, second, third, hfirst, hsecond, hthird, _, _, _, hA, hB⟩
    exact ⟨first, second, third, hfirst, hsecond, hthird, hA, hB⟩

end Probability
end Math
