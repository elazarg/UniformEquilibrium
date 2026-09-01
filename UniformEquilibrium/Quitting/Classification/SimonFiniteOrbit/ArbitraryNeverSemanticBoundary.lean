/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.CompactSpineSurvivalBoundary
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.PositiveRhoLandingCompactLimit

/-!
# The source-faithful semantic boundary of arbitrary-never extraction

Running the reached-prefix extraction at a support tolerance below both the
requested tolerance and the canonical compact scale gives one exhaustive
cross-scale alternative.  Either every scale supplies a literal low-survival
source, or one scale supplies a bounded support--Bellman spine at the requested
tolerance.  Combining the already checked consumers on both arms exposes the
remaining semantic residuals without postulating an adapter between them.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The canonical extraction error at a support scale no larger than the
compact scale is below the low-survival family's canonical error. -/
theorem quittingSimonExtractionAccuracy_le_compactAccuracy
    {M supportScale u : ℝ} (hM : 0 ≤ M) (hsupport : 0 < supportScale)
    {compactScale : ℝ} (hcompact : supportScale ≤ compactScale)
    (hu : 0 < u) (horizon : ℕ) :
    u * quittingSimonReachedPrefixThreshold supportScale *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) M supportScale horizon / 2 ≤
      u * compactScale ^ 2 / 2 := by
  let denominator : ℝ :=
    16 * (1 + 4 * M * (Fintype.card ι : ℝ) +
      2 * M * (Fintype.card ι : ℝ) * (horizon : ℝ))
  have hdenominator : 1 ≤ denominator := by
    dsimp only [denominator]
    have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
    have htime : 0 ≤ (horizon : ℝ) := by positivity
    nlinarith [mul_nonneg hM hcard,
      mul_nonneg (mul_nonneg hM hcard) htime]
  have hdisplacement :
      quittingSimonReachedPrefixDisplacement
          (ι := ι) M supportScale horizon ≤ supportScale := by
    unfold quittingSimonReachedPrefixDisplacement
    change supportScale / denominator ≤ supportScale
    exact div_le_self hsupport.le hdenominator
  have hthreshold : quittingSimonReachedPrefixThreshold supportScale =
      supportScale / 4 := rfl
  have hproduct :
      quittingSimonReachedPrefixThreshold supportScale *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) M supportScale horizon ≤ supportScale ^ 2 / 4 := by
    rw [hthreshold]
    have := mul_le_mul_of_nonneg_left hdisplacement
      (div_nonneg hsupport.le (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith
  have hsquare : supportScale ^ 2 ≤ compactScale ^ 2 := by
    have hcompactNonneg : 0 ≤ compactScale := hsupport.le.trans hcompact
    nlinarith [mul_nonneg (sub_nonneg.mpr hcompact)
      (add_nonneg hcompactNonneg hsupport.le)]
  have huHalf : 0 ≤ u / 2 := by positivity
  calc
    u * quittingSimonReachedPrefixThreshold supportScale *
          quittingSimonReachedPrefixDisplacement
            (ι := ι) M supportScale horizon / 2 =
        (u / 2) *
          (quittingSimonReachedPrefixThreshold supportScale *
            quittingSimonReachedPrefixDisplacement
              (ι := ι) M supportScale horizon) := by ring
    _ ≤ (u / 2) * (supportScale ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hproduct huHalf
    _ ≤ (u / 2) * compactScale ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ huHalf
      nlinarith [sq_nonneg supportScale, hsquare]
    _ = u * compactScale ^ 2 / 2 := by ring

/-- Increasing the Nash allowance preserves a literal low-survival source
without changing its roots, stage, or horizon. -/
theorem QuittingLowSurvivalApproximatePrefixAt.mono_accuracy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy accuracy' : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalApproximatePrefixAt
      reward u accuracy horizon)
    (hle : accuracy ≤ accuracy') :
    QuittingLowSurvivalApproximatePrefixAt reward u accuracy' horizon := by
  obtain ⟨roots, stage, hnash, hstage, hsurvival⟩ := source
  refine ⟨roots, stage, ?_, hstage, hsurvival⟩
  intro who hazard
  linarith [hnash who hazard]

namespace QuittingLCPClassification

/-- Across the canonical vanishing scales, arbitrary-never approximate
equilibrium existence gives either literal low-survival sources at every
scale or one bounded support--Bellman spine at the requested tolerance. -/
theorem
    QuittingPayoffTable.lowSurvivalAtCompactScales_or_boundedSupportBellmanSpine
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) :
    HasLowSurvivalPrefixesAtCompactScales table.zeroNeverReward u ∨
      ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
        (∀ time who,
          |value time who| ≤ quittingRewardBound table.zeroNeverReward) ∧
        (∀ time, value time = quittingRootSuccessorPayoff
          table.zeroNeverReward (value (time + 1)) (roots time)) ∧
        ∀ time, IsQuittingRootSupportApproxNash table.zeroNeverReward
          (value (time + 1)) δ (roots time) := by
  by_cases hlow : HasLowSurvivalPrefixesAtCompactScales
      table.zeroNeverReward u
  · exact Or.inl hlow
  · right
    simp only [HasLowSurvivalPrefixesAtCompactScales, not_forall,
      not_exists] at hlow
    obtain ⟨n, hn⟩ := hlow
    let compactScale := quittingLowSurvivalCompactScale n
    let supportScale := min compactScale (δ / 2)
    have hcompactPos : 0 < compactScale :=
      quittingLowSurvivalCompactScale_pos n
    have hsupportPos : 0 < supportScale := by
      dsimp only [supportScale]
      exact lt_min hcompactPos (half_pos hδ)
    have hsupportCompact : supportScale ≤ compactScale := min_le_left _ _
    have hsupportδ : supportScale ≤ δ := by
      exact (min_le_right _ _).trans (by linarith)
    rcases table.lowSurvivalPrefix_or_exists_boundedSupportBellmanSpine
        hequilibrium supportScale u hsupportPos hu with
      ⟨horizon, hpref⟩ | ⟨value, roots, hvalue, hbellman, hsupport⟩
    · exact False.elim (hn horizon (hpref.mono_accuracy
        (quittingSimonExtractionAccuracy_le_compactAccuracy
          (ι := ι) (quittingRewardBound_nonneg table.zeroNeverReward)
          hsupportPos hsupportCompact hu horizon)))
    · exact ⟨value, roots, hvalue, hbellman,
        fun time ↦ (hsupport time).mono hsupportδ⟩

/-- **Cross-wave semantic capstone.**  The arbitrary-never hypothesis now
reaches every checked consumer on both sides of the compact extraction.  At
one requested support tolerance the only unresolved outputs are the
positive-solo all-Continue phantom, the positive-absorption two-edge
attachment residual, and the positive-survival suffix defect. -/
theorem QuittingPayoffTable.semanticBoundary_of_approximateEquilibriumExistence
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ u : ℝ) (hδ : 0 < δ) (hu : 0 < u) (huOne : u < 1) :
    QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
      QuittingInstantPunishmentεEquilibriumExistence table.zeroNeverReward ∨
      (∃ payoff : Payoff ι,
        (quittingGame table.zeroNeverReward).IsUniformEquilibriumPayoff
          none payoff) ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom
        table.zeroNeverReward) ∨
      Nonempty (QuittingLowSurvivalPositiveAbsorptionAttachmentResidual
        table.zeroNeverReward u) ∨
      ∃ datum : QuittingSupportBellmanPositiveSurvivalBoundary
          table.zeroNeverReward δ,
        Nonempty datum.PositiveSingletonSuffixDefect := by
  rcases table.lowSurvivalAtCompactScales_or_boundedSupportBellmanSpine
      hequilibrium δ u hδ hu with hlow | ⟨value, roots, hvalue, hbellman, hsupport⟩
  · rcases
        instantPunishment_or_uniformPayoff_or_phantom_or_attachmentResidual_of_lowSurvivalPrefixes
          table.zeroNeverReward hu huOne hlow with
      hinstant | huniform | hphantom | hattachment
    · exact Or.inr (Or.inl hinstant)
    · exact Or.inr (Or.inr (Or.inl huniform))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hphantom)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hattachment))))
  · rcases
        quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary
          table.zeroNeverReward value roots δ hvalue hbellman hsupport with
      hwell | hboundary
    · exact Or.inl hwell
    · obtain ⟨datum⟩ := hboundary
      rcases
          datum.zero_isUniformEquilibriumPayoff_or_nonempty_positiveSingletonSuffixDefect
        with hzero | hdefect
      · exact Or.inr (Or.inr (Or.inl ⟨0, hzero⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨datum, hdefect⟩))))

/-- **Scale-free semantic boundary.**  Branch selection removes the displayed
support tolerance from `semanticBoundary_of_approximateEquilibriumExistence`.
If the well-supported absorbing branch does not hold at every positive scale,
one scale at which it fails feeds the pointwise theorem.  All other outputs
are scale-independent except for the retained positive-survival suffix datum.

This is still a boundary theorem, not AKRS Theorem 3.4: the uniform-payoff,
phantom, attachment, and suffix-defect outputs are not silently identified
with one of the paper's three branches. -/
theorem
    QuittingPayoffTable.globalSemanticBoundary_of_approximateEquilibriumExistence
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (u : ℝ) (hu : 0 < u) (huOne : u < 1) :
    QuittingWellSupportedAbsorbingSequenceExistence table.zeroNeverReward ∨
      QuittingInstantPunishmentεEquilibriumExistence table.zeroNeverReward ∨
      (∃ payoff : Payoff ι,
        (quittingGame table.zeroNeverReward).IsUniformEquilibriumPayoff
          none payoff) ∨
      Nonempty (QuittingLowSurvivalAllContinuePhantom
        table.zeroNeverReward) ∨
      Nonempty (QuittingLowSurvivalPositiveAbsorptionAttachmentResidual
        table.zeroNeverReward u) ∨
      ∃ δ : ℝ, 0 < δ ∧
        ∃ datum : QuittingSupportBellmanPositiveSurvivalBoundary
            table.zeroNeverReward δ,
          Nonempty datum.PositiveSingletonSuffixDefect := by
  by_cases hwell :
      QuittingWellSupportedAbsorbingSequenceExistence table.zeroNeverReward
  · exact Or.inl hwell
  · right
    rw [QuittingWellSupportedAbsorbingSequenceExistence] at hwell
    push Not at hwell
    obtain ⟨δ, hδ, hnoWell⟩ := hwell
    rcases table.semanticBoundary_of_approximateEquilibriumExistence
        hequilibrium δ u hδ hu huOne with
      hwellAt | hinstant | huniform | hphantom | hattachment | hboundary
    · obtain ⟨roots, habsorbing, hsupport⟩ := hwellAt
      exact False.elim (hnoWell roots habsorbing hsupport)
    · exact Or.inl hinstant
    · exact Or.inr (Or.inl huniform)
    · exact Or.inr (Or.inr (Or.inl hphantom))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hattachment)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨δ, hδ, hboundary⟩)))

end QuittingLCPClassification
end GameTheory
