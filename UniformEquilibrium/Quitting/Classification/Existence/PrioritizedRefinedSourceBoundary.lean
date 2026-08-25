/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveRhoLandingClassificationBoundary

/-!
# Priority-safe refined source boundary

A refined corrected-pointwise source residual can coexist with an already
available classified branch.  Consequently the residual should be retained
only after the four corrected pointwise branches have been given priority.

This file records the exact fixed-branch alternative with that priority.  If
none of the stationary, instant-punishment, well-supported absorbing, or
diffuse stationarily generated branches exists globally, then arbitrarily
small positive scales carry a refined source residual at which all four
pointwise branches fail.  This is a strictly sharper proof obligation than
unconditional nonexistence of every raw residual.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A refined source residual retained only after every corrected pointwise
classified branch has failed at the same scale. -/
structure QuittingPrioritizedRefinedSourceResidualAt
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (delta : ℝ) : Prop where
  residual : QuittingCorrectedPointwiseRefinedSourceResidualAt reward delta
  not_stationary : ¬QuittingStationaryεEquilibriumAt reward delta
  not_instant : ¬QuittingInstantPunishmentεEquilibriumAt reward delta
  not_wellSupported : ¬QuittingWellSupportedAbsorbingSequenceAt reward delta
  not_generated :
    ¬QuittingStationarilyGeneratedApproximateEquilibriaAt reward delta

namespace QuittingLCPClassification

/-- **Priority-safe corrected source boundary.**  The first four disjuncts
are the fixed corrected branches.  If all fail, refined source residuals
occur cofinally toward zero, and each retained residual is at a scale where
none of the four pointwise branches is available.

This conclusion follows from the checked arbitrary-Never source extraction;
it does not assume that refined residuals are globally impossible. -/
theorem
    QuittingPayoffTable.fixedCorrectedBranches_or_cofinally_prioritizedResidual
    (table : QuittingPayoffTable iota)
    (hequilibrium : table.ApproximateEquilibriumExistence) :
    QuittingStationaryεEquilibriumExistence table.zeroNeverReward ∨
      QuittingInstantPunishmentεEquilibriumExistence table.zeroNeverReward ∨
        QuittingWellSupportedAbsorbingSequenceExistence table.zeroNeverReward ∨
          QuittingDiffuseStationarilyGeneratedApproximateEquilibria
              table.zeroNeverReward ∨
            ∀ target : ℝ, 0 < target →
              ∃ delta : ℝ, 0 < delta ∧ delta ≤ target ∧
                QuittingPrioritizedRefinedSourceResidualAt
                  table.zeroNeverReward delta := by
  classical
  cases isEmpty_or_nonempty iota with
  | inl hempty =>
      left
      intro delta _hdelta
      refine ⟨fun who ↦ hempty.elim who, ?_⟩
      intro who
      exact hempty.elim who
  | inr hnonempty =>
      letI := hnonempty
      by_cases hstationary :
          QuittingStationaryεEquilibriumExistence table.zeroNeverReward
      · exact Or.inl hstationary
      right
      by_cases hinstant :
          QuittingInstantPunishmentεEquilibriumExistence table.zeroNeverReward
      · exact Or.inl hinstant
      right
      by_cases hwellSupported :
          QuittingWellSupportedAbsorbingSequenceExistence table.zeroNeverReward
      · exact Or.inl hwellSupported
      right
      by_cases hdiffuse :
          QuittingDiffuseStationarilyGeneratedApproximateEquilibria
            table.zeroNeverReward
      · exact Or.inl hdiffuse
      right
      have hgenerated :
          ¬QuittingStationarilyGeneratedApproximateEquilibria
            table.zeroNeverReward := by
        intro hgenerated
        rcases quittingInstant_or_diffuseStationarilyGenerated hgenerated with
          hinstant' | hdiffuse'
        · exact hinstant hinstant'
        · exact hdiffuse hdiffuse'
      rw [QuittingStationaryεEquilibriumExistence] at hstationary
      rw [QuittingInstantPunishmentεEquilibriumExistence] at hinstant
      rw [QuittingWellSupportedAbsorbingSequenceExistence] at hwellSupported
      rw [QuittingStationarilyGeneratedApproximateEquilibria] at hgenerated
      push Not at hstationary hinstant hwellSupported hgenerated
      obtain ⟨stationaryScale, hstationaryScale, hnoStationary⟩ := hstationary
      obtain ⟨instantScale, hinstantScale, hnoInstant⟩ := hinstant
      obtain ⟨wellSupportedScale, hwellSupportedScale, hnoWellSupported⟩ :=
        hwellSupported
      obtain ⟨generatedScale, hgeneratedScale, hnoGenerated⟩ := hgenerated
      intro target htarget
      let scale := min target
        (min stationaryScale
          (min instantScale (min wellSupportedScale generatedScale))) / 2
      have hscale : 0 < scale := by
        dsimp only [scale]
        positivity
      have hscaleTarget : scale ≤ target := by
        dsimp only [scale]
        have hmin : min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) ≤
            target := min_le_left _ _
        have hminPos : 0 < min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) := by
          positivity
        linarith
      have hscaleStationary : scale ≤ stationaryScale := by
        dsimp only [scale]
        have hmin : min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) ≤
            stationaryScale := (min_le_right _ _).trans (min_le_left _ _)
        have hminPos : 0 < min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) := by
          positivity
        linarith
      have hscaleInstant : scale ≤ instantScale := by
        dsimp only [scale]
        have hmin : min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) ≤
            instantScale := (min_le_right _ _).trans
              ((min_le_right _ _).trans (min_le_left _ _))
        have hminPos : 0 < min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) := by
          positivity
        linarith
      have hscaleWellSupported : scale ≤ wellSupportedScale := by
        dsimp only [scale]
        have hmin : min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) ≤
            wellSupportedScale := (min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_left _ _)))
        have hminPos : 0 < min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) := by
          positivity
        linarith
      have hscaleGenerated : scale ≤ generatedScale := by
        dsimp only [scale]
        have hmin : min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) ≤
            generatedScale := (min_le_right _ _).trans
              ((min_le_right _ _).trans
                ((min_le_right _ _).trans (min_le_right _ _)))
        have hminPos : 0 < min target
            (min stationaryScale
              (min instantScale (min wellSupportedScale generatedScale))) := by
          positivity
        linarith
      rcases table.correctedPointwiseAlternative_or_refinedSourceResidualAt
          hequilibrium scale hscale with
        hsmall | hsmall | hsmall | hsmall | hresidual
      · obtain ⟨root, hnash⟩ := hsmall.mono hscaleStationary
        exact False.elim (hnoStationary root hnash)
      · obtain ⟨quitter, root, punishment, hquitter, hcap, hnash⟩ :=
          hsmall.mono hscaleInstant
        exact False.elim
          (hnoInstant quitter root punishment hquitter hcap hnash)
      · obtain ⟨roots, habsorbing, hsupport⟩ :=
          hsmall.mono hscaleWellSupported
        exact False.elim (hnoWellSupported roots habsorbing hsupport)
      · exact False.elim (hnoGenerated (hsmall.mono hscaleGenerated))
      · refine ⟨scale, hscale, hscaleTarget, {
          residual := hresidual
          not_stationary := ?_
          not_instant := ?_
          not_wellSupported := ?_
          not_generated := ?_ }⟩
        · intro hsmall
          obtain ⟨root, hnash⟩ := hsmall.mono hscaleStationary
          exact hnoStationary root hnash
        · intro hsmall
          obtain ⟨quitter, root, punishment, hquitter, hcap, hnash⟩ :=
            hsmall.mono hscaleInstant
          exact hnoInstant quitter root punishment hquitter hcap hnash
        · intro hsmall
          obtain ⟨roots, habsorbing, hsupport⟩ :=
            hsmall.mono hscaleWellSupported
          exact hnoWellSupported roots habsorbing hsupport
        · intro hsmall
          exact hnoGenerated (hsmall.mono hscaleGenerated)

end QuittingLCPClassification
end GameTheory
