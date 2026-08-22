/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence

/-!
# The corrected fixed-branch boundary for quitting games

Simon (2012) corrects the residual in the 2007 classification from stationary
to stationarily generated approximate equilibria.  Consequently a pointwise
structured extraction has four semantic outputs, not three: stationary,
instant punishment, well-supported absorption, or stationarily generated.

The theorem below performs only the exact finite-branch compactification that
is currently justified.  In the fourth branch it uses
`quittingInstant_or_diffuseStationarilyGenerated` to remove sure first-stage
roots.  What remains retains a positive live mass, the finite repeated-root
horizon, the actual behavioral punishment cap, and the global deviation
inequality.  Eliminating this fourth branch requires an additional theorem
turning those diffuse finite-prefix witnesses into one of the first or third
branches; it is not a consequence of branch selection alone.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A pointwise four-way semantic alternative has one fixed branch at every
positive scale.  The corrected stationarily generated branch either compiles
to `S.2` or leaves the explicit positive-live-mass residual.

This is the fixed-branch consumer for a future Solan--Vieille extraction
theorem.  Its pointwise premise is displayed rather than hidden in a named
claim, so this declaration does not assert that arbitrary approximate
equilibria already supply the alternative. -/
theorem fixedCorrectedQuittingBranch_of_pointwiseAlternative
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hpointwise : ∀ ε : ℝ, 0 < ε →
      QuittingStationaryεEquilibriumAt reward ε ∨
        QuittingInstantPunishmentεEquilibriumAt reward ε ∨
          QuittingWellSupportedAbsorbingSequenceAt reward ε ∨
            QuittingStationarilyGeneratedApproximateEquilibriaAt reward ε) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward ∨
          QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward := by
  classical
  by_cases hstationary : QuittingStationaryεEquilibriumExistence reward
  · exact Or.inl hstationary
  right
  by_cases hinstant : QuittingInstantPunishmentεEquilibriumExistence reward
  · exact Or.inl hinstant
  right
  by_cases hsequential : QuittingWellSupportedAbsorbingSequenceExistence reward
  · exact Or.inl hsequential
  right
  have hnoInstantBranch := hinstant
  rw [QuittingStationaryεEquilibriumExistence] at hstationary
  rw [QuittingInstantPunishmentεEquilibriumExistence] at hinstant
  rw [QuittingWellSupportedAbsorbingSequenceExistence] at hsequential
  push Not at hstationary hinstant hsequential
  have hgenerated :
      QuittingStationarilyGeneratedApproximateEquilibria reward := by
    intro δ hδ
    obtain ⟨stationaryScale, hstationaryScale, hnoStationary⟩ := hstationary
    obtain ⟨instantScale, hinstantScale, hnoInstant⟩ := hinstant
    obtain ⟨sequentialScale, hsequentialScale, hnoSequential⟩ := hsequential
    let scale := min δ (min stationaryScale (min instantScale sequentialScale)) / 2
    have hscale : 0 < scale := by
      dsimp only [scale]
      positivity
    have hscaleδ : scale ≤ δ := by
      dsimp only [scale]
      have hmin : min δ (min stationaryScale (min instantScale sequentialScale)) ≤ δ :=
        min_le_left _ _
      have hminPos :
          0 < min δ (min stationaryScale (min instantScale sequentialScale)) := by
        positivity
      linarith
    have hscaleStationary : scale ≤ stationaryScale := by
      dsimp only [scale]
      have hmin : min δ (min stationaryScale (min instantScale sequentialScale)) ≤
          stationaryScale :=
        (min_le_right _ _).trans (min_le_left _ _)
      have hminPos :
          0 < min δ (min stationaryScale (min instantScale sequentialScale)) := by
        positivity
      linarith
    have hscaleInstant : scale ≤ instantScale := by
      dsimp only [scale]
      have hmin : min δ (min stationaryScale (min instantScale sequentialScale)) ≤
          instantScale :=
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _))
      have hminPos :
          0 < min δ (min stationaryScale (min instantScale sequentialScale)) := by
        positivity
      linarith
    have hscaleSequential : scale ≤ sequentialScale := by
      dsimp only [scale]
      have hmin : min δ (min stationaryScale (min instantScale sequentialScale)) ≤
          sequentialScale :=
        (min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_right _ _))
      have hminPos :
          0 < min δ (min stationaryScale (min instantScale sequentialScale)) := by
        positivity
      linarith
    rcases hpointwise scale hscale with
      hsmall | hsmall | hsmall | hsmall
    · obtain ⟨root, hnash⟩ := hsmall.mono hscaleStationary
      exact False.elim (hnoStationary root hnash)
    · obtain ⟨quitter, root, punishRow, hquitter, hcap, hnash⟩ :=
        hsmall.mono hscaleInstant
      exact False.elim
        (hnoInstant quitter root punishRow hquitter hcap hnash)
    · obtain ⟨roots, habsorb, hsupport⟩ := hsmall.mono hscaleSequential
      exact False.elim (hnoSequential roots habsorb hsupport)
    · exact hsmall.mono hscaleδ
  rcases quittingInstant_or_diffuseStationarilyGenerated hgenerated with
    hinstant' | hdiffuse
  · exact False.elim (hnoInstantBranch hinstant')
  · exact hdiffuse

/-- The exact additional compactification needed to recover the familiar
three-way conclusion is a producer sending the diffuse stationarily
generated residual to either the stationary branch or the well-supported
absorbing branch.  No implication to the instant branch is needed: sure
first-stage roots were already compiled to `S.2` above. -/
theorem fixedThreeQuittingBranches_of_pointwiseAlternative_of_diffuseCompactification
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hpointwise : ∀ ε : ℝ, 0 < ε →
      QuittingStationaryεEquilibriumAt reward ε ∨
        QuittingInstantPunishmentεEquilibriumAt reward ε ∨
          QuittingWellSupportedAbsorbingSequenceAt reward ε ∨
            QuittingStationarilyGeneratedApproximateEquilibriaAt reward ε)
    (hcompactify : QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward →
      QuittingStationaryεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward := by
  rcases fixedCorrectedQuittingBranch_of_pointwiseAlternative hpointwise with
    hstationary | hinstant | hsequential | hdiffuse
  · exact Or.inl hstationary
  · exact Or.inr (Or.inl hinstant)
  · exact Or.inr (Or.inr hsequential)
  · rcases hcompactify hdiffuse with hstationary | hsequential
    · exact Or.inl hstationary
    · exact Or.inr (Or.inr hsequential)

end GameTheory
