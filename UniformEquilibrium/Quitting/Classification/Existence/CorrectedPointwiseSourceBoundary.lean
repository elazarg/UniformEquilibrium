/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.AGKRSTheorem34Dependencies
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.ArbitraryNeverSemanticBoundary

/-!
# Actual-source boundary for the corrected pointwise extraction

Dependency A in the AGKRS classification asks for a stationary,
instant-punishment, well-supported absorbing, or stationarily generated
witness at each positive error.  The arbitrary-Never hypothesis reaches two
of these outputs directly.  The only remaining outputs of the checked
reached-prefix compactification are concrete source objects: a positive-rho
low-survival landing family or a bounded support--Bellman spine with positive
suffix survival.

The decomposition below retains those objects rather than replacing them by
uniform-payoff existence.  The latter follows independently from the original
approximate-equilibrium hypothesis and therefore does not select any of the
four classified forms.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The two actual-source residuals left by the checked pointwise
compactification at tolerance `δ`.  The low-survival scale is fixed at
`1 / 2`; no conclusion or prospective adapter is stored in this predicate. -/
def QuittingCorrectedPointwiseSourceResidualAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) : Prop :=
  Nonempty (QuittingLowSurvivalPositiveRhoLandingFamily reward (1 / 2)) ∨
    Nonempty (QuittingSupportBellmanPositiveSurvivalBoundary reward δ)

namespace QuittingLCPClassification

/-- **Source-faithful pointwise boundary for Dependency A.**  Arbitrary-Never
behavioral approximate equilibria give the instant branch, the
well-supported absorbing branch, or one of the two literal source residuals.

The theorem keeps the positive-rho landing family and the positive-survival
support--Bellman spine intact.  It does not use the logically weaker fact that
the hypothesis already selects some uniform payoff. -/
theorem QuittingPayoffTable.instant_or_wellSupported_or_correctedSourceResidualAt
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ : ℝ) (hδ : 0 < δ) :
    QuittingInstantPunishmentεEquilibriumAt table.zeroNeverReward δ ∨
      QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
        QuittingCorrectedPointwiseSourceResidualAt
          table.zeroNeverReward δ := by
  rcases table.lowSurvivalAtCompactScales_or_boundedSupportBellmanSpine
      hequilibrium δ (1 / 2) hδ (by norm_num) with
    hlow | ⟨value, roots, hvalue, hbellman, hsupport⟩
  · rcases
        instantPunishmentExistence_or_positiveRhoLandingFamily_of_lowSurvivalPrefixes
          table.zeroNeverReward (by norm_num) (by norm_num) hlow with
      hinstant | hlanding
    · exact Or.inl (hinstant δ hδ)
    · exact Or.inr (Or.inr (Or.inl hlanding))
  · rcases
        quittingWellSupportedAbsorbingSequenceAt_or_exists_positiveSurvivalBoundary
          table.zeroNeverReward value roots δ hvalue hbellman hsupport with
      hwellSupported | hboundary
    · exact Or.inr (Or.inl hwellSupported)
    · exact Or.inr (Or.inr (Or.inr hboundary))

/-- The exact corrected four-way pointwise alternative, with only the two
actual-source residuals appended.  The stationary and stationarily generated
disjuncts are displayed to make the remaining distance to Dependency A
literal; the checked extraction already lands in the middle two disjuncts
whenever no source residual remains. -/
theorem QuittingPayoffTable.correctedPointwiseAlternative_or_sourceResidualAt
    [Nonempty ι]
    (table : QuittingPayoffTable ι)
    (hequilibrium : table.ApproximateEquilibriumExistence)
    (δ : ℝ) (hδ : 0 < δ) :
    QuittingStationaryεEquilibriumAt table.zeroNeverReward δ ∨
      QuittingInstantPunishmentεEquilibriumAt table.zeroNeverReward δ ∨
        QuittingWellSupportedAbsorbingSequenceAt table.zeroNeverReward δ ∨
          QuittingStationarilyGeneratedApproximateEquilibriaAt
            table.zeroNeverReward δ ∨
            QuittingCorrectedPointwiseSourceResidualAt
              table.zeroNeverReward δ := by
  rcases table.instant_or_wellSupported_or_correctedSourceResidualAt
      hequilibrium δ hδ with hinstant | hwellSupported | hresidual
  · exact Or.inr (Or.inl hinstant)
  · exact Or.inr (Or.inr (Or.inl hwellSupported))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hresidual)))

/-- Excluding the two concrete source residuals at every scale closes
Dependency A.  Unlike a supplied four-way selector, the premise only rules
out objects produced unconditionally by the reached-prefix extraction. -/
theorem QuittingPayoffTable.hasCorrectedPointwiseFourWayExtraction_of_noSourceResidual
    (table : QuittingPayoffTable ι)
    (hnoResidual : ∀ δ : ℝ, 0 < δ →
      ¬QuittingCorrectedPointwiseSourceResidualAt
        table.zeroNeverReward δ) :
    table.HasCorrectedPointwiseFourWayExtraction := by
  intro hequilibrium δ hδ
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      left
      refine ⟨fun who => hempty.elim who, ?_⟩
      intro who
      exact hempty.elim who
  | inr hnonempty =>
      letI := hnonempty
      rcases table.correctedPointwiseAlternative_or_sourceResidualAt
          hequilibrium δ hδ with
        hstationary | hinstant | hwellSupported | hgenerated | hresidual
      · exact Or.inl hstationary
      · exact Or.inr (Or.inl hinstant)
      · exact Or.inr (Or.inr (Or.inl hwellSupported))
      · exact Or.inr (Or.inr (Or.inr hgenerated))
      · exact False.elim (hnoResidual δ hδ hresidual)

end QuittingLCPClassification
end GameTheory
