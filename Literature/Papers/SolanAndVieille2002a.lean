import Literature.Catalog
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingletonPeriodTwo

/-!
# Literature audit

Bibliography label: Solan & Vieille 2002a

The published four-player example was inspected. Its qualitative results and
the disputed primary continuation probability in its printed numerical packet
are recorded separately.
-/

namespace Literature.Papers.SolanAndVieille2002a

open GameTheory

/-- The numerical parameter assertion in the normalized transcription of the
printed period-two packet: its continuation probability `1 / √2` is the
unique primary parameter selected by the exact period-two equations for the
displayed table. -/
def PrintedPeriodTwoContinuationClaim : Prop :=
  FourPlayerPairedSingleton.periodTwoParameter = (Real.sqrt 2)⁻¹

/-- The printed continuation probability is not the exact primary parameter.
This refutes that scalar assertion, not the existence of period-two equilibria. -/
theorem not_printedPeriodTwoContinuationClaim :
    ¬ PrintedPeriodTwoContinuationClaim := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsquare : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hinvPos : 0 < (Real.sqrt 2)⁻¹ := inv_pos.mpr hsqrt
  have hinvSquare : ((Real.sqrt 2)⁻¹) ^ 2 = (1 : ℝ) / 2 := by
    rw [inv_pow, hsquare]
    norm_num
  have hinvLt : (Real.sqrt 2)⁻¹ < (37 : ℝ) / 50 := by
    by_contra h
    have hge : (37 : ℝ) / 50 ≤ (Real.sqrt 2)⁻¹ := le_of_not_gt h
    nlinarith
  intro hprinted
  have hselected :=
    FourPlayerPairedSingleton.thirtySeven_fiftieths_lt_periodTwoParameter
  rw [PrintedPeriodTwoContinuationClaim] at hprinted
  linarith

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2002a"
  bibliographyLabel := "Solan & Vieille 2002a"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2002a"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "no_stationary_equilibrium"
        sourceLocator := "Section 3.2"
        summary := "The example has no stationary limiting-average equilibrium."
        status := .sourceOnly },
      { claimId := "no_stationary_epsilon_equilibrium"
        sourceLocator := "Section 3.2"
        summary := "The example has no stationary epsilon-equilibrium for small errors."
        status := .sourceOnly },
      { claimId := "no_perturbed_epsilon_equilibrium"
        sourceLocator := "Section 3.3"
        summary := "The example excludes the perturbed epsilon-equilibrium fallback."
        status := .sourceOnly },
      { claimId := "no_solo_convex_hull_equilibrium_payoff"
        sourceLocator := "Section 3"
        summary := "No equilibrium payoff lies in the convex hull of the solo payoffs."
        status := .sourceOnly },
      { claimId := "printed_period_two_packet"
        sourceLocator := "Figure 2 and the period-two calculation"
        summary :=
          "The printed primary continuation probability is the exact selected parameter."
        status := .refutedInLean
          "Literature.Papers.SolanAndVieille2002a.PrintedPeriodTwoContinuationClaim"
          "Literature.Papers.SolanAndVieille2002a.\
not_printedPeriodTwoContinuationClaim" } ]

end Literature.Papers.SolanAndVieille2002a
