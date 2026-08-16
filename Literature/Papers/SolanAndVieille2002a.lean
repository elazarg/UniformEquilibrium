import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2002a

The published four-player example was inspected. Its qualitative results and
its disputed printed numerical packet are recorded separately.
-/

namespace Literature.Papers.SolanAndVieille2002a

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2002a"
  bibliographyLabel := "Solan & Vieille 2002a"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2002a"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "four_player_fallback_collapse"
        sourceLocator := "Section 3"
        summary := "The example excludes the stationary and perturbed fallback classes."
        status := .sourceOnly },
      { claimId := "printed_period_two_packet"
        sourceLocator := "Figure 2 and the period-two calculation"
        summary := "The paper prints a specific period-two packet and payoff vector."
        status := .sourceOnly } ]

end Literature.Papers.SolanAndVieille2002a
