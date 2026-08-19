import Literature.Catalog

/-!
# Literature audit

Bibliography label: Rosenberg, Solan & Vieille 2002

The primary paper supplies the source statement recorded below.
-/

namespace Literature.RosenbergSolanAndVieille2002

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "rosenberg_solan_and_vieille_2002"
  bibliographyLabel := "Rosenberg, Solan & Vieille 2002"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Rosenberg, Solan & Vieille 2002"
  role := .zeroSumBoundary
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "pomdp_uniform_expected_average_value"
        sourceLocator := "Theorem 1"
        summary := "Every finite POMDP has a uniform expected-average value."
        status := .sourceOnly } ]

end Literature.RosenbergSolanAndVieille2002
