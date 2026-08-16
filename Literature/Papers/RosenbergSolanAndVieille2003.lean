import Literature.Catalog

/-!
# Literature audit

Bibliography label: Rosenberg, Solan & Vieille 2003

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.RosenbergSolanAndVieille2003

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "rosenberg_solan_and_vieille_2003"
  bibliographyLabel := "Rosenberg, Solan & Vieille 2003"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Rosenberg, Solan & Vieille 2003"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.RosenbergSolanAndVieille2003
