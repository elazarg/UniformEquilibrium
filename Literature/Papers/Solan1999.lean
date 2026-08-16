import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 1999

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Solan1999

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_1999"
  bibliographyLabel := "Solan 1999"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan 1999"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Solan1999
