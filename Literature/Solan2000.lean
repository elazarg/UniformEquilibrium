import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 2000

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Solan2000

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_2000"
  bibliographyLabel := "Solan 2000"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan 2000"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Solan2000
