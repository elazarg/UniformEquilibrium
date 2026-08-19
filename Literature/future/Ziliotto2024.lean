import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ziliotto 2024

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Ziliotto2024

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ziliotto_2024"
  bibliographyLabel := "Ziliotto 2024"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Ziliotto 2024"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Ziliotto2024
