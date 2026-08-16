import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vigeral 2013

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.Vigeral2013

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vigeral_2013"
  bibliographyLabel := "Vigeral 2013"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Vigeral 2013"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.Vigeral2013
