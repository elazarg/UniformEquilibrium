import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault 2011

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Renault2011

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_2011"
  bibliographyLabel := "Renault 2011"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Renault 2011"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Renault2011
