import Literature.Catalog

/-!
# Literature audit

Bibliography label: Coulomb 2003

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Coulomb2003

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "coulomb_2003"
  bibliographyLabel := "Coulomb 2003"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Coulomb 2003"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Coulomb2003
