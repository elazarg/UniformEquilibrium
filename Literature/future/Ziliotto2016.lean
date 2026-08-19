import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ziliotto 2016

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Ziliotto2016

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ziliotto_2016"
  bibliographyLabel := "Ziliotto 2016"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Ziliotto 2016"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Ziliotto2016
