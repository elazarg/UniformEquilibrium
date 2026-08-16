import Literature.Catalog

/-!
# Literature audit

Bibliography label: Venel & Ziliotto 2016

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.VenelAndZiliotto2016

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "venel_and_ziliotto_2016"
  bibliographyLabel := "Venel & Ziliotto 2016"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Venel & Ziliotto 2016"
  role := .zeroSumBoundary
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.VenelAndZiliotto2016
