import Literature.Catalog

/-!
# Literature audit

Bibliography label: Venel & Ziliotto 2016

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.VenelAndZiliotto2016

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "venel_and_ziliotto_2016"
  bibliographyLabel := "Venel & Ziliotto 2016"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Venel & Ziliotto 2016"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.VenelAndZiliotto2016
