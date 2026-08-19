import Literature.Catalog

/-!
# Literature audit

Bibliography label: Oliu-Barton 2014

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.OliuBarton2014

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "oliu_barton_2014"
  bibliographyLabel := "Oliu-Barton 2014"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Oliu-Barton 2014"
  role := .zeroSumUniformValue
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.OliuBarton2014
