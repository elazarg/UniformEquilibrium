import Literature.Catalog

/-!
# Literature audit

Bibliography label: Oliu-Barton 2014

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.OliuBarton2014

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "oliu_barton_2014"
  bibliographyLabel := "Oliu-Barton 2014"
  bibliographyLocator := "Published source: Oliu-Barton 2014"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.OliuBarton2014
