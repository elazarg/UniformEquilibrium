import Literature.Catalog

/-!
# Literature audit

Bibliography label: Renault 2019

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Renault2019

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "renault_2019"
  bibliographyLabel := "Renault 2019"
  bibliographyLocator := "Published source: Renault 2019"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Renault2019
