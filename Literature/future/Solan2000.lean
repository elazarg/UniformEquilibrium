import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 2000

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Solan2000

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_2000"
  bibliographyLabel := "Solan 2000"
  bibliographyLocator := "Published source: Solan 2000"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Solan2000
