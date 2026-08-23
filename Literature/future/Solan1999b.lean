import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan 1999b

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Solan1999b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_1999b"
  bibliographyLabel := "Solan 1999b"
  bibliographyLocator := "Published source: Solan 1999b"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Solan1999b
