import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vieille 2000b

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Vieille2000b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vieille_2000b"
  bibliographyLabel := "Vieille 2000b"
  bibliographyLocator := "Published source: Vieille 2000b"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Vieille2000b
