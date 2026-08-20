import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vieille 2000a

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.Vieille2000a

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vieille_2000a"
  bibliographyLabel := "Vieille 2000a"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Vieille 2000a"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Vieille2000a
