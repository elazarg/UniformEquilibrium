import Literature.Catalog

/-!
# Literature audit

Bibliography label: Vieille 2000c

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Vieille2000c

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "vieille_2000c"
  bibliographyLabel := "Vieille 2000c"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Vieille 2000c"
  role := .nonzeroSumExistence
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Vieille2000c
