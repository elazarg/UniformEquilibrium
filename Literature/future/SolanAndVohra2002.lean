import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vohra 2002

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SolanAndVohra2002

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vohra_2002"
  bibliographyLabel := "Solan & Vohra 2002"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vohra 2002"
  role := .nonzeroSumExistence
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndVohra2002
