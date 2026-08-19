import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2015

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.SolanAndVieille2015

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2015"
  bibliographyLabel := "Solan & Vieille 2015"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2015"
  role := .surveys
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndVieille2015
