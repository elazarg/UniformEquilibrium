import Literature.Catalog

/-!
# Literature audit

Bibliography label: Munk & Solan 2020

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.MunkAndSolan2020

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "munk_and_solan_2020"
  bibliographyLabel := "Munk & Solan 2020"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Munk & Solan 2020"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.MunkAndSolan2020
