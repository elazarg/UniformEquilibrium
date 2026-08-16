import Literature.Catalog

/-!
# Literature audit

Bibliography label: Flesch & Solan 2023

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.FleschAndSolan2023

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "flesch_and_solan_2023"
  bibliographyLabel := "Flesch & Solan 2023"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Flesch & Solan 2023"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.FleschAndSolan2023
