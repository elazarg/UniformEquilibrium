import Literature.Catalog

/-!
# Literature audit

Bibliography label: Schäffeler & Abdulaziz 2021

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SchaffelerAndAbdulaziz2021

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "schaffeler_and_abdulaziz_2021"
  bibliographyLabel := "Schäffeler & Abdulaziz 2021"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Schäffeler & Abdulaziz 2021"
  role := .formalization
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SchaffelerAndAbdulaziz2021
