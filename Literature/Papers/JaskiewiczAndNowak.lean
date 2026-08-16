import Literature.Catalog

/-!
# Literature audit

Bibliography label: Jaśkiewicz & Nowak

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.JaskiewiczAndNowak

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "jaskiewicz_and_nowak"
  bibliographyLabel := "Jaśkiewicz & Nowak"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Jaśkiewicz & Nowak"
  role := .surveys
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.JaskiewiczAndNowak
