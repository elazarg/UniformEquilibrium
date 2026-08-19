import Literature.Catalog

/-!
# Literature audit

Bibliography label: Laraki & Sorin

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.LarakiAndSorin

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "laraki_and_sorin"
  bibliographyLabel := "Laraki & Sorin"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Laraki & Sorin"
  role := .surveys
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.LarakiAndSorin
