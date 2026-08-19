import Literature.Catalog

/-!
# Literature audit

Bibliography label: Le Roux, Martin-Dorel & Smaus 2017

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.LeRouxMartinDorelAndSmaus2017

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "le_roux_martin_dorel_and_smaus_2017"
  bibliographyLabel := "Le Roux, Martin-Dorel & Smaus 2017"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Le Roux, Martin-Dorel & Smaus 2017"
  role := .formalization
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.LeRouxMartinDorelAndSmaus2017
