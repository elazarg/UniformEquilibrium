import Literature.Catalog

/-!
# Literature audit

Bibliography label: Hansen, Ibsen-Jensen & Neyman 2023

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.HansenIbsenJensenAndNeyman2023

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "hansen_ibsen_jensen_and_neyman_2023"
  bibliographyLabel := "Hansen, Ibsen-Jensen & Neyman 2023"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Hansen, Ibsen-Jensen & Neyman 2023"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.HansenIbsenJensenAndNeyman2023
