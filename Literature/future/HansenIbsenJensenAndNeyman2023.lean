import Literature.Catalog

/-!
# Literature audit

Bibliography label: Hansen, Ibsen-Jensen & Neyman 2023

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.HansenIbsenJensenAndNeyman2023

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "hansen_ibsen_jensen_and_neyman_2023"
  bibliographyLabel := "Hansen, Ibsen-Jensen & Neyman 2023"
  bibliographyLocator := "Published source: Hansen, Ibsen-Jensen & Neyman 2023"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.HansenIbsenJensenAndNeyman2023
