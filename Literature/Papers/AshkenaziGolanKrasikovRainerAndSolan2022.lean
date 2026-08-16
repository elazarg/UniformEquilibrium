import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ashkenazi-Golan, Krasikov, Rainer & Solan 2022

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ashkenazi_golan_krasikov_rainer_and_solan_2022"
  bibliographyLabel := "Ashkenazi-Golan, Krasikov, Rainer & Solan 2022"
  bibliographyLocator :=
    "docs/references/00_BIBLIOGRAPHY.md :: " ++
      "Ashkenazi-Golan, Krasikov, Rainer & Solan 2022"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.AshkenaziGolanKrasikovRainerAndSolan2022
