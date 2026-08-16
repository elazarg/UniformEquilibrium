import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Solan 2018/19

This record contains bibliographic coverage and no source-claim
correspondence.
-/

namespace Literature.Papers.SolanAndSolan201819

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_solan_2018_19"
  bibliographyLabel := "Solan & Solan 2018/19"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Solan 2018/19"
  role := .recentNonzeroSum
  sourceEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.Papers.SolanAndSolan201819
