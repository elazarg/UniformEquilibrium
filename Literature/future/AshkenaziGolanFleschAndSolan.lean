import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ashkenazi-Golan, Flesch & Solan

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.AshkenaziGolanFleschAndSolan

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ashkenazi_golan_flesch_and_solan"
  bibliographyLabel := "Ashkenazi-Golan, Flesch & Solan"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Ashkenazi-Golan, Flesch & Solan"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.AshkenaziGolanFleschAndSolan
