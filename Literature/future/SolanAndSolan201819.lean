import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Solan 2018/19

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SolanAndSolan201819

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_solan_2018_19"
  bibliographyLabel := "Solan & Solan 2018/19"
  bibliographyLocator := "Published source: Solan & Solan 2018/19"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndSolan201819
