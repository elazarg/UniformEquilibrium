import Literature.Catalog

/-!
# Literature audit

Bibliography label: Rosenberg, Solan & Vieille 2003

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.RosenbergSolanAndVieille2003

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "rosenberg_solan_and_vieille_2003"
  bibliographyLabel := "Rosenberg, Solan & Vieille 2003"
  bibliographyLocator := "Published source: Rosenberg, Solan & Vieille 2003"
  role := .zeroSumBoundary
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.RosenbergSolanAndVieille2003
