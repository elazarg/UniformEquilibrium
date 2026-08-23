import Literature.Catalog

/-!
# Literature audit

Bibliography label: Solan & Vieille 2025b

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.SolanAndVieille2025b

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2025b"
  bibliographyLabel := "Solan & Vieille 2025b"
  bibliographyLocator := "Published source: Solan & Vieille 2025b"
  role := .recentNonzeroSum
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.SolanAndVieille2025b
