import Literature.Catalog

/-!
# Literature audit

Bibliography label: Simon 2007

Only abstract-level text and secondary corroboration are recorded; the theorem
text is not treated as primary-source audited.
-/

namespace Literature.Papers.Simon2007

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "simon_2007"
  bibliographyLabel := "Simon 2007"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Simon 2007"
  role := .nonzeroSumExistence
  sourceEvidence := .abstractInspected
  auditStatus := .sourceInspected
  claims := []

end Literature.Papers.Simon2007
