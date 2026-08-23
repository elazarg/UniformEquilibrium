import Literature.Catalog

/-!
# Literature audit

Bibliography label: Mertens & Neyman 1981

This record contains bibliographic coverage and no paper-claim
correspondence.
-/

namespace Literature.MertensAndNeyman1981

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "mertens_and_neyman_1981"
  bibliographyLabel := "Mertens & Neyman 1981"
  bibliographyLocator := "Published source: Mertens & Neyman 1981"
  role := .zeroSumUniformValue
  paperEvidence := .bibliographic
  auditStatus := .catalogued
  claims := []

end Literature.MertensAndNeyman1981
