import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ummels & Wojtczak 2009

The primary precursor and its proof-sketch qualification were inspected.
-/

namespace Literature.UmmelsAndWojtczak2009

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ummels_and_wojtczak_2009"
  bibliographyLabel := "Ummels & Wojtczak 2009"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Ummels & Wojtczak 2009"
  role := .finiteMemoryAlgorithms
  paperEvidence := .primaryInspected
  auditStatus := .paperInspected
  claims := []

end Literature.UmmelsAndWojtczak2009
