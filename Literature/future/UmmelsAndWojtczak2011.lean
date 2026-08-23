import Literature.Catalog

/-!
# Literature audit

Bibliography label: Ummels & Wojtczak 2011

The peer-reviewed paper and its proof-sketch qualification were inspected.
-/

namespace Literature.UmmelsAndWojtczak2011

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "ummels_and_wojtczak_2011"
  bibliographyLabel := "Ummels & Wojtczak 2011"
  bibliographyLocator := "Published source: Ummels & Wojtczak 2011"
  role := .finiteMemoryAlgorithms
  paperEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_memory_nash_undecidable"
        paperLocator := "Theorem 4.14"
        summary := "FinNE and PureFinNE are undecidable for 14-player SSMGs."
        status := .paperOnly } ]

end Literature.UmmelsAndWojtczak2011
