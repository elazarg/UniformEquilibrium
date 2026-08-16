import Literature.Catalog

/-!
# Literature audit

Bibliography label: Sorin 1986

The primary paper was inspected for both equilibrium-payoff-set statements and
their separation.
-/

namespace Literature.Papers.Sorin1986

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "sorin_1986"
  bibliographyLabel := "Sorin 1986"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Sorin 1986"
  role := .counterexamples
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "finite_and_discounted_payoff_sets"
        sourceLocator := "Theorem 1"
        summary := "Every finite-horizon and discounted equilibrium payoff set is {V}."
        status := .sourceOnly },
      { claimId := "uniform_equilibrium_payoff_set"
        sourceLocator := "Theorem 2"
        summary := "The uniform equilibrium payoff set is the bounded Pareto segment F."
        status := .sourceOnly },
      { claimId := "approximation_sets_disjoint_from_uniform_set"
        sourceLocator := "separation statement on page 107"
        summary := "The constant approximation payoff set is disjoint from F."
        status := .sourceOnly } ]

end Literature.Papers.Sorin1986
