import Literature.Catalog
import UniformEquilibrium.Quitting.Examples.FTV.CyclicAdmissibleCycle

/-!
# Literature audit

Bibliography label: Flesch, Thuijsman & Vrieze 1997

The published paper and its exact three-player game table were inspected.
-/

namespace Literature.FleschThuijsmanAndVrieze1997

open Filter GameTheory GameTheory.StochasticGame

/-- The finite-horizon average payoff of the displayed cyclic Markov profile
converges coordinatewise to the paper's vector `(1, 2, 1)`. -/
theorem tendsto_cyclicMarkovProfile_payoff
    (who : Fin 3) :
    Tendsto
      (fun horizon : ℕ =>
        (quittingGame FTVCyclicAdmissibleCycle.ftvReward).finiteAveragePayoff
          none horizon
          FTVCyclicAdmissibleCycle.ftvCyclicProfile who)
      atTop (nhds (FTVCyclicMinimality.namedTarget who)) :=
  FTVCyclicAdmissibleCycle.tendsto_finiteAveragePayoff_ftvCyclicProfile who

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "flesch_thuijsman_and_vrieze_1997"
  bibliographyLabel := "Flesch, Thuijsman & Vrieze 1997"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Flesch, Thuijsman & Vrieze 1997"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "no_stationary_equilibrium"
        sourceLocator := "Lemma 3.1"
        summary := "The displayed game has no stationary equilibrium."
        status := .sourceOnly },
      { claimId := "small_error_stationary_impossibility"
        sourceLocator := "Theorem 3.2 and its proof"
        summary := "Stationary epsilon-equilibria fail for all sufficiently small errors."
        status := .sourceOnly },
      { claimId := "cyclic_markov_payoff"
        sourceLocator := "Theorem 3.3"
        summary := "The displayed cyclic Markov profile has payoff (1,2,1)."
        status := .provedInLean
          "Literature.FleschThuijsmanAndVrieze1997.\
tendsto_cyclicMarkovProfile_payoff"
          "GameTheory.FTVCyclicAdmissibleCycle.\
tendsto_finiteAveragePayoff_ftvCyclicProfile" },
      { claimId := "one_randomizer_per_stage"
        sourceLocator := "Theorem 3.4"
        summary := "Every equilibrium has one player randomizing at each stage."
        status := .sourceOnly } ]

end Literature.FleschThuijsmanAndVrieze1997
