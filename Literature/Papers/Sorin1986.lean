import Literature.Catalog
import UniformEquilibrium.Examples.Sorin.OccupationVanishing

/-!
# Literature audit

Bibliography label: Sorin 1986

The primary paper was inspected for both equilibrium-payoff-set statements and
their separation.
-/

namespace Literature.Papers.Sorin1986

open GameTheory StochasticGame

/-! The source's `E(∞)` is the set of semantic uniform-equilibrium
payoffs from the live state.  The bounds in the parametrization are part of
the claim; the affine equation alone is strictly weaker. -/

def UniformEquilibriumPayoffSetClaim : Prop :=
  ∀ payoff : Payoff SorinAbsorbingGame.Player,
    SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
        SorinAbsorbingGame.State.live payoff ↔
      ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 2 / 3 ∧
        payoff = SorinAbsorbingGame.pair a (2 * (1 - a))

/-- The discount-constant endpoint of Sorin's displayed stationary family is
not a uniform-equilibrium payoff of the displayed absorbing game. -/
theorem discountedEndpoint_not_isUniformEquilibriumPayoff :
    ¬ SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live
      (SorinAbsorbingGame.pair (1 / 2) (2 / 3)) :=
  SorinAbsorbingGame.discountedEndpoint_not_isUniformEquilibriumPayoff

/-- Every uniform-equilibrium payoff of Sorin's displayed game lies on the
affine line `2 * payoff false + payoff true = 2`. -/
theorem uniformEquilibriumPayoff_weighted_eq_two
    (payoff : GameTheory.Payoff SorinAbsorbingGame.Player)
    (hpayoff : SorinAbsorbingGame.game.IsUniformEquilibriumPayoff
      SorinAbsorbingGame.State.live payoff) :
    2 * payoff false + payoff true = 2 :=
  SorinAbsorbingGame.uniformEquilibriumPayoff_weighted_eq_two payoff hpayoff

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
        status := .openInLean
          "Literature.Papers.Sorin1986.UniformEquilibriumPayoffSetClaim" },
      { claimId := "approximation_sets_disjoint_from_uniform_set"
        sourceLocator := "separation statement on page 107"
        summary := "The constant approximation payoff set is disjoint from F."
        status := .sourceOnly },
      { claimId := "discounted_endpoint_not_uniform"
        sourceLocator := "separation statement on page 107"
        summary := "The discount-constant endpoint (1/2, 2/3) is not a uniform payoff."
        status := .provedInLean
          "Literature.Papers.Sorin1986.discountedEndpoint_not_isUniformEquilibriumPayoff"
          "GameTheory.StochasticGame.SorinAbsorbingGame.\
discountedEndpoint_not_isUniformEquilibriumPayoff" },
      { claimId := "uniform_payoffs_satisfy_affine_line"
        sourceLocator := "Theorem 2"
        summary := "Every uniform payoff lies on 2 w1 + w2 = 2."
        status := .provedInLean
          "Literature.Papers.Sorin1986.uniformEquilibriumPayoff_weighted_eq_two"
          "GameTheory.StochasticGame.SorinAbsorbingGame.\
uniformEquilibriumPayoff_weighted_eq_two" } ]

end Literature.Papers.Sorin1986
