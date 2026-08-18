import Literature.Catalog
import UniformEquilibrium.Quitting.Classification.SoloExitPreferenceExistence
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Literature audit

Bibliography label: Solan & Vieille 2001

The published paper was inspected directly for the terminal-to-uniform bridge
and for the two assumptions carried by its existence theorem.
-/

namespace Literature.Papers.SolanAndVieille2001

open GameTheory StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proposition 2.13 in the finite-quitting-game semantics: an
`ε`-terminal Nash profile is a uniform `ε'`-equilibrium whenever `ε < ε'`. -/
theorem terminalNash_isUniformEquilibrium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {ε ε' : ℝ} (herror : ε < ε')
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    (quittingGame reward).IsUniformεEquilibrium none ε' profile :=
  quittingGame_isUniformεEquilibrium_of_terminalNash
    reward profile herror hnash

/-! ## Theorem 1.2 and its two assumptions

Solan and Vieille, *Quitting games*, Math. Oper. Res. **26** (2001), 265–285,
Theorem 1.2 assumes

* A.1, `r^i_{i} = 1` for every player `i`; and
* A.2, `r^i_S ≤ 1` for every player `i` and every coalition `S` containing `i`,

and concludes that the game has a cyclic subgame-perfect uniform
`ε`-equilibrium for every positive `ε`.

Solan and Solan, *Quitting games and linear complementarity problems*,
Math. Oper. Res. **45** (2020), restate the hypothesis invariantly as each
player preferring to quit alone rather than alongside others.  Under A.1 that
restatement is `QuittingWeakSoloExitPreference`, by
`GameTheory.quittingCappedJointExit_iff_weakSoloExitPreference`; without A.1 it
is strictly weaker, since A.1 also fixes the common solo value.  The claim
below is stated at A.1 and A.2, as the source proves it.
-/

/-- **Open proposition.**  The equilibrium-existence half of Theorem 1.2:
under A.1 and A.2, a uniform `ε`-equilibrium exists for every positive `ε`.

This drops the source's cyclic subgame-perfection, so it is weaker than
Theorem 1.2 and is recorded as a separate claim.  It is not proved anywhere in
this development. -/
def UniformεEquilibriumUnderSoloExitAssumptionsClaim
    (ι : Type) [Fintype ι] [DecidableEq ι] : Prop :=
  QuittingCappedJointExitUniformεExistence ι

/-- **Conditional.**  Granting the claim, a quitting game satisfying A.1 and
A.2 has one fixed uniform-equilibrium payoff.

The source's conclusion quantifies existentially inside the accuracy, so its
profile and payoff vector may both move with `ε`; a uniform-equilibrium payoff
fixes one target first.  For finite quitting games the two are equivalent, by
`GameTheory.quittingGame_exists_uniformEquilibriumPayoff_iff_uniformεEquilibrium_all_errors`.
The claim itself remains unproved. -/
theorem exists_uniformEquilibriumPayoff_of_claim
    (hclaim : UniformεEquilibriumUnderSoloExitAssumptionsClaim ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hunit : QuittingUnitSoloExit reward)
    (hcapped : QuittingCappedJointExit reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_cappedJointExit hclaim hunit hcapped

/-- Paper-level coverage record. -/
def record : Literature.PaperRecord where
  paperId := "solan_and_vieille_2001"
  bibliographyLabel := "Solan & Vieille 2001"
  bibliographyLocator := "docs/references/00_BIBLIOGRAPHY.md :: Solan & Vieille 2001"
  role := .nonzeroSumExistence
  sourceEvidence := .primaryInspected
  auditStatus := .claimAuditInProgress
  claims :=
    [ { claimId := "cyclic_subgame_perfect_uniform_equilibrium"
        sourceLocator := "Theorem 1.2"
        summary :=
          "Under A.1 and A.2, every quitting game has cyclic subgame-perfect " ++
          "uniform epsilon-equilibria."
        status := .sourceOnly },
      { claimId := "uniform_equilibrium_under_solo_exit_assumptions"
        sourceLocator := "Theorem 1.2"
        summary :=
          "Under A.1 and A.2, a uniform epsilon-equilibrium exists at every " ++
          "positive epsilon; cyclic subgame-perfection is dropped."
        status := .openInLean
          "Literature.Papers.SolanAndVieille2001.\
UniformεEquilibriumUnderSoloExitAssumptionsClaim" },
      { claimId := "stationary_or_subgame_perfect_profile"
        sourceLocator := "Proposition 2.4"
        summary :=
          "The constructed profile is subgame-perfect at the stated error, " ++
          "or a stationary equilibrium exists."
        status := .sourceOnly },
      { claimId := "terminal_equilibrium_to_uniform_equilibrium"
        sourceLocator := "Proposition 2.13"
        summary := "An epsilon terminal equilibrium is uniform at every larger error."
        status := .provedInLean
          "Literature.Papers.SolanAndVieille2001.terminalNash_isUniformEquilibrium"
          "GameTheory.quittingGame_isUniformεEquilibrium_of_terminalNash" } ]

end Literature.Papers.SolanAndVieille2001
