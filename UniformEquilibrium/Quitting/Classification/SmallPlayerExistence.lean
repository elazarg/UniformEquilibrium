import UniformEquilibrium.Quitting.Classification.TerminalExploitabilitySmallPlayers
import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-! # Uniform-equilibrium existence for tables of at most three players -/

noncomputable section

namespace GameTheory

open StochasticGame

/-- Every finite quitting game with at most three players has a
uniform-equilibrium payoff. This collects the unconditional one-, two-, and
three-player existence theorems and the empty player type. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
    {κ : Type} [Fintype κ] [DecidableEq κ] (hcard : Fintype.card κ ≤ 3)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    ∃ payoff : Payoff κ,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  interval_cases hcase : Fintype.card κ
  · let : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcase
    by_contra hno
    obtain ⟨witness⟩ :=
      (not_exists_uniformEquilibriumPayoff_iff_nonempty_terminalExploitabilityWitness
        reward).1 hno
    exact QuittingTerminalExploitabilityWitness.elim_isEmpty witness
  · let : Unique κ := (Fintype.card_eq_one_iff_nonempty_unique.mp hcase).some
    exact quittingGame_exists_uniformEquilibriumPayoff_onePlayer reward
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two hcase reward
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three hcase reward

/-- No quitting game on at most three players has a strictly positive
terminal exploitability gap. No strategy or payoff is lifted to a larger game. -/
theorem not_hasTerminalExploitabilityGap_of_card_le_three
    {κ : Type} [Fintype κ] [DecidableEq κ] (hcard : Fintype.card κ ≤ 3)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ)
    {gap : ℝ} (hgap : 0 < gap) :
    ¬ HasTerminalExploitabilityGap reward gap := by
  intro hexploit
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      reward hgap hexploit)
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three hcard reward)

end GameTheory
