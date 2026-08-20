/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSmallSurvivorDeletion
import UniformEquilibrium.Quitting.Classification.BlockDeletionInequality

/-!
# The block deletion excess bound at small survivor counts

`UniformEquilibrium/Quitting/Classification/BlockDeletionInequality.lean`
bounds a deleted player's best-response excess against the lift of a survivor
profile whose per-stage absorption is controlled, and specializes to a
solo-escape versus atomic-temptation dichotomy at a singleton block.  That
dichotomy is stated against an arbitrary survivor approximate equilibrium
sharper than the exploitability gap; here the survivor game is solved
outright rather than assumed, using the unconditional small-player existence
theorem
`quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three` of
`UniformEquilibrium/Diagnostics/Quitting/TerminalSemanticSmallSurvivorDeletion.lean`.

`exists_terminalNash_deleteBlock_of_card_le_three` supplies terminal
approximate equilibria at every positive accuracy to any survivor game left
with at most three players.  Deleting a single player leaves at most three
survivors as soon as there are at most four players
(`card_quittingBlockSurvivor_singleton_le`), so
`exists_terminalNash_deleteSingleton_of_card_le_four` specializes it to
singleton deletion, and
`exists_terminalNash_soloEscape_or_atomicTemptation_of_card_le_four` composes
it with `singletonDeletion_soloEscape_or_atomicTemptation` to reach the
dichotomy unconditionally at every player and every positive gap, with no
survivor-equilibrium hypothesis left to supply.

This is a necessary condition on a counterexample with at most four players,
not a characterization: a four-player table can be solved by a profile in
which every player quits, and no lift of a subgame equilibrium sees such a
profile.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A survivor game with at most three players has terminal approximate
equilibria at every positive accuracy, unconditionally. -/
theorem exists_terminalNash_deleteBlock_of_card_le_three
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (B : Finset ι)
    (hcard : Fintype.card (QuittingBlockSurvivor B) ≤ 3) :
    ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward B)).BehaviorProfile,
        (quittingGame (quittingDeleteBlockReward reward B)).IsεAsymptoticNash
          (quittingTerminalPayoff (quittingDeleteBlockReward reward B))
          error profile := by
  obtain ⟨payoff, hpayoff⟩ :=
    quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three hcard
      (quittingDeleteBlockReward reward B)
  exact quittingGame_terminalNash_all_errors_of_isUniformEquilibriumPayoff
    (quittingDeleteBlockReward reward B) payoff hpayoff

/-- With at most four players, the subgame omitting one player has terminal
approximate equilibria at every positive accuracy. -/
theorem exists_terminalNash_deleteSingleton_of_card_le_four
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card ι ≤ 4) (owner : ι) :
    ∀ error : ℝ, 0 < error →
      ∃ profile : (quittingGame
          (quittingDeleteBlockReward reward
            ({owner} : Finset ι))).BehaviorProfile,
        (quittingGame
            (quittingDeleteBlockReward reward
              ({owner} : Finset ι))).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteBlockReward reward ({owner} : Finset ι)))
          error profile :=
  exists_terminalNash_deleteBlock_of_card_le_three reward {owner}
    (card_quittingBlockSurvivor_singleton_le hcard owner)

/-- **The dichotomy at most four players.**  With at most four players and a
positive gap, every player admits a subgame approximate equilibrium sharper
than the gap, and against any per-stage absorption bound for it the omitted
player either escapes on its own or is atomically tempted.

This is a necessary condition on a counterexample.  It does not characterize
solvability: a four-player table can be solved by a profile in which every
player quits, and no lift of a subgame equilibrium sees such a profile. -/
theorem exists_terminalNash_soloEscape_or_atomicTemptation_of_card_le_four
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card ι ≤ 4) (owner : ι) {gap error : ℝ}
    (hgap : 0 < gap) (hexploit : HasTerminalExploitabilityGap reward gap)
    (herrorPos : 0 < error) (herror : error < gap) :
    ∃ profile : (quittingGame
        (quittingDeleteBlockReward reward ({owner} : Finset ι))).BehaviorProfile,
      (quittingGame
          (quittingDeleteBlockReward reward
            ({owner} : Finset ι))).IsεAsymptoticNash
        (quittingTerminalPayoff
          (quittingDeleteBlockReward reward ({owner} : Finset ι)))
        error profile ∧
      ∀ absorptionBound : ℝ,
        (∀ time, 1 - quittingStationaryContinueMass
          (quittingProfileLiveRoot
            (quittingDeleteBlockReward reward ({owner} : Finset ι))
            profile time) ≤ absorptionBound) →
        gap / 2 ≤ reward (quittingSingletonTerminal owner) owner -
            quittingBlockContinueFloor reward {owner} owner ∨
          (0 < quittingBlockJoinCap reward {owner} owner ∧
            gap / 2 ≤
              absorptionBound * quittingBlockJoinCap reward {owner} owner) := by
  obtain ⟨profile, hnash⟩ :=
    exists_terminalNash_deleteSingleton_of_card_le_four reward hcard owner error
      herrorPos
  exact ⟨profile, hnash, fun absorptionBound habsorb =>
    singletonDeletion_soloEscape_or_atomicTemptation reward owner hgap hexploit
      profile hnash herror habsorb⟩

end GameTheory
