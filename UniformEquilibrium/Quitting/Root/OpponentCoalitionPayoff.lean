/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors.
-/

import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Opponent-coalition payoff expansions

This file expands the two pure endpoint payoffs of one quitting root over the
exact coalition law of the other players.  The identities are low semantic
facts; polarity-specific defect diagnostics build on them elsewhere.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At one opponent coalition, the selected player's pure-Quit advantage is
the payoff after inserting the player minus the payoff without it.  At the
empty coalition the latter payoff is the literal tail value. -/
def quittingEndpointInsertionToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) (coalition : Finset ι) : ℝ :=
  quittingStageCoalitionPayoff reward tail (insert who coalition) who -
    quittingStageCoalitionPayoff reward tail coalition who

/-- Pure Quit is the opponent-coalition average of the payoff after inserting
the selected player. -/
theorem quittingRootQuitPayoff_eq_sum_opponentCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootQuitPayoff reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingStageCoalitionPayoff reward tail
            (insert who coalition) who := by
  rw [quittingRootQuitPayoff_eq_sigmaValue]
  unfold sigmaValue quittingOpponentCoalitionMass
  apply Finset.sum_congr rfl
  intro coalition hcoalition
  rw [Finset.mem_powerset] at hcoalition
  have hnonempty : (insert who coalition).Nonempty :=
    Finset.insert_nonempty who coalition
  simp only [hazardOfRoot, weightOfReward,
    quittingStageCoalitionPayoff, hnonempty, dif_pos]
  simp_rw [pmfBool_false_toReal]

/-- Pure Continue is the same opponent-coalition average without inserting
the player.  The empty-coalition summand is exactly the literal tail. -/
theorem quittingRootContinuePayoff_eq_sum_opponentCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingStageCoalitionPayoff reward tail coalition who := by
  rw [quittingRootContinuePayoff_eq_gammaValue]
  unfold gammaValue excludedValue continueMassExcl
    quittingOpponentCoalitionMass
  let carrier := (Finset.univ.erase who).powerset
  let summand : Finset ι → ℝ := fun coalition ↦
    ((∏ player ∈ coalition, (root player true).toReal) *
      ∏ player ∈ Finset.univ.erase who \ coalition,
        (root player false).toReal) *
      quittingStageCoalitionPayoff reward tail coalition who
  have hempty : (∅ : Finset ι) ∈ carrier := by
    simp [carrier]
  change
    (∑ coalition ∈ carrier.erase ∅,
        ((∏ player ∈ coalition, (root player true).toReal) *
          ∏ player ∈ Finset.univ.erase who \ coalition,
            (1 - (root player true).toReal)) *
          weightOfReward reward coalition who) +
        (∏ player ∈ Finset.univ.erase who,
          (1 - (root player true).toReal)) * tail who =
      ∑ coalition ∈ carrier, summand coalition
  conv_rhs => rw [← Finset.add_sum_erase carrier summand hempty]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_
  · simp [summand, quittingStageCoalitionPayoff, pmfBool_false_toReal]
  · apply Finset.sum_congr rfl
    intro coalition hcoalition
    rw [Finset.mem_erase] at hcoalition
    have hnonempty : coalition.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hcoalition.1
    simp only [weightOfReward,
      quittingStageCoalitionPayoff, hnonempty, dif_pos, summand]
    simp_rw [pmfBool_false_toReal]

/-- Quit-minus-Continue is the opponent-coalition average of the state-matched
insertion toggle. -/
theorem quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        quittingOpponentCoalitionMass root who coalition *
          quittingEndpointInsertionToggle reward tail who coalition := by
  unfold quittingRootEndpointDifference quittingEndpointInsertionToggle
  rw [quittingRootQuitPayoff_eq_sum_opponentCoalitionMass,
    quittingRootContinuePayoff_eq_sum_opponentCoalitionMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

/-- Multiplying the endpoint expansion by the probability that the player
actually played Continue gives the exact signed played-action gap. -/
theorem quittingContinueProbability_mul_endpointDifference_eq_sum_atoms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    (root who false).toReal *
        quittingRootEndpointDifference reward tail root who =
      ∑ coalition ∈ (Finset.univ.erase who).powerset,
        (root who false).toReal *
          quittingOpponentCoalitionMass root who coalition *
            quittingEndpointInsertionToggle reward tail who coalition := by
  rw [quittingRootEndpointDifference_eq_sum_opponentCoalitionToggle,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coalition _
  ring

omit [Fintype ι] in
/-- The empty label is exactly the solo reward minus the literal tail. -/
theorem quittingEndpointInsertionToggle_empty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) :
    quittingEndpointInsertionToggle reward tail who ∅ =
      reward (quittingSingletonTerminal who) who - tail who := by
  simp [quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    quittingSingletonTerminal]

omit [Fintype ι] in
/-- A nonempty label is the static payoff toggle obtained by adding the
selected player to that coalition. -/
theorem quittingEndpointInsertionToggle_of_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (who : ι) (coalition : Finset ι)
    (hcoalition : coalition.Nonempty) :
    quittingEndpointInsertionToggle reward tail who coalition =
      reward ⟨insert who coalition, Finset.insert_nonempty who coalition⟩ who -
        reward ⟨coalition, hcoalition⟩ who := by
  simp [quittingEndpointInsertionToggle, quittingStageCoalitionPayoff,
    hcoalition]

end GameTheory
