/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import UniformEquilibrium.Quitting.Classification.ExistenceBranches

/-!
# Closedness of well-supported quitting rows

One-stage player perfection is closed when the error, continuation payoff,
and product row converge.  At zero error, the two closed pure-action upper
bounds and the mixture identities reconstruct equality on every action used
with positive probability.

Roots use the project's simplex coordinates because the raw Boolean `PMF`
profile has no topology here.
-/

noncomputable section

namespace GameTheory

open Filter Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- If neither pure action beats one player's prescribed successor payoff,
then that player is exactly well-supported at the row.  The mixture identity
forces equality on every action used with positive probability. -/
theorem quittingPlayerRowZeroPerfect_of_purePayoff_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι)
    (hquit : quittingRootQuitPayoff reward tail root player ≤
      quittingRootSuccessorPayoff reward tail root player)
    (hcontinue : quittingRootContinuePayoff reward tail root player ≤
      quittingRootSuccessorPayoff reward tail root player) :
    QuittingPlayerRowεPerfect reward tail root player 0 := by
  refine ⟨by simpa using hquit, by simpa using hcontinue, ?_, ?_⟩
  · intro hused
    have hpositive : 0 < (root player true).toReal :=
      ENNReal.toReal_pos hused (PMF.apply_ne_top _ _)
    have hdifference : 0 ≤
        quittingRootEndpointDifference reward tail root player := by
      have hidentity := quittingRootContinuePayoff_sub_successorPayoff
        reward tail root player
      have : quittingRootContinuePayoff reward tail root player -
          quittingRootSuccessorPayoff reward tail root player ≤ 0 := by
        linarith
      rw [hidentity] at this
      have hprobability : 0 ≤ (root player true).toReal :=
        ENNReal.toReal_nonneg
      nlinarith
    have hidentity := quittingRootQuitPayoff_sub_successorPayoff
      reward tail root player
    have hproduct : 0 ≤ (root player false).toReal *
        quittingRootEndpointDifference reward tail root player :=
      mul_nonneg ENNReal.toReal_nonneg hdifference
    linarith
  · intro hused
    have hpositive : 0 < (root player false).toReal :=
      ENNReal.toReal_pos hused (PMF.apply_ne_top _ _)
    have hdifference :
        quittingRootEndpointDifference reward tail root player ≤ 0 := by
      have hidentity := quittingRootQuitPayoff_sub_successorPayoff
        reward tail root player
      have : quittingRootQuitPayoff reward tail root player -
          quittingRootSuccessorPayoff reward tail root player ≤ 0 := by
        linarith
      rw [hidentity] at this
      have hprobability : 0 ≤ (root player false).toReal :=
        ENNReal.toReal_nonneg
      nlinarith
    have hidentity := quittingRootContinuePayoff_sub_successorPayoff
      reward tail root player
    have hproduct : 0 ≤ -((root player true).toReal *
        quittingRootEndpointDifference reward tail root player) :=
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        ENNReal.toReal_nonneg hdifference)
    linarith

/-- The two pure-action upper bounds for one player form a closed subset of
the error, continuation-payoff, and simplex-root space. -/
theorem isClosed_quittingPlayerPurePayoffUpperBounds_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι) :
    IsClosed {point : ℝ × Payoff ι × QuittingRootSimplex ι |
      quittingRootQuitPayoff reward point.2.1
            (quittingRootOfSimplex point.2.2) player ≤
          quittingRootSuccessorPayoff reward point.2.1
              (quittingRootOfSimplex point.2.2) player + point.1 ∧
        quittingRootContinuePayoff reward point.2.1
            (quittingRootOfSimplex point.2.2) player ≤
          quittingRootSuccessorPayoff reward point.2.1
              (quittingRootOfSimplex point.2.2) player + point.1} := by
  have hsuccessor : Continuous
      (fun point : ℝ × Payoff ι × QuittingRootSimplex ι ↦
        quittingRootSuccessorPayoff reward point.2.1
          (quittingRootOfSimplex point.2.2) player) :=
    ((continuous_apply player).comp
      (continuous_quittingRootSuccessorPayoff_simplex reward)).comp
        continuous_snd
  exact (isClosed_le
      ((continuous_quittingRootQuitPayoff_simplex reward player).comp
        continuous_snd)
      (hsuccessor.add continuous_fst)).inter
    (isClosed_le
      ((continuous_quittingRootContinuePayoff_simplex reward player).comp
        continuous_snd)
      (hsuccessor.add continuous_fst))

/-- Playerwise one-stage perfection survives joint convergence of a vanishing
error, continuation payoff, and simplex root. -/
theorem quittingPlayerRowεPerfect_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (errors : α → ℝ) (tails : α → Payoff ι)
    (roots : α → QuittingRootSimplex ι)
    {tail : Payoff ι} {root : QuittingRootSimplex ι}
    (herrors : Tendsto errors l (nhds 0))
    (htails : Tendsto tails l (nhds tail))
    (hroots : Tendsto roots l (nhds root))
    (hperfect : ∀ᶠ index in l,
      QuittingPlayerRowεPerfect reward (tails index)
        (quittingRootOfSimplex (roots index)) player (errors index)) :
    QuittingPlayerRowεPerfect reward tail
      (quittingRootOfSimplex root) player 0 := by
  have hbounds :=
    (isClosed_quittingPlayerPurePayoffUpperBounds_simplex reward player).mem_of_tendsto
      (herrors.prodMk_nhds (htails.prodMk_nhds hroots))
      (hperfect.mono fun _ hrow ↦ ⟨hrow.1, hrow.2.1⟩)
  apply quittingPlayerRowZeroPerfect_of_purePayoff_le reward tail
    (quittingRootOfSimplex root) player
  · simpa using hbounds.1
  · simpa using hbounds.2

/-- Collective one-stage perfection survives joint convergence of a vanishing
error, continuation payoff, and simplex root. -/
theorem quittingRowεPerfect_of_tendsto
    {α : Type*} {l : Filter α} [l.NeBot]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (errors : α → ℝ) (tails : α → Payoff ι)
    (roots : α → QuittingRootSimplex ι)
    {tail : Payoff ι} {root : QuittingRootSimplex ι}
    (herrors : Tendsto errors l (nhds 0))
    (htails : Tendsto tails l (nhds tail))
    (hroots : Tendsto roots l (nhds root))
    (hperfect : ∀ᶠ index in l,
      QuittingRowεPerfect reward (tails index)
        (quittingRootOfSimplex (roots index)) (errors index)) :
    QuittingRowεPerfect reward tail (quittingRootOfSimplex root) 0 := by
  intro player
  exact quittingPlayerRowεPerfect_of_tendsto reward player errors tails roots
    herrors htails hroots (hperfect.mono fun _ hrow ↦ hrow player)

end GameTheory
