/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity

/-!
# Affinity of stopping-law rays on a minimum-debt fiber

Semantic debt is coordinatewise convex along a complete stopping-law mixture.
Near a global minimum of total debt, the sum of the coordinatewise convexity
gaps is controlled by the near-minimum error and by the endpoint's total-debt
rise.  In particular, a stopping-law chord whose endpoint remains on the same
minimum-debt fiber is exactly affine in every debt coordinate.

This is the radial-homogeneity interface needed to replace scalar-weighted
stopping-law tangent columns by literal player-specific reset scales.  It does
not compose several player resets or assert a chronological return.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Quantitative minimum-fiber chord gap.**

Let the source profile be within `epsilon` of the global minimum of total
semantic debt.  Along any complete stopping-law mixture, one coordinate's
convexity gap is nonnegative and is bounded by

`epsilon + lambda * (endpoint total debt - source total debt)`.

The estimate has no factor depending on the number of players: the observed
gap is one nonnegative summand of the full chord gap. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda epsilon : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) ≤
        quittingTerminalSemanticDebtSum candidate + epsilon) :
    let sourcePair := quittingTerminalSemanticPair reward
      (Function.update profile mover source)
    let targetPair := quittingTerminalSemanticPair reward
      (Function.update profile mover target)
    let mixedPair := quittingTerminalSemanticPair reward
      (Function.update profile mover
        (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
          lambda hlambda0 hlambda1))
    0 ≤
        (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
          lambda * quittingTerminalSemanticDebt targetPair observer -
            quittingTerminalSemanticDebt mixedPair observer ∧
      (1 - lambda) * quittingTerminalSemanticDebt sourcePair observer +
          lambda * quittingTerminalSemanticDebt targetPair observer -
            quittingTerminalSemanticDebt mixedPair observer ≤
        epsilon + lambda *
          (quittingTerminalSemanticDebtSum targetPair -
            quittingTerminalSemanticDebtSum sourcePair) := by
  dsimp only
  let sourceProfile := Function.update profile mover source
  let targetProfile := Function.update profile mover target
  let mixedProfile := Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
      lambda hlambda0 hlambda1)
  let sourcePair := quittingTerminalSemanticPair reward sourceProfile
  let targetPair := quittingTerminalSemanticPair reward targetProfile
  let mixedPair := quittingTerminalSemanticPair reward mixedProfile
  let gap : ι → ℝ := fun who =>
    (1 - lambda) * quittingTerminalSemanticDebt sourcePair who +
      lambda * quittingTerminalSemanticDebt targetPair who -
        quittingTerminalSemanticDebt mixedPair who
  change 0 ≤ gap observer ∧
    gap observer ≤ epsilon + lambda *
      (quittingTerminalSemanticDebtSum targetPair -
        quittingTerminalSemanticDebtSum sourcePair)
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt mixedPair who ≤
        (1 - lambda) * quittingTerminalSemanticDebt sourcePair who +
          lambda * quittingTerminalSemanticDebt targetPair who := by
    intro who
    dsimp only [mixedPair, sourcePair, targetPair, mixedProfile,
      sourceProfile, targetProfile]
    exact quittingTerminalSemanticDebt_stoppingLawMixture_le
      reward profile mover who source target lambda hlambda0 hlambda1
  have hgapNonneg : ∀ who, 0 ≤ gap who := by
    intro who
    dsimp only [gap]
    linarith [hcoordinate who]
  have hmixedFloor :
      quittingTerminalSemanticDebtSum sourcePair ≤
        quittingTerminalSemanticDebtSum mixedPair + epsilon := by
    dsimp only [sourcePair, mixedPair, sourceProfile, mixedProfile]
    exact hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward mixedProfile)
  have hsumGap :
      (∑ who, gap who) =
        (1 - lambda) * quittingTerminalSemanticDebtSum sourcePair +
          lambda * quittingTerminalSemanticDebtSum targetPair -
            quittingTerminalSemanticDebtSum mixedPair := by
    dsimp only [gap]
    unfold quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have hsumUpper :
      (∑ who, gap who) ≤ epsilon + lambda *
        (quittingTerminalSemanticDebtSum targetPair -
          quittingTerminalSemanticDebtSum sourcePair) := by
    rw [hsumGap]
    linarith
  have hrestNonneg :
      0 ≤ ∑ who ∈ Finset.univ.erase observer, gap who :=
    Finset.sum_nonneg fun who _whoMem => hgapNonneg who
  have hdecompose := Finset.sum_erase_add (Finset.univ) gap
    (Finset.mem_univ observer)
  have hobserverLe : gap observer ≤ ∑ who, gap who := by
    linarith
  exact ⟨hgapNonneg observer, hobserverLe.trans hsumUpper⟩

/-- On one exact minimum-debt fiber, every coordinate of a complete
stopping-law mixture is exactly affine.  Thus a tangent column can be scaled
radially without changing its strategic debt direction, provided the full
endpoint remains on the same total-debt fiber. -/
theorem quittingTerminalSemanticDebt_stoppingLawMixture_eq_of_minimum_sameDebtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι)
    (source target : (quittingGame reward).BehaviorStrategy mover)
    (lambda : ℝ)
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsame :
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) =
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source))) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover source target
              lambda hlambda0 hlambda1))) observer =
      (1 - lambda) * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) observer +
        lambda * quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile mover target)) observer := by
  have hnear : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (Function.update profile mover source)) ≤
        quittingTerminalSemanticDebtSum candidate + 0 := by
    intro candidate hcandidate
    simpa using hminimum candidate hcandidate
  have hgap :=
    quittingTerminalSemanticDebt_stoppingLawMixture_chordGap_le_nearMinimum
      reward profile mover observer source target lambda 0
        hlambda0 hlambda1 hnear
  dsimp only at hgap
  rw [hsame, sub_self, mul_zero, add_zero] at hgap
  linarith

end GameTheory
