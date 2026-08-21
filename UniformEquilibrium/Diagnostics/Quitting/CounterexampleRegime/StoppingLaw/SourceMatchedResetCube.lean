/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedChattering
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawResetCube

/-!
# A literal reset cube for source-matched stopping-law chords

Every column in a stopping-law frontier is realized at one common profile and
one common reset scale. Extending the active replacements by the unchanged
source strategy produces one literal stopping-law reset cube. Its frozen debt
edge for an active player is exactly the common reset scale times the actual
normalized debt direction.

This is the exact adapter from the source-matched charged star to cubical
reset geometry. Multiplicities remain external scalar weights: the theorem
does not identify a weighted star with a sequentially executable reset word.
-/

noncomputable section

namespace GameTheory

open Math.Finset.CubicalResetIntegrability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleStoppingLawFrontier

/-- Extend the active frontier replacement family by the unchanged source
strategy on inactive players. -/
def sourceMatchedReplacement
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  if hwho : who ∈ frontier.active then
    frontier.bestResponse ⟨who, hwho⟩ (frontier.subseq rank)
  else
    frontier.profiles (frontier.subseq rank) who

@[simp]
theorem sourceMatchedReplacement_active
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    frontier.sourceMatchedReplacement rank mover.1 =
      frontier.bestResponse mover (frontier.subseq rank) := by
  simp [sourceMatchedReplacement, mover.property]

/-- The common-source, common-scale reset cube underlying one actual frontier
index. -/
def sourceMatchedResetCubeData
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) : QuittingStoppingLawResetCubeData reward where
  source := frontier.profiles (frontier.subseq rank)
  target := frontier.sourceMatchedReplacement rank
  scale := fun _who ↦ frontier.lambda (frontier.subseq rank)
  scale_nonneg := fun _who ↦ (frontier.lambda_pos (frontier.subseq rank)).le
  scale_le_one := fun _who ↦ frontier.lambda_le_one (frontier.subseq rank)

@[simp]
theorem sourceMatchedResetCubeData_profile_empty
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) :
    (frontier.sourceMatchedResetCubeData rank).profile ∅ =
      frontier.profiles (frontier.subseq rank) := by
  funext who
  simp [QuittingStoppingLawResetCubeData.profile,
    sourceMatchedResetCubeData]

/-- The singleton vertex for an active mover is its literal frontier reset. -/
theorem sourceMatchedResetCubeData_profile_singleton
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active}) :
    (frontier.sourceMatchedResetCubeData rank).profile {mover.1} =
      quittingStoppingLawResetProfile reward
        (frontier.profiles (frontier.subseq rank)) mover.1
        (frontier.bestResponse mover (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank)) := by
  funext observer
  by_cases hobserver : observer = mover.1
  · subst observer
    simp [QuittingStoppingLawResetCubeData.profile,
      sourceMatchedResetCubeData, quittingStoppingLawResetProfile,
      sourceMatchedReplacement, mover.property]
  · simp [QuittingStoppingLawResetCubeData.profile,
      sourceMatchedResetCubeData, quittingStoppingLawResetProfile,
      hobserver]

/-- Every actual normalized frontier column is exactly the corresponding
frozen debt-cube edge divided by the common positive reset scale. -/
theorem sourceMatchedResetCubeData_debtEdge_eq_scale_mul_actualDirection
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (mover : {who // who ∈ frontier.active})
    (observer : ι) :
    let data := frontier.sourceMatchedResetCubeData rank
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    edge (data.value debt) ∅ mover.1 =
      frontier.lambda (frontier.subseq rank) *
        frontier.actualDebtDirection rank mover observer := by
  dsimp only
  rw [edge]
  change
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedResetCubeData rank).profile {mover.1}))
          observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedResetCubeData rank).profile ∅)) observer =
      frontier.lambda (frontier.subseq rank) *
        frontier.actualDebtDirection rank mover observer
  rw [sourceMatchedResetCubeData_profile_singleton,
    sourceMatchedResetCubeData_profile_empty]
  unfold actualDebtDirection quittingStoppingLawNormalizedDebtDirection
    quittingTerminalSemanticDebtChange
  field_simp [ne_of_gt (frontier.lambda_pos (frontier.subseq rank))]

/-- A scalar-weighted source star in the reset cube is exactly the common
reset scale times the corresponding weighted normalized-debt star. -/
theorem sum_mul_sourceMatchedResetCubeData_debtEdge_eq
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (coefficient : {who // who ∈ frontier.active} → ℝ)
    (observer : ι) :
    let data := frontier.sourceMatchedResetCubeData rank
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    (∑ mover, coefficient mover * edge (data.value debt) ∅ mover.1) =
      frontier.lambda (frontier.subseq rank) *
        ∑ mover, coefficient mover *
          frontier.actualDebtDirection rank mover observer := by
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mover _
  rw [frontier.sourceMatchedResetCubeData_debtEdge_eq_scale_mul_actualDirection]
  ring

/-- **The charged source-matched packet is a small literal reset-cube star.**

At every positive rounding scale, all weighted frozen edges belong to one
actual reset cube. Their aggregate debt displacement is bounded by the common
reset scale times `O(1/N)`, while the normalized mover charge remains
`1 - O(1/N)`. This still does not compose the star chronologically. -/
theorem exists_sourceMatchedChatteringResetCubeStar
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.active frontier.tangent) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ N : ℕ, 0 < N →
      ∃ rank : ℕ, N ≤ rank ∧
        ∃ count : {who // who ∈ frontier.active} → ℕ,
          (∀ observer,
            let data := frontier.sourceMatchedResetCubeData rank
            let debt := fun candidate :
                (quittingGame reward).BehaviorProfile ↦
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward candidate) observer
            |∑ mover, ((count mover : ℝ) / N) *
                edge (data.value debt) ∅ mover.1| ≤
              frontier.lambda (frontier.subseq rank) *
                ((∑ mover, |frontier.tangent mover observer|) + budget) / N) ∧
          1 - ((∑ mover, |frontier.tangent mover mover.1|) + budget) / N ≤
            ∑ mover, ((count mover : ℝ) / N) *
              frontier.actualGain rank mover := by
  obtain ⟨budget, hbudget, hpacket⟩ :=
    frontier.exists_sourceMatchedChattering hcirculation
  refine ⟨budget, hbudget, ?_⟩
  intro N hN
  obtain ⟨rank, hrank, count, hdisplacement, hcharge⟩ := hpacket N hN
  refine ⟨rank, hrank, count, ?_, hcharge⟩
  intro observer
  dsimp only
  rw [frontier.sum_mul_sourceMatchedResetCubeData_debtEdge_eq]
  rw [abs_mul, abs_of_pos (frontier.lambda_pos (frontier.subseq rank))]
  calc
    frontier.lambda (frontier.subseq rank) *
          |∑ mover, ((count mover : ℝ) / N) *
            frontier.actualDebtDirection rank mover observer| ≤
        frontier.lambda (frontier.subseq rank) *
          (((∑ mover, |frontier.tangent mover observer|) + budget) / N) :=
      mul_le_mul_of_nonneg_left (hdisplacement observer)
        (frontier.lambda_pos (frontier.subseq rank)).le
    _ = frontier.lambda (frontier.subseq rank) *
        ((∑ mover, |frontier.tangent mover observer|) + budget) / N := by
      ring

end QuittingCounterexampleStoppingLawFrontier
end GameTheory
