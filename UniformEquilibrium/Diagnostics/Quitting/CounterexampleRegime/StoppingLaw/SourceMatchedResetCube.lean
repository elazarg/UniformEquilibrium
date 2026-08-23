/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedChattering
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawResetCubeOrientation

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
open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {witness : QuittingTerminalExploitabilityWitness reward}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- Extend the active frontier replacement family by the unchanged source
strategy on inactive players. -/
def sourceMatchedReplacement
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  if hwho : who ∈ frontier.positiveDebtSupport then
    frontier.replacement ⟨who, hwho⟩ rank
  else
    frontier.source rank who

@[simp]
theorem sourceMatchedReplacement_active
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    frontier.sourceMatchedReplacement rank mover.1 =
      frontier.replacement mover rank := by
  unfold sourceMatchedReplacement
  rw [dif_pos mover.property]
  congr

/-- The common-source, common-scale reset cube underlying one actual frontier
index. -/
def sourceMatchedResetCubeData
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) : QuittingStoppingLawResetCubeData reward where
  source := frontier.source rank
  target := frontier.sourceMatchedReplacement rank
  scale := fun _who ↦ frontier.scale rank
  scale_nonneg := fun _who ↦ (frontier.scale_pos rank).le
  scale_le_one := fun _who ↦ frontier.scale_le_one rank

@[simp]
theorem sourceMatchedResetCubeData_profile_empty
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) :
    (frontier.sourceMatchedResetCubeData rank).profile ∅ =
      frontier.source rank := by
  funext who
  simp [QuittingStoppingLawResetCubeData.profile,
    sourceMatchedResetCubeData]

/-- Any reset cube inherits the exact carrier-minimum lower bound between its
empty face and every other face. -/
theorem resetCubeData_totalDebtChange_ge_neg_sourceExcess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (data : QuittingStoppingLawResetCubeData reward)
    (face : Finset ι) :
    -(quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (data.profile ∅)) -
        quittingTerminalSemanticDebtSum frontier.base) ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (data.profile face)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward (data.profile ∅)) := by
  have hminimum := frontier.base_minimum
    (quittingTerminalSemanticPair reward (data.profile face))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  linarith

/-- Scale-normalized exact-minimum bound for an arbitrary reset cube. -/
theorem resetCubeData_normalizedTotalDebtChange_ge_neg_sourceExcess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (data : QuittingStoppingLawResetCubeData reward)
    (face : Finset ι) :
    -(quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (data.profile ∅)) -
          quittingTerminalSemanticDebtSum frontier.base) /
        frontier.scale rank ≤
      (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (data.profile face)) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward (data.profile ∅))) /
        frontier.scale rank := by
  apply (div_le_div_iff_of_pos_right
    (frontier.scale_pos rank)).2
  exact frontier.resetCubeData_totalDebtChange_ge_neg_sourceExcess
    data face

/-- Uniform asymptotic one-sided minimality for any sequence of reset cubes
whose empty face is the selected frontier source. -/
theorem eventually_all_resetCubeData_normalizedTotalDebtChange_gt_neg
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (data : ℕ → QuittingStoppingLawResetCubeData reward)
    (hsource : ∀ rank,
      (data rank).profile ∅ = frontier.source rank)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ rank in atTop, ∀ face : Finset ι,
      -epsilon <
        (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward ((data rank).profile face)) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward ((data rank).profile ∅))) /
          frontier.scale rank := by
  have hsmall :=
    (tendsto_order.1 frontier.source_excess_over_scale_tendsto_zero).2
      epsilon hepsilon
  apply hsmall.mono
  intro rank hrank face
  have hlower := frontier.resetCubeData_normalizedTotalDebtChange_ge_neg_sourceExcess
    rank (data rank) face
  rw [hsource rank] at hlower
  rw [neg_div] at hlower
  rw [hsource rank]
  linarith

/-- Every face of the literal source-matched cube stays above the exact
minimum-debt carrier point. Consequently, its total-debt change from the
source is bounded below by the negative source excess. -/
theorem sourceMatchedResetCubeData_totalDebtChange_ge_neg_sourceExcess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (face : Finset ι) :
    -(quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedResetCubeData rank).profile ∅)) -
        quittingTerminalSemanticDebtSum frontier.base) ≤
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedResetCubeData rank).profile face)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            ((frontier.sourceMatchedResetCubeData rank).profile ∅)) := by
  exact frontier.resetCubeData_totalDebtChange_ge_neg_sourceExcess
    (frontier.sourceMatchedResetCubeData rank) face

/-- Scale-normalized form of the exact minimum-debt face bound. -/
theorem sourceMatchedResetCubeData_normalizedTotalDebtChange_ge_neg_sourceExcess
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (face : Finset ι) :
    -(quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              ((frontier.sourceMatchedResetCubeData rank).profile ∅)) -
          quittingTerminalSemanticDebtSum frontier.base) /
        frontier.scale rank ≤
      (quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              ((frontier.sourceMatchedResetCubeData rank).profile face)) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              ((frontier.sourceMatchedResetCubeData rank).profile ∅))) /
        frontier.scale rank := by
  exact frontier.resetCubeData_normalizedTotalDebtChange_ge_neg_sourceExcess rank
    (frontier.sourceMatchedResetCubeData rank) face

/-- **Uniform asymptotic one-sided minimality of every reset-cube face.**

The source excess is `o(lambda)`, while every face remains in the semantic
carrier above the exact minimum. Hence, eventually, every face at once has
normalized total-debt change greater than `-epsilon`. No variational
selection or finiteness of the face family is needed. -/
theorem eventually_all_sourceMatchedResetCubeData_normalizedTotalDebtChange_gt_neg
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ rank in atTop, ∀ face : Finset ι,
      -epsilon <
        (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                ((frontier.sourceMatchedResetCubeData rank).profile face)) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                ((frontier.sourceMatchedResetCubeData rank).profile ∅))) /
          frontier.scale rank := by
  exact frontier.eventually_all_resetCubeData_normalizedTotalDebtChange_gt_neg
    frontier.sourceMatchedResetCubeData
    frontier.sourceMatchedResetCubeData_profile_empty hepsilon

/-- The singleton vertex for an active mover is its literal frontier reset. -/
theorem sourceMatchedResetCubeData_profile_singleton
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    (frontier.sourceMatchedResetCubeData rank).profile {mover.1} =
      quittingStoppingLawResetProfile reward
        (frontier.source rank) mover.1
        (frontier.replacement mover rank)
        (frontier.scale rank)
        (frontier.scale_pos rank).le
        (frontier.scale_le_one rank) := by
  funext observer
  by_cases hobserver : observer = mover.1
  · subst observer
    simp [QuittingStoppingLawResetCubeData.profile,
      sourceMatchedResetCubeData, quittingStoppingLawResetProfile,
      frontier.sourceMatchedReplacement_active rank mover]
  · simp [QuittingStoppingLawResetCubeData.profile,
      sourceMatchedResetCubeData, quittingStoppingLawResetProfile,
      hobserver]

/-- Every actual normalized frontier column is exactly the corresponding
frozen debt-cube edge divided by the common positive reset scale. -/
theorem sourceMatchedResetCubeData_debtEdge_eq_scale_mul_actualDirection
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport})
    (observer : ι) :
    let data := frontier.sourceMatchedResetCubeData rank
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    edge (data.value debt) ∅ mover.1 =
      frontier.scale rank *
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
      frontier.scale rank *
        frontier.actualDebtDirection rank mover observer
  rw [sourceMatchedResetCubeData_profile_singleton,
    sourceMatchedResetCubeData_profile_empty]
  unfold actualDebtDirection quittingStoppingLawNormalizedDebtDirection
    quittingTerminalSemanticDebtChange
  field_simp [ne_of_gt (frontier.scale_pos rank)]

/-- A scalar-weighted source star in the reset cube is exactly the common
reset scale times the corresponding weighted normalized-debt star. -/
theorem sum_mul_sourceMatchedResetCubeData_debtEdge_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (coefficient : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (observer : ι) :
    let data := frontier.sourceMatchedResetCubeData rank
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    (∑ mover, coefficient mover * edge (data.value debt) ∅ mover.1) =
      frontier.scale rank *
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
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ budget : ℝ, 0 ≤ budget ∧ ∀ N : ℕ, 0 < N →
      ∃ rank : ℕ, N ≤ rank ∧
        ∃ count : {who // who ∈ frontier.positiveDebtSupport} → ℕ,
          (∀ observer,
            let data := frontier.sourceMatchedResetCubeData rank
            let debt := fun candidate :
                (quittingGame reward).BehaviorProfile ↦
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward candidate) observer
            |∑ mover, ((count mover : ℝ) / N) *
                edge (data.value debt) ∅ mover.1| ≤
              frontier.scale rank *
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
  rw [abs_mul, abs_of_pos (frontier.scale_pos rank)]
  calc
    frontier.scale rank *
          |∑ mover, ((count mover : ℝ) / N) *
            frontier.actualDebtDirection rank mover observer| ≤
        frontier.scale rank *
          (((∑ mover, |frontier.tangent mover observer|) + budget) / N) :=
      mul_le_mul_of_nonneg_left (hdisplacement observer)
        (frontier.scale_pos rank).le
    _ = frontier.scale rank *
        ((∑ mover, |frontier.tangent mover observer|) + budget) / N := by
      ring

/-- The edge-localized pure-time switch theorem on the literal reset cube at
one actual frontier rank.  Both reset directions are active source-matched
best-response chords, and the returned edge retains which one of their movers
changes.  The result is static cube geometry, not play chronology. -/
theorem exists_sourceMatchedResetCubePureTimeWitnessSwitch_of_abs_debtCurvature
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (observer : ι) (base : Finset ι)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (hfirst : first.1 ∉ base) (hsecond : second.1 ∉ base)
    (hne : first.1 ≠ second.1)
    (hobserverFirst : observer ≠ first.1)
    (hobserverSecond : observer ≠ second.1)
    (prescribedBound q charge eta : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hprescribed :
      let data := frontier.sourceMatchedResetCubeData rank
      |quittingTerminalPayoff reward
              (data.profile (insert second.1 (insert first.1 base))) observer -
          quittingTerminalPayoff reward (data.profile (insert first.1 base))
            observer -
          quittingTerminalPayoff reward (data.profile (insert second.1 base))
            observer +
          quittingTerminalPayoff reward (data.profile base) observer| ≤
        prescribedBound)
    (hface :
      let data := frontier.sourceMatchedResetCubeData rank
      ∀ quitTime : Option ℕ,
        |quittingPureTimeDeviationPayoff reward
                (data.profile (insert second.1 (insert first.1 base))) observer
                quitTime -
            quittingPureTimeDeviationPayoff reward
                (data.profile (insert first.1 base)) observer quitTime -
            quittingPureTimeDeviationPayoff reward
                (data.profile (insert second.1 base)) observer quitTime +
            quittingPureTimeDeviationPayoff reward (data.profile base) observer
                quitTime| ≤ q)
    (hcurvature :
      let data := frontier.sourceMatchedResetCubeData rank
      charge + prescribedBound + q + 3 * eta ≤
        |quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (data.profile (insert second.1 (insert first.1 base))))
                observer -
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (data.profile (insert first.1 base))) observer -
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward
                  (data.profile (insert second.1 base))) observer +
            quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward (data.profile base))
                observer|) :
    let data := frontier.sourceMatchedResetCubeData rank
    (∃ certificate : QuittingPureTimeWitnessSwitchCertificate reward
        (data.profile (insert second.1 (insert first.1 base)))
        (data.profile base) observer charge eta,
      HasQuittingPureTimeResetSquareEdgeWitnessSwitch data observer base
        first.1 second.1 certificate.switch.sourceWitness
          ((charge + eta) / 2)) ∨
      (∃ certificate : QuittingPureTimeWitnessSwitchCertificate reward
          (data.profile (insert first.1 base))
          (data.profile (insert second.1 base)) observer charge eta,
        HasQuittingPureTimeResetSquareEdgeWitnessSwitch data observer base
          first.1 second.1 certificate.switch.sourceWitness
            ((charge + eta) / 2)) := by
  dsimp only at hprescribed hface hcurvature ⊢
  exact exists_resetCubePureTimeSquareEdgeWitnessSwitch_of_abs_debtCurvature
    (frontier.sourceMatchedResetCubeData rank) observer base first.1 second.1
    hfirst hsecond hne hobserverFirst hobserverSecond prescribedBound q charge
      eta hcharge heta hprescribed hface hcurvature

end QuittingPositiveMinimumDebtTangentFamily
end GameTheory
