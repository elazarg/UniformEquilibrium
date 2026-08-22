/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.CubicalResetIntegrability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedRadialResetCube
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeWitnessSwitchConsumer

/-!
# Game-facing consumer for radial cap squares

Excess cap nonadditivity on the source-matched radial cube is localized to a
negative square of the behavioral best-response envelope. Fixed pure-time
payoffs have only quadratic square curvature. The generic oriented supremum
switch theorem therefore produces two near-best deterministic quit times on
one diagonal of the literal square.

This file performs the missing game-facing composition. The profitable edge
between those two pure times is decoded at its first disagreement into an
actual reached Quit-versus-Continue comparison on the certificate's literal
receiving profile. The square coordinates, face, sign, observer, profile, and
quantitative source-unit gain are all retained. No chronological reset-cube
path or equilibrium compiler is asserted.
-/

noncomputable section

namespace Math.Finset
namespace CubicalResetIntegrability

variable {Coordinate : Type*} [DecidableEq Coordinate]

/-- A square localized along a duplicate-free word has two fresh, distinct
coordinates at one reached background face. This extraction is kept beside
its game-facing consumer rather than extending the reusable MathUE inventory. -/
theorem exists_fresh_square_of_hasSquareAboveAlong
    (value : Finset Coordinate → ℝ) (threshold : ℝ)
    (source : Finset Coordinate) (word : List Coordinate)
    (hnodup : word.Nodup) (hdisjoint : Disjoint word.toFinset source)
    (hlarge : HasSquareAboveAlong value threshold source word) :
    ∃ background first second,
      first ∉ background ∧ second ∉ background ∧ first ≠ second ∧
        threshold < square value background first second := by
  induction word generalizing source with
  | nil =>
      simp [HasSquareAboveAlong] at hlarge
  | cons coordinate rest ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hcoordinateNotSource : coordinate ∉ source := by
        intro hsource
        exact Finset.disjoint_left.mp hdisjoint (by simp) hsource
      have hrestDisjoint : Disjoint rest.toFinset (insert coordinate source) := by
        rw [Finset.disjoint_left]
        intro other hotherRest hotherInsert
        simp only [List.toFinset_cons, Finset.disjoint_insert_left] at hdisjoint
        rcases Finset.mem_insert.mp hotherInsert with rfl | hotherSource
        · exact hnodupParts.1 (by simpa using hotherRest)
        · exact Finset.disjoint_left.mp hdisjoint.2 hotherRest hotherSource
      simp only [HasSquareAboveAlong] at hlarge
      rcases hlarge with hrest | ⟨other, hotherRest, hpositive⟩
      · exact ih (insert coordinate source) hnodupParts.2 hrestDisjoint hrest
      · have hotherNotSource : other ∉ source := by
          intro hotherSource
          exact Finset.disjoint_left.mp hdisjoint
            (by simp [hotherRest]) hotherSource
        have hne : coordinate ≠ other := by
          intro heq
          subst other
          exact hnodupParts.1 hotherRest
        exact ⟨source, coordinate, other, hcoordinateNotSource,
          hotherNotSource, hne, hpositive⟩

end CubicalResetIntegrability
end Math.Finset

namespace GameTheory

open Math.Finset.CubicalResetIntegrability
open Math.Optimization

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

/-- A negative radial cap square together with its reached first-disagreement
consumer. The generic switch theorem has two possible receiving diagonals:
the square base, or the side obtained by inserting `second`. -/
def HasQuittingSourceMatchedRadialCapSquareFirstDisagreementConsumer
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold lower : ℝ) : Prop :=
  ∃ base first second,
    first ∉ base ∧ second ∉ base ∧ first ≠ second ∧
      threshold < square
        (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
          hweight1 observer face) base first second ∧
      let data := frontier.sourceMatchedRadialResetCubeData rank weight
        hweight0 hweight1
      (HasQuittingPureTimeFirstDisagreementGain reward
          (data.profile (frontier.sourceMatchedRadialActiveFace base))
          observer lower ∨
        HasQuittingPureTimeFirstDisagreementGain reward
          (data.profile
            (frontier.sourceMatchedRadialActiveFace (insert second base)))
          observer lower)

/-- **Localized negative cap square to a literal reached action comparison.**

The fixed-witness square budget is the exact radial `O(lambda²)` bound. Once
the localized negative cap square exceeds `charge + q + 3 * eta`, the oriented
supremum theorem produces a full quitting-game witness-switch certificate on
one diagonal. Its receiving payoff edge then lands in the exact
first-disagreement consumer with source-unit gain `charge + eta`. -/
theorem has_sourceMatchedRadialCapSquareFirstDisagreementConsumer_of_negativeSquare
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta bound : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hbudget : charge +
        4 * bound * frontier.lambda (frontier.subseq rank) *
          frontier.lambda (frontier.subseq rank) + 3 * eta ≤ threshold)
    (hnegative : HasSquareAboveAlong
      (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
        hweight1 observer face) threshold ∅
      (Finset.univ : Finset {who // who ∈ frontier.active}).toList) :
    HasQuittingSourceMatchedRadialCapSquareFirstDisagreementConsumer
      frontier rank weight hweight0 hweight1 observer threshold
        (charge + eta) := by
  let activeWord :=
    (Finset.univ : Finset {who // who ∈ frontier.active}).toList
  have hwordNodup : activeWord.Nodup := by
    exact (Finset.univ : Finset {who // who ∈ frontier.active}).nodup_toList
  have hwordDisjoint : Disjoint activeWord.toFinset
      (∅ : Finset {who // who ∈ frontier.active}) := by
    simp
  obtain ⟨base, first, second, hfirst, hsecond, hne, hsquare⟩ :=
    exists_fresh_square_of_hasSquareAboveAlong
      (fun face ↦ -frontier.sourceMatchedRadialFaceCap rank weight hweight0
        hweight1 observer face) threshold ∅ activeWord hwordNodup
          hwordDisjoint (by simpa only [activeWord] using hnegative)
  let cap := frontier.sourceMatchedRadialFaceCap rank weight hweight0 hweight1
    observer
  have hnegSquareEq :
      square (fun face ↦ -cap face) base first second =
        -square cap base first second := by
    simp [square, edge]
    ring
  have hsquare' : threshold < -square cap base first second := by
    rw [← hnegSquareEq]
    simpa only [cap] using hsquare
  let q := 4 * bound * frontier.lambda (frontier.subseq rank) *
    frontier.lambda (frontier.subseq rank)
  have hq : 0 ≤ q := by
    dsimp only [q]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbound)
        (frontier.lambda_pos (frontier.subseq rank)).le)
      (frontier.lambda_pos (frontier.subseq rank)).le
  have hthresholdPositive : 0 < threshold := by
    dsimp only [q] at hq
    nlinarith
  have hcapSquareNegative : square cap base first second < 0 := by
    linarith
  have hcurvature : charge + q + 3 * eta ≤
      |square cap base first second| := by
    rw [abs_of_neg hcapSquareNegative]
    dsimp only [q]
    linarith
  let data := frontier.sourceMatchedRadialResetCubeData rank weight
    hweight0 hweight1
  let x00 := data.profile (frontier.sourceMatchedRadialActiveFace base)
  let x10 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert first base))
  let x01 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert second base))
  let x11 := data.profile
    (frontier.sourceMatchedRadialActiveFace (insert second (insert first base)))
  have hface : ∀ quitTime : Option ℕ,
      |quittingPureTimeDeviationPayoff reward x11 observer quitTime -
          quittingPureTimeDeviationPayoff reward x10 observer quitTime -
          quittingPureTimeDeviationPayoff reward x01 observer quitTime +
          quittingPureTimeDeviationPayoff reward x00 observer quitTime| ≤ q := by
    intro quitTime
    have hfixed := frontier.abs_sourceMatchedRadialFacePayoff_square_le
      rank weight hweight0 hweight1 observer quitTime base first second hfirst
        hsecond hne bound hbound hreward
    simpa only [square, edge, sourceMatchedRadialFacePayoff, data, x00, x10,
      x01, x11, q] using hfixed
  have hcurvature' : charge + q + 3 * eta ≤
      |quittingContinuationBestResponseValue reward x11 observer -
          quittingContinuationBestResponseValue reward x10 observer -
          quittingContinuationBestResponseValue reward x01 observer +
          quittingContinuationBestResponseValue reward x00 observer| := by
    simpa only [cap, square, edge, sourceMatchedRadialFaceCap, data, x00, x10,
      x01, x11] using hcurvature
  have hswitch :=
    exists_pureTimeWitnessSwitchCertificate_of_abs_envelopeCurvature reward
      x00 x10 x01 x11 observer q charge eta hcharge heta hface hcurvature'
  have hpositive : 0 < charge + eta := add_pos hcharge heta
  unfold HasQuittingSourceMatchedRadialCapSquareFirstDisagreementConsumer
  refine ⟨base, first, second, hfirst, hsecond, hne, hsquare, ?_⟩
  dsimp only
  rcases hswitch with ⟨certificate⟩ | ⟨certificate⟩
  · left
    simpa only [data, x00] using
      certificate.hasReceivingFirstDisagreementGain hpositive
  · right
    simpa only [data, x01] using
      certificate.hasReceivingFirstDisagreementGain hpositive

/-- **Cap nonadditivity is either small or game-semantically consumed.**

This is the direct composition of the radial cap-square localizer with the
first-disagreement consumer above. The right branch no longer stops at a
static cap square: it contains an actual reached Quit-versus-Continue
comparison on one literal receiving profile of that square. -/
theorem sourceMatchedRadialFaceCapNonadditivity_le_or_hasFirstDisagreementConsumer
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (rank : ℕ) (weight : {who // who ∈ frontier.active} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold charge eta bound : ℝ)
    (hcharge : 0 < charge) (heta : 0 < eta)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hbudget : charge +
        4 * bound * frontier.lambda (frontier.subseq rank) *
          frontier.lambda (frontier.subseq rank) + 3 * eta ≤ threshold) :
    finiteCubeCapNonadditivity
          (frontier.sourceMatchedRadialFaceCap rank weight hweight0 hweight1
            observer) ≤
        (squareCount
          (Finset.univ : Finset {who // who ∈ frontier.active}).toList : ℝ) *
          threshold ∨
      HasQuittingSourceMatchedRadialCapSquareFirstDisagreementConsumer
        frontier rank weight hweight0 hweight1 observer threshold
          (charge + eta) := by
  rcases frontier.sourceMatchedRadialFaceCapNonadditivity_le_or_hasNegativeSquare
      rank weight hweight0 hweight1 observer threshold with hnear | hnegative
  · exact Or.inl hnear
  · exact Or.inr
      (frontier.has_sourceMatchedRadialCapSquareFirstDisagreementConsumer_of_negativeSquare
        rank weight hweight0 hweight1 observer threshold charge eta bound
          hcharge heta hbound hreward hbudget hnegative)

end GameTheory
