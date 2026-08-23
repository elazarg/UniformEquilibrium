/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Frozen.RadialScaling
import UniformEquilibrium.Diagnostics.Quitting.Frozen.ResetCube

/-!
# Radially scaled frozen common-source stopping-law reset cubes

A flat charged circulation supplies one legal radial coefficient for every
active player.  This file places those coefficients in one literal reset cube
at the common frontier source.  Every frozen active edge is exactly the
frontier reset scale times the corresponding radial debt direction.

Consequently, the whole frozen cube star is asymptotically balanced after
normalization by the frontier scale, while its mover-diagonal charge converges
to a strictly positive number.  This is a simultaneous-profile realization
of the charged star.  It does not assert that the cube path is a chronological
quitting-game prefix.
-/

noncomputable section

namespace GameTheory

open Filter Finset Math.Finset.CubicalResetIntegrability Math.Optimization
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingPositiveMinimumDebtTangentFamily

/-- Extend the active inner resets by the unchanged source strategies. -/
def frozenRadialCubeTarget
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (who : ι) :
    (quittingGame reward).BehaviorStrategy who :=
  if hwho : who ∈ frontier.positiveDebtSupport then
    frontier.frozenRadialInnerResetStrategy rank ⟨who, hwho⟩
  else
    frontier.source rank who

/-- Extend radial coefficients by zero on inactive players. -/
def frozenRadialCubeScale
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ) (who : ι) : ℝ :=
  if hwho : who ∈ frontier.positiveDebtSupport then weight ⟨who, hwho⟩ else 0

@[simp]
theorem frozenRadialCubeTarget_active
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    frontier.frozenRadialCubeTarget rank mover.1 =
      frontier.frozenRadialInnerResetStrategy rank mover := by
  simp [frozenRadialCubeTarget, mover.property]

@[simp]
theorem frozenRadialCubeScale_active
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    frontier.frozenRadialCubeScale weight mover.1 = weight mover := by
  simp [frozenRadialCubeScale, mover.property]

/-- One variable-scale reset cube containing all radially scaled active
frontier columns. -/
def frozenRadialResetCubeData
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) :
    QuittingStoppingLawResetCubeData reward where
  source := frontier.source rank
  target := frontier.frozenRadialCubeTarget rank
  scale := frontier.frozenRadialCubeScale weight
  scale_nonneg := by
    intro who
    by_cases hwho : who ∈ frontier.positiveDebtSupport
    · simpa [frozenRadialCubeScale, hwho] using hweight0 ⟨who, hwho⟩
    · simp [frozenRadialCubeScale, hwho]
  scale_le_one := by
    intro who
    by_cases hwho : who ∈ frontier.positiveDebtSupport
    · simpa [frozenRadialCubeScale, hwho] using hweight1 ⟨who, hwho⟩
    · simp [frozenRadialCubeScale, hwho]

@[simp]
theorem frozenRadialResetCubeData_profile_empty
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) :
    (frontier.frozenRadialResetCubeData rank weight hweight0 hweight1).profile ∅ =
      frontier.source rank := by
  funext who
  simp [QuittingStoppingLawResetCubeData.profile,
    frozenRadialResetCubeData]

/-- **Uniform asymptotic one-sided minimality of every radial-cube face.**

Every radial face is an actual behavioral profile in the semantic carrier,
and the empty face is the frontier source. The exact carrier minimum and the
source's `o(lambda)` excess therefore control all faces simultaneously. -/
theorem eventually_all_frozenRadialResetCubeData_normalizedTotalDebtChange_gt_neg
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ rank in atTop, ∀ face : Finset ι,
      -epsilon <
        (quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                ((frontier.frozenRadialResetCubeData rank weight
                  hweight0 hweight1).profile face)) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                ((frontier.frozenRadialResetCubeData rank weight
                  hweight0 hweight1).profile ∅))) /
          frontier.scale rank := by
  exact frontier.eventually_all_resetCubeData_normalizedTotalDebtChange_gt_neg
    (fun rank ↦ frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1)
    (fun rank ↦ frontier.frozenRadialResetCubeData_profile_empty rank
      weight hweight0 hweight1)
    hepsilon

/-! ## Actual active-face passport/switch adapter -/

/-- Forget the active-subtype labels of a face, obtaining the corresponding
literal reset coordinates in the ambient player cube. -/
def frozenRadialActiveFace
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (face : Finset {who // who ∈ frontier.positiveDebtSupport}) : Finset ι :=
  face.image Subtype.val

@[simp]
private theorem frozenRadialActiveFace_empty
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward) :
    frontier.frozenRadialActiveFace ∅ = ∅ := by
  simp [frozenRadialActiveFace]

@[simp]
private theorem frozenRadialActiveFace_singleton
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    frontier.frozenRadialActiveFace {mover} = {mover.1} := by
  simp [frozenRadialActiveFace]

@[simp]
private theorem frozenRadialActiveFace_insert
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    frontier.frozenRadialActiveFace (insert mover face) =
      insert mover.1 (frontier.frozenRadialActiveFace face) := by
  simp [frozenRadialActiveFace]

@[simp]
private theorem frozenRadialActiveFace_univ
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward) :
    frontier.frozenRadialActiveFace Finset.univ = frontier.positiveDebtSupport := by
  ext who
  simp [frozenRadialActiveFace]

/-- After rebasing at a profile which retains one active player's source
strategy, the singleton vertex of the inner frozen common-source cube is exactly
the corresponding inner reset. -/
theorem frozenSourceResetCubeData_rebase_profile_singleton_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (profile : (quittingGame reward).BehaviorProfile)
    (mover : {who // who ∈ frontier.positiveDebtSupport})
    (hsource : profile mover.1 =
      frontier.source rank mover.1) :
    ((frontier.frozenSourceResetCubeData rank).rebase profile).profile
        {mover.1} =
      Function.update profile mover.1
        (frontier.frozenRadialInnerResetStrategy rank mover) := by
  let data := (frontier.frozenSourceResetCubeData rank).rebase profile
  change data.profile (insert mover.1 ∅) = _
  rw [data.profile_insert_eq_reset_of_not_mem ∅ mover.1 (by simp),
    QuittingStoppingLawResetCubeData.rebase_profile_empty]
  unfold quittingStoppingLawResetProfile
  apply congrArg (Function.update profile mover.1)
  unfold frozenRadialInnerResetStrategy
  simp [data, QuittingStoppingLawResetCubeData.rebase,
    frozenSourceResetCubeData, frozenSourceReplacement, mover.property,
    hsource]
  congr

/-- The two-coordinate vertex of the same rebased inner cube applies the two
literal inner resets in either order. -/
theorem frozenSourceResetCubeData_rebase_profile_pair_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (profile : (quittingGame reward).BehaviorProfile)
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (hne : first.1 ≠ second.1)
    (hfirstSource : profile first.1 =
      frontier.source rank first.1)
    (hsecondSource : profile second.1 =
      frontier.source rank second.1) :
    ((frontier.frozenSourceResetCubeData rank).rebase profile).profile
        (insert second.1 {first.1}) =
      Function.update
        (Function.update profile first.1
          (frontier.frozenRadialInnerResetStrategy rank first))
        second.1 (frontier.frozenRadialInnerResetStrategy rank second) := by
  let data := (frontier.frozenSourceResetCubeData rank).rebase profile
  have hsecondFresh : second.1 ∉ ({first.1} : Finset ι) := by
    simpa [eq_comm] using hne
  rw [data.profile_insert_eq_reset_of_not_mem {first.1} second.1 hsecondFresh,
    frontier.frozenSourceResetCubeData_rebase_profile_singleton_eq rank
      profile first hfirstSource]
  unfold quittingStoppingLawResetProfile
  have hcurrentSecond :
      Function.update profile first.1
          (frontier.frozenRadialInnerResetStrategy rank first) second.1 =
        profile second.1 := by
    rw [Function.update_of_ne (Ne.symm hne)]
  rw [hcurrentSecond]
  apply congrArg (Function.update
    (Function.update profile first.1
      (frontier.frozenRadialInnerResetStrategy rank first)) second.1)
  unfold frozenRadialInnerResetStrategy
  simp [data, QuittingStoppingLawResetCubeData.rebase,
    frozenSourceResetCubeData, frozenSourceReplacement, second.property,
    hsecondSource]
  congr

/-- One pure-time deviation evaluated on an actual active face of the radial
frozen common-source cube. -/
def frozenRadialFacePayoff
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (quitTime : Option ℕ) : ℝ :=
  quittingPureTimeDeviationPayoff reward
    ((frontier.frozenRadialResetCubeData rank weight hweight0
      hweight1).profile (frontier.frozenRadialActiveFace face))
    observer quitTime

/-- The behavioral best-response cap on one actual active radial face. -/
def frozenRadialFaceCap
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (face : Finset {who // who ∈ frontier.positiveDebtSupport}) : ℝ :=
  quittingContinuationBestResponseValue reward
    ((frontier.frozenRadialResetCubeData rank weight hweight0
      hweight1).profile (frontier.frozenRadialActiveFace face)) observer

/-- Cap nonadditivity on the actual radial cube is either below the requested
full-word budget or localized to one literal negative cap square. -/
theorem frozenRadialFaceCapNonadditivity_le_or_hasNegativeSquare
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (threshold : ℝ) :
    finiteCubeCapNonadditivity
          (frontier.frozenRadialFaceCap rank weight hweight0 hweight1
            observer) ≤
        (squareCount
          (Finset.univ : Finset {who // who ∈ frontier.positiveDebtSupport}).toList : ℝ) *
          threshold ∨
      HasSquareAboveAlong
        (fun face ↦ -frontier.frozenRadialFaceCap rank weight hweight0
          hweight1 observer face) threshold ∅
        (Finset.univ : Finset {who // who ∈ frontier.positiveDebtSupport}).toList := by
  exact finiteCubeCapNonadditivity_le_or_hasNegativeSquare
    (frontier.frozenRadialFaceCap rank weight hweight0 hweight1 observer)
      threshold

/-- **Exact nested square law for the radial frozen common-source cube.**

For a fixed pure-time deviation, a square in two opponent coordinates is the
product of the outer radial weights times the corresponding square in the
inner common-scale frozen common-source cube rebased at that deviation. The inner
square therefore carries another factor `lambda²`. -/
theorem frozenRadialFacePayoff_square_eq_weights_mul_innerSquare
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (quitTime : Option ℕ)
    (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (hfirst : first ∉ face) (hsecond : second ∉ face)
    (hne : first.1 ≠ second.1) (hobserverFirst : observer ≠ first.1)
    (hobserverSecond : observer ≠ second.1) :
    let radialData := frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1
    let ambientFace := frontier.frozenRadialActiveFace face
    let deviationProfile := Function.update (radialData.profile ambientFace)
      observer (quittingPureTimeBehaviorStrategy reward observer quitTime)
    let innerData := (frontier.frozenSourceResetCubeData rank).rebase
      deviationProfile
    square
        (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
          hweight0 hweight1 observer reset quitTime) face first second =
      weight first * weight second *
        square (innerData.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
          ∅ first.1 second.1 := by
  dsimp only
  let radialData := frontier.frozenRadialResetCubeData rank weight
    hweight0 hweight1
  let ambientFace := frontier.frozenRadialActiveFace face
  let deviation := quittingPureTimeBehaviorStrategy reward observer quitTime
  let deviationProfile := Function.update (radialData.profile ambientFace)
    observer deviation
  let innerData := (frontier.frozenSourceResetCubeData rank).rebase
    deviationProfile
  have hfirstAmbient : first.1 ∉ ambientFace := by
    simpa [ambientFace, frozenRadialActiveFace] using hfirst
  have hsecondAmbient : second.1 ∉ ambientFace := by
    simpa [ambientFace, frozenRadialActiveFace] using hsecond
  have hdeviationFirst : deviationProfile first.1 =
      frontier.source rank first.1 := by
    dsimp only [deviationProfile]
    rw [Function.update_of_ne (Ne.symm hobserverFirst)]
    exact radialData.profile_apply_of_not_mem ambientFace first.1 hfirstAmbient
  have hdeviationSecond : deviationProfile second.1 =
      frontier.source rank second.1 := by
    dsimp only [deviationProfile]
    rw [Function.update_of_ne (Ne.symm hobserverSecond)]
    exact radialData.profile_apply_of_not_mem ambientFace second.1 hsecondAmbient
  have hinnerEmpty : innerData.profile ∅ = deviationProfile := by
    exact QuittingStoppingLawResetCubeData.rebase_profile_empty _ _
  have hinnerFirst : innerData.profile {first.1} =
      Function.update deviationProfile first.1
        (frontier.frozenRadialInnerResetStrategy rank first) := by
    exact frontier.frozenSourceResetCubeData_rebase_profile_singleton_eq
      rank deviationProfile first hdeviationFirst
  have hinnerSecond : innerData.profile {second.1} =
      Function.update deviationProfile second.1
        (frontier.frozenRadialInnerResetStrategy rank second) := by
    exact frontier.frozenSourceResetCubeData_rebase_profile_singleton_eq
      rank deviationProfile second hdeviationSecond
  have hinnerPair : innerData.profile (insert second.1 {first.1}) =
      Function.update
        (Function.update deviationProfile first.1
          (frontier.frozenRadialInnerResetStrategy rank first))
        second.1
          (frontier.frozenRadialInnerResetStrategy rank second) := by
    exact frontier.frozenSourceResetCubeData_rebase_profile_pair_eq rank
      deviationProfile first second hne hdeviationFirst hdeviationSecond
  have houter := quittingPureTimeDeviationPayoff_resetCube_square_eq radialData
    observer quitTime ambientFace first.1 second.1 hfirstAmbient hsecondAmbient
      hne hobserverFirst hobserverSecond
  have hfaceSquare :
      square
          (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
            hweight0 hweight1 observer reset quitTime) face first second =
        square
          (fun reset ↦ quittingPureTimeDeviationPayoff reward
            (radialData.profile reset) observer quitTime)
          ambientFace first.1 second.1 := by
    simp [square, edge, frozenRadialFacePayoff, radialData, ambientFace]
  have hscaleFirst : radialData.scale first.1 = weight first := by
    exact frontier.frozenRadialCubeScale_active weight first
  have hscaleSecond : radialData.scale second.1 = weight second := by
    exact frontier.frozenRadialCubeScale_active weight second
  have htargetFirst : radialData.target first.1 =
      frontier.frozenRadialInnerResetStrategy rank first := by
    exact frontier.frozenRadialCubeTarget_active rank first
  have htargetSecond : radialData.target second.1 =
      frontier.frozenRadialInnerResetStrategy rank second := by
    exact frontier.frozenRadialCubeTarget_active rank second
  have hinnerFirst' : innerData.profile (insert first.1 ∅) =
      Function.update deviationProfile first.1
        (frontier.frozenRadialInnerResetStrategy rank first) := by
    simpa using hinnerFirst
  have hinnerSecond' : innerData.profile (insert second.1 ∅) =
      Function.update deviationProfile second.1
        (frontier.frozenRadialInnerResetStrategy rank second) := by
    simpa using hinnerSecond
  have hinnerPair' : innerData.profile (insert second.1 (insert first.1 ∅)) =
      Function.update
        (Function.update deviationProfile first.1
          (frontier.frozenRadialInnerResetStrategy rank first))
        second.1
          (frontier.frozenRadialInnerResetStrategy rank second) := by
    simpa using hinnerPair
  have hinnerSquare :
      square (innerData.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
          ∅ first.1 second.1 =
        quittingTerminalPayoff reward
              (Function.update
                (Function.update deviationProfile first.1
                  (frontier.frozenRadialInnerResetStrategy rank first))
                second.1
                  (frontier.frozenRadialInnerResetStrategy rank second))
              observer -
          quittingTerminalPayoff reward
              (Function.update deviationProfile first.1
                (frontier.frozenRadialInnerResetStrategy rank first)) observer -
          quittingTerminalPayoff reward
              (Function.update deviationProfile second.1
                (frontier.frozenRadialInnerResetStrategy rank second)) observer +
          quittingTerminalPayoff reward deviationProfile observer := by
    simp only [square, edge, QuittingStoppingLawResetCubeData.value]
    rw [hinnerEmpty, hinnerFirst', hinnerSecond', hinnerPair']
    ring
  rw [hfaceSquare, houter]
  rw [hscaleFirst, hscaleSecond, htargetFirst, htargetSecond, hinnerSquare]

/-- Every opponent square of a radial pure-time payoff is uniformly
`O(lambda²)`, independently of the face, quit time, and radial weights. -/
theorem abs_frozenRadialFacePayoff_square_le_of_ne
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (quitTime : Option ℕ)
    (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (hfirst : first ∉ face) (hsecond : second ∉ face)
    (hne : first.1 ≠ second.1) (hobserverFirst : observer ≠ first.1)
    (hobserverSecond : observer ≠ second.1) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |square
        (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
          hweight0 hweight1 observer reset quitTime) face first second| ≤
      4 * bound * frontier.scale rank *
        frontier.scale rank := by
  rw [frontier.frozenRadialFacePayoff_square_eq_weights_mul_innerSquare
    rank weight hweight0 hweight1 observer quitTime face first second hfirst
      hsecond hne hobserverFirst hobserverSecond]
  let radialData := frontier.frozenRadialResetCubeData rank weight
    hweight0 hweight1
  let ambientFace := frontier.frozenRadialActiveFace face
  let deviationProfile := Function.update (radialData.profile ambientFace)
    observer (quittingPureTimeBehaviorStrategy reward observer quitTime)
  let innerData := (frontier.frozenSourceResetCubeData rank).rebase
    deviationProfile
  have hinner := abs_quittingTerminalPayoff_resetCube_square_le innerData
    observer ∅ first.1 second.1 (by simp) (by simp) hne bound hreward
  have hinner' :
      |square (innerData.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
          ∅ first.1 second.1| ≤
        4 * bound * frontier.scale rank *
          frontier.scale rank := by
    simpa [innerData, frozenSourceResetCubeData,
      QuittingStoppingLawResetCubeData.rebase] using hinner
  rw [abs_mul, abs_mul, abs_of_nonneg (hweight0 first),
    abs_of_nonneg (hweight0 second)]
  have hweights : weight first * weight second ≤ 1 := by
    nlinarith [hweight0 first, hweight0 second, hweight1 first,
      hweight1 second]
  have hweightProduct : 0 ≤ weight first * weight second :=
    mul_nonneg (hweight0 first) (hweight0 second)
  have hscale := (frontier.scale_pos rank).le
  have htarget : 0 ≤
      4 * bound * frontier.scale rank *
        frontier.scale rank := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbound)
        (frontier.scale_pos rank).le)
      (frontier.scale_pos rank).le
  calc
    weight first * weight second *
          |square (innerData.value fun candidate ↦
            quittingTerminalPayoff reward candidate observer)
            ∅ first.1 second.1| ≤
        weight first * weight second *
          (4 * bound * frontier.scale rank *
            frontier.scale rank) := by
      exact mul_le_mul_of_nonneg_left hinner' hweightProduct
    _ ≤ 1 * (4 * bound * frontier.scale rank *
          frontier.scale rank) := by
      exact mul_le_mul_of_nonneg_right hweights htarget
    _ = 4 * bound * frontier.scale rank *
          frontier.scale rank := one_mul _

/-- The same quadratic bound holds without excluding the observer: a square
using the observer coordinate vanishes because the pure deviation overwrites
that reset. -/
theorem abs_frozenRadialFacePayoff_square_le
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (quitTime : Option ℕ)
    (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (first second : {who // who ∈ frontier.positiveDebtSupport})
    (hfirst : first ∉ face) (hsecond : second ∉ face)
    (hne : first ≠ second) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |square
        (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
          hweight0 hweight1 observer reset quitTime) face first second| ≤
      4 * bound * frontier.scale rank *
        frontier.scale rank := by
  have htarget : 0 ≤
      4 * bound * frontier.scale rank *
        frontier.scale rank := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbound)
        (frontier.scale_pos rank).le)
      (frontier.scale_pos rank).le
  by_cases hfirstObserver : observer = first.1
  · have hfaceSquare :
        square
            (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
              hweight0 hweight1 observer reset quitTime) face first second =
          square
            (fun reset ↦ quittingPureTimeDeviationPayoff reward
              ((frontier.frozenRadialResetCubeData rank weight hweight0
                hweight1).profile reset) observer quitTime)
            (frontier.frozenRadialActiveFace face) first.1 second.1 := by
      simp [square, edge, frozenRadialFacePayoff]
    rw [hfaceSquare,
      quittingPureTimeDeviationPayoff_resetCube_square_eq_zero_of_observer
        _ observer quitTime _ first.1 second.1 (Or.inl hfirstObserver)]
    simpa using htarget
  · by_cases hsecondObserver : observer = second.1
    · have hfaceSquare :
          square
              (fun reset ↦ frontier.frozenRadialFacePayoff rank weight
                hweight0 hweight1 observer reset quitTime) face first second =
            square
              (fun reset ↦ quittingPureTimeDeviationPayoff reward
                ((frontier.frozenRadialResetCubeData rank weight hweight0
                  hweight1).profile reset) observer quitTime)
              (frontier.frozenRadialActiveFace face) first.1 second.1 := by
        simp [square, edge, frozenRadialFacePayoff]
      rw [hfaceSquare,
        quittingPureTimeDeviationPayoff_resetCube_square_eq_zero_of_observer
          _ observer quitTime _ first.1 second.1 (Or.inr hsecondObserver)]
      simpa using htarget
    · exact frontier.abs_frozenRadialFacePayoff_square_le_of_ne rank
        weight hweight0 hweight1 observer quitTime face first second hfirst
        hsecond (Subtype.val_injective.ne hne) hfirstObserver hsecondObserver
        bound hbound hreward

/-- The affine remainder of every fixed pure-time witness on every radial
face is explicitly quadratic in the frontier reset scale. -/
theorem abs_frozenRadialFacePayoff_affineRemainder_le
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (quitTime : Option ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |finiteCubeAffineRemainder
        (frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
          observer) face quitTime| ≤
      (squareCount face.toList : ℝ) *
        (4 * bound * frontier.scale rank *
          frontier.scale rank) := by
  apply abs_finiteCubeAffineRemainder_le_of_fresh
  intro background first second hfirst hsecond hne
  exact frontier.abs_frozenRadialFacePayoff_square_le rank weight
    hweight0 hweight1 observer quitTime background first second hfirst hsecond
      hne bound hbound hreward

/-- A single coarse quadratic budget controls the affine remainder of every
face and every pure-time witness in the finite active cube. -/
theorem abs_frozenRadialFacePayoff_affineRemainder_le_uniform
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    (quitTime : Option ℕ) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |finiteCubeAffineRemainder
        (frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
          observer) face quitTime| ≤
      (Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 *
        (4 * bound * frontier.scale rank *
          frontier.scale rank) := by
  have hface :=
    frontier.abs_frozenRadialFacePayoff_affineRemainder_le rank weight
      hweight0 hweight1 observer face quitTime bound hbound hreward
  have hsquareCount : squareCount face.toList ≤ face.card * face.card := by
    simpa using squareCount_le_length_mul_length face.toList
  have hcard : face.card ≤ Fintype.card {who // who ∈ frontier.positiveDebtSupport} := by
    simpa using Finset.card_le_card (Finset.subset_univ face)
  have hcoefficient :
      (squareCount face.toList : ℝ) ≤
        (Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 := by
    have hnat := hsquareCount.trans (Nat.mul_le_mul hcard hcard)
    simpa [pow_two] using (show
      (squareCount face.toList : ℝ) ≤
        (Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) *
          Fintype.card {who // who ∈ frontier.positiveDebtSupport} by exact_mod_cast hnat)
  have hquadratic : 0 ≤
      4 * bound * frontier.scale rank *
        frontier.scale rank := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hbound)
        (frontier.scale_pos rank).le)
      (frontier.scale_pos rank).le
  exact hface.trans (mul_le_mul_of_nonneg_right hcoefficient hquadratic)

/-- The uniform quadratic affine-remainder budget is `o(lambda)` after
normalization by the positive frontier scale. -/
theorem frozenRadialFacePayoff_affineRemainderBudget_div_tendsto_zero
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (bound : ℝ) :
    Tendsto (fun rank ↦
      ((Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 *
          (4 * bound * frontier.scale rank *
            frontier.scale rank)) /
        frontier.scale rank) atTop (nhds 0) := by
  have hlimit := (tendsto_const_nhds : Tendsto (fun _rank : ℕ ↦
      (Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 *
        (4 * bound)) atTop (nhds _)).mul frontier.scale_tendsto_zero
  convert hlimit using 1
  · funext rank
    field_simp [ne_of_gt (frontier.scale_pos rank)]
  · simp

/-- Equivalently, every face and pure-time witness eventually has affine
remainder at most `epsilon * lambda`, uniformly over the finite cube. -/
theorem eventually_all_frozenRadialFacePayoff_affineRemainder_le
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (bound : ℝ) (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ rank in atTop, ∀ face quitTime,
      |finiteCubeAffineRemainder
          (frontier.frozenRadialFacePayoff rank weight hweight0
            hweight1 observer) face quitTime| ≤
        epsilon * frontier.scale rank := by
  have hbudget :=
    frontier.frozenRadialFacePayoff_affineRemainderBudget_div_tendsto_zero
      bound
  have heventually : ∀ᶠ rank in atTop,
      ((Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 *
          (4 * bound * frontier.scale rank *
            frontier.scale rank)) /
        frontier.scale rank < epsilon :=
    (tendsto_order.1 hbudget).2 _ hepsilon
  filter_upwards [heventually] with rank hrank face quitTime
  have hremainder :=
    frontier.abs_frozenRadialFacePayoff_affineRemainder_le_uniform rank
      weight hweight0 hweight1 observer face quitTime bound hbound hreward
  have hlambda := frontier.scale_pos rank
  apply hremainder.trans
  apply (le_of_lt ((div_lt_iff₀ hlambda).mp hrank))

/-- Every actual radial face admits an `eta`-optimal pure-time witness. -/
theorem exists_frozenRadialFaceWitness
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (face : Finset {who // who ∈ frontier.positiveDebtSupport})
    {eta : ℝ} (heta : 0 < eta) :
    ∃ quitTime : Option ℕ,
      frontier.frozenRadialFaceCap rank weight hweight0 hweight1
            observer face - eta ≤
        frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
          observer face quitTime := by
  let profile :=
    (frontier.frozenRadialResetCubeData rank weight hweight0
      hweight1).profile (frontier.frozenRadialActiveFace face)
  have hbounded :=
    bddAbove_range_quittingPureTimeDeviationPayoff reward profile observer
  have hnonempty :
      (Set.range (quittingPureTimeDeviationPayoff reward profile observer)).Nonempty :=
    Set.range_nonempty _
  have hcap :=
    quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff
      reward profile observer
  have hnear : sSup
        (Set.range (quittingPureTimeDeviationPayoff reward profile observer)) - eta <
      sSup (Set.range
        (quittingPureTimeDeviationPayoff reward profile observer)) := by
    exact sub_lt_self _ heta
  obtain ⟨value, ⟨quitTime, rfl⟩, hvalue⟩ :=
    (lt_csSup_iff hbounded hnonempty).mp hnear
  refine ⟨quitTime, ?_⟩
  dsimp only [frozenRadialFaceCap, frozenRadialFacePayoff, profile]
  rw [hcap]
  exact hvalue.le

/-- **The generic finite-cube passport/switch theorem on the actual radial
frozen common-source cube.**

Approximate pure-time witnesses are selected internally on every active face,
pure-time values are automatically below the behavioral cap, and exact nested
bilinearity supplies the displayed uniform `O(lambda²)` affine-remainder
budget. Thus cap nonadditivity is the only strategic input left. The edge
alternative is a literal active-coordinate edge of this radial cube; the
passport alternative controls the selected full-face witness on every active
face. No chronology is asserted. -/
theorem exists_frozenRadial_commonPassport_or_edgeWitnessSwitch
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observer : ι) (eta beta delta bound : ℝ)
    (heta : 0 < eta) (hetaBeta : eta ≤ beta)
    (hbound : 0 ≤ bound)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hnonadditivity : finiteCubeCapNonadditivity
        (frontier.frozenRadialFaceCap rank weight hweight0 hweight1
          observer) ≤ delta) :
    ∃ witness : Finset {who // who ∈ frontier.positiveDebtSupport} → Option ℕ,
      (∀ face,
        frontier.frozenRadialFaceCap rank weight hweight0 hweight1
              observer face - eta ≤
          frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
            observer face (witness face)) ∧
      ((∃ face base mover,
          face.Nonempty ∧ base ⊆ face ∧ mover ∈ face ∧ mover ∉ base ∧
            (beta - eta) / (face.card : ℝ) <
              finiteCubeRegret
                  (frontier.frozenRadialFaceCap rank weight hweight0
                    hweight1 observer)
                  (frontier.frozenRadialFacePayoff rank weight hweight0
                    hweight1 observer)
                  base (witness face) -
                finiteCubeRegret
                  (frontier.frozenRadialFaceCap rank weight hweight0
                    hweight1 observer)
                  (frontier.frozenRadialFacePayoff rank weight hweight0
                    hweight1 observer)
                  (insert mover base) (witness face)) ∨
        ∀ face,
          finiteCubeRegret
              (frontier.frozenRadialFaceCap rank weight hweight0
                hweight1 observer)
              (frontier.frozenRadialFacePayoff rank weight hweight0
                hweight1 observer)
              face (witness Finset.univ) ≤
            if face = ∅ then beta else
              delta + 2 * eta +
                (((Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) - 1) +
                    ((face.card : ℝ) - 1)) * beta +
                  3 * ((Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^
                    2 * (4 * bound * frontier.scale rank *
                      frontier.scale rank))) := by
  classical
  have hchoice : ∀ face : Finset {who // who ∈ frontier.positiveDebtSupport},
      ∃ quitTime : Option ℕ,
        frontier.frozenRadialFaceCap rank weight hweight0 hweight1
              observer face - eta ≤
          frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
            observer face quitTime := by
    intro face
    exact frontier.exists_frozenRadialFaceWitness rank weight hweight0
      hweight1 observer face heta
  choose witness hwitness using hchoice
  refine ⟨witness, hwitness, ?_⟩
  have hupper : ∀ face quitTime,
      frontier.frozenRadialFacePayoff rank weight hweight0 hweight1
          observer face quitTime ≤
        frontier.frozenRadialFaceCap rank weight hweight0 hweight1
          observer face := by
    intro face quitTime
    dsimp only [frozenRadialFaceCap, frozenRadialFacePayoff]
    exact quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward _ observer
        (quittingPureTimeBehaviorStrategy reward observer quitTime)
  let omega :=
    (Fintype.card {who // who ∈ frontier.positiveDebtSupport} : ℝ) ^ 2 *
      (4 * bound * frontier.scale rank *
        frontier.scale rank)
  have hremainder : ∀ face quitTime,
      |finiteCubeAffineRemainder
          (frontier.frozenRadialFacePayoff rank weight hweight0
            hweight1 observer) face quitTime| ≤ omega := by
    intro face quitTime
    exact frontier.abs_frozenRadialFacePayoff_affineRemainder_le_uniform
      rank weight hweight0 hweight1 observer face quitTime bound hbound hreward
  exact finiteCube_commonPassport_or_edgeWitnessSwitch
    (frontier.frozenRadialFaceCap rank weight hweight0 hweight1 observer)
    (frontier.frozenRadialFacePayoff rank weight hweight0 hweight1 observer)
    witness eta beta delta omega hetaBeta hupper hwitness hremainder
      hnonadditivity

/-- Every active singleton vertex is exactly its literal radial reset. -/
theorem frozenRadialResetCubeData_profile_singleton
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    (frontier.frozenRadialResetCubeData rank weight hweight0 hweight1).profile
        {mover.1} =
      frontier.frozenRadialResetProfile rank mover (weight mover)
        (hweight0 mover) (hweight1 mover) := by
  let data := frontier.frozenRadialResetCubeData rank weight
    hweight0 hweight1
  change data.profile {mover.1} = _
  funext observer
  by_cases hobserver : observer = mover.1
  · subst observer
    rw [data.profile_apply_of_mem {mover.1} mover.1 (by simp)]
    simp only [frozenRadialResetProfile, Function.update_self]
    have htarget : data.target mover.1 =
        frontier.frozenRadialInnerResetStrategy rank mover := by
      exact frontier.frozenRadialCubeTarget_active rank mover
    have hscale : data.scale mover.1 = weight mover := by
      exact frontier.frozenRadialCubeScale_active weight mover
    have hsource : data.source mover.1 =
        frontier.source rank mover.1 := rfl
    rw [htarget, hsource]
    simpa only using
      quittingStoppingLawMixtureBehaviorStrategy_congr_scale reward mover.1
        (frontier.source rank mover.1)
        (frontier.frozenRadialInnerResetStrategy rank mover)
        (data.scale mover.1) (weight mover) (data.scale_nonneg mover.1)
        (data.scale_le_one mover.1) hscale
  · rw [data.profile_apply_of_not_mem {mover.1} observer (by simpa)]
    simp [data, frozenRadialResetCubeData,
      frozenRadialResetProfile, hobserver]

/-- A frozen active cube edge divided by the positive frontier scale is
exactly its normalized radial debt direction. -/
theorem frozenRadialResetCubeData_debtEdge_div_eq_radialDirection
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) (observer : ι) :
    let data := frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    edge (data.value debt) ∅ mover.1 /
        frontier.scale rank =
      frontier.frozenRadialDebtDirection rank mover (weight mover)
        (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [edge]
  change
    (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.frozenRadialResetCubeData rank weight
              hweight0 hweight1).profile {mover.1})) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            ((frontier.frozenRadialResetCubeData rank weight
              hweight0 hweight1).profile ∅)) observer) /
      frontier.scale rank = _
  rw [frontier.frozenRadialResetCubeData_profile_singleton,
    frontier.frozenRadialResetCubeData_profile_empty]
  rfl

/-- The normalized frozen active star is exactly the sum of the normalized
radial debt directions. -/
theorem sum_frozenRadialResetCubeData_debtEdge_div_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) (observer : ι) :
    let data := frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    (∑ mover : {who // who ∈ frontier.positiveDebtSupport},
      edge (data.value debt) ∅ mover.1) /
        frontier.scale rank =
      ∑ mover, frontier.frozenRadialDebtDirection rank mover
        (weight mover) (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mover _moverMem
  exact frontier.frozenRadialResetCubeData_debtEdge_div_eq_radialDirection
    rank weight hweight0 hweight1 mover observer

/-- Listing every active player once turns the cubical frozen-edge sum into
the active-subtype star. -/
theorem frozenEdgeSum_frozenRadialResetCubeData_eq_sum
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1)
    (observable : (quittingGame reward).BehaviorProfile → ℝ) :
    let data := frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1
    frozenEdgeSum (data.value observable) ∅ frontier.positiveDebtSupport.toList =
      ∑ mover : {who // who ∈ frontier.positiveDebtSupport},
        edge (data.value observable) ∅ mover.1 := by
  dsimp only
  rw [frozenEdgeSum,
    ← List.sum_toFinset _ frontier.positiveDebtSupport.nodup_toList]
  simp only [Finset.toList_toFinset]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- The normalized frozen edge sum along the active reset word is exactly the
sum of normalized radial debt directions. -/
theorem frozenEdgeSum_frozenRadialResetCubeData_debt_div_eq
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (rank : ℕ) (weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ)
    (hweight0 : ∀ mover, 0 ≤ weight mover)
    (hweight1 : ∀ mover, weight mover ≤ 1) (observer : ι) :
    let data := frontier.frozenRadialResetCubeData rank weight
      hweight0 hweight1
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    frozenEdgeSum (data.value debt) ∅ frontier.positiveDebtSupport.toList /
        frontier.scale rank =
      ∑ mover, frontier.frozenRadialDebtDirection rank mover
        (weight mover) (hweight0 mover) (hweight1 mover) observer := by
  dsimp only
  rw [frontier.frozenEdgeSum_frozenRadialResetCubeData_eq_sum]
  exact frontier.sum_frozenRadialResetCubeData_debtEdge_div_eq
    rank weight hweight0 hweight1 observer

/-- **A flat charged circulation is one asymptotically balanced literal
variable-scale reset cube.**

There is one cube coordinate per active player.  The normalized frozen debt
star converges coordinatewise to zero, while the normalized mover-diagonal
charge converges to a strictly positive limit. -/
theorem exists_frozenRadialBoundedResetCube
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (hflat : ∀ mover, ∑ observer, frontier.tangent mover observer = 0)
    (hcirculation : HasQuittingStoppingLawFlatChargedCirculation
      frontier.positiveDebtSupport frontier.tangent) :
    ∃ weight : {who // who ∈ frontier.positiveDebtSupport} → ℝ,
      ∃ hweight0 : ∀ mover, 0 ≤ weight mover,
      ∃ hweight1 : ∀ mover, weight mover ≤ 1,
      ∃ charge : ℝ, 0 < charge ∧
        (∀ observer,
          Tendsto (fun rank =>
            let data := frontier.frozenRadialResetCubeData rank weight
              hweight0 hweight1
            let debt := fun candidate :
                (quittingGame reward).BehaviorProfile ↦
              quittingTerminalSemanticDebt
                (quittingTerminalSemanticPair reward candidate) observer
            frozenEdgeSum (data.value debt) ∅ frontier.positiveDebtSupport.toList /
              frontier.scale rank)
            atTop (nhds 0)) ∧
        Tendsto (fun rank =>
          ∑ mover : {who // who ∈ frontier.positiveDebtSupport},
            -(let data := frontier.frozenRadialResetCubeData rank weight
                hweight0 hweight1
              let debt := fun candidate :
                  (quittingGame reward).BehaviorProfile ↦
                quittingTerminalSemanticDebt
                  (quittingTerminalSemanticPair reward candidate) mover.1
              edge (data.value debt) ∅ mover.1 /
                frontier.scale rank))
          atTop (nhds charge) := by
  obtain ⟨weight, hweight0, hweight1, hbalance, charge, hcharge, hchargeLimit⟩ :=
    frontier.exists_frozenRadialBoundedCirculation hflat hcirculation
  refine ⟨weight, hweight0, hweight1, charge, hcharge, ?_, ?_⟩
  · intro observer
    convert hbalance observer using 1
    funext rank
    exact frontier.frozenEdgeSum_frozenRadialResetCubeData_debt_div_eq
      rank weight hweight0 hweight1 observer
  · convert hchargeLimit using 1
    funext rank
    apply Finset.sum_congr rfl
    intro mover _moverMem
    rw [frontier.frozenRadialResetCubeData_debtEdge_div_eq_radialDirection]

end QuittingPositiveMinimumDebtTangentFamily
end GameTheory
