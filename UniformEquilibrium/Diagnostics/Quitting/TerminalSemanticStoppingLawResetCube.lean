/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.CubicalResetIntegrability
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction

/-!
# Literal commuting squares for stopping-law resets

Stopping-law resets of distinct players commute when their source strategies,
target strategies, and mixture scales are frozen at one literal profile.  The
result is therefore an actual Boolean cube of behavior profiles, not merely a
debt-vector analogy.

Every scalar semantic observable has zero signed holonomy around each literal
square.  Nonlinearity enters only when one assigns *strategic charge* to an
edge by re-optimizing best responses at its source. Downstream game-facing
arguments therefore separate common-witness passports from quantitative
two-reset envelope curvature.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Resets of distinct players commute exactly when both mixture segments are
defined from the same original profile. -/
theorem quittingStoppingLawResetProfile_comm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hne : first ≠ second)
    (firstTarget : (quittingGame reward).BehaviorStrategy first)
    (secondTarget : (quittingGame reward).BehaviorStrategy second)
    (firstScale secondScale : ℝ)
    (hfirst0 : 0 ≤ firstScale) (hfirst1 : firstScale ≤ 1)
    (hsecond0 : 0 ≤ secondScale) (hsecond1 : secondScale ≤ 1) :
    quittingStoppingLawResetProfile reward
        (quittingStoppingLawResetProfile reward profile first firstTarget
          firstScale hfirst0 hfirst1)
        second secondTarget secondScale hsecond0 hsecond1 =
      quittingStoppingLawResetProfile reward
        (quittingStoppingLawResetProfile reward profile second secondTarget
          secondScale hsecond0 hsecond1)
        first firstTarget firstScale hfirst0 hfirst1 := by
  unfold quittingStoppingLawResetProfile
  rw [Function.update_of_ne (Ne.symm hne), Function.update_of_ne hne]
  exact Function.update_comm hne _ _ profile

/-- Frozen source, target, and scale data for a Boolean cube of simultaneous
stopping-law resets. -/
structure QuittingStoppingLawResetCubeData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    where
  /-- The common source profile from which every reset segment is frozen. -/
  source : (quittingGame reward).BehaviorProfile
  /-- The target stopping law for each reset coordinate. -/
  target : ∀ who, (quittingGame reward).BehaviorStrategy who
  /-- The reset scale for each coordinate. -/
  scale : ι → ℝ
  /-- Every reset scale is nonnegative. -/
  scale_nonneg : ∀ who, 0 ≤ scale who
  /-- Every reset scale is at most one. -/
  scale_le_one : ∀ who, scale who ≤ 1

namespace QuittingStoppingLawResetCubeData

open Math.Finset
open Math.Finset.CubicalResetIntegrability

/-- The simultaneous profile at a cube vertex. Each selected coordinate is
mixed from the common frozen source, independently of the other selections. -/
def profile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (reset : Finset ι) :
    (quittingGame reward).BehaviorProfile :=
  fun who ↦
    if _hwho : who ∈ reset then
      quittingStoppingLawMixtureBehaviorStrategy reward who
        (data.source who) (data.target who) (data.scale who)
        (data.scale_nonneg who) (data.scale_le_one who)
    else
      data.source who

@[simp] theorem profile_apply_of_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (reset : Finset ι) (who : ι) (hwho : who ∈ reset) :
    data.profile reset who =
      quittingStoppingLawMixtureBehaviorStrategy reward who
        (data.source who) (data.target who) (data.scale who)
        (data.scale_nonneg who) (data.scale_le_one who) := by
  simp [profile, hwho]

@[simp] theorem profile_apply_of_not_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (reset : Finset ι) (who : ι) (hwho : who ∉ reset) :
    data.profile reset who = data.source who := by
  simp [profile, hwho]

/-- Inserting a fresh coordinate into the cube is the literal stopping-law
reset of that coordinate from the reached cube vertex. -/
theorem profile_insert_eq_reset_of_not_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (reset : Finset ι) (who : ι) (hwho : who ∉ reset) :
    data.profile (insert who reset) =
      quittingStoppingLawResetProfile reward (data.profile reset) who
        (data.target who) (data.scale who)
        (data.scale_nonneg who) (data.scale_le_one who) := by
  funext observer
  by_cases hobserver : observer = who
  · subst observer
    simp [profile, quittingStoppingLawResetProfile, hwho]
  · simp [profile, quittingStoppingLawResetProfile, hobserver]

/-- A scalar observable evaluated on every vertex of a frozen stopping-law
reset cube. -/
def value
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (reset : Finset ι) : ℝ :=
  observable (data.profile reset)

/-- Consecutive cube-edge increments telescope exactly to the simultaneous
frozen-reset endpoint. -/
theorem pathEdgeSum_eq_endpoint_sub
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (source : Finset ι) (word : List ι) :
    pathEdgeSum (data.value observable) source word =
      data.value observable (finalSet source word) -
        data.value observable source :=
  CubicalResetIntegrability.pathEdgeSum_eq_endpoint_sub
    (data.value observable) source word

/-- The excess of a simultaneous frozen-reset endpoint over its common-source
star is exactly the triangular sum of two-coordinate square curvatures. -/
theorem endpoint_sub_source_sub_frozen_eq_squareCurvatureSum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (source : Finset ι) (word : List ι) :
    data.value observable (finalSet source word) -
          data.value observable source -
        frozenEdgeSum (data.value observable) source word =
      squareCurvatureSum (data.value observable) source word :=
  CubicalResetIntegrability.endpoint_sub_source_sub_frozen_eq_squareCurvatureSum
      (data.value observable) source word

/-- A positive simultaneous-reset gain beyond the frozen one-coordinate star
forces a positive two-coordinate square at a literal reached cube vertex. -/
theorem hasPositiveSquareAlong_of_frozen_lt_endpoint_sub_source
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (source : Finset ι) (word : List ι)
    (hpositive :
      frozenEdgeSum (data.value observable) source word <
        data.value observable (finalSet source word) -
          data.value observable source) :
    HasPositiveSquareAlong (data.value observable) source word :=
  CubicalResetIntegrability.hasPositiveSquareAlong_of_frozen_lt_endpoint_sub_source
      (data.value observable) source word hpositive

/-- **Source-matched near return or signed two-reset curvature.** For a
frozen reset cube, either the endpoint/path discrepancy is bounded by the
number of square faces times `threshold`, or one literal two-reset square has
curvature larger than `threshold` in one of the two orientations. -/
theorem nearFrozenReturn_or_signedSquareAbove
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (source : Finset ι) (word : List ι)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    |data.value observable (finalSet source word) -
          data.value observable source -
        frozenEdgeSum (data.value observable) source word| ≤
          (squareCount word : ℝ) * threshold ∨
      HasSquareAboveAlong (data.value observable) threshold source word ∨
        HasSquareAboveAlong (fun reset ↦ -data.value observable reset)
          threshold source word :=
  CubicalResetIntegrability.nearFrozenReturn_or_signedSquareAbove
    (data.value observable) source word threshold hthreshold

/-- Either the endpoint itself is close to the source up to the frozen-star
size and the accumulated square threshold, or one signed square exceeds the
threshold. -/
theorem nearReturn_or_signedSquareAbove
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observable : (quittingGame reward).BehaviorProfile → ℝ)
    (source : Finset ι) (word : List ι)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    |data.value observable (finalSet source word) -
        data.value observable source| ≤
          |frozenEdgeSum (data.value observable) source word| +
            (squareCount word : ℝ) * threshold ∨
      HasSquareAboveAlong (data.value observable) threshold source word ∨
        HasSquareAboveAlong (fun reset ↦ -data.value observable reset)
          threshold source word := by
  rcases data.nearFrozenReturn_or_signedSquareAbove observable source word
      threshold hthreshold with hnear | hpositive | hnegative
  · left
    calc
      |data.value observable (finalSet source word) -
          data.value observable source| =
          |(data.value observable (finalSet source word) -
              data.value observable source -
                frozenEdgeSum (data.value observable) source word) +
            frozenEdgeSum (data.value observable) source word| := by ring_nf
      _ ≤
          |data.value observable (finalSet source word) -
              data.value observable source -
                frozenEdgeSum (data.value observable) source word| +
            |frozenEdgeSum (data.value observable) source word| := abs_add_le _ _
      _ ≤ |frozenEdgeSum (data.value observable) source word| +
            (squareCount word : ℝ) * threshold := by linarith
  · exact Or.inr (Or.inl hpositive)
  · exact Or.inr (Or.inr hnegative)

/-- Coordinatewise terminal-debt specialization of the source-matched reset
cube dichotomy. -/
theorem terminalSemanticDebt_nearFrozenReturn_or_signedSquareAbove
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (source : Finset ι) (word : List ι)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    |data.value debt (finalSet source word) - data.value debt source -
        frozenEdgeSum (data.value debt) source word| ≤
          (squareCount word : ℝ) * threshold ∨
      HasSquareAboveAlong (data.value debt) threshold source word ∨
        HasSquareAboveAlong (fun reset ↦ -data.value debt reset)
          threshold source word := by
  dsimp only
  exact data.nearFrozenReturn_or_signedSquareAbove
    (fun candidate ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward candidate) observer)
    source word threshold hthreshold

/-- Rebase a frozen reset cube at a supplied profile while retaining every
target and scale. -/
def rebase
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (source : (quittingGame reward).BehaviorProfile) :
    QuittingStoppingLawResetCubeData reward where
  source := source
  target := data.target
  scale := data.scale
  scale_nonneg := data.scale_nonneg
  scale_le_one := data.scale_le_one

omit [DecidableEq ι] in
@[simp]
theorem rebase_target
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (source : (quittingGame reward).BehaviorProfile) (who : ι) :
    (data.rebase source).target who = data.target who := rfl

omit [DecidableEq ι] in
@[simp]
theorem rebase_scale
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (source : (quittingGame reward).BehaviorProfile) (who : ι) :
    (data.rebase source).scale who = data.scale who := rfl

@[simp]
theorem rebase_profile_empty
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (source : (quittingGame reward).BehaviorProfile) :
    (data.rebase source).profile ∅ = source := by
  funext who
  simp [rebase, profile]

/-- Rebasing at a unilateral deviation commutes with any fresh family of
opponent resets. -/
theorem rebase_deviation_profile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (source reset : Finset ι) (observer : ι)
    (deviation : (quittingGame reward).BehaviorStrategy observer)
    (hdisjoint : Disjoint reset source) (hobserver : observer ∉ reset) :
    (data.rebase (Function.update (data.profile source) observer deviation)).profile
        reset =
      Function.update (data.profile (source ∪ reset)) observer deviation := by
  funext who
  by_cases hwhoReset : who ∈ reset
  · have hwhoSource : who ∉ source := Finset.disjoint_left.mp hdisjoint hwhoReset
    have hwhoObserver : who ≠ observer := by
      intro heq
      subst who
      exact hobserver hwhoReset
    simp [profile, rebase, hwhoReset, hwhoSource, hwhoObserver]
  · by_cases hwhoObserver : who = observer
    · subst who
      simp [profile, rebase, hobserver]
    · simp [profile, rebase, hwhoReset, hwhoObserver]

end QuittingStoppingLawResetCubeData

/-- Every scalar observable has the exact square identity on two literal
stopping-law resets. -/
theorem stoppingLawReset_square_identity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι) (hne : first ≠ second)
    (firstTarget : (quittingGame reward).BehaviorStrategy first)
    (secondTarget : (quittingGame reward).BehaviorStrategy second)
    (firstScale secondScale : ℝ)
    (hfirst0 : 0 ≤ firstScale) (hfirst1 : firstScale ≤ 1)
    (hsecond0 : 0 ≤ secondScale) (hsecond1 : secondScale ≤ 1)
    (observable : (quittingGame reward).BehaviorProfile → ℝ) :
    let firstProfile := quittingStoppingLawResetProfile reward profile first
      firstTarget firstScale hfirst0 hfirst1
    let secondProfile := quittingStoppingLawResetProfile reward profile second
      secondTarget secondScale hsecond0 hsecond1
    let bothFromFirst := quittingStoppingLawResetProfile reward firstProfile
      second secondTarget secondScale hsecond0 hsecond1
    let bothFromSecond := quittingStoppingLawResetProfile reward secondProfile
      first firstTarget firstScale hfirst0 hfirst1
    (observable bothFromFirst - observable firstProfile) -
        (observable secondProfile - observable profile) =
      (observable bothFromSecond - observable secondProfile) -
        (observable firstProfile - observable profile) := by
  dsimp only
  rw [quittingStoppingLawResetProfile_comm reward profile first second hne
    firstTarget secondTarget firstScale secondScale hfirst0 hfirst1 hsecond0 hsecond1]
  ring

/-- Terminal payoff is bilinear in two distinct complete stopping-law mixture
coordinates. This is the profile-level form of the reset-cube square law. -/
theorem quittingTerminalPayoff_twoStoppingLawMixtures_rectangle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (observer first second : ι) (hne : first ≠ second)
    (firstTarget : (quittingGame reward).BehaviorStrategy first)
    (secondTarget : (quittingGame reward).BehaviorStrategy second)
    (firstScale secondScale : ℝ)
    (hfirst0 : 0 ≤ firstScale) (hfirst1 : firstScale ≤ 1)
    (hsecond0 : 0 ≤ secondScale) (hsecond1 : secondScale ≤ 1) :
    let firstMixed := quittingStoppingLawMixtureBehaviorStrategy reward first
      (profile first) firstTarget firstScale hfirst0 hfirst1
    let secondMixed := quittingStoppingLawMixtureBehaviorStrategy reward second
      (profile second) secondTarget secondScale hsecond0 hsecond1
    quittingTerminalPayoff reward
          (Function.update (Function.update profile first firstMixed) second
            secondMixed) observer -
        quittingTerminalPayoff reward
          (Function.update profile first firstMixed) observer -
      (quittingTerminalPayoff reward
          (Function.update profile second secondMixed) observer -
        quittingTerminalPayoff reward profile observer) =
      firstScale * secondScale *
        (quittingTerminalPayoff reward
              (Function.update (Function.update profile first firstTarget)
                second secondTarget) observer -
          quittingTerminalPayoff reward
              (Function.update profile first firstTarget) observer -
          quittingTerminalPayoff reward
              (Function.update profile second secondTarget) observer +
          quittingTerminalPayoff reward profile observer) := by
  dsimp only
  let firstMixed := quittingStoppingLawMixtureBehaviorStrategy reward first
    (profile first) firstTarget firstScale hfirst0 hfirst1
  let secondMixed := quittingStoppingLawMixtureBehaviorStrategy reward second
    (profile second) secondTarget secondScale hsecond0 hsecond1
  have hsecondAtSource := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile second observer (profile second) secondTarget secondScale
      hsecond0 hsecond1
  have hsecondAtFirst := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile first firstMixed) second observer
      (profile second) secondTarget secondScale hsecond0 hsecond1
  have hfirstAtSource := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile first observer (profile first) firstTarget firstScale
      hfirst0 hfirst1
  have hfirstAtSecondTarget := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile second secondTarget) first observer
      (profile first) firstTarget firstScale hfirst0 hfirst1
  have hcommuteTarget :
      Function.update (Function.update profile first firstTarget) second
          secondTarget =
        Function.update (Function.update profile second secondTarget) first
          firstTarget := Function.update_comm hne _ _ _
  have hcommuteFirstMixedSecondTarget :
      Function.update (Function.update profile first firstMixed) second
          secondTarget =
        Function.update (Function.update profile second secondTarget) first
          firstMixed := Function.update_comm hne _ _ _
  have hfirstSourceAtSecond :
      Function.update profile second secondTarget first = profile first := by
    rw [Function.update_of_ne hne]
  have hsecondSourceAtFirst :
      Function.update profile first firstMixed second = profile second := by
    rw [Function.update_of_ne (Ne.symm hne)]
  have hupdateSecondSourceAtFirst :
      Function.update (Function.update profile first firstMixed) second
          (profile second) = Function.update profile first firstMixed := by
    rw [← hsecondSourceAtFirst]
    exact Function.update_eq_self second _
  have hupdateFirstSourceAtSecond :
      Function.update (Function.update profile second secondTarget) first
          (profile first) = Function.update profile second secondTarget := by
    rw [← hfirstSourceAtSecond]
    exact Function.update_eq_self first _
  rw [hupdateSecondSourceAtFirst] at hsecondAtFirst
  rw [hupdateFirstSourceAtSecond] at hfirstAtSecondTarget
  simp only [Function.update_eq_self] at hsecondAtSource hfirstAtSource
  rw [← hcommuteFirstMixedSecondTarget, ← hcommuteTarget]
    at hfirstAtSecondTarget
  rw [hsecondAtFirst, hsecondAtSource, hfirstAtSecondTarget, hfirstAtSource]
  ring

/-- **Exact bilinear scaling of a terminal-payoff reset square.**

For two fresh reset coordinates, the mixed square is the product of the two
stopping-law scales times the rectangle obtained by replacing both strategies
fully by their frozen targets. Other coordinates may already be reset in the
background face. -/
theorem quittingTerminalPayoff_resetCube_square_eq_scale_mul_scale_mul
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (source : Finset ι) (first second : ι)
    (hfirst : first ∉ source) (hsecond : second ∉ source)
    (hne : first ≠ second) :
    let profile := data.profile source
    Math.Finset.CubicalResetIntegrability.square
        (data.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
        source first second =
      data.scale first * data.scale second *
        (quittingTerminalPayoff reward
              (Function.update (Function.update profile first
                (data.target first)) second (data.target second)) observer -
          quittingTerminalPayoff reward
              (Function.update profile first (data.target first)) observer -
          quittingTerminalPayoff reward
              (Function.update profile second (data.target second)) observer +
          quittingTerminalPayoff reward profile observer) := by
  dsimp only
  let profile := data.profile source
  let firstMixed := quittingStoppingLawMixtureBehaviorStrategy reward first
    (profile first) (data.target first) (data.scale first)
      (data.scale_nonneg first) (data.scale_le_one first)
  let secondMixed := quittingStoppingLawMixtureBehaviorStrategy reward second
    (profile second) (data.target second) (data.scale second)
      (data.scale_nonneg second) (data.scale_le_one second)
  have hfirstProfile : data.profile (insert first source) =
      Function.update profile first firstMixed := by
    rw [data.profile_insert_eq_reset_of_not_mem source first hfirst]
    rfl
  have hsecondProfile : data.profile (insert second source) =
      Function.update profile second secondMixed := by
    rw [data.profile_insert_eq_reset_of_not_mem source second hsecond]
    rfl
  have hsecondFresh : second ∉ insert first source := by
    simp [hsecond, Ne.symm hne]
  have hbothProfile : data.profile (insert second (insert first source)) =
      Function.update (Function.update profile first firstMixed)
        second secondMixed := by
    rw [data.profile_insert_eq_reset_of_not_mem
      (insert first source) second hsecondFresh]
    unfold quittingStoppingLawResetProfile
    rw [hfirstProfile]
    have hsourceSecond : Function.update profile first firstMixed second =
        profile second := by
      rw [Function.update_of_ne (Ne.symm hne)]
    rw [hsourceSecond]
  have hsecondAtSource := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile second observer (profile second) (data.target second)
      (data.scale second) (data.scale_nonneg second)
        (data.scale_le_one second)
  have hsecondAtFirst := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile first firstMixed) second observer
      (profile second) (data.target second) (data.scale second)
        (data.scale_nonneg second) (data.scale_le_one second)
  have hfirstAtSource := quittingTerminalPayoff_stoppingLawMixture_eq
    reward profile first observer (profile first) (data.target first)
      (data.scale first) (data.scale_nonneg first) (data.scale_le_one first)
  have hfirstAtSecondTarget := quittingTerminalPayoff_stoppingLawMixture_eq
    reward (Function.update profile second (data.target second)) first observer
      (profile first) (data.target first) (data.scale first)
        (data.scale_nonneg first) (data.scale_le_one first)
  have hcommuteTarget :
      Function.update (Function.update profile first (data.target first)) second
          (data.target second) =
        Function.update (Function.update profile second (data.target second)) first
          (data.target first) := Function.update_comm hne _ _ _
  have hcommuteFirstMixedSecondTarget :
      Function.update (Function.update profile first firstMixed) second
          (data.target second) =
        Function.update (Function.update profile second (data.target second)) first
          firstMixed := Function.update_comm hne _ _ _
  have hfirstSourceAtSecond :
      Function.update profile second (data.target second) first = profile first := by
    rw [Function.update_of_ne hne]
  have hsecondSourceAtFirst :
      Function.update profile first firstMixed second = profile second := by
    rw [Function.update_of_ne (Ne.symm hne)]
  have hupdateSecondSourceAtFirst :
      Function.update (Function.update profile first firstMixed) second
          (profile second) = Function.update profile first firstMixed := by
    rw [← hsecondSourceAtFirst]
    exact Function.update_eq_self second _
  have hupdateFirstSourceAtSecond :
      Function.update (Function.update profile second (data.target second)) first
          (profile first) =
        Function.update profile second (data.target second) := by
    rw [← hfirstSourceAtSecond]
    exact Function.update_eq_self first _
  rw [hupdateSecondSourceAtFirst] at hsecondAtFirst
  rw [hupdateFirstSourceAtSecond] at hfirstAtSecondTarget
  simp only [Function.update_eq_self] at hsecondAtSource hfirstAtSource
  rw [← hcommuteFirstMixedSecondTarget, ← hcommuteTarget]
    at hfirstAtSecondTarget
  simp only [Math.Finset.CubicalResetIntegrability.square,
    Math.Finset.CubicalResetIntegrability.edge,
    QuittingStoppingLawResetCubeData.value]
  rw [hfirstProfile, hsecondProfile, hbothProfile]
  change
    quittingTerminalPayoff reward
          (Function.update (Function.update profile first firstMixed) second
            secondMixed) observer -
        quittingTerminalPayoff reward
          (Function.update profile first firstMixed) observer -
      (quittingTerminalPayoff reward
          (Function.update profile second secondMixed) observer -
        quittingTerminalPayoff reward profile observer) = _
  rw [hsecondAtFirst, hsecondAtSource, hfirstAtSecondTarget, hfirstAtSource]
  ring

/-- A terminal-payoff square is quadratically bounded by its two reset scales.
The constant `4 * bound` is the sharp bound obtained from four terminal payoff
corners in `[-bound, bound]`. -/
theorem abs_quittingTerminalPayoff_resetCube_square_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (source : Finset ι) (first second : ι)
    (hfirst : first ∉ source) (hsecond : second ∉ source)
    (hne : first ≠ second) (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |Math.Finset.CubicalResetIntegrability.square
        (data.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
        source first second| ≤
      4 * bound * data.scale first * data.scale second := by
  let profile := data.profile source
  let both := Function.update (Function.update profile first
    (data.target first)) second (data.target second)
  let firstOnly := Function.update profile first (data.target first)
  let secondOnly := Function.update profile second (data.target second)
  let rectangle := quittingTerminalPayoff reward both observer -
    quittingTerminalPayoff reward firstOnly observer -
    quittingTerminalPayoff reward secondOnly observer +
    quittingTerminalPayoff reward profile observer
  have hboth := abs_quittingTerminalPayoff_le reward both observer hreward
  have hfirstOnly :=
    abs_quittingTerminalPayoff_le reward firstOnly observer hreward
  have hsecondOnly :=
    abs_quittingTerminalPayoff_le reward secondOnly observer hreward
  have hprofile := abs_quittingTerminalPayoff_le reward profile observer hreward
  have hrectangle : |rectangle| ≤ 4 * bound := by
    calc
      |rectangle| ≤
          |quittingTerminalPayoff reward both observer -
              quittingTerminalPayoff reward firstOnly observer -
              quittingTerminalPayoff reward secondOnly observer| +
            |quittingTerminalPayoff reward profile observer| := by
        dsimp only [rectangle]
        exact abs_add_le _ _
      _ ≤
          |quittingTerminalPayoff reward both observer -
              quittingTerminalPayoff reward firstOnly observer| +
            |quittingTerminalPayoff reward secondOnly observer| +
            |quittingTerminalPayoff reward profile observer| := by
        gcongr
        exact abs_sub _ _
      _ ≤
          |quittingTerminalPayoff reward both observer| +
            |quittingTerminalPayoff reward firstOnly observer| +
            |quittingTerminalPayoff reward secondOnly observer| +
            |quittingTerminalPayoff reward profile observer| := by
        gcongr
        exact abs_sub _ _
      _ ≤ 4 * bound := by linarith
  rw [quittingTerminalPayoff_resetCube_square_eq_scale_mul_scale_mul
    data observer source first second hfirst hsecond hne]
  change |data.scale first * data.scale second * rectangle| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg (data.scale_nonneg first),
    abs_of_nonneg (data.scale_nonneg second)]
  have hscaled := mul_le_mul_of_nonneg_left hrectangle
    (mul_nonneg (data.scale_nonneg first) (data.scale_nonneg second))
  nlinarith

/-- Replacing the observer by a pure quit time turns every fresh opponent
square into the terminal-payoff square of the cube rebased at that deviation.
This exact adapter also covers background faces containing the observer,
because the unilateral update overwrites that coordinate. -/
theorem quittingPureTimeDeviationPayoff_resetCube_square_eq_rebase
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (quitTime : Option ℕ)
    (source : Finset ι) (first second : ι)
    (hfirst : first ∉ source) (hsecond : second ∉ source)
    (hobserverFirst : observer ≠ first)
    (hobserverSecond : observer ≠ second) :
    let deviation := quittingPureTimeBehaviorStrategy reward observer quitTime
    let rebased := data.rebase
      (Function.update (data.profile source) observer deviation)
    Math.Finset.CubicalResetIntegrability.square
        (fun reset ↦ quittingPureTimeDeviationPayoff reward
          (data.profile reset) observer quitTime)
        source first second =
      Math.Finset.CubicalResetIntegrability.square
        (rebased.value fun candidate ↦
          quittingTerminalPayoff reward candidate observer)
        ∅ first second := by
  dsimp only
  let deviation := quittingPureTimeBehaviorStrategy reward observer quitTime
  let rebased := data.rebase
    (Function.update (data.profile source) observer deviation)
  have hempty : rebased.profile ∅ =
      Function.update (data.profile source) observer deviation := by
    exact data.rebase_profile_empty _
  have hfirstDisjoint : Disjoint ({first} : Finset ι) source := by
    simpa [Finset.disjoint_left] using hfirst
  have hfirstCorner : rebased.profile {first} =
      Function.update (data.profile (insert first source)) observer deviation := by
    simpa [rebased, Finset.union_comm] using
      data.rebase_deviation_profile source {first} observer deviation
        hfirstDisjoint (by simpa using hobserverFirst)
  have hsecondDisjoint : Disjoint ({second} : Finset ι) source := by
    simpa [Finset.disjoint_left] using hsecond
  have hsecondCorner : rebased.profile {second} =
      Function.update (data.profile (insert second source)) observer deviation := by
    simpa [rebased, Finset.union_comm] using
      data.rebase_deviation_profile source {second} observer deviation
        hsecondDisjoint (by simpa using hobserverSecond)
  have hpairDisjoint : Disjoint ({first, second} : Finset ι) source := by
    simp [Finset.disjoint_left, hfirst, hsecond]
  have hpairCorner : rebased.profile {first, second} =
      Function.update (data.profile (insert second (insert first source)))
        observer deviation := by
    simpa [rebased, Finset.union_comm, Finset.insert_comm] using
      data.rebase_deviation_profile source {first, second} observer deviation
        hpairDisjoint (by simp [hobserverFirst, hobserverSecond])
  have hfirstCorner' : rebased.profile (insert first ∅) =
      Function.update (data.profile (insert first source)) observer deviation := by
    simpa using hfirstCorner
  have hsecondCorner' : rebased.profile (insert second ∅) =
      Function.update (data.profile (insert second source)) observer deviation := by
    simpa using hsecondCorner
  have hpairCorner' : rebased.profile (insert second (insert first ∅)) =
      Function.update (data.profile (insert second (insert first source)))
        observer deviation := by
    have hset : insert second (insert first ∅) = ({first, second} : Finset ι) := by
      ext who
      simp [or_comm]
    rw [hset]
    exact hpairCorner
  simp only [Math.Finset.CubicalResetIntegrability.square,
    Math.Finset.CubicalResetIntegrability.edge,
    quittingPureTimeDeviationPayoff,
    QuittingStoppingLawResetCubeData.value]
  rw [hempty, hfirstCorner', hsecondCorner', hpairCorner']

/-- Exact bilinear scaling of a pure-time deviation payoff square in two
fresh opponent reset coordinates. -/
theorem quittingPureTimeDeviationPayoff_resetCube_square_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (quitTime : Option ℕ)
    (source : Finset ι) (first second : ι)
    (hfirst : first ∉ source) (hsecond : second ∉ source)
    (hne : first ≠ second) (hobserverFirst : observer ≠ first)
    (hobserverSecond : observer ≠ second) :
    let deviationProfile := Function.update (data.profile source) observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)
    Math.Finset.CubicalResetIntegrability.square
        (fun reset ↦ quittingPureTimeDeviationPayoff reward
          (data.profile reset) observer quitTime)
        source first second =
      data.scale first * data.scale second *
        (quittingTerminalPayoff reward
              (Function.update (Function.update deviationProfile first
                (data.target first)) second (data.target second)) observer -
          quittingTerminalPayoff reward
              (Function.update deviationProfile first (data.target first))
                observer -
          quittingTerminalPayoff reward
              (Function.update deviationProfile second (data.target second))
                observer +
          quittingTerminalPayoff reward deviationProfile observer) := by
  dsimp only
  rw [quittingPureTimeDeviationPayoff_resetCube_square_eq_rebase data observer
    quitTime source first second hfirst hsecond hobserverFirst hobserverSecond]
  simpa using quittingTerminalPayoff_resetCube_square_eq_scale_mul_scale_mul
    (data.rebase (Function.update (data.profile source) observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)))
    observer ∅ first second (by simp) (by simp) hne

/-- Pure-time deviation payoffs inherit the quadratic square bound in every
pair of fresh opponent reset coordinates. -/
theorem abs_quittingPureTimeDeviationPayoff_resetCube_square_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (quitTime : Option ℕ)
    (source : Finset ι) (first second : ι)
    (hfirst : first ∉ source) (hsecond : second ∉ source)
    (hne : first ≠ second) (hobserverFirst : observer ≠ first)
    (hobserverSecond : observer ≠ second) (bound : ℝ)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    |Math.Finset.CubicalResetIntegrability.square
        (fun reset ↦ quittingPureTimeDeviationPayoff reward
          (data.profile reset) observer quitTime)
        source first second| ≤
      4 * bound * data.scale first * data.scale second := by
  rw [quittingPureTimeDeviationPayoff_resetCube_square_eq_rebase data observer
    quitTime source first second hfirst hsecond hobserverFirst hobserverSecond]
  exact abs_quittingTerminalPayoff_resetCube_square_le
    (data.rebase (Function.update (data.profile source) observer
      (quittingPureTimeBehaviorStrategy reward observer quitTime)))
    observer ∅ first second (by simp) (by simp) hne bound hreward

/-- Resetting the deviating player's prescribed coordinate does not change
that player's pure-time deviation payoff, because the deviation overwrites
the coordinate. -/
theorem quittingPureTimeDeviationPayoff_profile_insert_self
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (quitTime : Option ℕ) (reset : Finset ι) :
    quittingPureTimeDeviationPayoff reward
        (data.profile (insert observer reset)) observer quitTime =
      quittingPureTimeDeviationPayoff reward
        (data.profile reset) observer quitTime := by
  unfold quittingPureTimeDeviationPayoff
  apply congrArg (fun candidate ↦
    quittingTerminalPayoff reward candidate observer)
  funext who
  by_cases hwho : who = observer
  · subst who
    simp
  · rw [Function.update_of_ne hwho, Function.update_of_ne hwho]
    simp [QuittingStoppingLawResetCubeData.profile, hwho]

/-- A pure-time deviation payoff square vanishes if either reset coordinate
is the deviating player's overwritten coordinate. -/
theorem quittingPureTimeDeviationPayoff_resetCube_square_eq_zero_of_observer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (data : QuittingStoppingLawResetCubeData reward)
    (observer : ι) (quitTime : Option ℕ)
    (source : Finset ι) (first second : ι)
    (hcoordinate : observer = first ∨ observer = second) :
    Math.Finset.CubicalResetIntegrability.square
        (fun reset ↦ quittingPureTimeDeviationPayoff reward
          (data.profile reset) observer quitTime)
        source first second = 0 := by
  rcases hcoordinate with rfl | rfl
  · simp only [Math.Finset.CubicalResetIntegrability.square,
      Math.Finset.CubicalResetIntegrability.edge]
    rw [Finset.insert_comm second observer]
    rw [quittingPureTimeDeviationPayoff_profile_insert_self data observer
        quitTime source,
      quittingPureTimeDeviationPayoff_profile_insert_self data observer
        quitTime (insert second source)]
    ring
  · simp only [Math.Finset.CubicalResetIntegrability.square,
      Math.Finset.CubicalResetIntegrability.edge]
    rw [quittingPureTimeDeviationPayoff_profile_insert_self data observer
        quitTime source,
      quittingPureTimeDeviationPayoff_profile_insert_self data observer
        quitTime (insert first source)]
    ring

/-- Coordinatewise specialization to terminal semantic debt.  Apparent debt
holonomy can only come from comparing a common-source star with re-optimized
strategic edges, not from the literal semantic endpoints. -/
theorem terminalSemanticDebt_stoppingLawReset_square_identity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second observer : ι) (hne : first ≠ second)
    (firstTarget : (quittingGame reward).BehaviorStrategy first)
    (secondTarget : (quittingGame reward).BehaviorStrategy second)
    (firstScale secondScale : ℝ)
    (hfirst0 : 0 ≤ firstScale) (hfirst1 : firstScale ≤ 1)
    (hsecond0 : 0 ≤ secondScale) (hsecond1 : secondScale ≤ 1) :
    let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer
    let firstProfile := quittingStoppingLawResetProfile reward profile first
      firstTarget firstScale hfirst0 hfirst1
    let secondProfile := quittingStoppingLawResetProfile reward profile second
      secondTarget secondScale hsecond0 hsecond1
    let bothFromFirst := quittingStoppingLawResetProfile reward firstProfile
      second secondTarget secondScale hsecond0 hsecond1
    let bothFromSecond := quittingStoppingLawResetProfile reward secondProfile
      first firstTarget firstScale hfirst0 hfirst1
    (debt bothFromFirst - debt firstProfile) -
        (debt secondProfile - debt profile) =
      (debt bothFromSecond - debt secondProfile) -
        (debt firstProfile - debt profile) := by
  exact stoppingLawReset_square_identity reward profile first second hne
    firstTarget secondTarget firstScale secondScale hfirst0 hfirst1 hsecond0
      hsecond1 (fun candidate ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward candidate) observer)

end GameTheory
