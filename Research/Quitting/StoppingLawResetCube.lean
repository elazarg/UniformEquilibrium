/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.CubicalResetIntegrability
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction

/-!
# Literal commuting squares for stopping-law resets

Stopping-law resets of distinct players commute when their source strategies,
target strategies, and mixture scales are frozen at one literal profile.  The
result is therefore an actual Boolean cube of behavior profiles, not merely a
debt-vector analogy.

Every scalar semantic observable has zero signed holonomy around each literal
square.  Nonlinearity enters only when one assigns *strategic charge* to an
edge by re-optimizing best responses at its source.  The game-facing missing
theorem is consequently a passport-or-curvature alternative: either the
frozen replacement remains sufficiently optimal on a reset order, or a
two-reset square witnesses quantitative envelope curvature.
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
