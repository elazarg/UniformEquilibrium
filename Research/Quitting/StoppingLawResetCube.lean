/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction
import Research.General.CubicalResetIntegrability

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

/-- The common double-reset endpoint, independent of reset order. -/
def quittingStoppingLawDoubleResetProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (first second : ι)
    (firstTarget : (quittingGame reward).BehaviorStrategy first)
    (secondTarget : (quittingGame reward).BehaviorStrategy second)
    (firstScale secondScale : ℝ)
    (hfirst0 : 0 ≤ firstScale) (hfirst1 : firstScale ≤ 1)
    (hsecond0 : 0 ≤ secondScale) (hsecond1 : secondScale ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawResetProfile reward
    (quittingStoppingLawResetProfile reward profile first firstTarget
      firstScale hfirst0 hfirst1)
    second secondTarget secondScale hsecond0 hsecond1

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
