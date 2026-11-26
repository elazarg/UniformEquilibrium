/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.Probability.FinitePMF
import UniformEquilibrium.MeasurableSelection.FiniteGameNash
import UniformEquilibrium.Quitting.Stationary.Payoff

/-!
# Measurable finite-stage selection in a quitting game

This module specializes measurable approximate-Nash selection to the binary
normal-form game obtained from one quitting table and a continuation vector.
The selector depends measurably on the complete one-stage utility table.  A
later backward recursion will prove that this table is measurable in the
actual payoff filtration at the stage where it is used.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The deterministic finite game form in which every player chooses Quit or
Continue and the outcome records the joint action. -/
abbrev quittingBinaryForm (ι : Type) : GameForm ι :=
  GameForm.deterministic
    { Strategy := fun _ ↦ Bool
      Outcome := ι → Bool }
    id

/-- Utility table of the one-stage quitting game with the supplied
continuation vector on the all-Continue action. -/
def quittingStageUtility
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) : (ι → Bool) → ι → ℝ :=
  fun action who ↦ quittingRootPayoff reward continuation action who

omit [DecidableEq ι] in
/-- Expected utility in the deterministic binary game form is the usual
one-stage quitting payoff under the independent product law. -/
theorem expectedUtility_quittingBinaryForm_eq
    (utility : (ι → Bool) → ι → ℝ)
    (profile : Profile (quittingBinaryForm ι).sig.mixed) (who : ι) :
    expectedUtility utility who
        ((quittingBinaryForm ι).mixed.play profile) =
      _root_.Math.Probability.expect
        (_root_.Math.PMFProduct.pmfPi profile)
        (fun action ↦ utility action who) := by
  rw [GameForm.mixed_play]
  change GameTheory.Math.Probability.expect ((independentProduct profile).bind PMF.pure)
    (fun action ↦ utility action who) = _
  rw [PMF.bind_pure]
  rfl

/-- The measurable strict approximate-Nash weight selector specialized to
the binary action form. -/
def quittingStageWeightsSelector {ε : ℝ} (hε : 0 < ε) :
    ((ι → Bool) → ι → ℝ) → mixedPolytope (quittingBinaryForm ι).sig :=
  Classical.choose
    (exists_measurable_isStrictApproximateNashWeights
      (F := quittingBinaryForm ι) hε)

/-- The selected independent quitting root, represented by Mathlib PMFs. -/
def quittingStageRootSelector {ε : ℝ} (hε : 0 < ε)
    (utility : (ι → Bool) → ι → ℝ) : ι → PMF Bool :=
  fun who ↦
    ofPolytope (quittingBinaryForm ι).sig
      (quittingStageWeightsSelector hε utility).2 who

/-- A selected action probability is measurable as the one-stage utility
table varies. -/
theorem measurable_quittingStageRootSelector_apply {ε : ℝ} (hε : 0 < ε)
    (who : ι) (action : Bool) :
    Measurable fun utility : (ι → Bool) → ι → ℝ ↦
      (quittingStageRootSelector hε utility who action).toReal := by
  have hselector : Measurable (quittingStageWeightsSelector hε) :=
    (Classical.choose_spec
      (exists_measurable_isStrictApproximateNashWeights
        (F := quittingBinaryForm ι) hε)).1
  have hcoordinate : Continuous fun weights :
      mixedPolytope (quittingBinaryForm ι).sig ↦
        weights.1 who action := by
    exact (continuous_apply action).comp
      ((continuous_apply who).comp continuous_subtype_val)
  change Measurable fun utility ↦
    (ofPolytope (quittingBinaryForm ι).sig
      (quittingStageWeightsSelector hε utility).2 who action).toReal
  convert hcoordinate.measurable.comp hselector using 1
  funext utility
  exact congrFun (congrFun
    (probs_ofPolytope (quittingBinaryForm ι).sig
      (quittingStageWeightsSelector hε utility).2) who) action

omit [DecidableEq ι] in
/-- If a random quitting table and continuation vector are measurable in a
sigma-algebra, then so is the complete one-stage normal-form utility table
presented to the selector. -/
theorem measurable_quittingStageUtility {Ω : Type*} {m : MeasurableSpace Ω}
    (reward : Ω → {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Ω → Payoff ι)
    (hreward : ∀ terminal who,
      @Measurable Ω ℝ m Real.measurableSpace
        (fun ω ↦ reward ω terminal who))
    (hcontinuation : ∀ who,
      @Measurable Ω ℝ m Real.measurableSpace
        (fun ω ↦ continuation ω who)) :
    @Measurable Ω ((ι → Bool) → ι → ℝ) m inferInstance
      (fun ω ↦ quittingStageUtility (reward ω) (continuation ω)) := by
  let : MeasurableSpace Ω := m
  apply Measurable.of_eval
  intro action
  apply Measurable.of_eval
  intro who
  by_cases hquit : (quittingQuitters action).Nonempty
  · simpa [quittingStageUtility, quittingRootPayoff, hquit] using
      hreward ⟨quittingQuitters action, hquit⟩ who
  · simpa [quittingStageUtility, quittingRootPayoff, hquit] using
      hcontinuation who

/-- Consequently, the selected one-stage root remains measurable in exactly
the sigma-algebra in which the random stage utility is measurable. -/
theorem measurable_quittingStageRootSelector_comp {Ω : Type*}
    {m : MeasurableSpace Ω} {ε : ℝ} (hε : 0 < ε)
    (utility : Ω → (ι → Bool) → ι → ℝ)
    (hutility : @Measurable Ω ((ι → Bool) → ι → ℝ)
      m inferInstance utility) (who : ι) (action : Bool) :
    @Measurable Ω ℝ m Real.measurableSpace (fun ω ↦
      (quittingStageRootSelector hε (utility ω) who action).toReal) :=
  (measurable_quittingStageRootSelector_apply hε who action).comp hutility

omit [DecidableEq ι] in
/-- The expected one-stage quitting payoff is measurable when the random
reward, continuation, and each marginal action probability are measurable. -/
theorem measurable_quittingRootExpectedPayoff {Ω : Type*}
    [MeasurableSpace Ω]
    (reward : Ω → {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Ω → Payoff ι) (root : Ω → ι → PMF Bool)
    (hreward : ∀ terminal player,
      Measurable fun ω ↦ reward ω terminal player)
    (hcontinuation : ∀ player,
      Measurable fun ω ↦ continuation ω player)
    (hroot : ∀ player action,
      Measurable fun ω ↦ (root ω player action).toReal)
    (who : ι) :
    Measurable fun ω ↦
      quittingRootExpectedPayoff (reward ω) (continuation ω)
        (root ω) who := by
  unfold quittingRootExpectedPayoff
  apply Measurable.tsum
  intro jointAction
  simp_rw [_root_.Math.PMFProduct.pmfPi_apply, ENNReal.toReal_prod]
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro player _
    exact hroot player (jointAction player)
  · change Measurable (fun ω => quittingRootPayoff (reward ω) (continuation ω) jointAction who)
    by_cases hquit : (quittingQuitters jointAction).Nonempty
    · simpa only [quittingRootPayoff_of_nonempty _ _ _ _ hquit] using
        hreward ⟨quittingQuitters jointAction, hquit⟩ who
    · simpa only [quittingRootPayoff_of_not_nonempty _ _ _ _ hquit] using hcontinuation who

omit [DecidableEq ι] in
/-- A random one-stage payoff is dominated by the reward envelope plus the
sum of the absolute continuation coordinates. -/
theorem abs_quittingRootExpectedPayoff_le_envelopeSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (rewardBound : ℝ) (hreward : ∀ terminal player,
      |reward terminal player| ≤ rewardBound) :
    |quittingRootExpectedPayoff reward continuation root who| ≤
      rewardBound + ∑ player, |continuation player| := by
  unfold quittingRootExpectedPayoff
  apply _root_.Math.Probability.abs_expect_le_of_abs_le
  intro jointAction
  by_cases hquit : (quittingQuitters jointAction).Nonempty
  · rw [quittingRootPayoff_of_nonempty _ _ _ _ hquit]
    exact (hreward ⟨quittingQuitters jointAction, hquit⟩ who).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
  · rw [quittingRootPayoff_of_not_nonempty _ _ _ _ hquit]
    exact (Finset.single_le_sum (fun player _ ↦ abs_nonneg (continuation player))
      (Finset.mem_univ who)).trans (le_add_of_nonneg_left
        (le_trans (abs_nonneg (reward ⟨{who}, by simp⟩ who))
          (hreward ⟨{who}, by simp⟩ who)))

/-- The selected binary root is an `ε`-Nash equilibrium of its one-stage
utility table. -/
theorem quittingStageRootSelector_isεNash {ε : ℝ} (hε : 0 < ε)
    (utility : (ι → Bool) → ι → ℝ) :
    IsεNash (quittingBinaryForm ι).mixed utility ε
      (quittingStageRootSelector hε utility) := by
  have hstrict := (Classical.choose_spec
    (exists_measurable_isStrictApproximateNashWeights
      (F := quittingBinaryForm ι) hε)).2 utility
  exact hstrict.isεNash

omit [Fintype ι] in
private theorem expectedUtility_deviation_le_of_finite_isεNash
    (F : GameForm ι) [Finite F.sig.Outcome] (utility : F.sig.Outcome → ι → ℝ)
    {ε : ℝ} {root : Profile F.sig} (hnash : IsεNash F utility ε root)
    (who : ι) (replacement : F.sig.Strategy who) :
    expectedUtility utility who (F.play (Profile.update root who replacement)) ≤
      expectedUtility utility who (F.play root) + ε :=
  (euPreferenceWithin_iff ε utility who _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp
      ((isNash_iff (weaklyPrefers := euPreferenceWithin ε utility) root).mp
        hnash who replacement)

private theorem quittingRootExpectedPayoff_deviation_le_of_isεNash {ε : ℝ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool)
    (hnash : IsεNash (quittingBinaryForm ι).mixed
      (quittingStageUtility reward continuation) ε root)
    (who : ι) (replacement : PMF Bool) :
    quittingRootExpectedPayoff reward continuation (Function.update root who replacement) who ≤
      quittingRootExpectedPayoff reward continuation root who + ε := by
  have hdeviation := expectedUtility_deviation_le_of_finite_isεNash
    (quittingBinaryForm ι).mixed (quittingStageUtility reward continuation) hnash who replacement
  rw [expectedUtility_quittingBinaryForm_eq,
    expectedUtility_quittingBinaryForm_eq] at hdeviation
  exact hdeviation

/-- In quitting notation, no randomized one-player replacement improves the
selected one-stage root payoff by more than `ε`. -/
theorem quittingStageRootSelector_deviation_le {ε : ℝ} (hε : 0 < ε)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (who : ι) (replacement : PMF Bool) :
    quittingRootExpectedPayoff reward continuation
        (Function.update
          (quittingStageRootSelector hε
            (quittingStageUtility reward continuation))
          who replacement) who ≤
      quittingRootExpectedPayoff reward continuation
          (quittingStageRootSelector hε
            (quittingStageUtility reward continuation)) who + ε := by
  exact quittingRootExpectedPayoff_deviation_le_of_isεNash reward continuation _
    (quittingStageRootSelector_isεNash hε (quittingStageUtility reward continuation))
    who replacement

end GameTheory
