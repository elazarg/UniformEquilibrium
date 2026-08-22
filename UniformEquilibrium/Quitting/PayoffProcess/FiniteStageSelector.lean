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
one-stage quitting payoff after converting its finite laws to PMFs. -/
theorem expectedUtility_quittingBinaryForm_eq
    (utility : (ι → Bool) → ι → ℝ)
    (profile : Profile (quittingBinaryForm ι).sig.mixed) (who : ι) :
    expectedUtility utility who
        ((quittingBinaryForm ι).mixed.play profile) =
      _root_.Math.Probability.expect
        (_root_.Math.PMFProduct.pmfPi
          (fun player ↦ (profile player).toPMF))
        (fun action ↦ utility action who) := by
  calc
    expectedUtility utility who
        ((quittingBinaryForm ι).mixed.play profile) =
        FinDist.expect (FinDist.pi profile)
          (fun action ↦ utility action who) := by
      simp [expectedUtility, quittingBinaryForm]
    _ = _ := by
      rw [← _root_.Math.Probability.expect_finDistOfPMF,
        _root_.Math.Probability.finDistOfPMF_pmfPi]
      simp

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
    ((ofPolytope (quittingBinaryForm ι).sig
      (quittingStageWeightsSelector hε utility).2) who).toPMF

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
      (quittingStageWeightsSelector hε utility).2 who).prob action
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
  letI : MeasurableSpace Ω := m
  apply measurable_pi_lambda
  intro action
  apply measurable_pi_lambda
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
  · by_cases hquit : (quittingQuitters jointAction).Nonempty
    · simpa only [quittingRootPayoff, hquit, ↓reduceDIte] using
        hreward ⟨quittingQuitters jointAction, hquit⟩ who
    · simpa only [quittingRootPayoff, hquit, ↓reduceDIte] using
        hcontinuation who

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
  · rw [quittingRootPayoff, dif_pos hquit]
    exact (hreward ⟨quittingQuitters jointAction, hquit⟩ who).trans
      (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _))
  · rw [quittingRootPayoff, dif_neg hquit]
    exact (Finset.single_le_sum (fun player _ ↦ abs_nonneg (continuation player))
      (Finset.mem_univ who)).trans (le_add_of_nonneg_left
        (le_trans (abs_nonneg (reward ⟨{who}, by simp⟩ who))
          (hreward ⟨{who}, by simp⟩ who)))

/-- The selected binary root is an `ε`-Nash equilibrium of its one-stage
utility table. -/
theorem quittingStageRootSelector_isεNash {ε : ℝ} (hε : 0 < ε)
    (utility : (ι → Bool) → ι → ℝ) :
    IsεNash (quittingBinaryForm ι).mixed utility ε
      (fun who ↦
        _root_.Math.Probability.finDistOfPMF
          (quittingStageRootSelector hε utility who)) := by
  have hstrict := (Classical.choose_spec
    (exists_measurable_isStrictApproximateNashWeights
      (F := quittingBinaryForm ι) hε)).2 utility
  have hnash := hstrict.isεNash
  convert hnash using 1
  funext who
  exact _root_.Math.Probability.finDistOfPMF_toPMF _

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
  have hnash := quittingStageRootSelector_isεNash
    (ι := ι) hε (quittingStageUtility reward continuation)
  rw [isεNash_iff] at hnash
  have hdeviation := hnash who
    (_root_.Math.Probability.finDistOfPMF replacement)
  rw [expectedUtility_quittingBinaryForm_eq,
    expectedUtility_quittingBinaryForm_eq] at hdeviation
  have hupdate :
      (fun player ↦
        FinDist.toPMF (Profile.update
          (sig := (quittingBinaryForm ι).sig.mixed)
          ((fun selected ↦
              _root_.Math.Probability.finDistOfPMF
                (quittingStageRootSelector hε
                  (quittingStageUtility reward continuation) selected)) :
            Profile (quittingBinaryForm ι).sig.mixed)
          who (_root_.Math.Probability.finDistOfPMF replacement)
          player)) =
        Function.update
          (quittingStageRootSelector hε
            (quittingStageUtility reward continuation)) who replacement := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp
    · simp [Profile.update, Function.update, hplayer]
  rw [hupdate] at hdeviation
  simpa [quittingStageUtility, quittingRootExpectedPayoff] using hdeviation

end GameTheory
