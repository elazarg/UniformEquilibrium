/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.Projective.Lasso

/-!
# Compact quantitative alternatives for corrected Simon rows

This module formalizes the finite-product rounding half of the corrected
compact-carrier alternative and isolates the remaining producer interface in
the normalized-motion half.  All equilibrium conclusions use unrestricted
behavioral deviations.

No claim about Simon's full theorem or the positive-solo sign clause is made.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A finite-product coordinate for rounding -/

omit [DecidableEq ι] in
/-- If the product Continue mass is below `rate ^ card`, some displayed
Continue probability is below `rate`. -/
theorem exists_continueProbability_lt_of_continueMass_lt_pow_card
    [Nonempty ι] (root : ι → PMF Bool) {rate : ℝ} (hrate : 0 ≤ rate)
    (hmass : quittingStationaryContinueMass root < rate ^ Fintype.card ι) :
    ∃ quitter, (root quitter false).toReal < rate := by
  by_contra hnot
  push Not at hnot
  rw [quittingStationaryContinueMass_eq_prod_continueProbability] at hmass
  have hproduct : rate ^ Fintype.card ι ≤
      ∏ who, (root who false).toReal := by
    calc
      rate ^ Fintype.card ι = ∏ _who : ι, rate := by simp
      _ ≤ ∏ who, (root who false).toReal :=
        Finset.prod_le_prod (fun _ _ => hrate) (fun who _ => hnot who)
  linarith

/-- Rounding one coordinate to sure Quit. -/
def quittingSureQuitRound
    (root : ι → PMF Bool) (quitter : ι) : ι → PMF Bool :=
  Function.update root quitter (PMF.pure true)

omit [Fintype ι] in
@[simp] theorem quittingSureQuitRound_quitter
    (root : ι → PMF Bool) (quitter : ι) :
    quittingSureQuitRound root quitter quitter = PMF.pure true := by
  simp [quittingSureQuitRound]

omit [Fintype ι] in
theorem quittingSureQuitRound_other
    (root : ι → PMF Bool) {quitter who : ι} (hne : who ≠ quitter) :
    quittingSureQuitRound root quitter who = root who := by
  exact Function.update_of_ne hne _ _

omit [Fintype ι] [DecidableEq ι] in
/-- The Quit-probability displacement caused by sure-Quit rounding equals the
old Continue probability. -/
theorem abs_sureQuitRound_quitProbability_sub_eq_continueProbability
    (root : ι → PMF Bool) (quitter : ι) :
    |(PMF.pure true true).toReal - (root quitter true).toReal| =
      (root quitter false).toReal := by
  have hsum := quittingRoot_continueProbability_add_quitProbability root quitter
  have hquitLe : (root quitter true).toReal ≤ 1 := by
    linarith [ENNReal.toReal_nonneg (a := root quitter false)]
  have hpure : (PMF.pure true true).toReal = 1 := by simp
  rw [hpure]
  rw [abs_of_nonneg (sub_nonneg.mpr hquitLe)]
  linarith

/-! ## Endpoint transport under sure-Quit rounding -/

/-- For a different player, either forced endpoint moves by at most
`rate * (2 * M)` when a coordinate within `rate` of sure Quit is rounded. -/
theorem abs_endpoint_sureQuitRound_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {quitter who : ι}
    (hne : who ≠ quitter) (action : Bool) {rate M : ℝ}
    (hrate : (root quitter false).toReal ≤ rate)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M) :
    |quittingRootExpectedPayoff reward tail
        (Function.update (quittingSureQuitRound root quitter) who
          (PMF.pure action)) who -
      quittingRootExpectedPayoff reward tail
        (Function.update root who (PMF.pure action)) who| ≤
      rate * (2 * M) := by
  have hcomm :
      Function.update (quittingSureQuitRound root quitter) who
          (PMF.pure action) =
        Function.update (Function.update root who (PMF.pure action))
          quitter (PMF.pure true) := by
    unfold quittingSureQuitRound
    exact Function.update_comm (Ne.symm hne) _ _ _
  have hcoord : Function.update root who (PMF.pure action) quitter =
      root quitter := Function.update_of_ne (Ne.symm hne) _ _
  have hbound := abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    reward tail (Function.update root who (PMF.pure action)) quitter who
      (PMF.pure true) hreward htail
  rw [hcoord,
    abs_sureQuitRound_quitProbability_sub_eq_continueProbability] at hbound
  rw [hcomm]
  exact hbound.trans (mul_le_mul_of_nonneg_right hrate (by positivity))

/-- The endpoint difference of a different player moves by at most
`4 * M * rate` under sure-Quit rounding. -/
theorem abs_endpointDifference_sureQuitRound_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {quitter who : ι}
    (hne : who ≠ quitter) {rate M : ℝ}
    (hrate : (root quitter false).toReal ≤ rate)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M) :
    |quittingRootEndpointDifference reward tail
        (quittingSureQuitRound root quitter) who -
      quittingRootEndpointDifference reward tail root who| ≤
      4 * M * rate := by
  have hquit := abs_endpoint_sureQuitRound_sub_le reward tail root hne true
    hrate hM hreward htail
  have hcontinue := abs_endpoint_sureQuitRound_sub_le reward tail root hne false
    hrate hM hreward htail
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  calc
    |_ - _| ≤
        |quittingRootExpectedPayoff reward tail
            (Function.update (quittingSureQuitRound root quitter) who
              (PMF.pure true)) who -
          quittingRootExpectedPayoff reward tail
            (Function.update root who (PMF.pure true)) who| +
        |quittingRootExpectedPayoff reward tail
            (Function.update (quittingSureQuitRound root quitter) who
              (PMF.pure false)) who -
          quittingRootExpectedPayoff reward tail
            (Function.update root who (PMF.pure false)) who| := by
      rw [show
        quittingRootExpectedPayoff reward tail
              (Function.update (quittingSureQuitRound root quitter) who
                (PMF.pure true)) who -
            quittingRootExpectedPayoff reward tail
              (Function.update (quittingSureQuitRound root quitter) who
                (PMF.pure false)) who -
            (quittingRootExpectedPayoff reward tail
                (Function.update root who (PMF.pure true)) who -
              quittingRootExpectedPayoff reward tail
                (Function.update root who (PMF.pure false)) who) =
          (quittingRootExpectedPayoff reward tail
              (Function.update (quittingSureQuitRound root quitter) who
                (PMF.pure true)) who -
            quittingRootExpectedPayoff reward tail
              (Function.update root who (PMF.pure true)) who) -
          (quittingRootExpectedPayoff reward tail
              (Function.update (quittingSureQuitRound root quitter) who
                (PMF.pure false)) who -
            quittingRootExpectedPayoff reward tail
              (Function.update root who (PMF.pure false)) who) by ring]
      apply abs_sub
    _ ≤ rate * (2 * M) + rate * (2 * M) := add_le_add hquit hcontinue
    _ = 4 * M * rate := by ring

/-- Quantitative support transport: rounding a coordinate within `rate` of
sure Quit costs at most `4 * M * rate` in the support-local tolerance. -/
theorem supportApproxNash_sureQuitRound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (quitter : ι)
    {γ rate M : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate < 1)
    (hcontinue : (root quitter false).toReal < rate)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (htail : ∀ player, |tail player| ≤ M)
    (hsupport : IsQuittingRootSupportApproxNash reward tail γ root) :
    IsQuittingRootSupportApproxNash reward tail (γ + 4 * M * rate)
      (quittingSureQuitRound root quitter) := by
  intro who
  by_cases hwho : who = quitter
  · subst who
    have hendpoint : quittingRootEndpointDifference reward tail
        (quittingSureQuitRound root quitter) quitter =
        quittingRootEndpointDifference reward tail root quitter := by
      exact quittingRootEndpointDifference_update_ownMarginal
        reward tail root quitter (PMF.pure true)
    have hquitPositive : 0 < (root quitter true).toReal := by
      have hsum := quittingRoot_continueProbability_add_quitProbability
        root quitter
      linarith
    constructor
    · intro _
      rw [hendpoint]
      have hbound := (hsupport quitter).1 hquitPositive
      have hcost : 0 ≤ 4 * M * rate := by positivity
      linarith
    · intro hfalse
      rw [quittingSureQuitRound_quitter] at hfalse
      simp at hfalse
  · have hrootWho := quittingSureQuitRound_other root hwho
    have hmove := abs_endpointDifference_sureQuitRound_sub_le
      reward tail root hwho hcontinue.le hM hreward htail
    rw [abs_le] at hmove
    constructor
    · intro hpositive
      have hpositiveRoot : 0 < (root who true).toReal := by
        rwa [hrootWho] at hpositive
      have hbound := (hsupport who).1 hpositiveRoot
      linarith
    · intro hpositive
      have hpositiveRoot : 0 < (root who false).toReal := by
        rwa [hrootWho] at hpositive
      have hbound := (hsupport who).2 hpositiveRoot
      linarith

/-! ## A production sure-row behavioral compiler -/

/-- A rational support-local row with a sure quitter compiles to an actual
one-stage punished profile.  The Nash conclusion covers every unilateral
behavioral deviation through the production first-branch theorem. -/
theorem exists_oneStagePunishedProfile_of_rational_support_sureQuitter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (quitter : ι)
    {η δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ)
    (hrational : QuittingSimonRationalPayoffAt reward η tail)
    (hsupport : IsQuittingRootSupportApproxNash reward tail η root)
    (hquit : root quitter = PMF.pure true) :
    ∃ punishRow : ι → PMF Bool,
      quittingStationaryUnilateralCap reward punishRow quitter ≤
          quittingPunishmentValue reward quitter + δ ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (2 * η + δ)
          (quittingOneStagePunishedProfile reward root punishRow) := by
  obtain ⟨punishRow, hpunish⟩ :=
    exists_punishRow_stationaryUnilateralCap_le reward quitter hδ
  let continuation := quittingStationaryProfile reward punishRow
  let best := quittingContinuationBestResponse reward continuation
  letI : Nonempty ((quittingGame reward).BehaviorStrategy quitter) :=
    ⟨fun _ _ => PMF.pure false⟩
  have hbest : best quitter ≤
      quittingStationaryUnilateralCap reward punishRow quitter := by
    dsimp only [best, quittingContinuationBestResponse]
    unfold quittingContinuationBestResponseValue
    rw [sSup_range]
    apply ciSup_le
    intro deviation
    exact quittingTerminalPayoff_update_stationary_le_cap
      reward punishRow quitter deviation
  have hbestTail : best quitter ≤ tail quitter + η + δ := by
    have hfloor := hrational quitter
    linarith
  have hendpoint := isQuittingRootEndpointNash_of_supportApproxNash
    reward tail root hη hsupport
  have hrootTail : IsεQuittingRootNash reward tail η root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail η root).mp hendpoint
  have hsure : QuittingRootHasSureQuitter root := ⟨quitter, hquit⟩
  have hrootBest : IsεQuittingRootNash reward best (2 * η + δ) root := by
    intro who deviation
    have htailBound := hrootTail who deviation
    by_cases hwho : who = quitter
    · subst who
      have happrox := quittingRootExpectedPayoff_continuation_le_add
        reward best tail (Function.update root quitter deviation) quitter
          (δ := η + δ) (add_nonneg hη hδ.le) (by linarith)
      have hprescribed := quittingRootExpectedPayoff_eq_of_hasSureQuitter
        reward root hsure best tail quitter
      linarith
    · have hsureDeviation : QuittingRootHasSureQuitter
          (Function.update root who deviation) := by
        refine ⟨quitter, ?_⟩
        rw [Function.update_of_ne (Ne.symm hwho), hquit]
      have hdeviation := quittingRootExpectedPayoff_eq_of_hasSureQuitter
        reward (Function.update root who deviation) hsureDeviation
          best tail who
      have hprescribed := quittingRootExpectedPayoff_eq_of_hasSureQuitter
        reward root hsure best tail who
      rw [hdeviation, hprescribed]
      exact htailBound.trans (by linarith)
  have hnash :=
    isεAsymptoticNash_quittingRootThenContinuation_of_isεQuittingRootNash
      reward root continuation hsure hrootBest
  refine ⟨punishRow, hpunish, ?_⟩
  rw [quittingOneStagePunishedProfile_eq_rootThenContinuation]
  exact hnash

/-! ## Near-total absorption implies the instant branch -/

/-- Arbitrarily small rational support-local rows with absorption tending to
one, on a uniformly bounded continuation carrier. -/
def HasArbitrarilySmallQuittingNearTotalSupportRows
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) : Prop :=
  ∀ threshold : ℝ, 0 < threshold →
    ∃ (γ : ℝ) (tail : Payoff ι) (root : ι → PMF Bool),
      0 < γ ∧ γ < threshold ∧
        (∀ who, |tail who| ≤ M) ∧
        QuittingSimonRationalPayoffAt reward γ tail ∧
        IsQuittingRootSupportApproxNash reward tail γ root ∧
        1 - γ < quittingRootAbsorptionMass root

/-- **Near-total-absorption compact alternative.**  Arbitrarily small
bounded rational support rows whose absorption tends to one yield the
production instant-punishment branch.  The proof uses the explicit polynomial
rounding modulus `γ + 4 * M * rate`, with the witness selected below
`rate ^ card`. -/
theorem quittingInstantPunishmentεEquilibriumExistence_of_nearTotalSupportRows
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hrows : HasArbitrarilySmallQuittingNearTotalSupportRows reward M) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  intro ε hε
  let rate := min (1 / 2 : ℝ) (ε / (64 * (M + 1)))
  have hMone : 0 < M + 1 := by linarith
  have hrate : 0 < rate := by
    dsimp only [rate]
    exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hMone))
  have hrateHalf : rate ≤ 1 / 2 := by
    exact min_le_left _ _
  have hrateOne : rate < 1 := hrateHalf.trans_lt (by norm_num)
  have hrateBound : rate ≤ ε / (64 * (M + 1)) := by
    exact min_le_right _ _
  let threshold := min (ε / 8) (rate ^ Fintype.card ι)
  have hthreshold : 0 < threshold := by
    dsimp only [threshold]
    exact lt_min (div_pos hε (by norm_num)) (pow_pos hrate _)
  obtain ⟨γ, tail, root, hγ, hγThreshold, htail, hrational,
      hsupport, habsorption⟩ := hrows threshold hthreshold
  have hγError : γ < ε / 8 :=
    hγThreshold.trans_le (min_le_left _ _)
  have hγRate : γ < rate ^ Fintype.card ι :=
    hγThreshold.trans_le (min_le_right _ _)
  have hcontinueMass : quittingStationaryContinueMass root < γ := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  obtain ⟨quitter, hquitterRate⟩ :=
    exists_continueProbability_lt_of_continueMass_lt_pow_card
      root hrate.le (hcontinueMass.trans hγRate)
  let rounded := quittingSureQuitRound root quitter
  let η := γ + 4 * M * rate
  have hη : 0 ≤ η := by
    dsimp only [η]
    positivity
  have hsupportRounded :
      IsQuittingRootSupportApproxNash reward tail η rounded := by
    exact supportApproxNash_sureQuitRound reward tail root quitter
      hrate.le hrateOne hquitterRate hM hreward htail hsupport
  have hrationalRounded : QuittingSimonRationalPayoffAt reward η tail := by
    intro who
    have hwho := hrational who
    have hcost : 0 ≤ 4 * M * rate := by positivity
    dsimp only [η]
    linarith
  have hrateScaled :=
    (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 64) hMone)).mp hrateBound
  have hroundingCost : 4 * M * rate ≤ ε / 16 := by
    nlinarith
  have hηError : η < ε / 4 := by
    dsimp only [η]
    linarith
  obtain ⟨punishRow, hpunish, hnash⟩ :=
    exists_oneStagePunishedProfile_of_rational_support_sureQuitter
      (η := η) (δ := ε / 4) reward tail rounded quitter hη
      (div_pos hε (by norm_num))
      hrationalRounded hsupportRounded
      (quittingSureQuitRound_quitter root quitter)
  refine ⟨quitter, rounded, punishRow,
    quittingSureQuitRound_quitter root quitter, ?_, ?_⟩
  · linarith
  · apply hnash.mono
    linarith

end GameTheory
