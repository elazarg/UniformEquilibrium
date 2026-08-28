/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.LowSurvivalSourceAdapter

/-!
# Compact scale alternatives for literal low-survival sources

The compact scalar attached to a floor-clipped purified crossing row is its
joint Continue mass.  Across errors tending to zero, these masses have an
exhaustive alternative: they tend to zero, producing source-matched
near-total rows, or they are bounded below by one positive constant
cofinally, producing actual survival-window landings.

This does not prove the global `SuppliedQuittingSimonCorrectedUniformSurvivalAt`
predicate.  The positive constant controls only the selected literal source
rows.  That is sufficient for the first-crossing calculation and is the
strongest conclusion supplied by scalar compactness alone.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A punishment-floor clip of an actual terminal payoff remains in the
canonical reward box when the clipping slack is nonnegative. -/
theorem abs_lowSurvival_clippedTail_le_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : (quittingGame reward).BehaviorProfile)
    {η : ℝ} (hη : 0 ≤ η) (who : ι) :
    |quittingPunishmentFloorClipAt reward η
        (fun player ↦ quittingTerminalPayoff reward continuation player) who| ≤
      quittingRewardBound reward := by
  let actual := fun player ↦
    quittingTerminalPayoff reward continuation player
  have hactual := abs_quittingTerminalPayoff_le_quittingRewardBound
    reward continuation who
  have hpunishment :=
    abs_quittingPunishmentValue_le_quittingRewardBound reward who
  rw [abs_le]
  constructor
  · exact (neg_le_of_abs_le hactual).trans
      (le_quittingPunishmentFloorClipAt reward η actual who)
  · rw [quittingPunishmentFloorClipAt_apply]
    apply max_le
    · exact le_of_abs_le hactual
    · linarith [le_of_abs_le hpunishment]

/-- The local data obtained before either compact scalar branch is chosen.
All objects are the literal clipped tail and simultaneous purification of one
first-crossing source. -/
structure QuittingLowSurvivalPurifiedCoreAt
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    (β d η : ℝ) : Prop where
  rational : QuittingSimonRationalPayoffAt reward η (source.clippedTail η)
  support : IsQuittingRootSupportApproxNash reward (source.clippedTail η) η
    (source.clippedPurifiedRoot η β)
  coordinateClose : ∀ who,
    |(source.clippedPurifiedRoot η β who true).toReal -
        (source.roots (source.crossingStage - 1) who true).toReal| < d
  tail_bound : ∀ who,
    |source.clippedTail η who| ≤ quittingRewardBound reward

/-- One literal first-crossing source supplies its clipped, rational,
support-purified row without either a global no-sure-quitter assumption or a
global uniform-survival assumption. -/
theorem QuittingLowSurvivalFirstCrossingSourceAt.floorClippedPurifiedCore
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d η : ℝ}
    (haccuracy : 0 < accuracy) (hu : 0 < u)
    (hβ : 0 < β) (hd : 0 < d) (hη : 0 < η)
    (hscale : accuracy < u * β * d)
    (herror : β + 4 * quittingRewardBound reward *
      (Fintype.card ι : ℝ) * d ≤ η) :
    QuittingLowSurvivalPurifiedCoreAt source β d η := by
  let survival := quittingJointSurvivalWeight source.roots 0
    (source.crossingStage - 1)
  have hsurvival : 0 < survival := hu.trans source.before
  have hshift := isεQuittingRootSequenceNash_shift_of_survival_ge
    reward source.roots haccuracy.le hsurvival source.sourceNash
      (source.crossingStage - 1) le_rfl
  have hprofileNash :
      (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (accuracy / survival)
        source.predecessorProfile := by
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
        (accuracy / survival)
        (fun offset ↦ source.roots
          (source.crossingStage - 1 + offset))).mp hshift
    have hprofile : quittingRootSequenceProfile reward
        (fun offset ↦ source.roots
          (source.crossingStage - 1 + offset)) 0 =
        source.predecessorProfile := by
      funext player time history
      simp [quittingRootSequenceProfile,
        QuittingLowSurvivalFirstCrossingSourceAt.predecessorProfile]
    rwa [hprofile] at hbehavior
  have hadapter :=
    (isεAsymptoticNash_firstStageAdapter_iff reward
      source.predecessorProfile (accuracy / survival)).mpr hprofileNash
  have hroot : quittingProfileRoot reward source.predecessorProfile =
      source.roots (source.crossingStage - 1) := by
    funext who
    rfl
  unfold quittingFirstStageAdapter at hadapter
  rw [hroot] at hadapter
  let actual : Payoff ι := fun who ↦
    quittingTerminalPayoff reward source.continuation who
  let clipped := source.clippedTail η
  let original := source.roots (source.crossingStage - 1)
  let purified := source.clippedPurifiedRoot η β
  have htail : ∀ who, actual who ≤ clipped who := by
    intro who
    exact le_quittingPunishmentFloorClipAt reward η actual who
  have hquitCap : ∀ who,
      quittingRootQuitPayoff reward actual original who ≤
        quittingRootSuccessorPayoff reward actual original who +
          accuracy / survival := by
    intro who
    exact quittingRootQuitPayoff_le_successor_add_of_spliceNash
      reward original source.continuation (accuracy / survival) hadapter who
  have hcontinueCap : ∀ who,
      quittingRootContinuePayoff reward clipped original who ≤
        quittingRootSuccessorPayoff reward actual original who +
          accuracy / survival := by
    intro who
    exact quittingRootContinuePayoff_floorClip_le_successor_add_of_spliceNash
      reward original source.continuation hη (accuracy / survival)
        hadapter who
  have hlocalError : 0 < accuracy / survival :=
    div_pos haccuracy hsurvival
  have hbadQuit : ∀ who,
      IsQuittingRootBadQuitAt reward clipped β original who →
        (original who true).toReal * β < accuracy / survival := by
    intro who hbad
    exact badQuit_quitProbability_mul_lt_of_endpointCaps
      reward actual clipped original hlocalError htail hcontinueCap who hbad
  have hbadContinue : ∀ who,
      IsQuittingRootBadContinueAt reward clipped β original who →
        (original who false).toReal * β < accuracy / survival := by
    intro who hbad
    exact badContinue_continueProbability_mul_lt_of_endpointCaps
      reward actual clipped original hlocalError htail hquitCap who hbad
  have hscaleActual : accuracy < survival * β * d := by
    calc
      accuracy < u * β * d := hscale
      _ = u * (β * d) := by ring
      _ < survival * (β * d) :=
        mul_lt_mul_of_pos_right source.before (mul_pos hβ hd)
      _ = survival * β * d := by ring
  have hclose : ∀ who,
      |(purified who true).toReal - (original who true).toReal| < d := by
    exact supportPurifiedRoot_coordinate_close_of_mul_bound
      reward clipped original hsurvival hβ hd hscaleActual
        hbadQuit hbadContinue
  have htailBound : ∀ who,
      |clipped who| ≤ quittingRewardBound reward := by
    intro who
    exact abs_lowSurvival_clippedTail_le_rewardBound
      reward source.continuation hη.le who
  have hstable := isQuittingRootEndpointStableWithin_of_uniformBound
    reward clipped original (d := d)
      (abs_reward_le_quittingRewardBound reward) htailBound
  have hsupport : IsQuittingRootSupportApproxNash reward clipped η purified := by
    apply isQuittingRootSupportApproxNash_supportPurifiedRoot
      reward clipped original hβ.le _ hstable hclose
    calc
      β + 2 * ((2 * quittingRewardBound reward) *
          ((Fintype.card ι : ℝ) * d)) =
          β + 4 * quittingRewardBound reward *
            (Fintype.card ι : ℝ) * d := by ring
      _ ≤ η := herror
  exact ⟨
    quittingSimonRationalPayoffAt_quittingPunishmentFloorClipAt
      reward η actual,
    hsupport, hclose, htailBound⟩

/-- A literal purified row with a positive displayed Continue-mass lower bound
supplies the full local floor-clipped certificate.  Positivity itself excludes
bad-Continue deletion and sure quitters; no global carrier predicate is used.
-/
theorem
    QuittingLowSurvivalFirstCrossingSourceAt.floorClippedCertificate_of_massLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d η ρ : ℝ}
    (core : QuittingLowSurvivalPurifiedCoreAt source β d η)
    (hβ : 0 ≤ β) (hρ : 0 < ρ)
    (hmass : ρ ≤ quittingStationaryContinueMass
      (source.clippedPurifiedRoot η β)) :
    QuittingFloorClippedPurificationCertificate reward
      (source.clippedTail η) d η ρ ((Fintype.card ι : ℝ) * d)
      (source.roots (source.crossingStage - 1))
      (source.clippedPurifiedRoot η β) := by
  let original := source.roots (source.crossingStage - 1)
  let purified := source.clippedPurifiedRoot η β
  have hmassPos : 0 < quittingStationaryContinueMass purified :=
    hρ.trans_le hmass
  have hnotSure : ¬QuittingRootHasSureQuitter purified := by
    rintro ⟨who, hwho⟩
    have hzero := quittingStationaryContinueMass_of_sureQuitter hwho
    linarith
  have hnoBadContinue : ∀ who,
      ¬IsQuittingRootBadContinueAt reward (source.clippedTail η) β
        original who := by
    intro who hbadContinue
    have hnotBadQuit : ¬IsQuittingRootBadQuitAt reward
        (source.clippedTail η) β original who := by
      intro hbadQuit
      exact not_badContinue_of_badQuit reward (source.clippedTail η)
        hβ original who hbadQuit hbadContinue
    have hpure := quittingSupportPurifiedRoot_eq_pure_true_of_badContinue
      reward (source.clippedTail η) β original who hnotBadQuit hbadContinue
    have hzero := quittingStationaryContinueMass_of_sureQuitter hpure
    exact hmassPos.ne' hzero
  have hquitLe : ∀ who,
      (purified who true).toReal ≤ (original who true).toReal := by
    exact supportPurifiedRoot_quitProbability_le_of_no_badContinue
      reward (source.clippedTail η) β original hnoBadContinue
  have hdeleted : ∀ who,
      (original who true).toReal - (purified who true).toReal ≤ d := by
    intro who
    have hclose := core.coordinateClose who
    have hle : (original who true).toReal - (purified who true).toReal ≤
        |(purified who true).toReal - (original who true).toReal| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith
  have hloss : quittingStationaryContinueMass purified -
      quittingStationaryContinueMass original ≤ (Fintype.card ι : ℝ) * d := by
    exact continueMass_supportPurifiedRoot_sub_le_card_mul
      reward (source.clippedTail η) β d original hnoBadContinue hdeleted
  exact ⟨core.rational, core.support, core.coordinateClose, hnotSure,
    hquitLe, hmass, hloss⟩

/-- A positive local mass lower bound and a sufficiently small purification
radius give the desired first-crossing landing for the literal source row.
-/
theorem QuittingLowSurvivalFirstCrossingSourceAt.floorClippedLanding_of_massLower
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {u accuracy : ℝ} {horizon : ℕ}
    (source : QuittingLowSurvivalFirstCrossingSourceAt
      reward u accuracy horizon)
    {β d η ρ : ℝ}
    (core : QuittingLowSurvivalPurifiedCoreAt source β d η)
    (hβ : 0 ≤ β) (hρ : 0 < ρ)
    (hmass : ρ ≤ quittingStationaryContinueMass
      (source.clippedPurifiedRoot η β))
    (hd : (Fintype.card ι : ℝ) * d < ρ / 2) :
    ρ / 2 < quittingStationaryContinueMass
        (source.roots (source.crossingStage - 1)) ∧
      u * ρ / 2 < quittingJointSurvivalWeight source.roots 0
        source.crossingStage ∧
      quittingJointSurvivalWeight source.roots 0 source.crossingStage ≤ u := by
  have certificate := source.floorClippedCertificate_of_massLower
    core hβ hρ hmass
  have horiginal := certificate.originalContinue_lower
  have hcontinue : ρ / 2 < quittingStationaryContinueMass
      (source.roots (source.crossingStage - 1)) := by
    linarith
  have hrecurrence : quittingJointSurvivalWeight source.roots 0
      source.crossingStage =
        quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1) *
        quittingStationaryContinueMass
          (source.roots (source.crossingStage - 1)) := by
    have hrec := quittingJointSurvivalWeight_succ source.roots 0
      (source.crossingStage - 1)
    rw [Nat.sub_add_cancel source.crossingStage_pos] at hrec
    simpa only [zero_add] using hrec
  have hproduct : u * (ρ / 2) <
      quittingJointSurvivalWeight source.roots 0
          (source.crossingStage - 1) *
        quittingStationaryContinueMass
          (source.roots (source.crossingStage - 1)) := by
    exact mul_lt_mul source.before hcontinue.le (div_pos hρ (by norm_num))
      (quittingJointSurvivalWeight_nonneg source.roots 0
        (source.crossingStage - 1))
  refine ⟨hcontinue, ?_, source.crossing⟩
  rw [hrecurrence]
  nlinarith [hproduct]

/-- A nonnegative scalar sequence either tends to zero or is bounded below by
one positive constant cofinally. -/
theorem tendsto_zero_or_exists_cofinally_lower
    (mass : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ mass n) :
    Tendsto mass atTop (nhds 0) ∨
      ∃ ρ, 0 < ρ ∧ ∀ cutoff, ∃ n, cutoff ≤ n ∧ ρ ≤ mass n := by
  by_cases hzero : Tendsto mass atTop (nhds 0)
  · exact Or.inl hzero
  · right
    rw [Metric.tendsto_atTop] at hzero
    push Not at hzero
    obtain ⟨ρ, hρ, hcofinal⟩ := hzero
    refine ⟨ρ, hρ, fun cutoff ↦ ?_⟩
    obtain ⟨n, hn, hfar⟩ := hcofinal cutoff
    refine ⟨n, hn, ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg n)] at hfar
    exact hfar

/-- Literal first-crossing sources chosen at errors tending to zero, with an
explicit purification schedule.  The family stores only source and scale
data; neither branch of the scalar compactness alternative is assumed. -/
structure QuittingLowSurvivalScaleFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) where
  accuracy : ℕ → ℝ
  horizon : ℕ → ℕ
  source : ∀ n, QuittingLowSurvivalFirstCrossingSourceAt
    reward u (accuracy n) (horizon n)
  beta : ℕ → ℝ
  radius : ℕ → ℝ
  tolerance : ℕ → ℝ
  u_pos : 0 < u
  accuracy_pos : ∀ n, 0 < accuracy n
  beta_pos : ∀ n, 0 < beta n
  radius_pos : ∀ n, 0 < radius n
  tolerance_pos : ∀ n, 0 < tolerance n
  scale : ∀ n, accuracy n < u * beta n * radius n
  support_budget : ∀ n,
    beta n + 4 * quittingRewardBound reward *
      (Fintype.card ι : ℝ) * radius n ≤ tolerance n
  radius_tendsto_zero : Tendsto radius atTop (nhds 0)
  tolerance_tendsto_zero : Tendsto tolerance atTop (nhds 0)

/-- Canonical positive scale used to turn low-survival prefixes at all small
accuracies into one scale family. -/
def quittingLowSurvivalCompactScale (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem quittingLowSurvivalCompactScale_pos (n : ℕ) :
    0 < quittingLowSurvivalCompactScale n := by
  unfold quittingLowSurvivalCompactScale
  positivity

theorem tendsto_quittingLowSurvivalCompactScale_zero :
    Tendsto quittingLowSurvivalCompactScale atTop (nhds 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The literal remaining low-survival arm at the canonical vanishing error
schedule.  It asks for actual approximate-equilibrium prefixes, not for
either conclusion of the compact alternative. -/
def HasLowSurvivalPrefixesAtCompactScales
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) : Prop :=
  ∀ n, ∃ horizon,
    QuittingLowSurvivalApproximatePrefixAt reward u
      (u * quittingLowSurvivalCompactScale n ^ 2 / 2) horizon

/-- Actual low-survival prefixes at the canonical scales produce a complete
source-matched purification family by first-crossing extraction. -/
theorem nonempty_lowSurvivalScaleFamily_of_prefixesAtCompactScales
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {u : ℝ} (hu : 0 < u) (huOne : u < 1)
    (hlow : HasLowSurvivalPrefixesAtCompactScales reward u) :
    Nonempty (QuittingLowSurvivalScaleFamily reward u) := by
  classical
  let accuracy : ℕ → ℝ := fun n ↦
    u * quittingLowSurvivalCompactScale n ^ 2 / 2
  let horizon : ℕ → ℕ := fun n ↦ Classical.choose (hlow n)
  have hprefix : ∀ n, QuittingLowSurvivalApproximatePrefixAt reward u
      (accuracy n) (horizon n) := by
    intro n
    exact Classical.choose_spec (hlow n)
  let source : ∀ n, QuittingLowSurvivalFirstCrossingSourceAt
      reward u (accuracy n) (horizon n) := fun n ↦
    Classical.choice
      (nonempty_lowSurvivalFirstCrossingSource_of_lowSurvivalApproximatePrefix
        reward huOne (hprefix n))
  let beta : ℕ → ℝ := quittingLowSurvivalCompactScale
  let radius : ℕ → ℝ := quittingLowSurvivalCompactScale
  let coefficient : ℝ :=
    1 + 4 * quittingRewardBound reward * (Fintype.card ι : ℝ)
  let tolerance : ℕ → ℝ := fun n ↦
    coefficient * quittingLowSurvivalCompactScale n
  refine ⟨{
    accuracy := accuracy
    horizon := horizon
    source := source
    beta := beta
    radius := radius
    tolerance := tolerance
    u_pos := hu
    accuracy_pos := ?_
    beta_pos := ?_
    radius_pos := ?_
    tolerance_pos := ?_
    scale := ?_
    support_budget := ?_
    radius_tendsto_zero := ?_
    tolerance_tendsto_zero := ?_ }⟩
  · intro n
    dsimp [accuracy]
    exact div_pos
      (mul_pos hu (sq_pos_of_pos (quittingLowSurvivalCompactScale_pos n)))
      (by norm_num)
  · exact quittingLowSurvivalCompactScale_pos
  · exact quittingLowSurvivalCompactScale_pos
  · intro n
    have hcoefficient : 0 < coefficient := by
      dsimp [coefficient]
      have hbound := quittingRewardBound_nonneg reward
      positivity
    exact mul_pos hcoefficient (quittingLowSurvivalCompactScale_pos n)
  · intro n
    dsimp [accuracy, beta, radius]
    have hscale := quittingLowSurvivalCompactScale_pos n
    have hproduct : 0 < u * quittingLowSurvivalCompactScale n ^ 2 :=
      mul_pos hu (sq_pos_of_pos hscale)
    calc
      u * quittingLowSurvivalCompactScale n ^ 2 / 2 <
          u * quittingLowSurvivalCompactScale n ^ 2 :=
        div_lt_self hproduct (by norm_num)
      _ = u * quittingLowSurvivalCompactScale n *
          quittingLowSurvivalCompactScale n := by ring
  · intro n
    dsimp [beta, radius, tolerance, coefficient]
    ring_nf
    exact le_rfl
  · exact tendsto_quittingLowSurvivalCompactScale_zero
  · simpa [tolerance] using
      tendsto_quittingLowSurvivalCompactScale_zero.const_mul coefficient

namespace QuittingLowSurvivalScaleFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
variable (family : QuittingLowSurvivalScaleFamily reward u)

/-- The actual floor-clipped purified crossing row at one scale. -/
def purifiedRoot (n : ℕ) : ι → PMF Bool :=
  (family.source n).clippedPurifiedRoot
    (family.tolerance n) (family.beta n)

/-- Its compact scalar coordinate. -/
def purifiedMass (n : ℕ) : ℝ :=
  quittingStationaryContinueMass (family.purifiedRoot n)

theorem purifiedMass_nonneg (n : ℕ) : 0 ≤ family.purifiedMass n :=
  quittingStationaryContinueMass_nonneg _

/-- Every scale in the family supplies the local source-matched purified
core. -/
theorem core (n : ℕ) : QuittingLowSurvivalPurifiedCoreAt
    (family.source n) (family.beta n) (family.radius n)
      (family.tolerance n) := by
  exact (family.source n).floorClippedPurifiedCore
    (family.accuracy_pos n) family.u_pos (family.beta_pos n)
      (family.radius_pos n) (family.tolerance_pos n) (family.scale n)
      (family.support_budget n)

/-- If the purified masses tend to zero, the literal clipped rows satisfy the
production near-total support-row interface at arbitrarily small errors. -/
theorem hasNearTotalSupportRows_of_purifiedMass_tendsto_zero
    (hmass : Tendsto family.purifiedMass atTop (nhds 0)) :
    HasArbitrarilySmallQuittingNearTotalSupportRows reward
      (quittingRewardBound reward) := by
  let gamma : ℕ → ℝ := fun n ↦
    family.tolerance n + family.purifiedMass n
  have hgamma : Tendsto gamma atTop (nhds 0) := by
    simpa [gamma] using family.tolerance_tendsto_zero.add hmass
  intro threshold hthreshold
  have heventually : ∀ᶠ n in atTop, gamma n < threshold :=
    (tendsto_order.1 hgamma).2 threshold hthreshold
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 heventually
  let n := cutoff
  let source := family.source n
  let tail := source.clippedTail (family.tolerance n)
  let root := family.purifiedRoot n
  have hcore := family.core n
  have hgammaPos : 0 < gamma n := by
    dsimp [gamma]
    exact add_pos_of_pos_of_nonneg (family.tolerance_pos n)
      (purifiedMass_nonneg family n)
  refine ⟨gamma n, tail, root, hgammaPos, hcutoff n le_rfl,
    ?_, ?_, ?_, ?_⟩
  · exact hcore.tail_bound
  · apply hcore.rational.mono
    dsimp [gamma]
    exact le_add_of_nonneg_right (purifiedMass_nonneg family n)
  · apply hcore.support.mono
    dsimp [gamma]
    exact le_add_of_nonneg_right (purifiedMass_nonneg family n)
  · unfold quittingRootAbsorptionMass
    change 1 - gamma n < 1 - family.purifiedMass n
    dsimp [gamma]
    linarith [family.tolerance_pos n]

/-- The zero-mass side immediately feeds the checked unrestricted-behavior
instant-punishment consumer. -/
theorem instantPunishmentExistence_of_purifiedMass_tendsto_zero
    [Nonempty ι]
    (hmass : Tendsto family.purifiedMass atTop (nhds 0)) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  exact quittingInstantPunishmentεEquilibriumExistence_of_nearTotalSupportRows
    reward (abs_reward_le_quittingRewardBound reward)
      (family.hasNearTotalSupportRows_of_purifiedMass_tendsto_zero hmass)

/-- Cofinal rows above one positive purified-mass floor yield cofinally many
literal first-crossing landings with the same `rho`. -/
theorem exists_cofinally_floorClippedLanding_of_cofinally_massLower
    [Nonempty ι] {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∀ cutoff, ∃ n, cutoff ≤ n ∧ ρ ≤ family.purifiedMass n) :
    ∀ cutoff, ∃ n, cutoff ≤ n ∧
      ρ ≤ family.purifiedMass n ∧
      ρ / 2 < quittingStationaryContinueMass
          ((family.source n).roots ((family.source n).crossingStage - 1)) ∧
        u * ρ / 2 < quittingJointSurvivalWeight
          (family.source n).roots 0 (family.source n).crossingStage ∧
        quittingJointSurvivalWeight (family.source n).roots 0
          (family.source n).crossingStage ≤ u := by
  have hradius : Tendsto (fun n ↦
      (Fintype.card ι : ℝ) * family.radius n) atTop (nhds 0) := by
    simpa using family.radius_tendsto_zero.const_mul (Fintype.card ι : ℝ)
  have heventually : ∀ᶠ n in atTop,
      (Fintype.card ι : ℝ) * family.radius n < ρ / 2 :=
    (tendsto_order.1 hradius).2 _ (div_pos hρ (by norm_num))
  obtain ⟨radiusCutoff, hradiusCutoff⟩ := eventually_atTop.1 heventually
  intro cutoff
  obtain ⟨n, hn, hnMass⟩ := hmass (max cutoff radiusCutoff)
  have hcutoff : cutoff ≤ n := (le_max_left _ _).trans hn
  have hradiusN := hradiusCutoff n ((le_max_right _ _).trans hn)
  have hlanding := (family.source n).floorClippedLanding_of_massLower
    (family.core n) (family.beta_pos n).le hρ hnMass hradiusN
  exact ⟨n, hcutoff, hnMass, hlanding⟩

/-- **Actual-data compact alternative for the low-survival arm.**  Scalar
compactness produces either the checked near-total row interface or one
uniform positive floor on cofinally many source-matched survival landings.
-/
theorem nearTotalSupportRows_or_exists_positiveRho_cofinallyLanding
    [Nonempty ι] :
    HasArbitrarilySmallQuittingNearTotalSupportRows reward
        (quittingRewardBound reward) ∨
      ∃ ρ, 0 < ρ ∧ ∀ cutoff, ∃ n, cutoff ≤ n ∧
        ρ ≤ family.purifiedMass n ∧
        ρ / 2 < quittingStationaryContinueMass
            ((family.source n).roots ((family.source n).crossingStage - 1)) ∧
          u * ρ / 2 < quittingJointSurvivalWeight
            (family.source n).roots 0 (family.source n).crossingStage ∧
          quittingJointSurvivalWeight (family.source n).roots 0
            (family.source n).crossingStage ≤ u := by
  rcases tendsto_zero_or_exists_cofinally_lower family.purifiedMass
      (purifiedMass_nonneg family) with hzero | ⟨ρ, hρ, hmass⟩
  · exact Or.inl
      (family.hasNearTotalSupportRows_of_purifiedMass_tendsto_zero hzero)
  · exact Or.inr ⟨ρ, hρ,
      family.exists_cofinally_floorClippedLanding_of_cofinally_massLower
        hρ hmass⟩

end QuittingLowSurvivalScaleFamily

/-- The positive side of the low-survival compact alternative, retaining the
entire literal source family and one common landing constant. -/
structure QuittingLowSurvivalPositiveRhoLandingFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (u : ℝ) where
  family : QuittingLowSurvivalScaleFamily reward u
  rho : ℝ
  rho_pos : 0 < rho
  cofinally_landing : ∀ cutoff, ∃ n, cutoff ≤ n ∧
    rho ≤ family.purifiedMass n ∧
    rho / 2 < quittingStationaryContinueMass
        ((family.source n).roots ((family.source n).crossingStage - 1)) ∧
      u * rho / 2 < quittingJointSurvivalWeight
        (family.source n).roots 0 (family.source n).crossingStage ∧
      quittingJointSurvivalWeight (family.source n).roots 0
        (family.source n).crossingStage ≤ u

/-- The positive landing family produces actual local floor-clipped
certificates at arbitrarily late scales. -/
theorem QuittingLowSurvivalPositiveRhoLandingFamily.exists_certificate_after
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {u : ℝ}
    (landing : QuittingLowSurvivalPositiveRhoLandingFamily reward u)
    (cutoff : ℕ) :
    ∃ n, cutoff ≤ n ∧
      QuittingFloorClippedPurificationCertificate reward
        ((landing.family.source n).clippedTail
          (landing.family.tolerance n))
        (landing.family.radius n) (landing.family.tolerance n) landing.rho
        ((Fintype.card ι : ℝ) * landing.family.radius n)
        ((landing.family.source n).roots
          ((landing.family.source n).crossingStage - 1))
        (landing.family.purifiedRoot n) := by
  obtain ⟨n, hn, hmass, _hlanding⟩ := landing.cofinally_landing cutoff
  refine ⟨n, hn, ?_⟩
  exact (landing.family.source n).floorClippedCertificate_of_massLower
    (landing.family.core n) (landing.family.beta_pos n).le
      landing.rho_pos hmass

/-- **Low-survival capstone at canonical scales.**  Actual low-survival
prefixes at every canonical error either feed the checked instant-punishment
consumer or yield a source-matched family with one positive landing constant.
-/
theorem instantPunishmentExistence_or_positiveRhoLandingFamily_of_lowSurvivalPrefixes
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {u : ℝ} (hu : 0 < u) (huOne : u < 1)
    (hlow : HasLowSurvivalPrefixesAtCompactScales reward u) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      Nonempty (QuittingLowSurvivalPositiveRhoLandingFamily reward u) := by
  obtain ⟨family⟩ :=
    nonempty_lowSurvivalScaleFamily_of_prefixesAtCompactScales
      reward hu huOne hlow
  rcases tendsto_zero_or_exists_cofinally_lower family.purifiedMass
      (QuittingLowSurvivalScaleFamily.purifiedMass_nonneg family) with
    hzero | ⟨rho, hrho, hmass⟩
  · exact Or.inl
      (family.instantPunishmentExistence_of_purifiedMass_tendsto_zero hzero)
  · exact Or.inr ⟨{
      family := family
      rho := rho
      rho_pos := hrho
      cofinally_landing :=
        family.exists_cofinally_floorClippedLanding_of_cofinally_massLower
          hrho hmass }⟩

end GameTheory
