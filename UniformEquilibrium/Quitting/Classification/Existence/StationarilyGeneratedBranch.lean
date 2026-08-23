/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Classification.InstantPunishmentEquivalence
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Stationarily generated approximate equilibria

Simon (2012) corrects the strategic hypothesis used in Simon (2007): the
proof excludes *stationarily generated* approximate equilibria, not merely
stationary approximate equilibria.  A stationarily generated profile repeats
one product root through a finite horizon and, conditional on surviving that
prefix, switches to an arbitrary punishment profile for one player.

The definitions here use root sequences.  This loses no behavior semantics in
a quitting game: only the all-Continue history remains live, and the theorems
below identify both prescribed and deviating payoffs with the corresponding
live-root sequence.  The punishment condition is the actual behavioral
best-reply cap, not a stationary proxy.

No implication from this corrected residual to the stationary branch is
asserted.  Such an implication would be the additional compactification
theorem needed to recover the three-branch statement cited in later work.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Repeat `root` through stage `horizon`, then switch to `punishment` from
stage `horizon + 1` onward. -/
def quittingStationaryPrefixThenRoots
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) : ℕ → ι → PMF Bool :=
  fun time => if time ≤ horizon then root
    else punishment (time - (horizon + 1))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingStationaryPrefixThenRoots_of_le
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) {time : ℕ} (htime : time ≤ horizon) :
    quittingStationaryPrefixThenRoots root horizon punishment time = root := by
  simp [quittingStationaryPrefixThenRoots, htime]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingStationaryPrefixThenRoots_add
    (root : ι → PMF Bool) (horizon offset : ℕ)
    (punishment : ℕ → ι → PMF Bool) :
    quittingStationaryPrefixThenRoots root horizon punishment
        (horizon + 1 + offset) =
      punishment offset := by
  rw [quittingStationaryPrefixThenRoots, if_neg (by omega)]
  congr
  omega

/-- A root-sequence punishment holds `who` to within `δ` of the quitting
min-max against every time-dependent hazard response. -/
def IsQuittingRootSequencePunishmentWithin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (δ : ℝ) (punishment : ℕ → ι → PMF Bool) : Prop :=
  ∀ hazard : ℕ → PMF Bool,
    quittingRootSequenceHazardTerminalValue reward punishment who hazard 0 ≤
      quittingPunishmentValue reward who + δ

/-- The root-sequence punishment predicate is exactly the behavioral
best-reply cap of its generated history-independent profile. -/
theorem isQuittingRootSequencePunishmentWithin_iff_bestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (δ : ℝ) (punishment : ℕ → ι → PMF Bool) :
    IsQuittingRootSequencePunishmentWithin reward who δ punishment ↔
      quittingBestReplyValue reward
          (quittingRootSequenceProfile reward punishment 0) who ≤
        quittingPunishmentValue reward who + δ := by
  letI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
    ⟨fun _time _history => PMF.pure false⟩
  constructor
  · intro hpunish
    unfold quittingBestReplyValue
    apply ciSup_le
    intro deviation
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    exact hpunish (quittingBehaviorLiveHazard reward deviation)
  · intro hpunish hazard
    let deviation : (quittingGame reward).BehaviorStrategy who :=
      fun time _history => hazard time
    have hle : quittingTerminalPayoff reward
        (Function.update (quittingRootSequenceProfile reward punishment 0)
          who deviation) who ≤
        quittingBestReplyValue reward
          (quittingRootSequenceProfile reward punishment 0) who :=
      le_ciSup
        (bddAbove_range_quittingTerminalPayoff_update reward
          (quittingRootSequenceProfile reward punishment 0) who)
        deviation
    rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero] at hle
    rw [show quittingBehaviorLiveHazard reward deviation = hazard by rfl] at hle
    exact hle.trans hpunish

/-- Approximate-equilibrium existence in root-sequence form. -/
def QuittingApproximateEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ roots : ℕ → ι → PMF Bool,
    IsεQuittingRootSequenceNash reward ε roots

/-- An arbitrary behavior profile's live roots preserve its full approximate
Nash property, including every behavioral deviation. -/
theorem isεQuittingRootSequenceNash_profileLiveRoot_of_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {ε : ℝ}
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    IsεQuittingRootSequenceNash reward ε
      (quittingProfileLiveRoot reward profile) := by
  intro who hazard
  let deviation : (quittingGame reward).BehaviorStrategy who :=
    fun time _history => hazard time
  have hdeviation := hnash who deviation
  rw [quittingTerminalPayoff_update_eq_rootSequenceHazardTerminalValue] at hdeviation
  have hhazard : quittingBehaviorLiveHazard reward deviation = hazard := rfl
  rw [hhazard, quittingTerminalPayoff_eq_rootSequence_profileLiveRoot] at hdeviation
  exact hdeviation

/-- Root-sequence approximate-equilibrium existence is equivalent to the
ordinary behavior-profile statement. -/
theorem quittingApproximateEquilibriumExistence_iff_behavior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingApproximateEquilibriumExistence reward ↔
      ∀ ε : ℝ, 0 < ε → ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  constructor
  · intro hexists ε hε
    obtain ⟨roots, hnash⟩ := hexists ε hε
    exact ⟨quittingRootSequenceProfile reward roots 0,
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
        reward ε roots).mp hnash⟩
  · intro hexists ε hε
    obtain ⟨profile, hnash⟩ := hexists ε hε
    exact ⟨quittingProfileLiveRoot reward profile,
      isεQuittingRootSequenceNash_profileLiveRoot_of_isεAsymptoticNash
        reward profile hnash⟩

/-- Root-sequence approximate equilibria at every positive accuracy already
select a uniform-equilibrium payoff.  This is the canonical direct consumer
of `QuittingApproximateEquilibriumExistence`; no stationary-prefix, punishment,
or finite-orbit classification hypothesis is needed. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_approximateEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors reward
    ((quittingApproximateEquilibriumExistence_iff_behavior reward).mp hequilibrium)

/-- The corrected Simon residual at a displayed punishment accuracy `δ`:
for every positive equilibrium slack, one finite repeated-root prefix followed
by a `δ`-punishment is an `(ε + δ)`-equilibrium. -/
def QuittingStationarilyGeneratedApproximateEquilibriaAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (root : ι → PMF Bool) (horizon : ℕ) (who : ι)
    (punishment : ℕ → ι → PMF Bool),
      1 < horizon ∧
        IsQuittingRootSequencePunishmentWithin reward who δ punishment ∧
        IsεQuittingRootSequenceNash reward (ε + δ)
          (quittingStationaryPrefixThenRoots root horizon punishment)

/-- Arbitrarily accurate stationarily generated approximate equilibria, with
the punishment accuracy quantified independently of the equilibrium slack. -/
def QuittingStationarilyGeneratedApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    QuittingStationarilyGeneratedApproximateEquilibriaAt reward δ

/-- A stationarily generated witness remains one when the displayed
punishment accuracy is relaxed. -/
theorem QuittingStationarilyGeneratedApproximateEquilibriaAt.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ δ' : ℝ}
    (hwitness : QuittingStationarilyGeneratedApproximateEquilibriaAt reward δ)
    (hle : δ ≤ δ') :
    QuittingStationarilyGeneratedApproximateEquilibriaAt reward δ' := by
  intro ε hε
  obtain ⟨root, horizon, who, punishment, hhorizon, hpunish, hnash⟩ :=
    hwitness ε hε
  refine ⟨root, horizon, who, punishment, hhorizon, ?_, ?_⟩
  · intro hazard
    have := hpunish hazard
    linarith
  · intro player hazard
    have := hnash player hazard
    linarith

/-- Stationarily generated approximate equilibria are genuine behavioral
approximate equilibria. -/
theorem quittingApproximateEquilibriumExistence_of_stationarilyGenerated
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingStationarilyGeneratedApproximateEquilibria reward) :
    QuittingApproximateEquilibriumExistence reward := by
  intro ε hε
  have hquarter : 0 < ε / 4 := by linarith
  obtain ⟨root, horizon, who, punishment, _hhorizon, _hpunish, hnash⟩ :=
    hgenerated (ε / 4) hquarter (ε / 4) hquarter
  refine ⟨quittingStationaryPrefixThenRoots root horizon punishment, ?_⟩
  intro player hazard
  have hbound := hnash player hazard
  have herror : ε / 4 + ε / 4 ≤ ε := by linarith
  exact hbound.trans (by linarith)

/-! ## The genuine residual after excluding the instant branch -/

/-- A root-sequence punishment remains valid when its error allowance is
relaxed. -/
theorem IsQuittingRootSequencePunishmentWithin.mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {who : ι} {punishment : ℕ → ι → PMF Bool} {δ δ' : ℝ}
    (hpunish : IsQuittingRootSequencePunishmentWithin reward who δ punishment)
    (hle : δ ≤ δ') :
    IsQuittingRootSequencePunishmentWithin reward who δ' punishment := by
  intro hazard
  have := hpunish hazard
  linarith

omit [DecidableEq ι] in
/-- If no marginal is surely Quit, the product row has positive probability
of remaining live for one more stage. -/
theorem quittingStationaryContinueMass_pos_of_noSureQuitter
    (root : ι → PMF Bool) (hnoSure : ¬QuittingRootHasSureQuitter root) :
    0 < quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  apply Finset.prod_pos
  intro who _hwho
  have hnonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  apply hnoSure
  refine ⟨who, (pmf_eq_pure_true_iff_apply_false_eq_zero (root who)).mpr ?_⟩
  rcases (ENNReal.toReal_eq_zero_iff (root who false)).mp hzero.symm with
    hzero' | htop
  · exact hzero'
  · exact absurd htop (PMF.apply_ne_top _ _)

/-- The stationarily generated residual at punishment accuracy `δ`, with
the additional information that the repeated root leaves positive one-stage
survival mass.  The witness retains the horizon, player, punishment cap, and
full behavioral equilibrium inequality needed by later purification steps. -/
def QuittingDiffuseStationarilyGeneratedApproximateEquilibriaAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (root : ι → PMF Bool) (horizon : ℕ) (who : ι)
    (punishment : ℕ → ι → PMF Bool),
      1 < horizon ∧
        IsQuittingRootSequencePunishmentWithin reward who δ punishment ∧
        IsεQuittingRootSequenceNash reward (ε + δ)
          (quittingStationaryPrefixThenRoots root horizon punishment) ∧
        0 < quittingStationaryContinueMass root

/-- Arbitrarily accurate stationarily generated witnesses whose repeated
root has positive live mass. -/
def QuittingDiffuseStationarilyGeneratedApproximateEquilibria
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    QuittingDiffuseStationarilyGeneratedApproximateEquilibriaAt reward δ

/-- After the instant branch is excluded, every stationarily generated
witness can be chosen with positive one-stage survival mass.  Otherwise sure
first-stage roots at every scale compile to branch `S.2`. -/
theorem quittingDiffuseStationarilyGeneratedApproximateEquilibria_of_not_instant
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward) :
    QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward := by
  classical
  have hmissing : ∃ threshold : ℝ, 0 < threshold ∧
      ¬∃ (quitter : ι) (root : ι → PMF Bool)
          (punish : (quittingGame reward).BehaviorProfile),
        root quitter = PMF.pure true ∧
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) threshold
            (quittingRootThenContinuationProfile reward root punish) := by
    by_contra hmissing
    apply hinstant
    apply quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
    push Not at hmissing
    exact hmissing
  obtain ⟨threshold, hthreshold, hnoSureProfile⟩ := hmissing
  intro δ hδ ε hε
  let scale := min (min δ ε) threshold / 4
  have hscale : 0 < scale := by
    dsimp only [scale]
    positivity
  have hscaleδ : scale ≤ δ := by
    dsimp only [scale]
    have hmin : min (min δ ε) threshold ≤ δ :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hminPos : 0 < min (min δ ε) threshold := by positivity
    linarith
  have hscaleε : scale ≤ ε := by
    dsimp only [scale]
    have hmin : min (min δ ε) threshold ≤ ε :=
      (min_le_left _ _).trans (min_le_right _ _)
    have hminPos : 0 < min (min δ ε) threshold := by positivity
    linarith
  have hscaleThreshold : 2 * scale ≤ threshold := by
    dsimp only [scale]
    have hmin : min (min δ ε) threshold ≤ threshold := min_le_right _ _
    have hminPos : 0 < min (min δ ε) threshold := by positivity
    linarith
  obtain ⟨root, horizon, who, punishment, hhorizon, hpunish, hnash⟩ :=
    hgenerated scale hscale scale hscale
  let roots := quittingStationaryPrefixThenRoots root horizon punishment
  have hrootZero : roots 0 = root := by
    exact quittingStationaryPrefixThenRoots_of_le root horizon punishment
      (Nat.zero_le horizon)
  have hnoSureRoot : ¬QuittingRootHasSureQuitter root := by
    rintro ⟨quitter, hquitter⟩
    apply hnoSureProfile
    refine ⟨quitter, root, quittingRootSequenceProfile reward roots 1,
      hquitter, ?_⟩
    have hbehavior : (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (2 * scale)
        (quittingRootSequenceProfile reward roots 0) := by
      apply (isεQuittingRootSequenceNash_iff_isεAsymptoticNash
        reward (2 * scale) roots).mp
      convert hnash using 1
      ring
    have hrelaxed := hbehavior.mono hscaleThreshold
    rwa [quittingRootSequenceProfile_eq_rootThenContinuation,
      hrootZero, Nat.zero_add] at hrelaxed
  refine ⟨root, horizon, who, punishment, hhorizon,
    hpunish.mono hscaleδ, ?_,
    quittingStationaryContinueMass_pos_of_noSureQuitter root hnoSureRoot⟩
  intro player hazard
  have hbound := hnash player hazard
  have herror : 2 * scale ≤ ε + δ := by linarith
  exact hbound.trans (by linarith)

/-- The corrected stationarily generated branch has a checked semantic
dichotomy: it either yields the instant branch, or leaves the positive-live-
mass residual above. -/
theorem quittingInstant_or_diffuseStationarilyGenerated
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingStationarilyGeneratedApproximateEquilibria reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      QuittingDiffuseStationarilyGeneratedApproximateEquilibria reward := by
  by_cases hinstant : QuittingInstantPunishmentεEquilibriumExistence reward
  · exact Or.inl hinstant
  · exact Or.inr
      (quittingDiffuseStationarilyGeneratedApproximateEquilibria_of_not_instant
        hgenerated hinstant)

end GameTheory
