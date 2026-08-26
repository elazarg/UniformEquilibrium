/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.TwoOwnerCommonWordRealization
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedNegativeOwnerBoundary
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedPositiveLiveLimit
import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointSummablePortPhantomReduction
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Paths.SurvivalPrefixBridge
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Divergent exceptional-owner dispatch to S.2 or S.3

A divergent unique-exceptional-owner source is consumed completely.  After
selecting a fixed punished label and a limit of the one-row live masses, a
zero limit gives instant punishment, an interior limit gives an absorbing
positive-live limit, and a unit limit forces the exceptional owner's
singleton vector to dominate every player's own singleton payoff.  The last
condition compiles directly to a well-supported absorbing solo sequence.

The result concerns the support-local sequential branch.  In particular, a
negative exceptional owner may profit from the global deviation that never
quits, so the solo sequence constructed here is not claimed to be terminal
Nash.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- If one singleton payoff vector dominates every player's own singleton
payoff, vanishing positive solo hazards give well-supported absorbing
sequences.  No sign or punishment-individual-rationality hypothesis is
needed. -/
theorem quittingWellSupportedAbsorbingSequenceExistence_of_singletonFloor
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (owner : iota)
    (hfloor : ∀ who,
      quittingSoloReward reward who who ≤
        quittingSoloReward reward owner who) :
    QuittingWellSupportedAbsorbingSequenceExistence reward := by
  intro delta hdelta
  let M := quittingRewardBound reward
  let q := delta / (2 * M + delta + 1)
  have hM : 0 ≤ M := quittingRewardBound_nonneg reward
  have hdenom : 0 < 2 * M + delta + 1 := by positivity
  have hq0 : 0 < q := div_pos hdelta hdenom
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [div_lt_one hdenom]
    linarith
  have hdefect : 2 * M * q < delta := by
    have hstrict : 2 * M < 2 * M + delta + 1 := by linarith
    have hmul := mul_lt_mul_of_pos_right hstrict hq0
    have hqdenom : (2 * M + delta + 1) * q = delta := by
      dsimp only [q]
      field_simp
    linarith
  let hazard := quittingHazardCoin q hq0.le hq1.le
  let root := quittingSoloStationaryRoot owner hazard
  let roots : ℕ → iota → PMF Bool := fun _ ↦ root
  have hrootMass : quittingStationaryContinueMass root = 1 - q := by
    dsimp only [root, hazard]
    rw [quittingStationaryContinueMass_solo,
      quittingHazardCoin_false_toReal]
  have hcomplete : IsCompletelyAbsorbing roots := by
    have hbase0 : 0 ≤ 1 - q := by linarith
    have hbase1 : 1 - q < 1 := by linarith
    have heq : quittingSurvivalPrefix roots = fun horizon ↦ (1 - q) ^ horizon := by
      funext horizon
      simp [quittingSurvivalPrefix, roots, hrootMass]
    unfold IsCompletelyAbsorbing
    rw [heq]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have htail : ∀ time,
      quittingRootSequenceTailVector reward roots time =
        quittingSoloReward reward owner := by
    have hvalue :=
      eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
        reward roots (fun _ ↦ quittingSoloReward reward owner) hq0
        (fun time ↦ by
          dsimp only [roots, root, hazard]
          rw [quittingRootAbsorptionMass_soloStationaryRoot,
            quittingHazardCoin_true_toReal])
        (abs_reward_le_quittingRewardBound reward)
        (fun _ who ↦ by
          exact abs_reward_le_quittingRewardBound reward
            (quittingSingletonTerminal owner) who)
        (fun _ ↦ by
          simpa [roots, root] using
            (quittingRootSuccessorPayoff_soloStationaryRoot_self
              reward owner hazard).symm)
    intro time
    funext who
    exact (congrFun (hvalue time) who).symm
  refine ⟨roots, hcomplete, fun time ↦ ?_⟩
  rw [htail (time + 1)]
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootEndpointDifference_soloStationaryRoot_owner]
    constructor <;> intro <;> linarith
  · have hquitZero : (root who true).toReal = 0 := by
      dsimp only [root]
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hcontinuePositive : 0 < (root who false).toReal := by
      dsimp only [root]
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hcollisionUpper :
        quittingSingletonCollisionReward reward owner who ≤ M := by
      exact (le_abs_self _).trans (by
        simpa [M, quittingSingletonCollisionReward] using
          (abs_reward_le_quittingRewardBound reward
            ⟨{owner, who}, by simp⟩ who))
    have htargetLower :
        -M ≤ quittingSoloReward reward owner who := by
      exact (abs_le.mp (abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal owner) who)).1
    have hgap :
        quittingRootEndpointDifference reward
            (quittingSoloReward reward owner) root who < delta := by
      rw [quittingRootEndpointDifference_soloStationaryRoot_other
        reward hwho]
      have htrue : (hazard true).toReal = q := by
        dsimp only [hazard]
        rw [quittingHazardCoin_true_toReal]
      have hfalse : (hazard false).toReal = 1 - q := by
        dsimp only [hazard]
        rw [quittingHazardCoin_false_toReal]
      rw [htrue, hfalse]
      have hfloorWho := hfloor who
      calc
        (1 - q) * quittingSoloReward reward who who +
              q * quittingSingletonCollisionReward reward owner who -
            quittingSoloReward reward owner who ≤
            q * (quittingSingletonCollisionReward reward owner who -
              quittingSoloReward reward owner who) := by
          nlinarith
        _ ≤ q * (2 * M) := by
          gcongr
          linarith
        _ < delta := by nlinarith
    constructor
    · intro hpositive
      exact False.elim ((not_lt_of_ge hquitZero.le) hpositive)
    · intro _
      exact hgap.le

/-- Full behavioral individual rationality of the source, passed to the
divergent exceptional-owner limit.  The selected punished label plays no
role: the inequality holds playerwise. -/
theorem QuittingUniqueExceptionalOwnerSource.quittingPunishmentValue_le_soloReward
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop)
    (who : iota) :
    quittingPunishmentValue reward who ≤
      quittingSoloReward reward source.owner who := by
  have hbound : ∀ n,
      quittingPunishmentValue reward who -
          2 * source.family.error (source.selected n) ≤
        quittingStationaryPrefixFamilyValue source.family
          (source.selected n) 0 who := by
    intro n
    let roots := quittingStationaryPrefixFamilyPlan source.family
      (source.selected n)
    have hnash :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward
        (2 * source.family.error (source.selected n)) roots).mp
        (source.family.nash (source.selected n))
    simpa [roots, quittingStationaryPrefixFamilyValue,
      quittingRootSequenceTailVector, quittingRootSequenceTerminalValue] using
      (punishmentValue_sub_le_terminalPayoff_of_isεAsymptoticNash
        (quittingRootSequenceProfile reward roots 0) hnash who)
  have hleft : Tendsto (fun n ↦
      quittingPunishmentValue reward who -
        2 * source.family.error (source.selected n)) atTop
      (nhds (quittingPunishmentValue reward who)) := by
    have herror := source.family.error_tendsto_zero.comp
      source.selected_strictMono.tendsto_atTop
    simpa using tendsto_const_nhds.sub (herror.const_mul 2)
  have hright := source.tendsto_initialValue_soloReward hhorizon who
  apply le_of_tendsto_of_tendsto hleft hright
  exact Filter.Eventually.of_forall hbound

/-- Every divergent unique-exceptional-owner source reaches either the
instant-punishment branch or the well-supported absorbing branch. -/
theorem QuittingUniqueExceptionalOwnerSource.instantPunishment_or_wellSupported
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (source : QuittingUniqueExceptionalOwnerSource reward)
    (hhorizon : Tendsto
      (fun n ↦ source.family.horizon (source.selected n)) atTop atTop) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward := by
  classical
  let label : ℕ → iota := fun n ↦
    source.family.punished (source.selected n)
  obtain ⟨punished, playerSubsequence, hplayerSubsequence, hpunished⟩ :=
    exists_fixedPlayer_strictMono_subsequence label
  let firstSubsequence := source.selected ∘ playerSubsequence
  have hfirstSubsequence : StrictMono firstSubsequence :=
    source.selected_strictMono.comp hplayerSubsequence
  have hpunishedFirst : ∀ n,
      source.family.punished (firstSubsequence n) = punished := by
    intro n
    exact hpunished n
  let liveMass : ℕ → ℝ := fun n ↦
    quittingStationaryContinueMass
      (source.family.root (firstSubsequence n))
  have hliveMem : ∀ n, liveMass n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n
    exact ⟨quittingStationaryContinueMass_nonneg _,
      quittingStationaryContinueMass_le_one _⟩
  obtain ⟨liveLimit, hliveLimitMem, liveSubsequence, hliveSubsequence,
      hliveLimit⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).tendsto_subseq hliveMem
  let subsequence := firstSubsequence ∘ liveSubsequence
  have hsubsequence : StrictMono subsequence :=
    hfirstSubsequence.comp hliveSubsequence
  have hpunishedFinal : ∀ n,
      source.family.punished (subsequence n) = punished :=
    fun n ↦ hpunishedFirst (liveSubsequence n)
  have hlive : Tendsto
      (fun n ↦ quittingStationaryContinueMass
        (source.family.root (subsequence n))) atTop (nhds liveLimit) := by
    simpa [liveMass, subsequence, Function.comp_def] using hliveLimit
  have hhorizonFinal : Tendsto
      (fun n ↦ source.family.horizon (subsequence n)) atTop atTop := by
    exact hhorizon.comp
      (hplayerSubsequence.comp hliveSubsequence).tendsto_atTop
  rcases eq_or_lt_of_le hliveLimitMem.1 with hliveZero | hlivePositive
  · left
    apply quittingInstantPunishment_of_stationaryPrefix_liveMass_tendsto_zero
      source.family subsequence hsubsequence
    simpa only [hliveZero] using hlive
  · by_cases hliveBelow : liveLimit < 1
    · right
      obtain ⟨limit, hlimit⟩ :=
        exists_quittingPositiveLiveStationaryPrefixLimit_with_liveMass_eq
          source.family subsequence punished liveLimit hsubsequence
          hpunishedFinal hlivePositive hlive hhorizonFinal
      exact limit.wellSupported_of_lt_one (by rwa [hlimit])
    · have hliveOne : liveLimit = 1 := by
        exact le_antisymm hliveLimitMem.2 (not_lt.mp hliveBelow)
      have hliveOne' : Tendsto
          (fun n ↦ quittingStationaryContinueMass
            (source.family.root (subsequence n))) atTop (nhds 1) := by
        simpa only [hliveOne] using hlive
      right
      apply quittingWellSupportedAbsorbingSequenceExistence_of_singletonFloor
        reward source.owner
      intro who
      have hopponent : Tendsto
          (fun n ↦ quittingRootOpponentAbsorptionMass
            (source.family.root (subsequence n)) who) atTop (nhds 0) := by
        apply squeeze_zero
        · intro n
          exact quittingRootOpponentAbsorptionMass_nonneg _ _
        · intro n
          have hmass :=
            quittingStationaryContinueMass_le_fixedOpponentsContinueMass
              (source.family.root (subsequence n)) who
          change quittingRootOpponentAbsorptionMass
              (source.family.root (subsequence n)) who ≤
            1 - quittingStationaryContinueMass
              (source.family.root (subsequence n))
          change 1 - quittingStationaryFixedOpponentsContinueMass
              (source.family.root (subsequence n)) who ≤ _
          linarith
        · have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
            tendsto_const_nhds
          simpa using hone.sub hliveOne'
      have hquitValue : Tendsto
          (fun n ↦ quittingStationaryFixedOpponentsQuitValue reward
            (source.family.root (subsequence n)) who) atTop
          (nhds (quittingSoloReward reward who who)) := by
        apply tendsto_iff_dist_tendsto_zero.mpr
        have hbound : ∀ n,
            |quittingStationaryFixedOpponentsQuitValue reward
                  (source.family.root (subsequence n)) who -
                quittingSoloReward reward who who| ≤
              2 * quittingRewardBound reward *
                quittingRootOpponentAbsorptionMass
                  (source.family.root (subsequence n)) who := by
          intro n
          exact abs_quittingStationaryFixedOpponentsQuitValue_sub_singleton_le
            (source.family.root (subsequence n)) who
            (abs_reward_le_quittingRewardBound reward)
        have herror : Tendsto (fun n ↦
            2 * quittingRewardBound reward *
              quittingRootOpponentAbsorptionMass
                (source.family.root (subsequence n)) who) atTop (nhds 0) := by
          simpa using hopponent.const_mul (2 * quittingRewardBound reward)
        simpa [Real.dist_eq] using
          squeeze_zero (fun _ ↦ abs_nonneg _) hbound herror
      have hvalue :=
        (source.tendsto_initialValue_soloReward hhorizon who).comp
          (hplayerSubsequence.comp hliveSubsequence).tendsto_atTop
      have herror : Tendsto (fun n ↦
          2 * source.family.error (subsequence n)) atTop (nhds 0) := by
        simpa using (source.family.error_tendsto_zero.comp
          hsubsequence.tendsto_atTop).const_mul 2
      have hright : Tendsto (fun n ↦
          quittingStationaryPrefixFamilyValue source.family
              (subsequence n) 0 who +
            2 * source.family.error (subsequence n)) atTop
          (nhds (quittingSoloReward reward source.owner who)) := by
        simpa [subsequence, firstSubsequence, Function.comp_def] using
          hvalue.add herror
      apply le_of_tendsto_of_tendsto hquitValue hright
      apply Filter.Eventually.of_forall
      intro n
      exact source.fixedOpponentsQuitValue_le_initialValue
        (playerSubsequence (liveSubsequence n)) who

/-- Actual-data adapter consuming the former divergent negative-owner
residual.  Its strict negative singleton field is unnecessary. -/
theorem
    QuittingDivergentNegativeExceptionalOwnerResidual.instantPunishment_or_wellSupported
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (residual : QuittingDivergentNegativeExceptionalOwnerResidual reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      QuittingWellSupportedAbsorbingSequenceExistence reward :=
  residual.source.instantPunishment_or_wellSupported residual.horizon_tendsto

/-- Every diffuse stationarily generated source reaches one of the three
classified branches or the canonical nonzero all-Continue phantom.  The two
producer residuals are consumed by their source-faithful dispatch theorems. -/
theorem
    quittingDiffuseGenerated_stationary_or_instant_or_wellSupported_or_allContinuePhantom
    {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        QuittingWellSupportedAbsorbingSequenceExistence reward ∨
          Nonempty (QuittingLowSurvivalAllContinuePhantom reward) := by
  rcases
      stationary_or_instant_or_wellSupported_or_noSureExit_or_negativeOwner
        hgenerated with
    hstationary | hinstant | hwellSupported | hpositive | hnegative
  · exact Or.inl hstationary
  · exact Or.inr (Or.inl hinstant)
  · exact Or.inr (Or.inr (Or.inl hwellSupported))
  · obtain ⟨residual⟩ := hpositive
    rcases residual.wellSupported_or_stationary_or_allContinuePhantom with
      hwellSupported | hstationary | hphantom
    · exact Or.inr (Or.inr (Or.inl hwellSupported))
    · exact Or.inl hstationary
    · exact Or.inr (Or.inr (Or.inr hphantom))
  · obtain ⟨residual⟩ := hnegative
    rcases residual.instantPunishment_or_wellSupported with
      hinstant | hwellSupported
    · exact Or.inr (Or.inl hinstant)
    · exact Or.inr (Or.inr (Or.inl hwellSupported))

end GameTheory
