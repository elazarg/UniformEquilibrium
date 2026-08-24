/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DiffuseStationaryPrefixSourceAttachments
import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding

/-!
# The reached punishment endpoint of a positive stationary prefix

If a finite stationary prefix reaches its actual punishment suffix with
probability bounded away from zero, global Nash transfers to that suffix after
division by the reach probability.  Consequently a positive-joint-reach
source supplies arbitrarily accurate unrestricted-behavior Nash punishment
tails.  The full prescribed payoff also has an exact absorption-law
decomposition into absorption inside the finite prefix plus the reached
punishment payoff.

This is the source-native attachment that the positive-reach seam genuinely
provides.  It does not make the punishment tails stationary or sequentially
perfect, and therefore does not by itself prove AGKRS branch S.1 or S.3.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual punishment profile carried by one row of a positive-reach
source. -/
def QuittingPositiveJointPrefixReachSource.punishmentProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (source.family.punishment (source.selected n)) 0

/-- The actual stationary-prefix-then-punishment profile at one selected
source row. -/
def QuittingPositiveJointPrefixReachSource.fullProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootSequenceProfile reward
    (quittingStationaryPrefixFamilyPlan source.family (source.selected n)) 0

/-- The terminal payoff collected by absorption inside the finite repeated
prefix, with all-Continue used after the prefix. -/
def QuittingPositiveJointPrefixReachSource.prefixAbsorptionPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    Payoff ι := fun who ↦
  quittingRootSequenceTerminalValue reward
    (quittingTruncatedRoots
      (fun _ ↦ source.family.root (source.selected n))
      (source.family.horizon (source.selected n) + 1)) who 0

/-- The conditional Nash error of the reached punishment suffix. -/
def QuittingPositiveJointPrefixReachSource.punishmentNashError
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) : ℝ :=
  2 * source.family.error (source.selected n) /
    source.family.prefixJointSurvival (source.selected n)

/-- The selected full plan reaches its punishment suffix with exactly the
source's whole-prefix joint survival. -/
theorem QuittingPositiveJointPrefixReachSource.fullPlan_survival_eq
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    quittingJointSurvivalWeight
        (quittingStationaryPrefixFamilyPlan source.family (source.selected n))
        0 (source.family.horizon (source.selected n) + 1) =
      source.family.prefixJointSurvival (source.selected n) := by
  rw [quittingStationaryPrefixFamilyPlan,
    quittingStationaryPrefixThenRoots_eq_phaseSwitch,
    quittingJointSurvivalWeight_quittingPhaseSwitchRoots_plan]
  rfl

/-- Restarting the selected full plan at its switch time is literally its
actual punishment root sequence. -/
theorem QuittingPositiveJointPrefixReachSource.fullPlan_shift_eq_punishment
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    (fun offset ↦
      quittingStationaryPrefixFamilyPlan source.family (source.selected n)
        (source.family.horizon (source.selected n) + 1 + offset)) =
      source.family.punishment (source.selected n) := by
  funext offset
  unfold quittingStationaryPrefixFamilyPlan
  exact quittingStationaryPrefixThenRoots_add
    (source.family.root (source.selected n))
    (source.family.horizon (source.selected n)) offset
    (source.family.punishment (source.selected n))

/-- Whenever the selected prefix has positive reach, its actual punishment
suffix is Nash against every time-dependent hazard at the divided error. -/
theorem QuittingPositiveJointPrefixReachSource.punishment_nash_of_joint_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ)
    (hjoint : 0 < source.family.prefixJointSurvival (source.selected n)) :
    IsεQuittingRootSequenceNash reward (source.punishmentNashError n)
      (source.family.punishment (source.selected n)) := by
  let roots :=
    quittingStationaryPrefixFamilyPlan source.family (source.selected n)
  let switch := source.family.horizon (source.selected n) + 1
  have hnash := isεQuittingRootSequenceNash_shift_of_survival_ge
    reward roots (mul_nonneg (by norm_num)
      (source.family.error_pos (source.selected n)).le)
    hjoint (source.family.nash (source.selected n)) switch
    (by rw [source.fullPlan_survival_eq n])
  rw [show (fun offset ↦ roots (switch + offset)) =
      source.family.punishment (source.selected n) by
    exact source.fullPlan_shift_eq_punishment n] at hnash
  exact hnash

/-- Positive limiting reach makes the divided punishment-tail Nash error tend
to zero along the actual source. -/
theorem QuittingPositiveJointPrefixReachSource.punishmentNashError_tendsto_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) :
    Tendsto source.punishmentNashError atTop (nhds 0) := by
  have herror : Tendsto
      (fun n ↦ 2 * source.family.error (source.selected n)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (source.family.error_tendsto_zero.comp
        source.selected_strictMono.tendsto_atTop)
  change Tendsto
    ((fun n ↦ 2 * source.family.error (source.selected n)) /
      fun n ↦ source.family.prefixJointSurvival (source.selected n))
      atTop (nhds 0)
  simpa using herror.div source.joint_tendsto
    (ne_of_gt source.jointLimit_pos)

/-- Eventually every selected prefix has positive actual reach. -/
theorem QuittingPositiveJointPrefixReachSource.eventually_joint_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) :
    ∀ᶠ n in atTop,
      0 < source.family.prefixJointSurvival (source.selected n) :=
  (tendsto_order.1 source.joint_tendsto).1 0 source.jointLimit_pos

/-- The reached punishment suffixes alone witness unrestricted approximate
equilibrium existence at every positive error. -/
theorem QuittingPositiveJointPrefixReachSource.punishment_approximateEquilibriumExistence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) :
    QuittingApproximateEquilibriumExistence reward := by
  intro ε hε
  have herrorSmall : ∀ᶠ n in atTop, source.punishmentNashError n < ε :=
    (tendsto_order.1 source.punishmentNashError_tendsto_zero).2 ε hε
  obtain ⟨n, hjoint, hsmall⟩ :=
    (source.eventually_joint_pos.and herrorSmall).exists
  refine ⟨source.family.punishment (source.selected n), ?_⟩
  intro who hazard
  have hbound := source.punishment_nash_of_joint_pos n hjoint who hazard
  linarith

/-- A semantic limit of the actually reached punishment tails.  It is a
zero-debt terminal endpoint for every player and retains the exact min-max cap
for one fixed punished player. -/
structure QuittingPositiveJointPrefixReachPunishmentEndpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  punished : ι
  endpoint : QuittingTerminalSemanticPair ι
  endpoint_mem : endpoint ∈ quittingTerminalSemanticCarrier reward
  debt_nonpos : ∀ who, quittingTerminalSemanticDebt endpoint who ≤ 0
  punishmentCap : endpoint.2 punished ≤
    quittingPunishmentValue reward punished

/-- Positive actual reach compactifies the punishment suffixes to a semantic
zero-debt endpoint while preserving one actual punishment cap. -/
theorem QuittingPositiveJointPrefixReachSource.exists_punishmentEndpoint
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) :
    Nonempty (QuittingPositiveJointPrefixReachPunishmentEndpoint reward) := by
  let label : ℕ → ι := fun n ↦
    source.family.punished (source.selected n)
  obtain ⟨punished, playerSubsequence, hplayerSubsequence, hpunished⟩ :=
    exists_fixedPlayer_strictMono_subsequence label
  let data : ℕ → QuittingTerminalSemanticPair ι := fun n ↦
    quittingTerminalSemanticPair reward
      (source.punishmentProfile (playerSubsequence n))
  have hdataMem : ∀ n, data n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact subset_closure ⟨source.punishmentProfile (playerSubsequence n), rfl⟩
  obtain ⟨endpoint, hendpointMem, limitSubsequence, hlimitSubsequence,
      hendpoint⟩ :=
    (quittingTerminalSemanticCarrier_isCompact reward).tendsto_subseq hdataMem
  let chosen : ℕ → ℕ := playerSubsequence ∘ limitSubsequence
  have hchosen : StrictMono chosen :=
    hplayerSubsequence.comp hlimitSubsequence
  have hjointPositive : ∀ᶠ n in atTop,
      0 < source.family.prefixJointSurvival
        (source.selected (chosen n)) :=
    (tendsto_order.1
      (source.joint_tendsto.comp hchosen.tendsto_atTop)).1 0
        source.jointLimit_pos
  have herror : Tendsto
      (fun n ↦ source.punishmentNashError (chosen n)) atTop (nhds 0) :=
    source.punishmentNashError_tendsto_zero.comp hchosen.tendsto_atTop
  have hdebt : ∀ who,
      quittingTerminalSemanticDebt endpoint who ≤ 0 := by
    intro who
    have hdebtLimit : Tendsto
        (fun n ↦ quittingTerminalSemanticDebt
          (data (limitSubsequence n)) who) atTop
        (nhds (quittingTerminalSemanticDebt endpoint who)) :=
      (continuous_quittingTerminalSemanticDebt who).tendsto endpoint |>.comp
        hendpoint
    apply le_of_tendsto_of_tendsto hdebtLimit herror
    filter_upwards [hjointPositive] with n hjoint
    have hnash := source.punishment_nash_of_joint_pos (chosen n) hjoint
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward _ _).mp hnash
    simpa [data, chosen, QuittingPositiveJointPrefixReachSource.punishmentProfile,
      Function.comp_apply] using
      quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
        reward _ _ hbehavior who
  have hcap : endpoint.2 punished ≤
      quittingPunishmentValue reward punished := by
    have hleft : Tendsto
        (fun n ↦ (data (limitSubsequence n)).2 punished) atTop
        (nhds (endpoint.2 punished)) :=
      ((continuous_apply punished).comp continuous_snd).tendsto endpoint |>.comp
        hendpoint
    have hsourceError : Tendsto
        (fun n ↦ quittingPunishmentValue reward punished +
          source.family.error (source.selected (chosen n))) atTop
        (nhds (quittingPunishmentValue reward punished)) := by
      simpa using tendsto_const_nhds.add
        (source.family.error_tendsto_zero.comp
          (source.selected_strictMono.comp hchosen).tendsto_atTop)
    apply le_of_tendsto_of_tendsto hleft hsourceError
    apply Filter.Eventually.of_forall
    intro n
    have hpunishedAt : source.family.punished
        (source.selected (chosen n)) = punished := by
      exact hpunished (limitSubsequence n)
    change quittingContinuationBestResponseValue reward
        (source.punishmentProfile (chosen n)) punished ≤ _
    rw [quittingContinuationBestResponseValue_eq_bestReplyValue]
    simpa [QuittingPositiveJointPrefixReachSource.punishmentProfile,
      hpunishedAt] using
      (isQuittingRootSequencePunishmentWithin_iff_bestReplyValue reward
        (source.family.punished (source.selected (chosen n)))
        (source.family.error (source.selected (chosen n)))
        (source.family.punishment (source.selected (chosen n)))).mp
          (source.family.punishmentWithin (source.selected (chosen n)))
  exact ⟨⟨punished, endpoint, hendpointMem, hdebt, hcap⟩⟩

/-- The reached zero-debt endpoint is the limit of actual behavioral terminal
semantic pairs, rather than a formal payoff/envelope annotation. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.exists_realizers
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      Tendsto (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
        atTop (nhds endpoint.endpoint) :=
  exists_terminalProfile_sequence_tendsto_semanticPair reward
    endpoint.endpoint endpoint.endpoint_mem

/-- Exact source-level absorption law: the full prescribed terminal payoff is
the payoff absorbed inside the repeated prefix plus the reached punishment
payoff weighted by whole-prefix survival. -/
theorem QuittingPositiveJointPrefixReachSource.fullPayoff_eq_prefix_add_reach_mul_tail
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) (n : ℕ) :
    quittingTerminalPayoff reward (source.fullProfile n) =
      source.prefixAbsorptionPayoff n +
        source.family.prefixJointSurvival (source.selected n) •
          quittingTerminalPayoff reward (source.punishmentProfile n) := by
  funext who
  change quittingRootSequenceTerminalValue reward
      (quittingStationaryPrefixFamilyPlan source.family (source.selected n))
      who 0 = _
  rw [quittingStationaryPrefixFamilyPlan,
    quittingStationaryPrefixThenRoots_eq_phaseSwitch,
    quittingRootSequenceTerminalValue_quittingPhaseSwitchRoots]
  change _ = source.prefixAbsorptionPayoff n who +
    source.family.prefixJointSurvival (source.selected n) *
      quittingRootSequenceTerminalValue reward
        (source.family.punishment (source.selected n)) who 0
  rw [QuittingPositiveJointPrefixReachSource.prefixAbsorptionPayoff]
  congr 1

end GameTheory
