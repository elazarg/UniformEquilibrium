/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.DiffuseStationaryPrefixSourceAttachments
import UniformEquilibrium.Quitting.Classification.Existence.PositiveAbsorptionStationarySplice
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

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

/-- Every semantic-carrier envelope coordinate is bounded below by the
behavioral punishment value.  This is the closure extension of the defining
min-max lower bound on literal profiles. -/
theorem quittingPunishmentValue_le_terminalSemanticEnvelope_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {pair : QuittingTerminalSemanticPair ι}
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) (who : ι) :
    quittingPunishmentValue reward who ≤ pair.2 who := by
  have hclosed : IsClosed {candidate : QuittingTerminalSemanticPair ι |
      quittingPunishmentValue reward who ≤ candidate.2 who} :=
    isClosed_le continuous_const
      ((continuous_apply who).comp continuous_snd)
  apply (closure_minimal ?_ hclosed) hpair
  rintro candidate ⟨profile, rfl⟩
  change quittingPunishmentValue reward who ≤
    quittingContinuationBestResponseValue reward profile who
  rw [quittingContinuationBestResponseValue_eq_bestReplyValue]
  exact quittingPunishmentValue_le reward who profile

/-- The reached endpoint has exactly zero best-response debt in every
coordinate.  Nonpositivity comes from the reached suffixes' vanishing Nash
error; nonnegativity is intrinsic to the literal semantic carrier. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.debt_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (who : ι) :
    quittingTerminalSemanticDebt endpoint.endpoint who = 0 := by
  exact le_antisymm (endpoint.debt_nonpos who)
    (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward endpoint.endpoint_mem who)

/-- Hence the reached punishment endpoint is diagonal: its prescribed payoff
and all-behavior best-response envelope agree coordinatewise. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.payoff_eq_envelope
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (who : ι) :
    endpoint.endpoint.1 who = endpoint.endpoint.2 who := by
  have hzero := endpoint.debt_eq_zero who
  unfold quittingTerminalSemanticDebt at hzero
  linarith

/-- The fixed punished coordinate does not merely satisfy an upper cap: the
semantic endpoint's envelope attains that player's behavioral punishment
value exactly. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.envelope_eq_punishmentValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    endpoint.endpoint.2 endpoint.punished =
      quittingPunishmentValue reward endpoint.punished := by
  exact le_antisymm endpoint.punishmentCap
    (quittingPunishmentValue_le_terminalSemanticEnvelope_of_mem_carrier
      reward endpoint.endpoint_mem endpoint.punished)

/-- The prescribed coordinate of the reached endpoint therefore also equals
the fixed player's behavioral punishment value. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.payoff_eq_punishmentValue
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    endpoint.endpoint.1 endpoint.punished =
      quittingPunishmentValue reward endpoint.punished := by
  rw [endpoint.payoff_eq_envelope endpoint.punished,
    endpoint.envelope_eq_punishmentValue]

/-- Finite-dimensional attachment condition for the reached endpoint: some
player surely quits in an exact one-stage Nash prefix over the endpoint
payoff.  Unlike the endpoint itself, the root is executable. -/
def QuittingPositiveJointPrefixReachPunishmentEndpoint.HasSureExitNashPrefix
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward) :
    Prop :=
  ∃ (quitter : ι) (root : ι → PMF Bool),
    root quitter = PMF.pure true ∧
      IsεQuittingRootNash reward endpoint.endpoint.1 0 root

/-- A sure-exit Nash prefix over the reached diagonal endpoint closes the
positive-joint-reach source into branch `S.2`.  The proof does not execute a
formal closure point: it approximates the endpoint by actual punishment
profiles, prefixes the fixed root, and uses continuity of semantic debt to
obtain executable terminal Nash profiles at every positive tolerance. -/
theorem QuittingPositiveJointPrefixReachPunishmentEndpoint.instantPunishment
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward)
    (hprefix : endpoint.HasSureExitNashPrefix) :
    QuittingInstantPunishmentεEquilibriumExistence reward := by
  obtain ⟨quitter, root, hquit, hnash⟩ := hprefix
  letI : Nonempty ι := ⟨quitter⟩
  have hdiagonal : endpoint.endpoint =
      (endpoint.endpoint.1, endpoint.endpoint.1) := by
    apply Prod.ext
    · rfl
    · funext who
      exact (endpoint.payoff_eq_envelope who).symm
  have hprefixed : quittingTerminalSemanticPrefix reward root
      endpoint.endpoint =
        (quittingRootSuccessorPayoff reward endpoint.endpoint.1 root,
          quittingRootSuccessorPayoff reward endpoint.endpoint.1 root) := by
    rw [hdiagonal]
    exact quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
      reward endpoint.endpoint.1 root hnash
  have hprefixedExploitability :
      quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPrefix reward root endpoint.endpoint) = 0 := by
    rw [hprefixed]
    unfold quittingTerminalSemanticExploitability
      QuittingBoundaryHolonomy.finitePlayerMax
    simp [quittingTerminalSemanticDebt]
  obtain ⟨tails, htails⟩ := endpoint.exists_realizers
  have hspliceSemantic : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root (tails n)))
      atTop
      (nhds (quittingTerminalSemanticPrefix reward root endpoint.endpoint)) := by
    have hprefixedTendsto :=
      (continuous_quittingTerminalSemanticPrefix reward root).tendsto
        endpoint.endpoint |>.comp htails
    simpa [Function.comp_def,
      quittingTerminalSemanticPair_rootThenContinuation] using
      hprefixedTendsto
  have hexploitability : Tendsto
      (fun n ↦ quittingTerminalSemanticExploitability
        (quittingTerminalSemanticPair reward
          (quittingRootThenContinuationProfile reward root (tails n))))
      atTop (nhds 0) := by
    have hcontinuous :=
      continuous_quittingTerminalSemanticExploitability.continuousAt.tendsto.comp
        hspliceSemantic
    rwa [hprefixedExploitability] at hcontinuous
  apply quittingInstantPunishmentεEquilibriumExistence_of_sureQuitter
  intro ε hε
  obtain ⟨n, hn⟩ :=
    (hexploitability.eventually (Iio_mem_nhds hε)).exists
  refine ⟨quitter, root, tails n, hquit, ?_⟩
  intro who deviation
  have hbest := quittingTerminalPayoff_update_le_continuationBestResponseValue
    reward (quittingRootThenContinuationProfile reward root (tails n))
      who deviation
  have hdebtLe : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingRootThenContinuationProfile reward root (tails n))) who ≤ ε := by
    apply le_trans (le_max_right 0 _)
    exact (QuittingBoundaryHolonomy.le_finitePlayerMax _ who).trans hn.le
  change quittingContinuationBestResponseValue reward
      (quittingRootThenContinuationProfile reward root (tails n)) who -
      quittingTerminalPayoff reward
        (quittingRootThenContinuationProfile reward root (tails n)) who ≤ ε
    at hdebtLe
  linarith

/-- Exact unresolved positive-reach boundary after the executable sure-exit
consumer is applied.  It retains the actual source and records that no
zero-debt reached endpoint admits any exact sure-exit Nash prefix. -/
structure QuittingPositiveJointPrefixReachNoSureExitResidual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  source : QuittingPositiveJointPrefixReachSource reward
  noSureExitNashPrefix :
    ∀ endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
      ¬endpoint.HasSureExitNashPrefix

/-- A positive-joint-reach source either closes branch `S.2`, or every
zero-debt endpoint at the exact punishment floor lies on the no-sure-exit
one-stage Nash face. -/
theorem QuittingPositiveJointPrefixReachSource.instantPunishment_or_noSureExitResidual
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingPositiveJointPrefixReachSource reward) :
    QuittingInstantPunishmentεEquilibriumExistence reward ∨
      Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual reward) := by
  by_cases hprefix : ∃ endpoint :
      QuittingPositiveJointPrefixReachPunishmentEndpoint reward,
      endpoint.HasSureExitNashPrefix
  · left
    obtain ⟨endpoint, hendpoint⟩ := hprefix
    exact endpoint.instantPunishment hendpoint
  · right
    refine ⟨⟨source, ?_⟩⟩
    intro endpoint hendpoint
    exact hprefix ⟨endpoint, hendpoint⟩

/-- Source-faithful diffuse boundary after consuming the sure-exit endpoint
subcase.  Positive joint reach is no longer a monolithic attachment: it
either gives branch `S.2`, or retains an actual source all of whose diagonal
punishment-floor endpoints fail the finite-dimensional sure-exit Nash test.
The unique-exceptional-owner source remains unchanged. -/
theorem stationary_or_instantPunishment_or_positiveJointNoSureExitResidual_or_uniqueOwner
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hgenerated : QuittingDiffuseStationarilyGeneratedApproximateEquilibria
      reward) :
    QuittingStationaryεEquilibriumExistence reward ∨
      QuittingInstantPunishmentεEquilibriumExistence reward ∨
        Nonempty (QuittingPositiveJointPrefixReachNoSureExitResidual reward) ∨
          Nonempty (QuittingUniqueExceptionalOwnerSource reward) := by
  rcases
      stationary_or_positiveJointPrefixReachSource_or_uniqueExceptionalOwnerSource
        hgenerated with hstationary | hpositive | hexceptional
  · exact Or.inl hstationary
  · obtain ⟨source⟩ := hpositive
    rcases source.instantPunishment_or_noSureExitResidual with
      hinstant | hresidual
    · exact Or.inr (Or.inl hinstant)
    · exact Or.inr (Or.inr (Or.inl hresidual))
  · exact Or.inr (Or.inr (Or.inr hexceptional))

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
