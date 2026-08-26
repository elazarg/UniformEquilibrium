/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.PositiveJointSummablePortPhantomReduction

/-!
# Source-matched positive-joint summable-port phantom

The endpoint used by the positive-joint exact-prefix route is not merely an
abstract terminal-semantic carrier point.  This module retains one strict
subsequence of the original positive-reach source, its fixed punished label,
the literal reached punishment-suffix profiles, and convergence of their full
terminal semantic pairs to that endpoint.

The source-matched summable-port package then keeps this convergence witness,
the no-sure-exit proof, exact-prefix port, phantom value, value identity, and
uniform-payoff certificate together.  This repairs provenance only; it does
not classify the surviving phantom into an AGKRS branch.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- A reached punishment endpoint together with the literal source
subsequence which produces it. -/
structure QuittingPositiveJointPrefixReachSource.SourceMatchedPunishmentEndpoint
    (source : QuittingPositiveJointPrefixReachSource reward) where
  endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward
  chosen : ℕ → ℕ
  chosen_strictMono : StrictMono chosen
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  profiles_eq_punishmentSuffix : ∀ n,
    profiles n = source.punishmentProfile (chosen n)
  punished_fixed : ∀ n,
    source.family.punished (source.selected (chosen n)) = endpoint.punished
  semantic_tendsto : Tendsto
    (fun n ↦ quittingTerminalSemanticPair reward (profiles n)) atTop
    (nhds endpoint.endpoint)

namespace QuittingPositiveJointPrefixReachSource

/-- Positive actual reach supplies a source-matched zero-debt endpoint while
retaining the exact subsequence and punishment suffixes used in the limit. -/
theorem nonempty_sourceMatchedPunishmentEndpoint
    (source : QuittingPositiveJointPrefixReachSource reward) :
    Nonempty source.SourceMatchedPunishmentEndpoint := by
  let label : ℕ → iota := fun n ↦
    source.family.punished (source.selected n)
  obtain ⟨punished, playerSubsequence, hplayerSubsequence, hpunished⟩ :=
    exists_fixedPlayer_strictMono_subsequence label
  let data : ℕ → QuittingTerminalSemanticPair iota := fun n ↦
    quittingTerminalSemanticPair reward
      (source.punishmentProfile (playerSubsequence n))
  have hdataMem : ∀ n, data n ∈ quittingTerminalSemanticCarrier reward := by
    intro n
    exact subset_closure ⟨source.punishmentProfile (playerSubsequence n), rfl⟩
  obtain ⟨endpointPair, hendpointMem, limitSubsequence, hlimitSubsequence,
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
      quittingTerminalSemanticDebt endpointPair who ≤ 0 := by
    intro who
    have hdebtLimit : Tendsto
        (fun n ↦ quittingTerminalSemanticDebt
          (data (limitSubsequence n)) who) atTop
        (nhds (quittingTerminalSemanticDebt endpointPair who)) :=
      (continuous_quittingTerminalSemanticDebt who).tendsto endpointPair |>.comp
        hendpoint
    apply le_of_tendsto_of_tendsto hdebtLimit herror
    filter_upwards [hjointPositive] with n hjoint
    have hnash := source.punishment_nash_of_joint_pos
      (chosen n) hjoint
    have hbehavior :=
      (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward _ _).mp hnash
    simpa [data, chosen,
      QuittingPositiveJointPrefixReachSource.punishmentProfile,
      Function.comp_apply] using
      quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
        reward _ _ hbehavior who
  have hcap : endpointPair.2 punished ≤
      quittingPunishmentValue reward punished := by
    have hleft : Tendsto
        (fun n ↦ (data (limitSubsequence n)).2 punished) atTop
        (nhds (endpointPair.2 punished)) :=
      ((continuous_apply punished).comp continuous_snd).tendsto
        endpointPair |>.comp hendpoint
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
  let endpoint : QuittingPositiveJointPrefixReachPunishmentEndpoint reward := {
    punished := punished
    endpoint := endpointPair
    endpoint_mem := hendpointMem
    debt_nonpos := hdebt
    punishmentCap := hcap }
  let profiles : ℕ → (quittingGame reward).BehaviorProfile := fun n ↦
    source.punishmentProfile (chosen n)
  refine ⟨{
    endpoint := endpoint
    chosen := chosen
    chosen_strictMono := hchosen
    profiles := profiles
    profiles_eq_punishmentSuffix := fun _ ↦ rfl
    punished_fixed := ?_
    semantic_tendsto := ?_ }⟩
  · intro n
    exact hpunished (limitSubsequence n)
  · change Tendsto (data ∘ limitSubsequence) atTop (nhds endpointPair)
    exact hendpoint

end QuittingPositiveJointPrefixReachSource

/-- The full source-matched all-Continue phantom package.  In particular the
endpoint used by the exact-prefix port is the limit of the displayed actual
punishment suffixes of `residual.source`. -/
structure QuittingPositiveJointSourceMatchedUniformAllContinuePhantom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) where
  residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward
  endpointLimit : residual.source.SourceMatchedPunishmentEndpoint
  noSureExit : ¬endpointLimit.endpoint.HasSureExitNashPrefix
  port : endpointLimit.endpoint.exactPrefixOrbit.SummableChargeAllContinuePort
  phantom : QuittingLowSurvivalAllContinuePhantom reward
  phantom_value_eq : phantom.value = port.limit
  uniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none phantom.value

namespace QuittingPositiveJointPrefixReachNoSureExitResidual

/-- The positive-joint residual reaches S.3, S.1, or a phantom retaining the
literal source subsequence which produced the endpoint used by its port. -/
theorem wellSupported_or_stationary_or_sourceMatchedUniformAllContinuePhantom
    (residual : QuittingPositiveJointPrefixReachNoSureExitResidual reward) :
    QuittingWellSupportedAbsorbingSequenceExistence reward ∨
      QuittingStationaryεEquilibriumExistence reward ∨
        Nonempty
          (QuittingPositiveJointSourceMatchedUniformAllContinuePhantom
            reward) := by
  obtain ⟨endpointLimit⟩ :=
    residual.source.nonempty_sourceMatchedPunishmentEndpoint
  let endpoint := endpointLimit.endpoint
  rcases endpoint.wellSupported_or_summableExactPrefixPort with
    hwellSupported | hport
  · exact Or.inl hwellSupported
  · obtain ⟨port⟩ := hport
    letI : Nonempty iota := ⟨endpoint.punished⟩
    rcases port.stationaryExistence_or_uniformAllContinuePhantom_of_endpoint
        endpoint with hstationary | ⟨phantom, hvalue, huniform⟩
    · exact Or.inr (Or.inl hstationary)
    · exact Or.inr (Or.inr ⟨{
        residual := residual
        endpointLimit := endpointLimit
        noSureExit := residual.noSureExitNashPrefix endpoint
        port := port
        phantom := phantom
        phantom_value_eq := hvalue
        uniformEquilibriumPayoff := huniform }⟩)

end QuittingPositiveJointPrefixReachNoSureExitResidual

end GameTheory
