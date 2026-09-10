/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.Certificate
import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

/-!
# Naturality of player reindexing

Player relabeling is functorial on finite quitting-game reward tables.  This
module records the identity, composition, and inverse laws and upgrades the
one-way equilibrium transport to an exact statement for the transported
payoff vector. Consequently existence and nonexistence of a uniform-equilibrium
payoff are invariant under relabeling.

Behavioral pushforward and pullback are inverse. Complete stopping laws,
terminal payoffs, and unrestricted behavioral deviation caps commute with
these maps; the cap identities transport every unilateral strategy.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι κ ν : Type}

/-- Reindexing a reward table along the identity equivalence changes nothing. -/
@[simp] theorem quittingRewardReindex_refl
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingRewardReindex (Equiv.refl ι) reward = reward := by
  funext S who
  change reward ((quittingCoalitionEquiv (Equiv.refl ι)).symm S) who =
    reward S who
  congr 2
  apply Subtype.ext
  ext i
  simp [quittingCoalitionEquiv]

/-- Successive player relabelings compose in the same order as the
equivalences. -/
theorem quittingRewardReindex_trans (e : ι ≃ κ) (f : κ ≃ ν)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingRewardReindex (e.trans f) reward =
      quittingRewardReindex f (quittingRewardReindex e reward) := by
  funext S who
  change reward ((quittingCoalitionEquiv (e.trans f)).symm S)
      ((e.trans f).symm who) =
    reward ((quittingCoalitionEquiv e).symm
      ((quittingCoalitionEquiv f).symm S)) (e.symm (f.symm who))
  have hcoal : ((quittingCoalitionEquiv (e.trans f)).symm S) =
      (quittingCoalitionEquiv e).symm
        ((quittingCoalitionEquiv f).symm S) := by
    apply Subtype.ext
    change S.1.map (e.trans f).symm.toEmbedding =
      (S.1.map f.symm.toEmbedding).map e.symm.toEmbedding
    rw [Finset.map_map]
    rfl
  rw [hcoal]
  rfl

/-- Relabeling and then relabeling back recovers the original reward table. -/
@[simp] theorem quittingRewardReindex_symm_apply
    (e : ι ≃ κ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingRewardReindex e.symm (quittingRewardReindex e reward) = reward := by
  rw [← quittingRewardReindex_trans]
  simp

/-- The reverse inverse law for reward-table relabeling. -/
@[simp] theorem quittingRewardReindex_apply_symm
    (e : ι ≃ κ) (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    quittingRewardReindex e (quittingRewardReindex e.symm reward) = reward := by
  rw [← quittingRewardReindex_trans]
  simp

section Security

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A one-sided security certificate transports covariantly with the secured
player under an equivalence of finite quitting-game player types. -/
theorem isOneSidedGuaranteeCertificateAt_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (value δ : ℝ)
    (hsecurity : (quittingGame reward).IsOneSidedGuaranteeCertificateAt
      none who value δ) :
    IsOneSidedGuaranteeCertificateAt
      (quittingGame (quittingRewardReindex e reward)) none (e who) value δ := by
  obtain ⟨σwho, T₀, hT₀, hsecurity⟩ := hsecurity
  let σwho' :
      (quittingGame (quittingRewardReindex e reward)).BehaviorStrategy (e who) :=
    fun t h ↦ σwho t ((quittingHistEquiv e reward t).symm h)
  refine ⟨σwho', T₀, hT₀, fun opp T hT ↦ ?_⟩
  have hpull :
      quittingProfilePullback e reward (Function.update opp (e who) σwho') =
        Function.update (quittingProfilePullback e reward opp) who σwho := by
    rw [quittingProfilePullback_update]
    refine congrArg
      (Function.update (quittingProfilePullback e reward opp) who) ?_
    funext t h
    simp only [σwho', Equiv.symm_apply_apply]
  have hpayoff := finiteAveragePayoff_quittingProfilePullback e reward
    (Function.update opp (e who) σwho') T who
  rw [hpull] at hpayoff
  rw [hpayoff]
  exact hsecurity (quittingProfilePullback e reward opp) T hT

/-- Vanishing-error one-sided security is invariant under player reindexing. -/
theorem isOneSidedGuaranteeCertificate_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (value : ℝ)
    (hsecurity : (quittingGame reward).IsOneSidedGuaranteeCertificate
      none who value) :
    IsOneSidedGuaranteeCertificate
      (quittingGame (quittingRewardReindex e reward)) none (e who) value := by
  intro δ hδ
  exact isOneSidedGuaranteeCertificateAt_reindex e reward who value δ
    (hsecurity δ hδ)

end Security

section Equilibrium

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Pullback preserves the specified uniform-equilibrium payoff vector, not
only the existence of some payoff. -/
theorem isUniformEquilibriumPayoff_of_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (payoff : Payoff κ)
    (hpayoff :
      (quittingGame (quittingRewardReindex e reward)).IsUniformEquilibriumPayoff
        none payoff) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (fun who ↦ payoff (e who)) := by
  intro ε hε
  obtain ⟨σ', T₀, hσ'⟩ := hpayoff ε hε
  refine ⟨quittingProfilePullback e reward σ', T₀, fun T hT ↦ ?_⟩
  obtain ⟨hNash, hclose⟩ := hσ' T hT
  constructor
  · intro who dev
    have hdev := hNash (e who)
      (fun t h' ↦ dev t ((quittingHistEquiv e reward t).symm h'))
    have hdevEq := finiteAveragePayoff_quittingProfilePullback e reward
      (Function.update σ' (e who)
        (fun t h' ↦ dev t ((quittingHistEquiv e reward t).symm h'))) T who
    have hpullEq : quittingProfilePullback e reward
        (Function.update σ' (e who)
          (fun t h' ↦ dev t ((quittingHistEquiv e reward t).symm h'))) =
        Function.update (quittingProfilePullback e reward σ') who dev := by
      rw [quittingProfilePullback_update]
      refine congrArg
        (Function.update (quittingProfilePullback e reward σ') who) ?_
      funext t h
      rw [Equiv.symm_apply_apply]
    rw [hpullEq] at hdevEq
    have hon := finiteAveragePayoff_quittingProfilePullback e reward σ' T who
    rw [hon, hdevEq] at hdev
    exact hdev
  · intro who
    have hon := finiteAveragePayoff_quittingProfilePullback e reward σ' T who
    rw [← hon]
    exact hclose (e who)

/-- A specified payoff is a uniform-equilibrium payoff exactly when its
coordinatewise relabeling is one for the reindexed reward table. -/
theorem isUniformEquilibriumPayoff_reindex_iff (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (payoff : Payoff ι) :
    (quittingGame (quittingRewardReindex e reward)).IsUniformEquilibriumPayoff
        none (fun who ↦ payoff (e.symm who)) ↔
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · intro h
    simpa using isUniformEquilibriumPayoff_of_reindex e reward _ h
  · intro h
    have hdouble :
        (quittingGame
          (quittingRewardReindex e.symm
            (quittingRewardReindex e reward))).IsUniformEquilibriumPayoff none
              payoff := by
      rw [quittingRewardReindex_symm_apply]
      exact h
    have h' := isUniformEquilibriumPayoff_of_reindex e.symm
      (quittingRewardReindex e reward) payoff hdouble
    simpa using h'

/-- Existence of a uniform-equilibrium payoff is invariant under player
relabeling. -/
theorem exists_uniformEquilibriumPayoff_reindex_iff (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff κ,
        (quittingGame (quittingRewardReindex e reward)).IsUniformEquilibriumPayoff
          none payoff) ↔
      ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  constructor
  · exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex e reward
  · rintro ⟨payoff, hpayoff⟩
    exact ⟨fun who ↦ payoff (e.symm who),
      (isUniformEquilibriumPayoff_reindex_iff e reward payoff).2 hpayoff⟩

/-- Nonexistence of a uniform-equilibrium payoff is invariant under player
relabeling. -/
theorem not_exists_uniformEquilibriumPayoff_reindex_iff (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (¬ ∃ payoff : Payoff κ,
        (quittingGame (quittingRewardReindex e reward)).IsUniformEquilibriumPayoff
          none payoff) ↔
      ¬ ∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact not_congr (exists_uniformEquilibriumPayoff_reindex_iff e reward)

end Equilibrium

section Terminal

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Push a behavioral profile forward along a player equivalence. -/
def quittingProfilePushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    (quittingGame (quittingRewardReindex e reward)).BehaviorProfile :=
  fun who time history =>
    profile (e.symm who) time ((quittingHistEquiv e reward time).symm history)

omit [DecidableEq ι] [DecidableEq κ] in
/-- The player reindexing sends the unique live history to the unique live history. -/
theorem quittingHistEquiv_liveHist (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (time : ℕ) :
    quittingHistEquiv e reward time (quittingLiveHist reward time) =
      quittingLiveHist (quittingRewardReindex e reward) time := by
  apply Prod.ext
  · funext stage
    apply Prod.ext
    · rfl
    · funext who
      rfl
  · rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- Complete stopping laws commute with behavioral pullback. -/
theorem quittingBehaviorStoppingLaw_profilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) (who : ι) :
    quittingBehaviorStoppingLaw reward
        (quittingProfilePullback e reward profile who) =
      quittingBehaviorStoppingLaw (quittingRewardReindex e reward)
        (profile (e who)) := by
  unfold quittingBehaviorStoppingLaw quittingBehaviorLiveHazard
  congr 1

omit [DecidableEq ι] [DecidableEq κ] in
/-- Terminal payoffs commute with behavioral pullback. -/
theorem quittingTerminalPayoff_profilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff (quittingRewardReindex e reward) profile (e who) =
      quittingTerminalPayoff reward
        (quittingProfilePullback e reward profile) who := by
  have hleft := tendsto_finiteAveragePayoff_quittingGame
    (quittingRewardReindex e reward) profile (e who)
  have hright := tendsto_finiteAveragePayoff_quittingGame reward
    (quittingProfilePullback e reward profile) who
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun horizon =>
    (finiteAveragePayoff_quittingProfilePullback
      e reward profile horizon who).symm)

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem quittingProfilePullback_pushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfilePullback e reward
        (quittingProfilePushforward e reward profile) = profile := by
  funext who time history
  simp only [quittingProfilePullback, quittingProfilePushforward,
    Equiv.symm_apply_apply]
  rw [e.symm_apply_apply]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Complete stopping laws commute with behavioral pushforward. -/
theorem quittingBehaviorStoppingLaw_profilePushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorStoppingLaw (quittingRewardReindex e reward)
        (quittingProfilePushforward e reward profile (e who)) =
      quittingBehaviorStoppingLaw reward (profile who) := by
  symm
  simpa only [quittingProfilePullback_pushforward] using
    quittingBehaviorStoppingLaw_profilePullback e reward
      (quittingProfilePushforward e reward profile) who

omit [DecidableEq ι] [DecidableEq κ] in
/-- Terminal payoffs commute with behavioral pushforward. -/
theorem quittingTerminalPayoff_profilePushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff (quittingRewardReindex e reward)
        (quittingProfilePushforward e reward profile) (e who) =
      quittingTerminalPayoff reward profile who := by
  rw [quittingTerminalPayoff_profilePullback,
    quittingProfilePullback_pushforward]

/-- Push a unilateral behavioral strategy forward along a player equivalence. -/
def quittingStrategyPushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    (quittingGame (quittingRewardReindex e reward)).BehaviorStrategy (e who) :=
  fun time history => deviation time ((quittingHistEquiv e reward time).symm history)

/-- Pushing forward a unilateral update updates the transported player. -/
theorem quittingProfilePushforward_update (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingProfilePushforward e reward (Function.update profile who deviation) =
      Function.update (quittingProfilePushforward e reward profile) (e who)
        (quittingStrategyPushforward e reward who deviation) := by
  funext player time history
  by_cases hplayer : player = e who
  · subst player
    change Function.update profile who deviation (e.symm (e who)) time _ = _
    rw [e.symm_apply_apply, Function.update_self]
    simp [quittingStrategyPushforward]
  · have hpreimage : e.symm player ≠ who := by
      intro heq
      apply hplayer
      simpa using congrArg e heq
    simp [quittingProfilePushforward,
      Function.update_of_ne hplayer, Function.update_of_ne hpreimage]

/-- The unrestricted behavioral deviation cap commutes with pushforward. -/
theorem quittingBehaviorDeviationPayoffCap_profilePushforward (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingBehaviorDeviationPayoffCap (quittingRewardReindex e reward)
        (quittingProfilePushforward e reward profile) (e who) =
      quittingBehaviorDeviationPayoffCap reward profile who := by
  unfold quittingBehaviorDeviationPayoffCap
  congr 1
  ext value
  constructor
  · rintro ⟨deviation, rfl⟩
    let pulled : (quittingGame reward).BehaviorStrategy who :=
      fun time history => deviation time (quittingHistEquiv e reward time history)
    refine ⟨pulled, ?_⟩
    have hupdate := quittingProfilePullback_update e reward
      (quittingProfilePushforward e reward profile) who deviation
    rw [quittingProfilePullback_pushforward] at hupdate
    change quittingTerminalPayoff reward (Function.update profile who pulled) who =
      quittingTerminalPayoff (quittingRewardReindex e reward)
        (Function.update (quittingProfilePushforward e reward profile) (e who)
          deviation) (e who)
    rw [quittingTerminalPayoff_profilePullback, hupdate]
  · rintro ⟨deviation, rfl⟩
    refine ⟨quittingStrategyPushforward e reward who deviation, ?_⟩
    change quittingTerminalPayoff (quittingRewardReindex e reward)
        (Function.update (quittingProfilePushforward e reward profile) (e who)
          (quittingStrategyPushforward e reward who deviation)) (e who) = _
    rw [← quittingProfilePushforward_update,
      quittingTerminalPayoff_profilePushforward]

/-- Regard a behavioral profile as a profile for an equal reward table. -/
def quittingProfileOfRewardEq
    {first second : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : first = second)
    (profile : (quittingGame second).BehaviorProfile) :
    (quittingGame first).BehaviorProfile := by
  rw [hreward]
  exact profile

omit [DecidableEq ι] in
@[simp] theorem quittingBehaviorStoppingLaw_profileOfRewardEq
    {first second : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : first = second)
    (profile : (quittingGame second).BehaviorProfile) (who : ι) :
    quittingBehaviorStoppingLaw first
        (quittingProfileOfRewardEq hreward profile who) =
      quittingBehaviorStoppingLaw second (profile who) := by
  subst second
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingTerminalPayoff_profileOfRewardEq
    {first second : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : first = second)
    (profile : (quittingGame second).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff first
        (quittingProfileOfRewardEq hreward profile) who =
      quittingTerminalPayoff second profile who := by
  subst second
  rfl

@[simp] theorem quittingBehaviorDeviationPayoffCap_profileOfRewardEq
    {first second : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : first = second)
    (profile : (quittingGame second).BehaviorProfile) (who : ι) :
    quittingBehaviorDeviationPayoffCap first
        (quittingProfileOfRewardEq hreward profile) who =
      quittingBehaviorDeviationPayoffCap second profile who := by
  subst second
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem quittingProfilePushforward_pullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) :
    quittingProfilePushforward e reward
        (quittingProfilePullback e reward profile) = profile := by
  funext who time history
  simp only [quittingProfilePushforward, quittingProfilePullback,
    Equiv.apply_symm_apply]
  rw [e.apply_symm_apply]

/-- The unrestricted behavioral deviation cap commutes with pullback. -/
theorem quittingBehaviorDeviationPayoffCap_profilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame
      (quittingRewardReindex e reward)).BehaviorProfile) (who : ι) :
    quittingBehaviorDeviationPayoffCap reward
        (quittingProfilePullback e reward profile) who =
      quittingBehaviorDeviationPayoffCap
        (quittingRewardReindex e reward) profile (e who) := by
  symm
  simpa only [quittingProfilePushforward_pullback] using
    quittingBehaviorDeviationPayoffCap_profilePushforward e reward
      (quittingProfilePullback e reward profile) who

end Terminal

end GameTheory
