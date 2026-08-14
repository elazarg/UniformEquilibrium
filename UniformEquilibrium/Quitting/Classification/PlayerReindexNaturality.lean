/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerReindex

/-!
# Naturality of player reindexing

Player relabeling is functorial on finite quitting-game reward tables.  This
module records the identity, composition, and inverse laws and upgrades the
one-way equilibrium transport to an exact statement for the transported
payoff vector. Consequently existence and nonexistence of a uniform-equilibrium
payoff are invariant under relabeling.
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

end GameTheory
