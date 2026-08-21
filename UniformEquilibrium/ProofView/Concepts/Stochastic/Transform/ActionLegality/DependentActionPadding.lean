/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.ActionLegality.BehaviorTransfer

/-!
# Padding state-dependent action families

`StochasticGame` has one action type per player.  A presentation whose action type also
depends on the current state embeds into that model by taking the sigma type of all tagged
local actions.  The tag-equality predicate is the legality predicate, and the existing
action-legality normalization supplies total semantics for actions carrying the wrong tag.

This module is only a semantic adapter.  It does not identify unrestricted strategies in the
padded game with strategies in the dependent-action presentation: a padded strategy may use
the otherwise observable tag of an illegal action.  The exact bridge below is for profiles
obtained by lifting local action laws, which are unconditionally legal.
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

namespace DependentAction

variable {ι State : Type} (Action : State → ι → Type)

open Classical

/-- The fixed action carrier obtained by tagging every local action with its state. -/
abbrev PaddedAction (i : ι) := Σ state, Action state i

/-- Embed an action available at `state` into the fixed padded carrier. -/
def embed (state : State) (i : ι) (action : Action state i) : PaddedAction Action i :=
  ⟨state, action⟩

/-- A padded action is legal exactly when its state tag is the current state. -/
def Legal (state : State) (i : ι) (action : PaddedAction Action i) : Prop :=
  action.1 = state

/-- The canonical embedded local action is legal. -/
@[simp] theorem legal_embed (state : State) (i : ι) (action : Action state i) :
    Legal Action state i (embed Action state i action) :=
  rfl

/-- Decode a padded action at the current state, using the supplied local fallback for an
incorrect tag. -/
def decode (fallback : ∀ state i, Action state i) (state : State) (i : ι)
    (action : PaddedAction Action i) : Action state i :=
  if h : action.1 = state then h ▸ action.2 else fallback state i

/-- Decoding an action embedded at the current state recovers that action. -/
@[simp] theorem decode_embed (fallback : ∀ state i, Action state i)
    (state : State) (i : ι) (action : Action state i) :
    decode Action fallback state i (embed Action state i action) = action := by
  simp [decode, embed]

/-- The fixed-action game before legality normalization.  Its values on incorrectly tagged
actions are immaterial: `game` below normalizes those actions first. -/
def rawGame (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1) :
    StochasticGame ι where
  State := State
  Act := PaddedAction Action
  stagePayoff state action :=
    stagePayoff state (fun i => decode Action fallback state i (action i))
  transition state action :=
    transition state (fun i => decode Action fallback state i (action i))
  discount := discount
  discount_nonneg := discount_nonneg
  discount_lt_one := discount_lt_one

/-- Every state/player pair has the local fallback as a legal padded action. -/
theorem exists_legal (fallback : ∀ state i, Action state i) :
    ∀ state i, ∃ action, Legal Action state i action :=
  fun state i => ⟨embed Action state i (fallback state i), rfl⟩

/-- The normalized fixed-action game associated with a dependent action family. -/
@[reducible] def game [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1) :
    StochasticGame ι :=
  (rawGame Action fallback stagePayoff transition discount discount_nonneg discount_lt_one)
    |>.normalizedGame (Legal Action) (exists_legal Action fallback)

/-- Embed a whole joint action available at one state. -/
def embedJoint (state : State) (action : ∀ i, Action state i) :
    ∀ i, PaddedAction Action i :=
  fun i => embed Action state i (action i)

/-- The padded game's stage payoff on an embedded legal joint action is the source payoff. -/
@[simp] theorem game_stagePayoff_embed [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1)
    (state : State) (action : ∀ i, Action state i) (who : ι) :
    (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).stagePayoff state (embedJoint Action state action) who =
      stagePayoff state action who := by
  rw [show (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).stagePayoff =
        (rawGame Action fallback stagePayoff transition discount discount_nonneg
          discount_lt_one).normStagePayoff (Legal Action) (exists_legal Action fallback) from rfl]
  rw [StochasticGame.normStagePayoff_of_jointlyLegal]
  · simp [rawGame, embedJoint]
  · exact fun i => legal_embed Action state i (action i)

/-- The padded game's transition on an embedded legal joint action is the source transition. -/
@[simp] theorem game_transition_embed [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1)
    (state : State) (action : ∀ i, Action state i) :
    (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).transition state (embedJoint Action state action) =
      transition state action := by
  rw [show (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).transition =
        (rawGame Action fallback stagePayoff transition discount discount_nonneg
          discount_lt_one).normTransition (Legal Action) (exists_legal Action fallback) from rfl]
  rw [StochasticGame.normTransition_of_jointlyLegal]
  · simp [rawGame, embedJoint]
  · exact fun i => legal_embed Action state i (action i)

/-- Lift local behavioral action laws to the padded game by attaching the current-state tag. -/
def liftBehaviorProfile [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1)
    (policy : ∀ (i : ι) (t : ℕ)
      (history : (game Action fallback stagePayoff transition discount discount_nonneg
        discount_lt_one).Hist t), PMF (Action history.2 i)) :
    (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).BehaviorProfile :=
  fun i t history => (policy i t history).map (embed Action history.2 i)

/-- A lifted local profile is unconditionally legal in the padded presentation. -/
theorem liftBehaviorProfile_isLegal [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1)
    (policy : ∀ (i : ι) (t : ℕ)
      (history : (game Action fallback stagePayoff transition discount discount_nonneg
        discount_lt_one).Hist t), PMF (Action history.2 i)) :
    (rawGame Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).IsLegalBehaviorProfile (Legal Action)
        (liftBehaviorProfile Action fallback stagePayoff transition discount discount_nonneg
          discount_lt_one policy) := by
  intro i t history action haction
  change action ∈ ((policy i t history).map (embed Action history.2 i)).support at haction
  rw [PMF.support_map] at haction
  rcases haction with ⟨localAction, -, rfl⟩
  exact legal_embed Action history.2 i localAction

/-- Under a lifted local profile, normalization does not change any finite-history law. -/
theorem histDist_game_eq_rawGame [Fintype ι] [DecidableEq ι]
    (fallback : ∀ state i, Action state i)
    (stagePayoff : (state : State) → (∀ i, Action state i) → ι → ℝ)
    (transition : (state : State) → (∀ i, Action state i) → PMF State)
    (discount : ℝ) (discount_nonneg : 0 ≤ discount) (discount_lt_one : discount < 1)
    (policy : ∀ (i : ι) (t : ℕ)
      (history : (game Action fallback stagePayoff transition discount discount_nonneg
        discount_lt_one).Hist t), PMF (Action history.2 i))
    (initial : State) (time : ℕ) :
    (game Action fallback stagePayoff transition discount discount_nonneg
      discount_lt_one).histDist
          (liftBehaviorProfile Action fallback stagePayoff transition discount discount_nonneg
            discount_lt_one policy) initial time =
      (rawGame Action fallback stagePayoff transition discount discount_nonneg
        discount_lt_one).histDist
          (liftBehaviorProfile Action fallback stagePayoff transition discount discount_nonneg
            discount_lt_one policy) initial time := by
  exact (rawGame Action fallback stagePayoff transition discount discount_nonneg
    discount_lt_one).histDist_normalizedGame_eq_of_isLegalBehaviorProfile
      (Legal Action) (exists_legal Action fallback)
      (liftBehaviorProfile_isLegal Action fallback stagePayoff transition discount
        discount_nonneg discount_lt_one policy) initial time

end DependentAction

end StochasticGame

end GameTheory
