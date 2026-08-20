/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.ConstraintPublicResponse
import MathUE.DirectedTransport.FiniteInequality.Sparse

/-!
# Rectangular mixed-player continuation compatibility

Bellman inequalities owned by player `i` depend only on player `i`'s
continuation coordinate. Separate playerwise feasibility therefore implies
simultaneous feasibility when the permitted continuation set is a product
of player-coordinate sets.

This file formalizes that sufficient condition and builds it directly into a
public-response branching recursion. The recursion's compatibility branch is
no longer an opaque proposition: it contains one whole-vector continuation
satisfying every coordinate permission and every player-owned linear
inequality.

The condition is genuinely restrictive. Coupled continuation sets such as
the diagonal segment in `FinkContinuationCompatibilityCounterexample` are
not rectangular and are intentionally outside the theorem.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.LinearAlgebra

variable {State Player : Type*}
  [Fintype State] [Fintype Player]
  {Constraint : Player → Type*}
  [∀ player, Fintype (Constraint player)]

/-- Player-block continuation geometry and player-owned Bellman
inequalities.

`coordinatePermitted player` is the player's factor of the permitted
continuation product. `delta` is normally a transition-difference row and
`rhs` its Bellman lower bound. -/
structure RectangularContinuationSystem
    (State Player : Type*)
    (Constraint : Player → Type*) where
  coordinatePermitted : ∀ _player : Player, (State → ℝ) → Prop
  delta : ∀ player, Constraint player → State → ℝ
  rhs : ∀ player, Constraint player → ℝ

namespace RectangularContinuationSystem

/-- Every player can choose a feasible continuation in their own coordinate
factor. -/
def PlayerwiseFeasible
    (S : RectangularContinuationSystem
      State Player Constraint) : Prop :=
  ∀ player,
    ∃ coordinate : State → ℝ,
      S.coordinatePermitted player coordinate ∧
        ∀ constraint,
          S.rhs player constraint ≤
            dotProduct (S.delta player constraint) coordinate

/-- One whole payoff-vector continuation is feasible for every player at
once. -/
def SimultaneouslyFeasible
    (S : RectangularContinuationSystem
      State Player Constraint) : Prop :=
  ∃ continuation : State → Player → ℝ,
    (∀ player,
      S.coordinatePermitted player
        (fun state => continuation state player)) ∧
    ∀ player constraint,
      S.rhs player constraint ≤
        dotProduct (S.delta player constraint)
          (fun state => continuation state player)

/-- Every continuation coordinate is permitted.  This is the natural case
when the rectangular system records only its explicit linear rows. -/
def HasUnrestrictedCoordinates
    (S : RectangularContinuationSystem State Player Constraint) : Prop :=
  ∀ player coordinate, S.coordinatePermitted player coordinate

omit [Fintype Player] [∀ player, Fintype (Constraint player)] in
/-- Rectangularity turns separate coordinate witnesses into one simultaneous
whole-vector continuation without loss or an additional compatibility
assumption. -/
theorem simultaneouslyFeasible_of_playerwise
    (S : RectangularContinuationSystem
      State Player Constraint)
    (playerwise : S.PlayerwiseFeasible) :
    S.SimultaneouslyFeasible := by
  choose coordinate coordinatePermitted inequalities using playerwise
  refine ⟨fun state player => coordinate player state, ?_, ?_⟩
  · intro player
    exact coordinatePermitted player
  · intro player constraint
    exact inequalities player constraint

omit [Fintype Player] [∀ player, Fintype (Constraint player)] in
/-- The simultaneous witness exposes a feasible finite inequality potential
in each player block. -/
theorem finiteInequalityFeasible_of_simultaneouslyFeasible
    (S : RectangularContinuationSystem
      State Player Constraint)
    (simultaneous : S.SimultaneouslyFeasible)
    (player : Player) :
    ∃ coordinate : State → ℝ,
      ∀ constraint,
        S.rhs player constraint ≤
          dotProduct (S.delta player constraint) coordinate := by
  obtain ⟨continuation, -, inequalities⟩ := simultaneous
  exact ⟨fun state => continuation state player,
    inequalities player⟩

omit [Fintype Player] [∀ player, Fintype (Constraint player)] in
/-- With unrestricted coordinate factors, simultaneous infeasibility is
already infeasibility of one player's finite inequality block. -/
theorem exists_infeasiblePlayer_of_not_simultaneouslyFeasible
    (S : RectangularContinuationSystem State Player Constraint)
    (hunrestricted : S.HasUnrestrictedCoordinates)
    (hinfeasible : ¬S.SimultaneouslyFeasible) :
    ∃ player, ¬∃ coordinate : State → ℝ,
      ∀ constraint,
        S.rhs player constraint ≤
          dotProduct (S.delta player constraint) coordinate := by
  classical
  by_contra hnone
  push Not at hnone
  apply hinfeasible
  apply S.simultaneouslyFeasible_of_playerwise
  intro player
  obtain ⟨coordinate, hrows⟩ := hnone player
  exact ⟨coordinate, hunrestricted player coordinate, hrows⟩

omit [Fintype Player] in
/-- Simultaneous infeasibility has a positive-circuit certificate in one
player's row block. -/
theorem exists_player_positiveCircuit_of_not_simultaneouslyFeasible
    (S : RectangularContinuationSystem State Player Constraint)
    (hunrestricted : S.HasUnrestrictedCoordinates)
    (hinfeasible : ¬S.SimultaneouslyFeasible) :
    ∃ (player : Player) (coefficient : Constraint player → ℝ),
      Math.FiniteInequality.IsPositiveCircuit
          (S.delta player) coefficient ∧
        0 < Math.FiniteInequality.certificateValue
          (S.rhs player) coefficient := by
  obtain ⟨player, hplayer⟩ :=
    S.exists_infeasiblePlayer_of_not_simultaneouslyFeasible
      hunrestricted hinfeasible
  obtain ⟨coefficient, hcircuit, hpositive⟩ :=
    Math.FiniteInequality.exists_positiveCircuit_of_infeasible
      (S.delta player) (S.rhs player) hplayer
  exact ⟨player, coefficient, hcircuit, hpositive⟩

omit [Fintype Player] in
/-- Simultaneous infeasibility is witnessed by one player and at most one
more row than the rank of that player's row normals. -/
theorem exists_player_rankSparseCertificate_of_not_simultaneouslyFeasible
    (S : RectangularContinuationSystem State Player Constraint)
    (hunrestricted : S.HasUnrestrictedCoordinates)
    (hinfeasible : ¬S.SimultaneouslyFeasible) :
    ∃ (player : Player) (coefficient : Constraint player → ℝ),
      Math.FiniteInequality.IsNormalizedCertificate
          (S.delta player) coefficient ∧
        0 < Math.FiniteInequality.certificateValue
          (S.rhs player) coefficient ∧
        Fintype.card {constraint : Constraint player //
          coefficient constraint ≠ 0} ≤
          (Set.range (S.delta player)).finrank ℝ + 1 := by
  obtain ⟨player, hplayer⟩ :=
    S.exists_infeasiblePlayer_of_not_simultaneouslyFeasible
      hunrestricted hinfeasible
  obtain ⟨coefficient, hcertificate, hpositive, hcard⟩ :=
    Math.FiniteInequality.exists_positive_normalizedCertificate_support_card_le_rank_add_one
      (S.delta player) (S.rhs player) hplayer
  exact ⟨player, coefficient, hcertificate, hpositive, hcard⟩

end RectangularContinuationSystem

variable {ι : Type} {G : StochasticGame ι}

/-- A public-response branching recursion whose compatible branch is
certified by rectangular player-block continuation geometry.

The response closer and legal core-history interface remain strategic data.
Only the mixed-player continuation-gluing obligation is discharged here. -/
structure RectangularContinuationBranchingRecursionAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Fintype G.State] [∀ player, Finite (G.Act player)]
    (Constraint : ι → Type*)
    [∀ player, Fintype (Constraint player)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    extends G.LocalResponseNodes s₀ v where
  continuationSystem :
    Node →
      RectangularContinuationSystem
        G.State ι Constraint
  PublicResponse : Node → Prop
  LegalCoreHistoryEntryInterface : Node → Prop
  playerwiseCompatibilityOrPublicResponse :
    ∀ node,
      (continuationSystem node).PlayerwiseFeasible ∨
        PublicResponse node
  legalCoreHistoryEntryInterface :
    ∀ node, LegalCoreHistoryEntryInterface node
  closeCompatible :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      (continuationSystem node).SimultaneouslyFeasible →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ
  closeResponse :
    ∀ node : Node,
      (∀ child : Node, rankLt (rank child) (rank node) →
        G.IsPublicPhasePunishmentSystemAt
          (entry child) (target child) δ) →
      PublicResponse node →
      LegalCoreHistoryEntryInterface node →
      G.IsPublicPhasePunishmentSystemAt
        (entry node) (target node) δ

namespace RectangularContinuationBranchingRecursionAt

variable
    [Fintype ι] [DecidableEq ι]
    [Fintype G.State] [∀ player, Finite (G.Act player)]
    {Constraint : ι → Type*}
    [∀ player, Fintype (Constraint player)]
    {s₀ : G.State} {v : Payoff ι} {δ : ℝ}

/-- Compile rectangular playerwise feasibility into the simultaneous
compatibility branch of the existing public-response recursion. -/
def toPublicResponseBranchingRecursionAt
    (C : G.RectangularContinuationBranchingRecursionAt
      Constraint s₀ v δ) :
    G.PublicResponseBranchingRecursionAt s₀ v δ where
  toLocalResponseNodes := C.toLocalResponseNodes
  CompatibleContinuation := fun node =>
    (C.continuationSystem node).SimultaneouslyFeasible
  PublicResponse := C.PublicResponse
  LegalCoreHistoryEntryInterface :=
    C.LegalCoreHistoryEntryInterface
  compatibilityOrPublicResponse := fun node =>
    (C.playerwiseCompatibilityOrPublicResponse node).imp
      (fun playerwise =>
        RectangularContinuationSystem.simultaneouslyFeasible_of_playerwise
          (C.continuationSystem node) playerwise)
      id
  legalCoreHistoryEntryInterface :=
    C.legalCoreHistoryEntryInterface
  closeCompatible := C.closeCompatible
  closeResponse := C.closeResponse

/-- Rectangular continuation compatibility compiles through the existing
well-founded public local-response verifier. -/
theorem toIsPublicPhasePunishmentSystemAt
    (C : G.RectangularContinuationBranchingRecursionAt
      Constraint s₀ v δ) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  PublicResponseBranchingRecursionAt.toIsPublicPhasePunishmentSystemAt
    C.toPublicResponseBranchingRecursionAt

end RectangularContinuationBranchingRecursionAt

end StochasticGame
end GameTheory
