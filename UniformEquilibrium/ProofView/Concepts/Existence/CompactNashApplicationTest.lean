/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.ProofView.Concepts.Existence.CompactNash

noncomputable section

open scoped BigOperators Topology

namespace GameTheory.CompactNashApplicationTest

open Set

/-- Minimal paper-facing wrapper used to verify the application theorem. -/
structure Game where
  Player : Type
  [finitePlayer : Fintype Player]
  [decidablePlayer : DecidableEq Player]
  Strategy : Player → Type
  [strategyTopology : ∀ i, TopologicalSpace (Strategy i)]
  [compactStrategy : ∀ i, CompactSpace (Strategy i)]
  [nonemptyStrategy : ∀ i, Nonempty (Strategy i)]
  payoff : (∀ i, Strategy i) → Player → ℝ
  payoffContinuous : ∀ who, Continuous fun profile => payoff profile who
  barycenter : ∀ i (n : ℕ),
    stdSimplex ℝ (Fin n) → (Fin n → Strategy i) → Strategy i
  barycenterContinuous : ∀ i (n : ℕ) (points : Fin n → Strategy i),
    Continuous fun weights : stdSimplex ℝ (Fin n) =>
      barycenter i n weights points
  payoffBarycentric : ∀ profile who (n : ℕ)
    (weights : stdSimplex ℝ (Fin n)) (points : Fin n → Strategy who),
    payoff (Function.update profile who
        (barycenter who n weights points)) who =
      ∑ a, weights a * payoff (Function.update profile who (points a)) who

attribute [instance] Game.finitePlayer
attribute [instance] Game.decidablePlayer
attribute [instance] Game.strategyTopology
attribute [instance] Game.compactStrategy
attribute [instance] Game.nonemptyStrategy

abbrev Game.Profile (G : Game) := ∀ i, G.Strategy i

def Game.IsNash (G : Game) (profile : G.Profile) : Prop :=
  ∀ who (deviation : G.Strategy who),
    G.payoff (Function.update profile who deviation) who ≤ G.payoff profile who

def Game.equilibriumPayoffs (G : Game) : Set (G.Player → ℝ) :=
  {v | ∃ profile : G.Profile, G.IsNash profile ∧ G.payoff profile = v}

noncomputable def Game.toCompactBarycentricGame (G : Game) :
    CompactBarycentricGame where
  Player := G.Player
  Strategy := G.Strategy
  payoff := G.payoff
  payoffContinuous := G.payoffContinuous
  barycenter := G.barycenter
  barycenterContinuous := G.barycenterContinuous
  payoffBarycentric := G.payoffBarycentric

theorem Game.continuous_update_const (G : Game) (who : G.Player)
    (deviation : G.Strategy who) :
    Continuous (fun profile : G.Profile =>
      Function.update profile who deviation) := by
  apply continuous_pi
  intro i
  by_cases hi : i = who
  · subst i
    simpa using (continuous_const :
      Continuous (fun _profile : G.Profile => deviation))
  · simpa [Function.update, hi] using
      (continuous_apply i : Continuous (fun profile : G.Profile => profile i))

theorem Game.isClosed_nashProfiles (G : Game) :
    IsClosed {profile : G.Profile | G.IsNash profile} := by
  rw [show {profile : G.Profile | G.IsNash profile} =
      ⋂ who, ⋂ deviation : G.Strategy who,
        {profile : G.Profile |
          G.payoff (Function.update profile who deviation) who ≤
            G.payoff profile who} by
    ext profile
    simp [Game.IsNash]]
  apply isClosed_iInter
  intro who
  apply isClosed_iInter
  intro deviation
  exact isClosed_le
    ((G.payoffContinuous who).comp
      (G.continuous_update_const who deviation))
    (G.payoffContinuous who)

/-- The compact Nash theorem gives nonempty compact equilibrium payoffs. -/
theorem property2 (G : Game) :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs := by
  have hnash : ∃ profile : G.Profile, G.IsNash profile := by
    obtain ⟨profile, hprofile⟩ := G.toCompactBarycentricGame.exists_nash
    refine ⟨profile, ?_⟩
    intro who deviation
    exact hprofile who deviation
  constructor
  · obtain ⟨profile, hprofile⟩ := hnash
    exact ⟨G.payoff profile, profile, hprofile, rfl⟩
  · have hpayoff : Continuous G.payoff := continuous_pi G.payoffContinuous
    have hcompactProfiles :
        IsCompact {profile : G.Profile | G.IsNash profile} :=
      G.isClosed_nashProfiles.isCompact
    have heq : G.equilibriumPayoffs =
        G.payoff '' {profile : G.Profile | G.IsNash profile} := by
      ext value
      constructor
      · rintro ⟨profile, hprofile, rfl⟩
        exact ⟨profile, hprofile, rfl⟩
      · rintro ⟨profile, hprofile, rfl⟩
        exact ⟨profile, hprofile, rfl⟩
    rw [heq]
    exact hcompactProfiles.image_of_continuousOn hpayoff.continuousOn

end GameTheory.CompactNashApplicationTest
