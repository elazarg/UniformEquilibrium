/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.OptimizationLocalGlobal
import UniformEquilibrium.ProofView.Concepts.Existence.ProductSimplexBrouwer

/-!
# Nash existence for compact barycentric games

This file proves the compact-strategy Nash theorem needed by Sorin's compact
repeated-game reduction.

Each player has a nonempty compact strategy space equipped with finite
barycentres. The payoff is continuous and preserves those barycentres in a
player's own coordinate. This is the intrinsic formulation of a compact
continuous mixed game: no ambient normed-space presentation and no
finite-dimensionality assumption on the strategy spaces are required.

The proof is finite-dimensional. If no Nash equilibrium exists, the open sets
on which a fixed unilateral deviation is profitable cover the compact profile
space. A finite subcover selects finitely many deviations. Add one base
strategy for each player and take the product of the corresponding finite
simplices. The barycentre map turns simplex profiles into game profiles. Nash's
positive-gain map is a continuous self-map of that finite product of
simplices, so Brouwer supplies a fixed point. Barycentricity makes the weighted
sum of unilateral gains zero; the fixed-point identities then force every
selected gain to be nonpositive, contradicting the finite cover.
-/

noncomputable section

open scoped BigOperators Topology

namespace GameTheory

open Set Function

universe u v

/-- A compact continuous game whose strategy spaces admit finite
barycentres and whose payoffs are affine in each player's own strategy. -/
structure CompactBarycentricGame where
  Player : Type u
  [finitePlayer : Fintype Player]
  [decidablePlayer : DecidableEq Player]
  Strategy : Player → Type v
  [strategyTopology : ∀ i, TopologicalSpace (Strategy i)]
  [compactStrategy : ∀ i, CompactSpace (Strategy i)]
  [nonemptyStrategy : ∀ i, Nonempty (Strategy i)]
  payoff : (∀ i, Strategy i) → Player → ℝ
  payoffContinuous : ∀ who, Continuous fun profile => payoff profile who
  barycenter : ∀ i {A : Type*} [Fintype A] [Nonempty A],
    stdSimplex ℝ A → (A → Strategy i) → Strategy i
  barycenterContinuous : ∀ i {A : Type*} [Fintype A] [Nonempty A]
    (points : A → Strategy i),
    Continuous fun weights : stdSimplex ℝ A => barycenter i weights points
  payoffBarycentric : ∀ (profile : ∀ i, Strategy i) (who : Player)
    {A : Type*} [Fintype A] [Nonempty A]
    (weights : stdSimplex ℝ A) (points : A → Strategy who),
    payoff (Function.update profile who
        (barycenter who weights points)) who =
      ∑ a, weights a * payoff (Function.update profile who (points a)) who

attribute [instance] CompactBarycentricGame.finitePlayer
attribute [instance] CompactBarycentricGame.decidablePlayer
attribute [instance] CompactBarycentricGame.strategyTopology
attribute [instance] CompactBarycentricGame.compactStrategy
attribute [instance] CompactBarycentricGame.nonemptyStrategy

namespace CompactBarycentricGame

variable (G : CompactBarycentricGame)

/-- A strategy profile. -/
abbrev Profile := ∀ i, G.Strategy i

/-- A unilateral deviation together with its owner. -/
abbrev Deviation := Σ i, G.Strategy i

/-- Nash equilibrium. -/
def IsNash (profile : G.Profile) : Prop :=
  ∀ who (deviation : G.Strategy who),
    G.payoff (Function.update profile who deviation) who ≤
      G.payoff profile who

/-- Gain from one unilateral deviation. -/
def deviationGain (profile : G.Profile) (deviation : G.Deviation) : ℝ :=
  G.payoff (Function.update profile deviation.1 deviation.2) deviation.1 -
    G.payoff profile deviation.1

/-- Positive part. -/
def pospart (x : ℝ) : ℝ := max x 0

@[simp] theorem pospart_nonneg (x : ℝ) : 0 ≤ pospart x :=
  le_max_right x 0

@[simp] theorem pospart_eq_zero_iff (x : ℝ) : pospart x = 0 ↔ x ≤ 0 := by
  simp [pospart]

@[fun_prop] theorem continuous_pospart : Continuous pospart :=
  continuous_id.max continuous_const

/-- Replacing one coordinate by a fixed strategy is continuous. -/
theorem continuous_update_const (who : G.Player) (deviation : G.Strategy who) :
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

/-- A fixed deviation's gain is continuous in the profile. -/
theorem continuous_deviationGain (deviation : G.Deviation) :
    Continuous (fun profile : G.Profile => G.deviationGain profile deviation) := by
  exact ((G.payoffContinuous deviation.1).comp
      (G.continuous_update_const deviation.1 deviation.2)).sub
    (G.payoffContinuous deviation.1)

/-- A fixed admissible base profile, used only to make every selected finite
simplex nonempty. -/
def baseProfile : G.Profile :=
  fun i => Classical.choice inferInstance

/-- Selected deviations owned by one player. -/
abbrev OwnedDeviation (selected : Finset G.Deviation) (who : G.Player) :=
  {d : {d : G.Deviation // d ∈ selected} // d.1.1 = who}

/-- The finite action index used in the Brouwer reduction. `none` denotes the
base strategy. -/
abbrev ApproxAction (selected : Finset G.Deviation) (who : G.Player) :=
  Option (G.OwnedDeviation selected who)

/-- Cast an owned selected deviation to its owner's strategy type. -/
def ownedStrategy {selected : Finset G.Deviation} {who : G.Player}
    (deviation : G.OwnedDeviation selected who) : G.Strategy who :=
  deviation.2 ▸ deviation.1.1.2

/-- The finite strategy family attached to one player. -/
def selectedPoint (selected : Finset G.Deviation) (who : G.Player) :
    G.ApproxAction selected who → G.Strategy who
  | none => G.baseProfile who
  | some deviation => G.ownedStrategy deviation

/-- Barycentric game profile represented by a profile of finite-simplex
weights. -/
def baryProfile (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected)) : G.Profile :=
  fun who => G.barycenter who (weights who) (G.selectedPoint selected who)

/-- The barycentric profile depends continuously on the simplex weights. -/
theorem continuous_baryProfile (selected : Finset G.Deviation) :
    Continuous (G.baryProfile selected) := by
  apply continuous_pi
  intro who
  exact (G.barycenterContinuous who (G.selectedPoint selected who)).comp
    (continuous_apply who)

/-- Gain of one point of a player's selected finite strategy family. -/
def pointGain (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (who : G.Player) (action : G.ApproxAction selected who) : ℝ :=
  G.payoff (Function.update (G.baryProfile selected weights) who
      (G.selectedPoint selected who action)) who -
    G.payoff (G.baryProfile selected weights) who

/-- One selected point's gain is continuous in the simplex profile. -/
theorem continuous_pointGain (selected : Finset G.Deviation)
    (who : G.Player) (action : G.ApproxAction selected who) :
    Continuous (fun weights : MixedSimplex G.Player (G.ApproxAction selected) =>
      G.pointGain selected weights who action) := by
  have hbary := G.continuous_baryProfile selected
  have hupdate : Continuous
      (fun weights : MixedSimplex G.Player (G.ApproxAction selected) =>
        Function.update (G.baryProfile selected weights) who
          (G.selectedPoint selected who action)) :=
    (G.continuous_update_const who
      (G.selectedPoint selected who action)).comp hbary
  exact ((G.payoffContinuous who).comp hupdate).sub
    ((G.payoffContinuous who).comp hbary)

/-- Sum of positive gains in one player's selected finite strategy family. -/
def gainSum (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (who : G.Player) : ℝ :=
  ∑ action : G.ApproxAction selected who,
    G.pospart (G.pointGain selected weights who action)

@[simp] theorem gainSum_nonneg (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (who : G.Player) :
    0 ≤ G.gainSum selected weights who :=
  Finset.sum_nonneg fun _ _ => G.pospart_nonneg _

/-- Nash's positive-gain map on the product of selected finite simplices. -/
def nashMap (selected : Finset G.Deviation) :
    MixedSimplex G.Player (G.ApproxAction selected) →
      MixedSimplex G.Player (G.ApproxAction selected) := by
  intro weights who
  let denominator := 1 + G.gainSum selected weights who
  refine ⟨fun action =>
      (weights who action +
        G.pospart (G.pointGain selected weights who action)) / denominator,
    ?_, ?_⟩
  · intro action
    exact div_nonneg
      (add_nonneg (stdSimplex.zero_le (weights who) action)
        (G.pospart_nonneg _))
      (by linarith [G.gainSum_nonneg selected weights who])
  · have hden_pos : 0 < denominator := by
      dsimp [denominator]
      linarith [G.gainSum_nonneg selected weights who]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    change
      ((∑ action, weights who action) +
          G.gainSum selected weights who) * denominator⁻¹ = 1
    rw [(weights who).property.2]
    exact mul_inv_cancel₀ hden_pos.ne'

@[simp] theorem nashMap_apply (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (who : G.Player) (action : G.ApproxAction selected who) :
    G.nashMap selected weights who action =
      (weights who action +
          G.pospart (G.pointGain selected weights who action)) /
        (1 + G.gainSum selected weights who) :=
  rfl

/-- The finite positive-gain Nash map is continuous. -/
theorem continuous_nashMap (selected : Finset G.Deviation) :
    Continuous (G.nashMap selected) := by
  have hcoord : ∀ who (action : G.ApproxAction selected who),
      Continuous
        (fun weights : MixedSimplex G.Player (G.ApproxAction selected) =>
          (weights who action +
              G.pospart (G.pointGain selected weights who action)) /
            (1 + G.gainSum selected weights who)) := by
    intro who action
    have hweight : Continuous
        (fun weights : MixedSimplex G.Player (G.ApproxAction selected) =>
          weights who action) :=
      (continuous_apply action).comp
        (continuous_subtype_val.comp (continuous_apply who))
    have hsum : Continuous
        (fun weights : MixedSimplex G.Player (G.ApproxAction selected) =>
          G.gainSum selected weights who) := by
      unfold gainSum
      exact continuous_finsetSum _ fun other _ =>
        G.continuous_pospart.comp
          (G.continuous_pointGain selected who other)
    have hden : ∀ weights : MixedSimplex G.Player (G.ApproxAction selected),
        1 + G.gainSum selected weights who ≠ 0 := by
      intro weights
      linarith [G.gainSum_nonneg selected weights who]
    exact (hweight.add (G.continuous_pospart.comp
      (G.continuous_pointGain selected who action))).div
        (continuous_const.add hsum) hden
  apply continuous_pi
  intro who
  apply Continuous.subtype_mk
  · apply continuous_pi
    intro action
    exact hcoord who action
  · intro weights
    exact (G.nashMap selected weights who).property

/-- Barycentricity makes the current finite mixture's weighted average gain
exactly zero. -/
theorem weighted_pointGain_sum_zero (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (who : G.Player) :
    ∑ action : G.ApproxAction selected who,
      weights who action * G.pointGain selected weights who action = 0 := by
  let profile := G.baryProfile selected weights
  let points := G.selectedPoint selected who
  have hbary := G.payoffBarycentric profile who (weights who) points
  have hself : Function.update profile who (profile who) = profile := by
    exact Function.update_eq_self who profile
  change
    ∑ action : G.ApproxAction selected who,
      weights who action *
        (G.payoff (Function.update profile who (points action)) who -
          G.payoff profile who) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]
  rw [(weights who).property.2, one_mul]
  change
    (∑ action : G.ApproxAction selected who,
      weights who action *
        G.payoff (Function.update profile who (points action)) who) -
      G.payoff profile who = 0
  rw [← hbary, hself]
  ring

/-- A fixed point of `nashMap` satisfies the coordinate identity used in the
positive-gain algebra. -/
theorem fixedPoint_identity (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (hfixed : G.nashMap selected weights = weights)
    (who : G.Player) (action : G.ApproxAction selected who) :
    weights who action * (1 + G.gainSum selected weights who) =
      weights who action + G.pospart (G.pointGain selected weights who action) := by
  have hcoordinate := congrArg Subtype.val (congrFun hfixed who)
  have hvalue := congrFun hcoordinate action
  rw [G.nashMap_apply] at hvalue
  have hden : 1 + G.gainSum selected weights who ≠ 0 := by
    linarith [G.gainSum_nonneg selected weights who]
  apply (eq_div_iff hden).mp
  exact hvalue.symm

/-- Every point in every selected finite family has nonpositive gain at a
fixed point of the positive-gain map. -/
theorem pointGain_nonpos_of_fixedPoint (selected : Finset G.Deviation)
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (hfixed : G.nashMap selected weights = weights)
    (who : G.Player) (action : G.ApproxAction selected who) :
    G.pointGain selected weights who action ≤ 0 := by
  let w : G.ApproxAction selected who → ℝ := fun a => weights who a
  let g : G.ApproxAction selected who → ℝ :=
    fun a => G.pointGain selected weights who a
  have hfp : ∀ a,
      w a * (1 + ∑ b, max (g b) 0) = w a + max (g a) 0 := by
    intro a
    simpa [w, g, CompactBarycentricGame.pospart,
      CompactBarycentricGame.gainSum] using
      G.fixedPoint_identity selected weights hfixed who a
  have hweighted : ∑ a, w a * g a = 0 := by
    simpa [w, g] using G.weighted_pointGain_sum_zero selected weights who
  exact Math.Optimization.LocalGlobal.all_nonpos_of_weighted_pospart_fixedPoint
    hfp hweighted action

/-- A selected deviation appears literally as a point of its owner's finite
strategy family. -/
def selectedAction {selected : Finset G.Deviation}
    (deviation : G.Deviation) (hdeviation : deviation ∈ selected) :
    G.ApproxAction selected deviation.1 :=
  some ⟨⟨deviation, hdeviation⟩, rfl⟩

@[simp] theorem selectedPoint_selectedAction
    {selected : Finset G.Deviation}
    (deviation : G.Deviation) (hdeviation : deviation ∈ selected) :
    G.selectedPoint selected deviation.1
      (G.selectedAction deviation hdeviation) = deviation.2 := by
  rfl

@[simp] theorem pointGain_selectedAction
    {selected : Finset G.Deviation}
    (weights : MixedSimplex G.Player (G.ApproxAction selected))
    (deviation : G.Deviation) (hdeviation : deviation ∈ selected) :
    G.pointGain selected weights deviation.1
      (G.selectedAction deviation hdeviation) =
        G.deviationGain (G.baryProfile selected weights) deviation := by
  simp [pointGain, deviationGain]

/-- **General compact Nash-existence theorem.** Every finite-player compact
barycentric continuous game has a Nash equilibrium. -/
theorem exists_nash : ∃ profile : G.Profile, G.IsNash profile := by
  classical
  by_contra hnone
  simp only [not_exists] at hnone
  have hprofitable : ∀ profile : G.Profile,
      ∃ deviation : G.Deviation, 0 < G.deviationGain profile deviation := by
    intro profile
    have hnash := hnone profile
    unfold IsNash at hnash
    push_neg at hnash
    obtain ⟨who, deviation, hgain⟩ := hnash
    exact ⟨⟨who, deviation⟩, sub_pos.mpr hgain⟩
  let profitable : G.Deviation → Set G.Profile :=
    fun deviation => {profile | 0 < G.deviationGain profile deviation}
  have hopen : ∀ deviation, IsOpen (profitable deviation) := by
    intro deviation
    exact isOpen_lt continuous_const (G.continuous_deviationGain deviation)
  have hcover : Set.univ ⊆ ⋃ deviation, profitable deviation := by
    intro profile _
    obtain ⟨deviation, hgain⟩ := hprofitable profile
    exact Set.mem_iUnion.2 ⟨deviation, hgain⟩
  obtain ⟨selected, hselected⟩ :=
    isCompact_univ.elim_finite_subcover hopen hcover
  obtain ⟨weights, hfixed⟩ :=
    brouwer_mixedSimplex (G.nashMap selected) (G.continuous_nashMap selected)
  let profile := G.baryProfile selected weights
  have hselected_cover : profile ∈ ⋃ deviation ∈ selected, profitable deviation :=
    hselected (Set.mem_univ profile)
  simp only [Set.mem_iUnion] at hselected_cover
  obtain ⟨deviation, hdeviation_selected, hdeviation_gain⟩ := hselected_cover
  have hnonpos := G.pointGain_nonpos_of_fixedPoint selected weights hfixed
    deviation.1 (G.selectedAction deviation hdeviation_selected)
  rw [G.pointGain_selectedAction weights deviation hdeviation_selected] at hnonpos
  exact (not_lt_of_ge hnonpos) hdeviation_gain

end CompactBarycentricGame

end GameTheory
