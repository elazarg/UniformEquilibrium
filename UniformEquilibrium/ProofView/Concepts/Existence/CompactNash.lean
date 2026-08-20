/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.OptimizationLocalGlobal
import UniformEquilibrium.ProofView.Concepts.Existence.ProductSimplexBrouwer

/-!
# Nash existence for compact barycentric games

Each player has a nonempty compact strategy space equipped with finite
barycentres. Payoffs are continuous and preserve barycentres in the player's
own coordinate. This is the intrinsic form of a compact continuous mixed game;
no ambient normed-space realization or finite-dimensionality assumption on the
strategy spaces is needed.

If no Nash equilibrium exists, the open sets on which a fixed unilateral
deviation is profitable cover the compact profile space. A finite subcover
selects finitely many deviations. Add one base strategy and take the product of
the resulting finite simplices. The barycentre map sends that finite product
back to the original game. Nash's positive-gain map is a continuous self-map of
the finite product, hence has a Brouwer fixed point. Barycentricity makes the
weighted sum of unilateral gains zero, while the fixed-point equations force
all selected gains to be nonpositive, contradicting the finite cover.
-/

noncomputable section

open scoped BigOperators Topology

namespace GameTheory

open Set Function

universe u

/-- A compact continuous game with finite barycentres and own-coordinate
affine payoffs. -/
structure CompactBarycentricGame where
  Player : Type u
  [finitePlayer : Fintype Player]
  [decidablePlayer : DecidableEq Player]
  Strategy : Player → Type u
  [strategyTopology : ∀ i, TopologicalSpace (Strategy i)]
  [compactStrategy : ∀ i, CompactSpace (Strategy i)]
  [nonemptyStrategy : ∀ i, Nonempty (Strategy i)]
  payoff : (∀ i, Strategy i) → Player → ℝ
  payoffContinuous : ∀ who, Continuous fun profile => payoff profile who
  barycenter : ∀ i (n : ℕ),
    stdSimplex ℝ (Fin (n + 1)) → (Fin (n + 1) → Strategy i) → Strategy i
  barycenterContinuous : ∀ i (n : ℕ) (points : Fin (n + 1) → Strategy i),
    Continuous fun weights : stdSimplex ℝ (Fin (n + 1)) =>
      barycenter i n weights points
  payoffBarycentric : ∀ (profile : ∀ i, Strategy i) (who : Player)
    (n : ℕ) (weights : stdSimplex ℝ (Fin (n + 1)))
    (points : Fin (n + 1) → Strategy who),
    payoff (Function.update profile who
        (barycenter who n weights points)) who =
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
private abbrev Deviation := Σ i, G.Strategy i

/-- Nash equilibrium. -/
def IsNash (profile : G.Profile) : Prop :=
  ∀ who (deviation : G.Strategy who),
    G.payoff (Function.update profile who deviation) who ≤
      G.payoff profile who

/-- Gain from one unilateral deviation. -/
private def deviationGain (profile : G.Profile) (deviation : G.Deviation) : ℝ :=
  G.payoff (Function.update profile deviation.1 deviation.2) deviation.1 -
    G.payoff profile deviation.1

/-- Positive part. -/
private def pospart (x : ℝ) : ℝ := max x 0

@[simp] private theorem pospart_nonneg (x : ℝ) : 0 ≤ pospart x :=
  le_max_right x 0

@[simp] private theorem pospart_eq_zero_iff (x : ℝ) : pospart x = 0 ↔ x ≤ 0 := by
  simp [pospart]

@[fun_prop] private theorem continuous_pospart : Continuous pospart :=
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
private theorem continuous_deviationGain (deviation : G.Deviation) :
    Continuous (fun profile : G.Profile => G.deviationGain profile deviation) := by
  exact ((G.payoffContinuous deviation.1).comp
      (G.continuous_update_const deviation.1 deviation.2)).sub
    (G.payoffContinuous deviation.1)

/-- A fixed base profile, used to make every finite approximation nonempty. -/
private def baseProfile : G.Profile :=
  fun _ => Classical.choice inferInstance

/-- The common finite action type used by the Brouwer approximation. -/
private abbrev ApproxAction (selected : Finset G.Deviation) (_who : G.Player) :=
  Fin (selected.card + 1)

/-- The selected deviation indexed by a positive finite action. -/
private def indexedDeviation (selected : Finset G.Deviation)
    (index : Fin selected.card) : G.Deviation :=
  (selected.equivFin.symm index).1

/-- The finite strategy family attached to player `who`. Index zero is the
base strategy. A later index carries its selected deviation when that
deviation belongs to `who`, and the base strategy otherwise. -/
private def selectedPoint (selected : Finset G.Deviation) (who : G.Player) :
    G.ApproxAction selected who → G.Strategy who :=
  Fin.cases (G.baseProfile who) fun index =>
    let deviation := G.indexedDeviation selected index
    if h : deviation.1 = who then h ▸ deviation.2 else G.baseProfile who

/-- Profiles of finite-simplex weights in the Brouwer approximation. -/
private abbrev ApproxProfile (selected : Finset G.Deviation) :=
  MixedSimplex G.Player (G.ApproxAction selected)

/-- Barycentric game profile represented by finite-simplex weights. -/
private def baryProfile (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected) : G.Profile :=
  fun who => G.barycenter who selected.card (weights who)
    (G.selectedPoint selected who)

/-- The barycentric profile depends continuously on the simplex weights. -/
private theorem continuous_baryProfile (selected : Finset G.Deviation) :
    Continuous (G.baryProfile selected) := by
  apply continuous_pi
  intro who
  exact (G.barycenterContinuous who selected.card
    (G.selectedPoint selected who)).comp (continuous_apply who)

/-- Gain of one point in a player's selected finite strategy family. -/
private def pointGain (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected)
    (who : G.Player) (action : G.ApproxAction selected who) : ℝ :=
  G.payoff (Function.update (G.baryProfile selected weights) who
      (G.selectedPoint selected who action)) who -
    G.payoff (G.baryProfile selected weights) who

/-- One selected point's gain is continuous in the simplex profile. -/
private theorem continuous_pointGain (selected : Finset G.Deviation)
    (who : G.Player) (action : G.ApproxAction selected who) :
    Continuous (fun weights : G.ApproxProfile selected =>
      G.pointGain selected weights who action) := by
  have hbary := G.continuous_baryProfile selected
  have hupdate : Continuous
      (fun weights : G.ApproxProfile selected =>
        Function.update (G.baryProfile selected weights) who
          (G.selectedPoint selected who action)) :=
    (G.continuous_update_const who
      (G.selectedPoint selected who action)).comp hbary
  exact ((G.payoffContinuous who).comp hupdate).sub
    ((G.payoffContinuous who).comp hbary)

/-- Sum of positive gains in one player's selected finite family. -/
private def gainSum (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected) (who : G.Player) : ℝ :=
  ∑ action : G.ApproxAction selected who,
    pospart (G.pointGain selected weights who action)

@[simp] private theorem gainSum_nonneg (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected) (who : G.Player) :
    0 ≤ G.gainSum selected weights who :=
  Finset.sum_nonneg fun _ _ => pospart_nonneg _

/-- Nash's positive-gain map on the product of selected finite simplices. -/
private def nashMap (selected : Finset G.Deviation) :
    G.ApproxProfile selected → G.ApproxProfile selected := by
  intro weights who
  let denominator : ℝ := 1 + G.gainSum selected weights who
  refine ⟨fun action =>
      (weights who action +
        pospart (G.pointGain selected weights who action)) / denominator,
    ?_, ?_⟩
  · intro action
    exact div_nonneg
      (add_nonneg (stdSimplex.zero_le (weights who) action)
        (pospart_nonneg _))
      (by
        dsimp [denominator]
        linarith [G.gainSum_nonneg selected weights who])
  · have hden_pos : 0 < denominator := by
      dsimp [denominator]
      linarith [G.gainSum_nonneg selected weights who]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
    have hweights_sum :
        (∑ action : G.ApproxAction selected who, weights who action) = 1 :=
      (weights who).property.2
    change
      ((∑ action : G.ApproxAction selected who, weights who action) +
          G.gainSum selected weights who) * denominator⁻¹ = 1
    rw [hweights_sum]
    exact mul_inv_cancel₀ hden_pos.ne'

@[simp] private theorem nashMap_apply (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected)
    (who : G.Player) (action : G.ApproxAction selected who) :
    G.nashMap selected weights who action =
      (weights who action +
          pospart (G.pointGain selected weights who action)) /
        (1 + G.gainSum selected weights who) :=
  rfl

/-- The finite positive-gain Nash map is continuous. -/
private theorem continuous_nashMap (selected : Finset G.Deviation) :
    Continuous (G.nashMap selected) := by
  have hcoord : ∀ who (action : G.ApproxAction selected who),
      Continuous
        (fun weights : G.ApproxProfile selected =>
          (weights who action +
              pospart (G.pointGain selected weights who action)) /
            (1 + G.gainSum selected weights who)) := by
    intro who action
    have hweight : Continuous
        (fun weights : G.ApproxProfile selected => weights who action) :=
      (continuous_apply action).comp
        (continuous_subtype_val.comp (continuous_apply who))
    have hsum : Continuous
        (fun weights : G.ApproxProfile selected =>
          G.gainSum selected weights who) := by
      unfold gainSum
      exact continuous_finsetSum _ fun other _ =>
        continuous_pospart.comp
          (G.continuous_pointGain selected who other)
    have hden : ∀ weights : G.ApproxProfile selected,
        1 + G.gainSum selected weights who ≠ 0 := by
      intro weights
      linarith [G.gainSum_nonneg selected weights who]
    exact (hweight.add (continuous_pospart.comp
      (G.continuous_pointGain selected who action))).div
        (continuous_const.add hsum) hden
  apply continuous_pi
  intro who
  apply Continuous.subtype_mk
  apply continuous_pi
  intro action
  exact hcoord who action

/-- Barycentricity makes the current finite mixture's weighted average gain
exactly zero. -/
private theorem weighted_pointGain_sum_zero (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected) (who : G.Player) :
    ∑ action : G.ApproxAction selected who,
      weights who action * G.pointGain selected weights who action = 0 := by
  let profile := G.baryProfile selected weights
  let points := G.selectedPoint selected who
  have hcurrent :
      G.barycenter who selected.card (weights who) points =
        profile who := by
    rfl
  have hupdate :
      Function.update profile who
          (G.barycenter who selected.card (weights who) points) =
        profile := by
    rw [hcurrent, Function.update_eq_self]
  have hmean :
      G.payoff profile who =
        ∑ action : G.ApproxAction selected who,
          weights who action *
            G.payoff (Function.update profile who (points action)) who := by
    have hbary := G.payoffBarycentric profile who selected.card
      (weights who) points
    rw [hupdate] at hbary
    exact hbary
  unfold pointGain
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hweights_sum :
      (∑ action : G.ApproxAction selected who, weights who action) = 1 :=
    (weights who).property.2
  rw [hweights_sum, one_mul]
  exact sub_eq_zero.mpr hmean.symm

/-- A fixed point of `nashMap` satisfies Nash's coordinate identity. -/
private theorem fixedPoint_identity (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected)
    (hfixed : G.nashMap selected weights = weights)
    (who : G.Player) (action : G.ApproxAction selected who) :
    weights who action * (1 + G.gainSum selected weights who) =
      weights who action + pospart (G.pointGain selected weights who action) := by
  have hvalue : G.nashMap selected weights who action = weights who action := by
    exact congrFun (congrArg Subtype.val (congrFun hfixed who)) action
  rw [G.nashMap_apply] at hvalue
  have hden : 1 + G.gainSum selected weights who ≠ 0 := by
    linarith [G.gainSum_nonneg selected weights who]
  exact ((div_eq_iff hden).mp hvalue).symm

/-- Every selected finite point has nonpositive gain at a fixed point. -/
private theorem pointGain_nonpos_of_fixedPoint (selected : Finset G.Deviation)
    (weights : G.ApproxProfile selected)
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
    (w := w) (g := g) hfp hweighted action

/-- The finite index of a selected deviation. -/
private def selectedAction {selected : Finset G.Deviation}
    (deviation : G.Deviation) (hdeviation : deviation ∈ selected) :
    G.ApproxAction selected deviation.1 :=
  Fin.succ (selected.equivFin ⟨deviation, hdeviation⟩)

@[simp] private theorem selectedPoint_selectedAction
    {selected : Finset G.Deviation}
    (deviation : G.Deviation) (hdeviation : deviation ∈ selected) :
    G.selectedPoint selected deviation.1
      (G.selectedAction deviation hdeviation) = deviation.2 := by
  classical
  unfold selectedAction selectedPoint
  simp only [Fin.cases_succ]
  have hindex :
      G.indexedDeviation selected
          (selected.equivFin ⟨deviation, hdeviation⟩) = deviation := by
    simp [indexedDeviation]
  rw [hindex]
  simp

@[simp] private theorem pointGain_selectedAction
    {selected : Finset G.Deviation}
    (weights : G.ApproxProfile selected)
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
  have hprofitable : ∀ profile : G.Profile,
      ∃ deviation : G.Deviation, 0 < G.deviationGain profile deviation := by
    intro profile
    have hnash : ¬G.IsNash profile := fun h => hnone ⟨profile, h⟩
    unfold IsNash at hnash
    push Not at hnash
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
    isCompact_univ.elim_finite_subcover profitable hopen hcover
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

/-- Nash-equilibrium profiles as a subset of the compact profile space. -/
def nashProfiles : Set G.Profile :=
  {profile | G.IsNash profile}

/-- The Nash-profile set is closed. -/
theorem isClosed_nashProfiles : IsClosed G.nashProfiles := by
  rw [show G.nashProfiles =
      ⋂ who, ⋂ deviation : G.Strategy who,
        {profile : G.Profile |
          G.payoff (Function.update profile who deviation) who ≤
            G.payoff profile who} by
    ext profile
    simp [nashProfiles, IsNash]]
  apply isClosed_iInter
  intro who
  apply isClosed_iInter
  intro deviation
  exact isClosed_le
    ((G.payoffContinuous who).comp
      (G.continuous_update_const who deviation))
    (G.payoffContinuous who)

/-- The Nash-profile set is compact. -/
theorem isCompact_nashProfiles : IsCompact G.nashProfiles :=
  G.isClosed_nashProfiles.isCompact

/-- Payoffs attained by Nash equilibria. -/
def equilibriumPayoffs : Set (G.Player → ℝ) :=
  {value | ∃ profile : G.Profile,
    G.IsNash profile ∧ G.payoff profile = value}

/-- The equilibrium-payoff set is the continuous image of the Nash-profile set. -/
theorem equilibriumPayoffs_eq_image :
    G.equilibriumPayoffs = G.payoff '' G.nashProfiles := by
  ext value
  constructor
  · rintro ⟨profile, hprofile, rfl⟩
    exact ⟨profile, hprofile, rfl⟩
  · rintro ⟨profile, hprofile, rfl⟩
    exact ⟨profile, hprofile, rfl⟩

/-- Compact barycentric games have a nonempty equilibrium-payoff set. -/
theorem equilibriumPayoffs_nonempty : G.equilibriumPayoffs.Nonempty := by
  obtain ⟨profile, hprofile⟩ := G.exists_nash
  exact ⟨G.payoff profile, profile, hprofile, rfl⟩

/-- The equilibrium-payoff set is compact. -/
theorem isCompact_equilibriumPayoffs : IsCompact G.equilibriumPayoffs := by
  rw [G.equilibriumPayoffs_eq_image]
  have hpayoff : Continuous G.payoff :=
    continuous_pi G.payoffContinuous
  exact G.isCompact_nashProfiles.image_of_continuousOn hpayoff.continuousOn

/-- Nonemptiness and compactness of the equilibrium-payoff set. -/
theorem equilibriumPayoffs_nonempty_and_compact :
    G.equilibriumPayoffs.Nonempty ∧ IsCompact G.equilibriumPayoffs :=
  ⟨G.equilibriumPayoffs_nonempty, G.isCompact_equilibriumPayoffs⟩

end CompactBarycentricGame

end GameTheory
