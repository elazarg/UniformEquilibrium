/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.SchauderFixedPoint
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerSingletonBlocker
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath

/-!
# The four-player singleton blocker nevertheless circulates

`FourPlayerSingletonBlocker` rules out a static complementary distribution.
This experiment shows that the same rational reward table has a dynamic
four-phase singleton-face circulation.  The four contraction ratios are a
fixed point of an explicit continuous self-map of a compact cube.
-/

noncomputable section

namespace GameTheory
namespace FourPlayerBlockerCirculation

open Finset Set
open Math.PMFProduct
open FourPlayerSingletonBlocker

private theorem vec4_apply_two (a b c d : ℝ) :
    ![a, b, c, d] (2 : Fin 4) = c := by
  rw [show (2 : Fin 4) = Fin.succ (Fin.succ (0 : Fin 2)) by decide]
  rfl

private theorem vec4_apply_three (a b c d : ℝ) :
    ![a, b, c, d] (3 : Fin 4) = d := by
  rw [show (3 : Fin 4) =
    Fin.succ (Fin.succ (Fin.succ (0 : Fin 1))) by decide]
  rfl

/-! ## A compact fixed-point problem for the four contraction ratios -/

/-- The common interval used for all four phase-contraction ratios. -/
def ratioCube : Set (Fin 4 → ℝ) :=
  Set.Icc (fun _ => (1 : ℝ) / 3) (fun _ => (7 : ℝ) / 10)

/-- The pinning equations, solved for the next iterate of `(a,b,c,d)`. -/
def ratioMap (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![1 / (3 - 2 * x 2 * x 3),
    1 / (3 + x 0 * (1 - 3 * x 3)),
    2 / (5 - x 1 * (2 * x 0 + 1)),
    3 / (6 - x 2 * (2 * x 1 + 1))]

private theorem coord_bounds {x : Fin 4 → ℝ} (hx : x ∈ ratioCube) (i : Fin 4) :
    (1 : ℝ) / 3 ≤ x i ∧ x i ≤ 7 / 10 :=
  ⟨hx.1 i, hx.2 i⟩

private theorem product_bounds {u v : ℝ}
    (hu : (1 : ℝ) / 3 ≤ u ∧ u ≤ 7 / 10)
    (hv : (1 : ℝ) / 3 ≤ v ∧ v ≤ 7 / 10) :
    (1 : ℝ) / 9 ≤ u * v ∧ u * v ≤ 49 / 100 := by
  have hv0 : 0 ≤ v := by linarith [hv.1]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.1) hv0]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hv0]

private theorem ratioMap_denominators_pos {x : Fin 4 → ℝ} (hx : x ∈ ratioCube) :
    0 < 3 - 2 * x 2 * x 3 ∧
    0 < 3 + x 0 * (1 - 3 * x 3) ∧
    0 < 5 - x 1 * (2 * x 0 + 1) ∧
    0 < 6 - x 2 * (2 * x 1 + 1) := by
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  have h23 := product_bounds h2 h3
  have h10 := product_bounds h1 h0
  have h21 := product_bounds h2 h1
  have hb : -(77 : ℝ) / 100 ≤ x 0 * (1 - 3 * x 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h0.2) (by linarith [h3.1] : 0 ≤ 3 * x 3 - 1)]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The rational map sends the entire closed ratio cube into itself. -/
theorem ratioMap_mem_ratioCube {x : Fin 4 → ℝ} (hx : x ∈ ratioCube) :
    ratioMap x ∈ ratioCube := by
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  have h01 := product_bounds h0 h1
  have h12 := product_bounds h1 h2
  have h23 := product_bounds h2 h3
  have hden := ratioMap_denominators_pos hx
  constructor <;> intro i <;> fin_cases i
  all_goals norm_num [ratioMap]
  · rw [← one_div]
    rw [le_div_iff₀ hden.1]
    nlinarith [h23.1]
  · rw [← one_div]
    rw [le_div_iff₀ hden.2.1]
    nlinarith [mul_nonneg (by linarith [h0.1] : 0 ≤ x 0)
      (by linarith [h3.1] : 0 ≤ 3 * x 3 - 1)]
  · rw [le_div_iff₀ hden.2.2.1]
    nlinarith [h01.1]
  · rw [le_div_iff₀ hden.2.2.2]
    nlinarith [h12.1]
  · rw [← one_div]
    rw [div_le_iff₀ hden.1]
    nlinarith [h23.2]
  · rw [← one_div]
    rw [div_le_iff₀ hden.2.1]
    nlinarith [mul_nonneg (sub_nonneg.mpr h0.2)
      (by linarith [h3.1] : 0 ≤ 3 * x 3 - 1)]
  · rw [div_le_iff₀ hden.2.2.1]
    nlinarith [h01.2]
  · rw [div_le_iff₀ hden.2.2.2]
    nlinarith [h12.2]

/-- Continuity of the ratio map after restricting its domain to the cube;
the positivity lemma is exactly what makes reciprocal continuity available. -/
theorem continuous_ratioMap_on_ratioCube :
    Continuous (fun x : ratioCube => ratioMap x.1) := by
  have hcoord (i : Fin 4) : Continuous (fun x : ratioCube => x.1 i) :=
    (continuous_apply i).comp continuous_subtype_val
  apply continuous_pi
  intro i
  fin_cases i
  all_goals norm_num [ratioMap]
  · exact
      (continuous_const.sub
        ((continuous_const.mul (hcoord 2)).mul (hcoord 3))).inv₀
        (fun x => ne_of_gt (ratioMap_denominators_pos x.property).1)
  · exact
      (continuous_const.add
        ((hcoord 0).mul (continuous_const.sub (continuous_const.mul (hcoord 3))))).inv₀
        (fun x => ne_of_gt (ratioMap_denominators_pos x.property).2.1)
  · exact continuous_const.div
      (continuous_const.sub
        ((hcoord 1).mul ((continuous_const.mul (hcoord 0)).add continuous_const)))
      (fun x => ne_of_gt (ratioMap_denominators_pos x.property).2.2.1)
  · exact continuous_const.div
      (continuous_const.sub
        ((hcoord 2).mul ((continuous_const.mul (hcoord 1)).add continuous_const)))
      (fun x => ne_of_gt (ratioMap_denominators_pos x.property).2.2.2)

/-- The bundled continuous self-map used by the fixed-point argument. -/
def ratioSelfMap : C(ratioCube, ratioCube) where
  toFun x := ⟨ratioMap x.1, ratioMap_mem_ratioCube x.2⟩
  continuous_toFun :=
    continuous_induced_rng.2 continuous_ratioMap_on_ratioCube

/-- **Exact ratio fixed point.**  No approximation or root isolation is
needed: Schauder/Brouwer supplies four contraction ratios in the displayed
rational cube satisfying all pinning equations simultaneously. -/
theorem exists_ratio_fixedPoint :
    ∃ x : Fin 4 → ℝ, x ∈ ratioCube ∧ ratioMap x = x := by
  have hconvex : Convex ℝ ratioCube := convex_Icc _ _
  have hcompact : IsCompact ratioCube := isCompact_Icc
  have hnonempty : ratioCube.Nonempty := by
    refine ⟨fun _ => (1 : ℝ) / 2, ?_⟩
    constructor <;> intro i <;> norm_num
  obtain ⟨x, hx⟩ :=
    Math.Schauder.schauder_fixed_point hconvex hcompact hnonempty ratioSelfMap
  exact ⟨x.1, x.2, congrArg Subtype.val hx⟩

/-! ## Turning a ratio fixed point into a singleton circulation -/

/-- A full coalition table extending the blocker's singleton table.  Only
singleton rows enter the circulation certificate. -/
def blockerWeight (S : Finset (Fin 4)) (who : Fin 4) : ℝ :=
  ∑ owner ∈ S, singletonReward who owner

@[simp] theorem blockerWeight_singleton (owner who : Fin 4) :
    blockerWeight {owner} who = singletonReward who owner := by
  simp [blockerWeight]

/-- The diagonal/rationality floor. -/
def blockerFloor (_who : Fin 4) : ℝ := 1

@[simp] theorem blockerWeight_diagonal (who : Fin 4) :
    blockerWeight {who} who = blockerFloor who := by
  simp [blockerFloor, singletonReward_diagonal]

/-- Exhaustion of the four cyclic phases. -/
theorem zmod_four_cases (l : ZMod 4) :
    l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by
  revert l
  decide

/-- Phase owners in the dynamically closing order `1,0,2,3`. -/
def blockerOwner (l : ZMod 4) : Fin 4 :=
  if l = 0 then 1 else if l = 1 then 0 else if l = 2 then 2 else 3

/-- A fixed point of `ratioMap` satisfies the four polynomial closing
equations used by the vertex calculation. -/
theorem ratio_fixedPoint_equations {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x) :
    x 0 * (3 - 2 * x 2 * x 3) = 1 ∧
    x 1 * (3 + x 0 * (1 - 3 * x 3)) = 1 ∧
    x 2 * (5 - x 1 * (2 * x 0 + 1)) = 2 ∧
    x 3 * (6 - x 2 * (2 * x 1 + 1)) = 3 := by
  have hden := ratioMap_denominators_pos hx
  have ha := congrFun hfix (0 : Fin 4)
  have hb := congrFun hfix (1 : Fin 4)
  have hc := congrFun hfix (2 : Fin 4)
  have hd := congrFun hfix (3 : Fin 4)
  norm_num [ratioMap] at ha hb hc hd
  simp only [vec4_apply_two] at hc
  simp only [vec4_apply_three] at hd
  field_simp [ne_of_gt hden.1] at ha
  field_simp [ne_of_gt hden.2.1] at hb
  field_simp [ne_of_gt hden.2.2.1] at hc
  field_simp [ne_of_gt hden.2.2.2] at hd
  constructor
  · nlinarith [ha]
  constructor
  · nlinarith [hb]
  constructor
  · nlinarith [hc]
  · nlinarith [hd]

/-- The four payoff vertices.  Subtracting the floor `1` displays the sparse
excess states found by the pinning calculation. -/
def blockerVertex (x : Fin 4 → ℝ) (l : ZMod 4) : Fin 4 → ℝ :=
  if l = 0 then
    ![1 + (1 - x 0) / (3 * x 0), 1, 1 + (1 - x 3), 1]
  else if l = 1 then
    ![1, 1, 1 + (1 - x 1) / (3 * x 1), 1 + 2 * (1 - x 0) / 3]
  else if l = 2 then
    ![1, 1 + 2 * (1 - x 1) / 3, 1, 1 + 2 * (1 - x 2) / (3 * x 2)]
  else
    ![1 + 2 * (1 - x 2) / 3, 1 + (1 - x 3) / x 3, 1, 1]

/-- The corresponding phase ratio. -/
def blockerRatio (x : Fin 4 → ℝ) (l : ZMod 4) : ℝ :=
  if l = 0 then x 0 else if l = 1 then x 1 else if l = 2 then x 2 else x 3

theorem blockerRatio_pos {x : Fin 4 → ℝ} (hx : x ∈ ratioCube) (l : ZMod 4) :
    0 < blockerRatio x l := by
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [blockerRatio] <;>
    linarith [h0.1, h1.1, h2.1, h3.1]

theorem blockerRatio_lt_one {x : Fin 4 → ℝ} (hx : x ∈ ratioCube) (l : ZMod 4) :
    blockerRatio x l < 1 := by
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [blockerRatio] <;>
    linarith [h0.2, h1.2, h2.2, h3.2]

/-- Every ideal vertex lies above the diagonal floor. -/
theorem blockerVertex_ge_floor {x : Fin 4 → ℝ} (hx : x ∈ ratioCube)
    (l : ZMod 4) (who : Fin 4) :
    blockerFloor who ≤ blockerVertex x l who := by
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  have hp0 : 0 < x 0 := by linarith [h0.1]
  have hp1 : 0 < x 1 := by linarith [h1.1]
  have hp2 : 0 < x 2 := by linarith [h2.1]
  have hp3 : 0 < x 3 := by linarith [h3.1]
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;> fin_cases who <;>
    simp +decide [blockerFloor, blockerVertex]
  all_goals
    first
    | exact div_nonneg (by linarith) (by positivity)
    | positivity
    | linarith

/-- The phase owner is pinned to its singleton diagonal at the phase vertex. -/
theorem blockerVertex_owner_pinned (x : Fin 4 → ℝ) (l : ZMod 4) :
    blockerVertex x l (blockerOwner l) =
      blockerWeight {blockerOwner l} (blockerOwner l) := by
  rw [blockerWeight_diagonal]
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [blockerVertex, blockerOwner, blockerFloor]

/-- The four sparse vertices obey the certificate's forward affine step.
Exactly four of the sixteen scalar identities use the fixed-point equations;
the remaining twelve are the pinning construction itself. -/
private theorem blockerVertex_step_zero {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x)
    (who : Fin 4) :
    blockerVertex x ((0 : ZMod 4) + 1) who =
      blockerRatio x 0 * blockerVertex x 0 who +
        (1 - blockerRatio x 0) * blockerWeight {blockerOwner 0} who := by
  have heq := ratio_fixedPoint_equations hx hfix
  have h0 := coord_bounds hx 0
  have h1 := coord_bounds hx 1
  have hp0 : 0 < x 0 := by linarith [h0.1]
  have hp1 : 0 < x 1 := by linarith [h1.1]
  fin_cases who <;>
    simp +decide [blockerVertex, blockerRatio, blockerOwner,
      singletonReward, excess] <;>
    field_simp [hp0.ne', hp1.ne'] <;>
    nlinarith [heq.1, heq.2.1]

private theorem blockerVertex_step_one {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x)
    (who : Fin 4) :
    blockerVertex x ((1 : ZMod 4) + 1) who =
      blockerRatio x 1 * blockerVertex x 1 who +
        (1 - blockerRatio x 1) * blockerWeight {blockerOwner 1} who := by
  have heq := ratio_fixedPoint_equations hx hfix
  have h1 := coord_bounds hx 1
  have h2 := coord_bounds hx 2
  have hp1 : 0 < x 1 := by linarith [h1.1]
  have hp2 : 0 < x 2 := by linarith [h2.1]
  fin_cases who <;>
    simp +decide [blockerVertex, blockerRatio, blockerOwner,
      singletonReward, excess] <;>
    field_simp [hp1.ne', hp2.ne'] <;>
    nlinarith [heq.2.1, heq.2.2.1]

private theorem blockerVertex_step_two {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x)
    (who : Fin 4) :
    blockerVertex x ((2 : ZMod 4) + 1) who =
      blockerRatio x 2 * blockerVertex x 2 who +
        (1 - blockerRatio x 2) * blockerWeight {blockerOwner 2} who := by
  have heq := ratio_fixedPoint_equations hx hfix
  have h2 := coord_bounds hx 2
  have h3 := coord_bounds hx 3
  have hp2 : 0 < x 2 := by linarith [h2.1]
  have hp3 : 0 < x 3 := by linarith [h3.1]
  fin_cases who <;>
    simp +decide [blockerVertex, blockerRatio, blockerOwner,
      singletonReward, excess] <;>
    field_simp [hp2.ne', hp3.ne'] <;>
    nlinarith [heq.2.2.1, heq.2.2.2]

private theorem blockerVertex_step_three {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x)
    (who : Fin 4) :
    blockerVertex x ((3 : ZMod 4) + 1) who =
      blockerRatio x 3 * blockerVertex x 3 who +
        (1 - blockerRatio x 3) * blockerWeight {blockerOwner 3} who := by
  have heq := ratio_fixedPoint_equations hx hfix
  have h0 := coord_bounds hx 0
  have h3 := coord_bounds hx 3
  have hp0 : 0 < x 0 := by linarith [h0.1]
  have hp3 : 0 < x 3 := by linarith [h3.1]
  fin_cases who <;>
    simp +decide [blockerVertex, blockerRatio, blockerOwner,
      singletonReward, excess] <;>
    field_simp [hp0.ne', hp3.ne'] <;>
    nlinarith [heq.1, heq.2.2.2]

theorem blockerVertex_step {x : Fin 4 → ℝ}
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x)
    (l : ZMod 4) (who : Fin 4) :
    blockerVertex x (l + 1) who =
      blockerRatio x l * blockerVertex x l who +
        (1 - blockerRatio x l) * blockerWeight {blockerOwner l} who := by
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl
  · exact blockerVertex_step_zero hx hfix who
  · exact blockerVertex_step_one hx hfix who
  · exact blockerVertex_step_two hx hfix who
  · exact blockerVertex_step_three hx hfix who

/-- A fixed ratio tuple packages into a genuine four-phase, point-mass
singleton-face circulation certificate. -/
def blockerCirculationOfFixedPoint (x : Fin 4 → ℝ)
    (hx : x ∈ ratioCube) (hfix : ratioMap x = x) :
    FaceCirculationCertificate blockerWeight blockerFloor 4 where
  vertex := blockerVertex x
  mixWeight := fun l who => if who = blockerOwner l then 1 else 0
  ratio := blockerRatio x
  mixWeight_nonneg := by
    intro l who
    split <;> norm_num
  mixWeight_sum := by
    intro l
    simp
  ratio_pos := blockerRatio_pos hx
  ratio_lt_one := blockerRatio_lt_one hx
  step := by
    intro l who
    simp only [mixTarget_single]
    exact blockerVertex_step hx hfix l who
  vertex_ge_floor := blockerVertex_ge_floor hx
  vertex_pinned := by
    intro l who hwho
    have howner : who = blockerOwner l := by
      by_contra hne
      simp [hne] at hwho
    subst howner
    exact blockerVertex_owner_pinned x l
  target_pinned := by
    intro l who hwho
    have howner : who = blockerOwner l := by
      by_contra hne
      simp [hne] at hwho
    subst howner
    rw [mixTarget_single]
  solo_le_floor := by
    intro who
    rw [blockerWeight_diagonal]

/-- A chosen exact tuple of blocker-cycle contraction ratios. -/
def fixedRatios : Fin 4 → ℝ :=
  Classical.choose exists_ratio_fixedPoint

theorem fixedRatios_mem_ratioCube : fixedRatios ∈ ratioCube :=
  (Classical.choose_spec exists_ratio_fixedPoint).1

theorem ratioMap_fixedRatios : ratioMap fixedRatios = fixedRatios :=
  (Classical.choose_spec exists_ratio_fixedPoint).2

/-- **Main four-player regression.**  The exact singleton table that blocks
every static complementary probability nevertheless admits a dynamic
four-phase singleton circulation. -/
def blockerCirculation :
    FaceCirculationCertificate blockerWeight blockerFloor 4 :=
  blockerCirculationOfFixedPoint fixedRatios
    fixedRatios_mem_ratioCube ratioMap_fixedRatios

/-- The certificate has literal one-owner phase support. -/
def blockerCirculationSupport : SingletonSupport blockerCirculation where
  owner := blockerOwner
  mixWeight_eq := fun _ => rfl

/-! ## Collision-independent extension -/

/-- The same circulation works for *any* full coalition table having the
blocker's four singleton rows.  Thus collision payoffs do not enter the
finite circulation geometry at all. -/
def blockerCirculationForExtension
    (r : Finset (Fin 4) → Fin 4 → ℝ)
    (hsingleton : ∀ owner who, r {owner} who = singletonReward who owner) :
    FaceCirculationCertificate r blockerFloor 4 where
  vertex := blockerVertex fixedRatios
  mixWeight := fun l who => if who = blockerOwner l then 1 else 0
  ratio := blockerRatio fixedRatios
  mixWeight_nonneg := by
    intro l who
    split <;> norm_num
  mixWeight_sum := by
    intro l
    simp
  ratio_pos := blockerRatio_pos fixedRatios_mem_ratioCube
  ratio_lt_one := blockerRatio_lt_one fixedRatios_mem_ratioCube
  step := by
    intro l who
    rw [mixTarget_single]
    change blockerVertex fixedRatios (l + 1) who =
      blockerRatio fixedRatios l * blockerVertex fixedRatios l who +
        (1 - blockerRatio fixedRatios l) * r {blockerOwner l} who
    rw [hsingleton]
    simpa using blockerVertex_step fixedRatios_mem_ratioCube
      ratioMap_fixedRatios l who
  vertex_ge_floor := blockerVertex_ge_floor fixedRatios_mem_ratioCube
  vertex_pinned := by
    intro l who hwho
    have howner : who = blockerOwner l := by
      by_contra hne
      simp [hne] at hwho
    subst howner
    rw [hsingleton]
    simpa using blockerVertex_owner_pinned fixedRatios l
  target_pinned := by
    intro l who hwho
    have howner : who = blockerOwner l := by
      by_contra hne
      simp [hne] at hwho
    subst howner
    rw [mixTarget_single]
  solo_le_floor := by
    intro who
    rw [hsingleton, singletonReward_diagonal]
    rfl

/-- Literal singleton support for every collision-payoff extension. -/
def blockerCirculationForExtensionSupport
    (r : Finset (Fin 4) → Fin 4 → ℝ)
    (hsingleton : ∀ owner who, r {owner} who = singletonReward who owner) :
    SingletonSupport (blockerCirculationForExtension r hsingleton) where
  owner := blockerOwner
  mixWeight_eq := fun _ => rfl

/-- Every blocker-cycle ratio is bounded by the rational cube endpoint. -/
theorem blockerCirculationForExtension_ratio_le
    (r : Finset (Fin 4) → Fin 4 → ℝ)
    (hsingleton : ∀ owner who, r {owner} who = singletonReward who owner)
    (l : ZMod 4) :
    (blockerCirculationForExtension r hsingleton).ratio l ≤ 7 / 10 := by
  have h0 := coord_bounds fixedRatios_mem_ratioCube 0
  have h1 := coord_bounds fixedRatios_mem_ratioCube 1
  have h2 := coord_bounds fixedRatios_mem_ratioCube 2
  have h3 := coord_bounds fixedRatios_mem_ratioCube 3
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [blockerCirculationForExtension, blockerRatio] <;>
    linarith [h0.2, h1.2, h2.2, h3.2]

/-- **Collision-independent one-active orbit.**  For every bounded full
quitting table extending the four singleton blocker rows, the exact cycle
discretises to singleton microsteps of arbitrarily small support error and
arbitrarily large cumulative quit mass.  Collision rewards enter only via
the harmless finite bound `M`, not via the cycle equations. -/
theorem exists_blockerOneActive_orbit_for_extension
    (r : Finset (Fin 4) → Fin 4 → ℝ)
    (hsingleton : ∀ owner who, r {owner} who = singletonReward who owner)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S who, |r S who| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    let C := blockerCirculationForExtension r hsingleton
    ∃ (N : ℕ) (β : ZMod 4 → ℝ) (word : ZMod 4 → ℕ → Fin 4), 0 < N ∧
      (∀ n who, multiActual C word β N (n + 1) who =
        oneStageNext r (multiRow word β N n) (multiActual C word β N n) who) ∧
      (∀ n, IsSupportPerfectRow r (multiRow word β N n)
        (multiActual C word β N n) ε) ∧
      (∀ n who, blockerFloor who - ε ≤ multiActual C word β N n who) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (multiRow word β N n)) := by
  dsimp only
  exact exists_multiCirculation_orbit_of_singletonSupport
    (blockerCirculationForExtension r hsingleton)
    (blockerCirculationForExtensionSupport r hsingleton)
    M hM0 hM (7 / 10)
    (blockerCirculationForExtension_ratio_le r hsingleton)
    (by norm_num) ε hε Q

/-- **Exact remaining boundary.**  Once an extension's actual punishment
values lie below the diagonal floor, the one-active blocker circulation
compiles all the way to a uniform-equilibrium payoff.  This assumption is
the only game-specific input left after fixing the singleton table and a
finite reward bound. -/
theorem blockerExtension_exists_uniformEquilibriumPayoff
    (r : Finset (Fin 4) → Fin 4 → ℝ)
    (hsingleton : ∀ owner who, r {owner} who = singletonReward who owner)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S who, |r S who| ≤ M)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ blockerFloor who) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff none payoff := by
  exact quittingGame_exists_uniformEquilibriumPayoff_of_singletonCirculation
    (blockerCirculationForExtension r hsingleton)
    (blockerCirculationForExtensionSupport r hsingleton)
    M hM0 hM (7 / 10)
    (blockerCirculationForExtension_ratio_le r hsingleton)
    (by norm_num) hpunishmentFloor

end FourPlayerBlockerCirculation
end GameTheory
