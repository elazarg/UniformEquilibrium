/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculationOrbit

/-!
# The four-player circulation certificate at its stress point

This file checks a singleton-face circulation certificate for the four-player
cyclic weight at `(x, λ) = (2, 1)`.  Its solo row pays `1` to the quitter, `3`
to the next player, `x` to the opposite player, and `0` to the preceding
player.  The Lean development below uses only this fixed table and the
displayed vertices.

The certificate instantiates the singleton-orbit theorem of
`SingletonFaceCirculationOrbit.lean` on it. The downstream module
`QuittingCirculationUniformPayoffExamples.lean` verifies the formal
punishment-floor condition and compiles this certificate to a
uniform-equilibrium payoff.

## The transcribed data

At `x = 2`, `λ = 1`:

* the contraction ratio is `a = 1/2`;
* the initial vertex is `V^0 = (1, 2, 2, 1)`;
* the four singleton payoff rows `R^k`, the rotations of `R^0 = (1, 3, 2, 0)`
  under `ρ(v₀, v₁, v₂, v₃) = (v₃, v₀, v₁, v₂)`: `R^0 = (1,3,2,0)`,
  `R^1 = (0,1,3,2)`, `R^2 = (2,0,1,3)`, `R^3 = (3,2,0,1)`.
* the four cycle vertices `V^k = ρ^k V^0`: `V^0 = (1,2,2,1)`, `V^1 = (1,1,2,2)`,
  `V^2 = (2,1,1,2)`, `V^3 = (2,2,1,1)`, satisfying
  `V^k = (1 - a) R^k + a V^{k+1}`.  This identity is checked below by
  `norm_num` at every `k` with exact rational arithmetic.

`FaceCirculationCertificate.step` is stated *forward*
(`vertex (l+1) = ratio l * vertex l + (1 - ratio l) * mixTarget ...`), while
the displayed identity is naturally indexed *backward*.  The certificate reads
the cycle in reverse, `vertex l := V^{-l}`, with phase `l`'s owner set to the
label of coordinate `V^{-l-1}`.  The identities `V^k_k = V^{k+1}_k = 1` make
the owner pinning below hold on the nose.

## The floor

The floor used below is the constant `1`.  It equals every solo diagonal and
is proved to dominate every cycle vertex.  This file makes no min-max claim.
The downstream compiler instead proves directly that the actual punishment
value is at most this floor.

## Contents

* `stressWeight`: the cyclic weight at `(x, λ) = (2, 1)`, all sixteen rows.
* `stressFloor`, `stressVertex`, `stressOwner`: the floor and reversed cycle.
* `stressCirculation`: the `FaceCirculationCertificate`, with every step
  identity, floor bound, and pinning clause checked by `norm_num`.
* `stressCirculationSupport`: its point-mass presentation.
* `exists_stressCirculation_orbit`: the instantiated singleton-orbit theorem
  -- for every `ε > 0` and target quit mass `Q`, a rational discretization
  whose states obey the one-stage recursion, stay support-perfect at
  tolerance `ε`, stay above the floor forever, and whose quit mass exceeds
  `Q` on a finite prefix.

## What this does and does not give

What is machine-checked: the four singleton payoff rows and the four cycle
vertices exist as stated with exact rational coordinates; the closing
identities `V^k = (1-a) R^k + a V^{k+1}` hold on the nose at `a = 1/2`; the
floor `1` dominates every solo value and every vertex sits above it; the
phase owners are pinned on both the ideal vertex and the phase target; and,
from all of that through `SingletonFaceCirculationOrbit.lean`'s general
machinery, orbits of arbitrarily large prefix quit mass exist at this weight,
support-perfect at any prescribed tolerance, above the floor forever.  All of
this is first proved at the level of `L` (the game's live-state Bellman
recursion, `oneStageNext`). The downstream singleton-circulation compiler
turns the resulting path into a uniform-equilibrium payoff.

No exact min-max value is asserted here.  The formal cashout in
`QuittingCirculationUniformPayoffExamples.lean` proves that the actual
`quittingPunishmentValue` is at most the floor `1` from the general
`max (solo payoff) 0` bound, and then applies the singleton-circulation
compiler.
-/

noncomputable section

namespace GameTheory
namespace RepairedFourPlayerStress

open Finset Math.PMFProduct

/-- The four cyclic players. -/
abbrev Player := Fin 4

/-- **The cyclic weight at the stress point `(x, λ) = (2, 1)`**: the solo
row `r({i})` pays
`i ↦ 1, i+1 ↦ 3, i+2 ↦ x, i+3 ↦ 0`; adjacent pairs `r({i,i+1})` pay
`i ↦ 1+λ, i+1 ↦ 0`, both outsiders `↦ 1`; distance-two pairs pay both
outsiders `↦ 1`, both members `↦ 0`; triples pay the outsider `↦ 1`, all
three members `↦ 0`; the full set is the zero vector.  Specialized to
`x = 2`, `λ = 1`. -/
def stressWeight (S : Finset Player) : Player → ℝ :=
  match decide (0 ∈ S), decide (1 ∈ S), decide (2 ∈ S), decide (3 ∈ S) with
  | false, false, false, false => ![0, 0, 0, 0]
  | true, false, false, false => ![1, 3, 2, 0]
  | false, true, false, false => ![0, 1, 3, 2]
  | false, false, true, false => ![2, 0, 1, 3]
  | false, false, false, true => ![3, 2, 0, 1]
  | true, true, false, false => ![2, 0, 1, 1]
  | true, false, true, false => ![0, 1, 0, 1]
  | true, false, false, true => ![0, 1, 1, 2]
  | false, true, true, false => ![1, 2, 0, 1]
  | false, true, false, true => ![1, 0, 1, 0]
  | false, false, true, true => ![1, 1, 2, 0]
  | true, true, true, false => ![0, 0, 0, 1]
  | true, true, false, true => ![0, 0, 1, 0]
  | true, false, true, true => ![0, 1, 0, 0]
  | false, true, true, true => ![1, 0, 0, 0]
  | true, true, true, true => ![0, 0, 0, 0]

/-! ## The four singleton rows -/

theorem stressWeight_zero : stressWeight {0} = ![1, 3, 2, 0] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_one : stressWeight {1} = ![0, 1, 3, 2] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_two : stressWeight {2} = ![2, 0, 1, 3] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

theorem stressWeight_three : stressWeight {3} = ![3, 2, 0, 1] := by
  funext i; fin_cases i <;> simp +decide [stressWeight]

/-- The solo diagonal `d_i` is `1` at every coordinate: read off directly
from the table, not from any min-max computation. -/
theorem stressWeight_diagonal (i : Player) : stressWeight {i} i = 1 := by
  fin_cases i <;>
    simp [stressWeight_zero, stressWeight_one, stressWeight_two, stressWeight_three]

/-- Every entry of the table has absolute value at most `3`. -/
theorem abs_stressWeight_le_three (S : Finset Player) (j : Player) :
    |stressWeight S j| ≤ 3 := by
  by_cases h0 : (0 : Player) ∈ S <;> by_cases h1 : (1 : Player) ∈ S <;>
    by_cases h2 : (2 : Player) ∈ S <;> by_cases h3 : (3 : Player) ∈ S <;>
    fin_cases j <;> simp [stressWeight, h0, h1, h2, h3] <;> norm_num

/-! ## The floor -/

/-- The rationality floor at the stress point: the constant `1`.  It equals
the solo diagonal `d_i` exactly (`stressWeight_diagonal`).  The downstream
compiler proves the required punishment-value bound directly. -/
def stressFloor : Player → ℝ := fun _ => 1

theorem stressWeight_solo_le_floor (j : Player) : stressWeight {j} j ≤ stressFloor j := by
  rw [stressWeight_diagonal, stressFloor]

/-! ## The reversed cycle of §4.1 -/

/-- The four phases of `ZMod 4`. -/
theorem zmod_four_cases (t : ZMod 4) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by
  revert t; decide

/-- The owner of phase `l`, reading the displayed cycle backwards: phase `l`
is owned by coordinate `3 - l`. -/
def stressOwner (l : ZMod 4) : Player :=
  if l = 0 then 3 else if l = 1 then 2 else if l = 2 then 1 else 0

/-- The ideal cycle of §4, equation (39), at `a = 1/2`: `V^0 = (1,2,2,1)`,
`V^1 = (1,1,2,2)`, `V^2 = (2,1,1,2)`, `V^3 = (2,2,1,1)`, indexed so that
`stressVertex l = V^{-l}` -- the order the certificate's forward step needs,
matching the orbit file's "backward orbit convention" remark. -/
def stressVertex (l : ZMod 4) : Player → ℝ :=
  if l = 0 then ![1, 2, 2, 1]
  else if l = 1 then ![2, 2, 1, 1]
  else if l = 2 then ![2, 1, 1, 2]
  else ![1, 1, 2, 2]

/-- **The four step identities of equation (40)**, `V^k = (1-a) R^k +
a V^{k+1}` at `a = 1/2`, read through the reversed indexing: exact rational
arithmetic, `norm_num` throughout. -/
theorem stressVertex_step (l : ZMod 4) (j : Player) :
    stressVertex (l + 1) j =
      (1 / 2 : ℝ) * stressVertex l j + (1 - 1 / 2) * stressWeight {stressOwner l} j := by
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [stressVertex, stressOwner, stressWeight_zero, stressWeight_one,
      stressWeight_two, stressWeight_three] <;> norm_num

/-- **The floor bound of equation (42)**: every vertex of the cycle lies at
or above `1` at every coordinate. -/
theorem stressVertex_ge_floor (l : ZMod 4) (j : Player) :
    stressFloor j ≤ stressVertex l j := by
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [stressVertex, stressFloor]

/-- **The owner pinning of equation (43)**, `V^k_k = V^{k+1}_k = 1`: each
phase's owner sits at its own solo value on the ideal vertex. -/
theorem stressVertex_owner_pinned (l : ZMod 4) :
    stressVertex l (stressOwner l) = stressWeight {stressOwner l} (stressOwner l) := by
  rw [stressWeight_diagonal]
  rcases zmod_four_cases l with rfl | rfl | rfl | rfl <;>
    simp +decide [stressVertex, stressOwner]

/-! ## The certificate -/

/-- **The stress-point circulation certificate**: the cycle
`V^0 → V^3 → V^2 → V^1 → V^0`, with point-mass phase distributions, owners
`3, 2, 1, 0`, and every contraction ratio `a = 1/2`. -/
def stressCirculation :
    FaceCirculationCertificate stressWeight stressFloor 4 where
  vertex := stressVertex
  mixWeight := fun l k => if k = stressOwner l then 1 else 0
  ratio := fun _ => 1 / 2
  mixWeight_nonneg := by
    intro l j
    split <;> norm_num
  mixWeight_sum := by
    intro l
    simp
  ratio_pos := by intro l; norm_num
  ratio_lt_one := by intro l; norm_num
  step := by
    intro l j
    simp only [mixTarget_single]
    exact stressVertex_step l j
  vertex_ge_floor := stressVertex_ge_floor
  vertex_pinned := by
    intro l j hj
    have hjl : j = stressOwner l := by by_contra hcon; simp [hcon] at hj
    subst hjl
    exact stressVertex_owner_pinned l
  target_pinned := by
    intro l j hj
    have hjl : j = stressOwner l := by by_contra hcon; simp [hcon] at hj
    subst hjl
    rw [mixTarget_single]
  solo_le_floor := stressWeight_solo_le_floor

/-- The stress-point certificate, presented with its point-mass supports. -/
def stressCirculationSupport : SingletonSupport stressCirculation where
  owner := stressOwner
  mixWeight_eq := fun _ => rfl

/-! ## The instantiated orbit theorem -/

/-- **Orbits of arbitrarily large quit mass at the stress point `(2, 1)`.**
For every tolerance `ε > 0` and every target quit mass `Q` there is a
discretisation of the stress-point certificate whose every microstep row is
support-perfect at tolerance `ε` against its own state, whose every state
stays at or above the floor `1`, whose states obey the one-stage Bellman
recursion `oneStageNext`, and a finite prefix of which has quit mass at least
`Q`. This theorem records the live-state orbit itself; the downstream module
`QuittingCirculationUniformPayoffExamples.lean` verifies its strategic floor
and compiles the certificate to a uniform-equilibrium payoff. -/
theorem exists_stressCirculation_orbit (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod 4 → ℝ), 0 < N ∧
      (∀ n j, circulationState stressCirculationSupport β N (n + 1) j =
        oneStageNext stressWeight (circulationRow stressCirculationSupport β N n)
          (circulationState stressCirculationSupport β N n) j) ∧
      (∀ n, IsSupportPerfectRow stressWeight
        (circulationRow stressCirculationSupport β N n)
        (circulationState stressCirculationSupport β N n) ε) ∧
      (∀ n j, stressFloor j ≤
        circulationState stressCirculationSupport β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (circulationRow stressCirculationSupport β N n)) := by
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le (1 / 2) (by norm_num) (by norm_num) (ε / 6) (by linarith)
  have hratio : ∀ l : ZMod 4, (fun _ : ZMod 4 => b) l ^ N = stressCirculation.ratio l :=
    fun _ => hbN
  have hb1' : ∀ l : ZMod 4, (fun _ : ZMod 4 => b) l ≤ 1 := fun _ => hb1.le
  have hb0' : ∀ l : ZMod 4, 0 ≤ (fun _ : ZMod 4 => b) l := fun _ => hb0
  refine ⟨N, fun _ => b, hN, ?_, ?_, ?_, ?_⟩
  · exact fun n j => circulationState_succ stressCirculationSupport _ N hN hratio n j
  · exact fun n => isSupportPerfectRow_circulation stressCirculationSupport _ N hN hb0' hb1'
      hratio 3 (by norm_num) abs_stressWeight_le_three ε (fun _ => by linarith) n
  · exact fun n j => circulationState_ge_floor stressCirculationSupport _ N hN hb0' hb1'
      hratio n j
  · exact exists_prefix_quitMass_ge stressCirculationSupport _ N b (fun _ => le_rfl) hb1 Q

end RepairedFourPlayerStress
end GameTheory
