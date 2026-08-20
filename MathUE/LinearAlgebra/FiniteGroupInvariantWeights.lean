import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Tactic

/-!
# Finite-group invariant welfare weights

Orbit-summing a player weight makes it invariant.  Nonnegativity together
with positivity at one selected coordinate makes its orbit sum positive, and
a family of inequalities for all translated weights sums to the corresponding
inequality for the invariant orbit weight.
-/

noncomputable section

namespace Math.FiniteGroupInvariantWeights

open scoped BigOperators

variable {Gamma Player : Type}
  [Group Gamma] [Fintype Gamma] [MulAction Gamma Player]

/-- Unnormalized Reynolds sum of a player weight. -/
def orbitWeight (weight : Player → ℝ) (player : Player) : ℝ :=
  ∑ g : Gamma, weight (g • player)

/-- Right translation permutes the finite group, so the orbit weight is
invariant under the player action. -/
theorem orbitWeight_smul (weight : Player → ℝ)
    (h : Gamma) (player : Player) :
    orbitWeight (Gamma := Gamma) weight (h • player) =
      orbitWeight (Gamma := Gamma) weight player := by
  simpa [orbitWeight, mul_smul] using
    Fintype.sum_bijective (fun g : Gamma => g * h)
      (Group.mulRight_bijective h)
      (fun g => weight (g • (h • player)))
      (fun g => weight (g • player)) (by simp [mul_smul])

/-- A weight nonnegative along `player`'s orbit and positive at `player` has
positive orbit sum at `player`. -/
theorem orbitWeight_pos (weight : Player → ℝ)
    (player : Player)
    (weight_nonneg : ∀ g : Gamma, 0 ≤ weight (g • player))
    (weight_pos : 0 < weight player) :
    0 < orbitWeight (Gamma := Gamma) weight player := by
  unfold orbitWeight
  apply Finset.sum_pos'
  · intro g g_mem
    exact weight_nonneg g
  · exact ⟨1, Finset.mem_univ 1, by simpa using weight_pos⟩

variable [Fintype Player]

/-- Weighted evaluation of a player-indexed vector. -/
def weightedValue (weight value : Player → ℝ) : ℝ :=
  ∑ player, weight player * value player

/-- Evaluation at the Reynolds-summed weight is the sum of evaluations at
all translated weights. -/
theorem weightedValue_orbitWeight (weight value : Player → ℝ) :
    weightedValue (orbitWeight (Gamma := Gamma) weight) value =
      ∑ g : Gamma,
        weightedValue (fun player => weight (g • player)) value := by
  simp only [weightedValue, orbitWeight, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Summing one cap for each translated weight gives the cap for the
invariant orbit weight. -/
theorem weightedValue_orbitWeight_le
    (weight value target : Player → ℝ) (error : ℝ)
    (translatedCaps : ∀ g : Gamma,
      weightedValue (fun player => weight (g • player)) value ≤
        weightedValue (fun player => weight (g • player)) target + error) :
    weightedValue (orbitWeight (Gamma := Gamma) weight) value ≤
      weightedValue (orbitWeight (Gamma := Gamma) weight) target +
        Fintype.card Gamma * error := by
  rw [weightedValue_orbitWeight, weightedValue_orbitWeight]
  calc
    (∑ g : Gamma,
        weightedValue (fun player => weight (g • player)) value) ≤
        ∑ g : Gamma,
          (weightedValue (fun player => weight (g • player)) target +
            error) :=
      Finset.sum_le_sum fun g _ => translatedCaps g
    _ = (∑ g : Gamma,
          weightedValue (fun player => weight (g • player)) target) +
        Fintype.card Gamma * error := by
      rw [Finset.sum_add_distrib]
      simp

end Math.FiniteGroupInvariantWeights
