import Mathlib

/-!
# Quantitative weighted-saturation defect

This is the finite-dimensional algebra behind Experiment E in
`ideas/CoalitionSecurityWelfareAssembly.md`.

If all coordinates except `i` lie at least `securityError` below their target,
and positive weighted total payoff exceeds weighted target by at most `slack`,
then coordinate `i` can exceed target by at most

`(slack + securityError * sum(other weights)) / weight i`.

Applied once to the assembled profile and once to a unilateral deviation, this
turns an imperfectly saturated welfare ceiling into explicit payoff-delivery
and exploitability bounds.  The statement is deliberately independent of the
game model; the stochastic-game inputs merely supply its two hypotheses.
-/

noncomputable section

namespace Experiments.WeightedSaturationDefect

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sharp coordinatewise consequence of an imperfect weighted ceiling. -/
theorem coordinate_excess_le
    (weight target payoff : ι → ℝ) (i : ι)
    (slack securityError : ℝ)
    (weight_pos : ∀ j, 0 < weight j)
    (lowerOthers : ∀ j, j ≠ i → target j - securityError ≤ payoff j)
    (weightedCap :
      (∑ j, weight j * payoff j) ≤
        (∑ j, weight j * target j) + slack) :
    payoff i - target i ≤
      (slack + securityError * ∑ j ∈ Finset.univ.erase i, weight j) /
        weight i := by
  let others : Finset ι := Finset.univ.erase i
  have othersTarget_le :
      (∑ j ∈ others, weight j * target j) ≤
        (∑ j ∈ others, weight j * payoff j) +
          securityError * ∑ j ∈ others, weight j := by
    calc
      (∑ j ∈ others, weight j * target j) ≤
          ∑ j ∈ others,
            (weight j * payoff j + weight j * securityError) := by
        apply Finset.sum_le_sum
        intro j j_mem
        have j_ne_i : j ≠ i := Finset.ne_of_mem_erase j_mem
        have weighted :=
          mul_le_mul_of_nonneg_left (lowerOthers j j_ne_i)
            (weight_pos j).le
        nlinarith
      _ = (∑ j ∈ others, weight j * payoff j) +
            securityError * ∑ j ∈ others, weight j := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        ring
  have capSplit := weightedCap
  rw [← Finset.sum_erase_add
        (s := (Finset.univ : Finset ι))
        (f := fun j => weight j * payoff j)
        (a := i) (Finset.mem_univ i),
      ← Finset.sum_erase_add
        (s := (Finset.univ : Finset ι))
        (f := fun j => weight j * target j)
        (a := i) (Finset.mem_univ i)] at capSplit
  have weightedExcess :
      weight i * (payoff i - target i) ≤
        slack + securityError * ∑ j ∈ others, weight j := by
    dsimp only [others] at othersTarget_le
    linarith
  apply (le_div_iff₀ (weight_pos i)).2
  simpa [others, Finset.sum_erase, mul_comm] using weightedExcess

/-- If every on-path coordinate has its security floor, the weighted defect
gives an explicit (generally asymmetric) target interval. -/
theorem coordinate_mem_security_saturation_interval
    (weight target payoff : ι → ℝ) (i : ι)
    (slack securityError : ℝ)
    (weight_pos : ∀ j, 0 < weight j)
    (lower : ∀ j, target j - securityError ≤ payoff j)
    (weightedCap :
      (∑ j, weight j * payoff j) ≤
        (∑ j, weight j * target j) + slack) :
    target i - securityError ≤ payoff i ∧
      payoff i ≤ target i +
        (slack + securityError * ∑ j ∈ Finset.univ.erase i, weight j) /
          weight i := by
  constructor
  · exact lower i
  · have upperExcess := coordinate_excess_le weight target payoff i
      slack securityError weight_pos (fun j _ => lower j) weightedCap
    linarith

/-- Quantitative exploitability bound.  The deviating profile only needs the
security floors of the *nondeviators*, exactly as in the assembly argument. -/
theorem deviation_gain_le
    (weight target onPath deviating : ι → ℝ) (i : ι)
    (slack securityError : ℝ)
    (weight_pos : ∀ j, 0 < weight j)
    (onPathFloor : target i - securityError ≤ onPath i)
    (deviatingOthersFloor :
      ∀ j, j ≠ i → target j - securityError ≤ deviating j)
    (deviatingWeightedCap :
      (∑ j, weight j * deviating j) ≤
        (∑ j, weight j * target j) + slack) :
    deviating i - onPath i ≤
      (slack + securityError * ∑ j ∈ Finset.univ.erase i, weight j) /
          weight i +
        securityError := by
  have deviatingExcess := coordinate_excess_le
    weight target deviating i slack securityError weight_pos
      deviatingOthersFloor deviatingWeightedCap
  linarith

end Experiments.WeightedSaturationDefect
