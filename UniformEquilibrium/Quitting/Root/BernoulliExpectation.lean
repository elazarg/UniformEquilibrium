import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import MathUE.PMFProduct.SmallHazardExpectation

/-!
# Actual root payoffs as finite Bernoulli expectations

The existing reward extension and literal root hazards identify the expected
payoff with the generic Bernoulli expectation, including its empty outcome.
The resulting singleton expansion retains separate tail and reward bounds.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Exact Bernoulli expectation of the supplied table, tail and product root. -/
theorem quittingRootExpectedPayoff_eq_smallHazardExpectation_weightOfReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootExpectedPayoff reward tail root who =
      smallHazardExpectation (fun coalition => weightOfReward reward coalition who)
        (tail who) (hazardOfRoot root) := by
  have hsum : quittingRootExpectedPayoff reward tail root who =
      ∑ coalition : Finset ι, coalitionMass (hazardOfRoot root) coalition *
        (if coalition.Nonempty then weightOfReward reward coalition who else tail who) := by
    unfold quittingRootExpectedPayoff
    have hroot : (fun i => if i ∈ Finset.univ then root i else PMF.pure false) = root := by
      funext i
      simp
    rw [← hroot]
    rw [expect_pmfPi_boolFamily_eq_sum_powerset'
      (t := Finset.univ) (q := root) (rest := fun _ => false)
      (k := fun action => quittingRootPayoff reward tail action who)]
    simp only [Finset.mem_univ, if_true, Finset.powerset_univ]
    apply Finset.sum_congr rfl
    intro coalition _
    have hquitters : quittingQuitters (fun i => decide (i ∈ coalition)) = coalition := by
      ext i
      simp [quittingQuitters]
    have haction : (fun i => if i ∈ coalition then true else false) =
        (fun i => decide (i ∈ coalition)) := by
      funext i
      by_cases hi : i ∈ coalition <;> simp [hi]
    rw [haction]
    by_cases hcoalition : coalition.Nonempty
    · have hreward : quittingRootPayoff reward tail
          (fun i => decide (i ∈ coalition)) who = weightOfReward reward coalition who := by
        unfold quittingRootPayoff weightOfReward
        rw [dif_pos (hquitters.symm ▸ hcoalition), dif_pos hcoalition]
        apply congrArg (fun terminal => reward terminal who)
        exact Subtype.ext hquitters
      rw [hreward, if_pos hcoalition]
      rfl
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hcoalition
      subst coalition
      simp [quittingRootPayoff, coalitionMass, hazardOfRoot]
  rw [hsum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (∅ : Finset ι))]
  simp only [Finset.not_nonempty_empty, if_false]
  unfold smallHazardExpectation
  congr 1
  · simp [coalitionMass, continueMass]
  · apply Finset.sum_congr rfl
    intro coalition hcoalition
    rw [if_pos (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hcoalition))]

/-- Uniform singleton expansion of the actual root, with separate box constants. -/
theorem abs_quittingRootExpectedPayoff_sub_singletonExpansion_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {K M : ℝ}
    (htail : |tail who| ≤ K) (hreward : ∀ terminal, |reward terminal who| ≤ M) :
    |quittingRootExpectedPayoff reward tail root who - tail who -
        ∑ owner, hazardOfRoot root owner *
          (reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who - tail who)| ≤
      (K / 2 + 3 * M / 2) * (∑ owner, hazardOfRoot root owner) ^ 2 := by
  have hK : 0 ≤ K := (abs_nonneg _).trans htail
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward ⟨{who}, Finset.singleton_nonempty who⟩)
  rw [quittingRootExpectedPayoff_eq_smallHazardExpectation_weightOfReward]
  have h := abs_smallHazardExpectation_sub_tail_sub_linearization_le
    (fun coalition => weightOfReward reward coalition who) (tail who)
    (hazardOfRoot root) hK hM htail
    (fun (coalition : Finset ι) (hcoalition : coalition.Nonempty) => by
      simpa [weightOfReward, hcoalition] using hreward ⟨coalition, hcoalition⟩)
    (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root)
  simpa [smallHazardLinearization, weightOfReward] using h

end GameTheory
