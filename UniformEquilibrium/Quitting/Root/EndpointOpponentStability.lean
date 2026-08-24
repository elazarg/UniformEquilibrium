/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.RootPerturbation
import UniformEquilibrium.Quitting.Root.SuccessorCertificate

/-!
# Opponent-product stability of a quitting endpoint difference

Changing all opponent Bernoulli marginals changes each forced-action payoff
by at most twice the payoff bound times the sum of marginal total-variation
distances.  Applying this to both forced actions gives the corresponding
four-times-bound estimate for their difference.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Sum of Bernoulli total-variation distances over all opponents. -/
def quittingRootOpponentTVSum
    (first second : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ other ∈ Finset.univ.erase who, pmfTV (first other) (second other)

private theorem pmfTV_forcedProduct_le_opponentTVSum
    (first second : ι → PMF Bool) (who : ι) (action : Bool) :
    pmfTV
        (pmfPi (Function.update first who (PMF.pure action)))
        (pmfPi (Function.update second who (PMF.pure action))) ≤
      quittingRootOpponentTVSum first second who := by
  let old := Function.update first who (PMF.pure action)
  let new := Function.update second who (PMF.pure action)
  let opponents := Finset.univ.erase who
  have hreplace :
      (fun index => if index ∈ opponents then new index else old index) = new := by
    funext index
    by_cases hindex : index = who
    · subst index
      simp [opponents, old, new]
    · simp [opponents, old, new, hindex]
  have htv := pmfTV_pmfPi_replaceOn_le_sum old new opponents
  rw [hreplace] at htv
  change pmfTV
      (pmfPi (Function.update first who (PMF.pure action)))
      (pmfPi (Function.update second who (PMF.pure action))) ≤
    ∑ other ∈ Finset.univ.erase who, pmfTV (first other) (second other)
  refine htv.trans_eq ?_
  apply Finset.sum_congr rfl
  intro other hother
  have hne : other ≠ who := (Finset.mem_erase.mp hother).1
  simp [old, new, hne]

/-- The forced-Quit payoff is Lipschitz in the full opponent product row. -/
theorem abs_quittingRootQuitPayoff_sub_le_opponentTVSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (first second : ι → PMF Bool) (who : ι)
    {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound) :
    |quittingRootQuitPayoff reward tail first who -
        quittingRootQuitPayoff reward tail second who| ≤
      2 * bound * quittingRootOpponentTVSum first second who := by
  have hvariation := abs_expect_sub_le_two_mul_pmfTV
    (pmfPi (Function.update first who (PMF.pure true)))
    (pmfPi (Function.update second who (PMF.pure true)))
    (fun joint => quittingRootPayoff reward tail joint who)
    (fun joint =>
      abs_quittingRootPayoff_le reward tail hreward htail joint who)
  have htv := pmfTV_forcedProduct_le_opponentTVSum
    first second who true
  have hboundNonneg : 0 ≤ bound :=
    (abs_nonneg (tail who)).trans (htail who)
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  exact hvariation.trans
    (mul_le_mul_of_nonneg_left htv (by positivity))

/-- The forced-Continue payoff is Lipschitz in the full opponent product
row. -/
theorem abs_quittingRootContinuePayoff_sub_le_opponentTVSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (first second : ι → PMF Bool) (who : ι)
    {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound) :
    |quittingRootContinuePayoff reward tail first who -
        quittingRootContinuePayoff reward tail second who| ≤
      2 * bound * quittingRootOpponentTVSum first second who := by
  have hvariation := abs_expect_sub_le_two_mul_pmfTV
    (pmfPi (Function.update first who (PMF.pure false)))
    (pmfPi (Function.update second who (PMF.pure false)))
    (fun joint => quittingRootPayoff reward tail joint who)
    (fun joint =>
      abs_quittingRootPayoff_le reward tail hreward htail joint who)
  have htv := pmfTV_forcedProduct_le_opponentTVSum
    first second who false
  have hboundNonneg : 0 ≤ bound :=
    (abs_nonneg (tail who)).trans (htail who)
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  exact hvariation.trans
    (mul_le_mul_of_nonneg_left htv (by positivity))

/-- Changing all opponent marginals changes the Quit-minus-Continue endpoint
difference by at most `4 * bound` times their summed Bernoulli TV distance. -/
theorem abs_quittingRootEndpointDifference_sub_le_opponentTVSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (first second : ι → PMF Bool) (who : ι)
    {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound) :
    |quittingRootEndpointDifference reward tail first who -
        quittingRootEndpointDifference reward tail second who| ≤
      4 * bound * quittingRootOpponentTVSum first second who := by
  have hquit := abs_quittingRootQuitPayoff_sub_le_opponentTVSum
    reward tail first second who hreward htail
  have hcontinue := abs_quittingRootContinuePayoff_sub_le_opponentTVSum
    reward tail first second who hreward htail
  unfold quittingRootEndpointDifference
  calc
    |(quittingRootQuitPayoff reward tail first who -
          quittingRootContinuePayoff reward tail first who) -
        (quittingRootQuitPayoff reward tail second who -
          quittingRootContinuePayoff reward tail second who)| =
        |(quittingRootQuitPayoff reward tail first who -
            quittingRootQuitPayoff reward tail second who) -
          (quittingRootContinuePayoff reward tail first who -
            quittingRootContinuePayoff reward tail second who)| := by ring_nf
    _ ≤ |quittingRootQuitPayoff reward tail first who -
          quittingRootQuitPayoff reward tail second who| +
        |quittingRootContinuePayoff reward tail first who -
          quittingRootContinuePayoff reward tail second who| := abs_sub _ _
    _ ≤ 2 * bound * quittingRootOpponentTVSum first second who +
        2 * bound * quittingRootOpponentTVSum first second who :=
      add_le_add hquit hcontinue
    _ = 4 * bound * quittingRootOpponentTVSum first second who := by ring

end GameTheory
