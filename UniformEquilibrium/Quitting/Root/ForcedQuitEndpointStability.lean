import UniformEquilibrium.Quitting.Root.EndpointOpponentStability

/-! # Endpoint stability after forcing one opponent to Quit -/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) {owner who : ι}
    (hne : who ≠ owner) (howner : root owner = PMF.pure true) :
    quittingRootEndpointDifference reward tail root who =
      quittingRootEndpointDifference reward 0 root who := by
  have hupdated (action : Bool) :
      Function.update root who (PMF.pure action) owner = PMF.pure true := by
    simp [Function.update_of_ne hne.symm, howner]
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingStationaryContinueMass_of_sureQuitter (hupdated true),
    quittingStationaryContinueMass_of_sureQuitter (hupdated false)]
  simp

/-- For a free player, forcing one opponent to Quit surely changes the
Quit-minus-Continue endpoint difference by at most four times the payoff bound
times the owner's Continue mass. -/
theorem abs_endpointDifference_forceSureOwner_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner who : ι)
    (hne : who ≠ owner) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound) :
    |quittingRootEndpointDifference reward tail
          (Function.update root owner (PMF.pure true)) who -
        quittingRootEndpointDifference reward tail root who| ≤
      4 * bound * (root owner false).toReal := by
  have hstability := abs_quittingRootEndpointDifference_sub_le_opponentTVSum
    reward tail (Function.update root owner (PMF.pure true)) root who hreward htail
  refine hstability.trans_eq ?_
  unfold quittingRootOpponentTVSum
  have hownerMem : owner ∈ Finset.univ.erase who := by simp [hne.symm]
  rw [Finset.sum_eq_single owner]
  · rw [Math.Probability.pmfTV_symm]
    simp
  · intro other hother hotherNe
    simp [Function.update_of_ne hotherNe]
  · exact fun hnot ↦ (hnot hownerMem).elim

/-- Exact root complementarity becomes the two genuine finite approximate
regret inequalities after forcing a nearly sure owner to Quit surely. -/
theorem forceSureOwner_weighted_endpoint_regrets
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (owner who : ι)
    (hne : who ≠ owner) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (htail : ∀ player, |tail player| ≤ bound)
    (hnash : IsεQuittingRootNash reward tail 0 root) :
    let forced := Function.update root owner (PMF.pure true)
    (root who false).toReal *
        quittingRootEndpointDifference reward 0 forced who ≤
          4 * bound * (root owner false).toReal ∧
      -(root who true).toReal *
        quittingRootEndpointDifference reward 0 forced who ≤
          4 * bound * (root owner false).toReal := by
  let forced := Function.update root owner (PMF.pure true)
  have htailScreen := quittingRootEndpointDifference_eq_zeroTail_of_sureOpponent
    reward tail forced hne (by simp [forced])
  have hclose := abs_endpointDifference_forceSureOwner_sub_le
    reward tail root owner who hne hreward htail
  have hendpoint :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).2
      hnash who
  have hfalse0 : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hfalse1 : (root who false).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by norm_num)).mpr
      (PMF.coe_le_one _ _) |>.trans_eq (by simp)
  have htrue0 : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have htrue1 : (root who true).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) (by norm_num)).mpr
      (PMF.coe_le_one _ _) |>.trans_eq (by simp)
  have hbound0 : 0 ≤ bound :=
    (abs_nonneg (tail who)).trans (htail who)
  dsimp only [forced]
  rw [← htailScreen]
  constructor <;> nlinarith [le_of_abs_le hclose, neg_le_of_abs_le hclose]

end GameTheory
