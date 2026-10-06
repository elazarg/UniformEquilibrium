import UniformEquilibrium.Quitting.Root.PairFullClippedJacobian

/-! # Actual proper pair roots on a dense annotation tie-avoidance domain

Indifference determines the candidate hazards and nonzero denominators.
The full inactive numerator then makes every inactive Nash gap strict,
including an unused player inside a larger premium core. The dense domain
comes from the checked coordinate-affine producer, not a strategic oracle.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingPairNash_second_probability_eq_ratio
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hjoining : quittingPairJoiningGap reward first second ≠ 0) :
    quittingPairHazardDenominator reward tail first second ≠ 0 ∧
      (secondLaw true).toReal =
        (tail first - reward (quittingSingletonTerminal first) first) /
          quittingPairHazardDenominator reward tail first second := by
  have hbalance := quittingPairJoiningGap_eq_survival_mul_denominator_of_pairNash
    reward tail hne firstLaw secondLaw hfirst hnash
  have hdenominator : quittingPairHazardDenominator reward tail first second ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hbalance
    exact hjoining hbalance
  refine ⟨hdenominator, (eq_div_iff hdenominator).mpr ?_⟩
  unfold quittingPairHazardDenominator at *
  nlinarith [hbalance]

theorem pairNash_inactive_gap_neg_of_numerator_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second player : ι} (hne : first ≠ second)
    (hfirstNe : player ≠ first) (hsecondNe : player ≠ second)
    (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hproduct : quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first ≠ 0)
    (hnumerator : quittingPairInactiveGapNumerator reward first second player tail ≠ 0) :
    quittingRootEndpointDifference reward tail
      (PairedCycle.root first second firstLaw secondLaw) player < 0 := by
  obtain ⟨hfirstDen, hsecondRatio⟩ := quittingPairNash_second_probability_eq_ratio
    reward tail hne firstLaw secondLaw hfirst hnash
      (left_ne_zero_of_mul hproduct)
  have hnashSwap : IsεQuittingRootNash reward tail 0
      (PairedCycle.root second first secondLaw firstLaw) := by
    rwa [← PairedCycle.root_swap hne firstLaw secondLaw]
  obtain ⟨hsecondDen, hfirstRatio⟩ := quittingPairNash_second_probability_eq_ratio
    reward tail hne.symm secondLaw firstLaw hsecond hnashSwap
      (right_ne_zero_of_mul hproduct)
  have hidentity := quittingPairInactiveGapNumerator_eq_mul_endpointDifference reward tail
    hne hfirstNe hsecondNe firstLaw secondLaw hfirstDen hsecondDen hfirstRatio hsecondRatio
  have hgapNonzero : quittingRootEndpointDifference reward tail
      (PairedCycle.root first second firstLaw secondLaw) player ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hidentity
    exact hnumerator hidentity
  have hgapNonpos := quittingRootEndpointDifference_nonpos_of_quitProbability_eq_zero
    reward tail (PairedCycle.root first second firstLaw secondLaw) player
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail _).mpr hnash)
      (by simp [PairedCycle.root_outside hfirstNe hsecondNe])
  exact lt_of_le_of_ne hgapNonpos hgapNonzero

theorem pairNash_hasFDerivAt_and_negative_det_of_numerator_avoidance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hproduct : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first)
    (havoid : ∀ player, player ≠ first → player ≠ second →
      quittingPairInactiveGapNumerator reward first second player tail ≠ 0) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)))
      (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)) ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det < 0 ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det ≠ 0 :=
  pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement reward tail hne
    firstLaw secondLaw hfirst hsecond hnash
    (fun player hfirstNe hsecondNe => pairNash_inactive_gap_neg_of_numerator_ne_zero
      reward tail hne hfirstNe hsecondNe firstLaw secondLaw hfirst hsecond hnash
        (ne_of_gt hproduct) (havoid player hfirstNe hsecondNe)) hproduct

def quittingPairTieAvoidanceDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pairs : Finset (ι × ι)) :
    Set (Payoff ι) :=
  {tail | ∀ pair ∈ pairs, ∀ player, player ≠ pair.1 → player ≠ pair.2 →
    quittingPairInactiveGapNumerator reward pair.1 pair.2 player tail ≠ 0}

private def PairTieConstraint (pairs : Finset (ι × ι)) :=
  {entry : (ι × ι) × ι // entry.1 ∈ pairs ∧ entry.2 ≠ entry.1.1 ∧ entry.2 ≠ entry.1.2}

private instance (pairs : Finset (ι × ι)) : Fintype (PairTieConstraint pairs) := by
  unfold PairTieConstraint
  infer_instance

omit [Fintype ι] in
private theorem quittingPairTieAvoidanceDomain_eq_iInter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pairs : Finset (ι × ι)) :
    quittingPairTieAvoidanceDomain reward pairs =
      ⋂ entry : PairTieConstraint pairs,
        {tail | quittingPairInactiveGapNumerator reward entry.val.1.1 entry.val.1.2
          entry.val.2 tail ≠ 0} := by
  ext tail
  simp only [quittingPairTieAvoidanceDomain, Set.mem_ofPred_eq, Set.mem_iInter]
  constructor
  · intro havoid entry
    exact havoid entry.val.1 entry.property.1 entry.val.2
      entry.property.2.1 entry.property.2.2
  · intro havoid pair hpair player hfirst hsecond
    exact havoid ⟨(pair, player), hpair, hfirst, hsecond⟩

theorem isOpen_quittingPairTieAvoidanceDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pairs : Finset (ι × ι)) :
    IsOpen (quittingPairTieAvoidanceDomain reward pairs) := by
  rw [quittingPairTieAvoidanceDomain_eq_iInter]
  apply isOpen_iInter_of_finite
  intro entry
  exact isOpen_ne.preimage (continuous_quittingPairInactiveGapNumerator reward _ _ _)

theorem dense_quittingPairTieAvoidanceDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pairs : Finset (ι × ι))
    (hproduct : ∀ pair ∈ pairs,
      quittingPairJoiningGap reward pair.1 pair.2 *
        quittingPairJoiningGap reward pair.2 pair.1 ≠ 0) :
    Dense (quittingPairTieAvoidanceDomain reward pairs) := by
  rw [quittingPairTieAvoidanceDomain_eq_iInter]
  exact dense_iInter_quittingPairInactiveGapNumerator_ne_zero reward
    (fun entry : PairTieConstraint pairs => entry.val.1.1)
    (fun entry => entry.val.1.2) (fun entry => entry.val.2)
    (fun entry => entry.property.2.1) (fun entry => entry.property.2.2)
    (fun entry => hproduct entry.val.1 entry.property.1)

end GameTheory
