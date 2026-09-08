import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import MathUE.Interval.UnitIntervalClip

/-!

# Actual discounted quitting displacement

The discount parameter is the complement of the usual discount factor. All
identities retain the supplied reward table and product root, including the
all-Continue root. This is the denominator and live-row algebra for a later
complete Bellman-assignment lift, not a fixed-point selection theorem.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The polynomial discounted displacement, using the existing coalition sums. -/
def quittingDiscountedDisplacement (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (hazard : ι → ℝ) (who : ι) : ℝ :=
  (1 - (1 - discountComplement) * continueMassExcl hazard who) *
    sigmaValue (weightOfReward reward) hazard who -
      excludedValue (weightOfReward reward) hazard who

/-- The denominator is positive at every product root for positive discount. -/
def quittingDiscountedDenominator (discountComplement : ℝ) (root : ι → PMF Bool) : ℝ :=
  1 - (1 - discountComplement) * quittingStationaryContinueMass root

/-- The normalized discounted live value, with absorbing stage rewards unchanged. -/
def quittingDiscountedLiveValue (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) : Payoff ι :=
  fun who => (1 - discountComplement) * quittingRootAbsorbingContribution reward root who /
    quittingDiscountedDenominator discountComplement root

omit [DecidableEq ι] in
theorem quittingDiscountedDenominator_eq
    (discountComplement : ℝ) (root : ι → PMF Bool) :
    quittingDiscountedDenominator discountComplement root =
      discountComplement + (1 - discountComplement) * quittingRootAbsorptionMass root := by
  unfold quittingDiscountedDenominator quittingRootAbsorptionMass
  ring

omit [DecidableEq ι] in
theorem discountComplement_le_quittingDiscountedDenominator
    {discountComplement : ℝ} (hdiscount : discountComplement ≤ 1)
    (root : ι → PMF Bool) :
    discountComplement ≤ quittingDiscountedDenominator discountComplement root := by
  rw [quittingDiscountedDenominator_eq]
  exact le_add_of_nonneg_right
    (mul_nonneg (sub_nonneg.mpr hdiscount) (quittingRootAbsorptionMass_nonneg root))

omit [DecidableEq ι] in
theorem quittingDiscountedDenominator_pos {discountComplement : ℝ}
    (hpositive : 0 < discountComplement) (hdiscount : discountComplement ≤ 1)
    (root : ι → PMF Bool) :
    0 < quittingDiscountedDenominator discountComplement root :=
  hpositive.trans_le (discountComplement_le_quittingDiscountedDenominator hdiscount root)

/-- The literal survival product splits off the supplied owner's marginal. -/
theorem quittingStationaryContinueMass_eq_hazard_split
    (root : ι → PMF Bool) (who : ι) :
    quittingStationaryContinueMass root =
      (1 - hazardOfRoot root who) * continueMassExcl (hazardOfRoot root) who := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp_rw [pmfBool_false_toReal]
  exact (Finset.mul_prod_erase Finset.univ
    (fun player => 1 - (root player true).toReal) (Finset.mem_univ who)).symm

/-- Actual one-step absorbing reward is the own-action mixture of existing sums. -/
theorem quittingRootAbsorbingContribution_eq_hazard_mixture
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootAbsorbingContribution reward root who =
      hazardOfRoot root who * sigmaValue (weightOfReward reward) (hazardOfRoot root) who +
        (1 - hazardOfRoot root who) *
          excludedValue (weightOfReward reward) (hazardOfRoot root) who := by
  change quittingRootSuccessorPayoff reward 0 root who = _
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    quittingRootQuitPayoff_eq_sigmaValue, quittingRootContinuePayoff_eq_gammaValue]
  simp [gammaValue, hazardOfRoot, pmfBool_false_toReal]

omit [DecidableEq ι] in
/-- Multiplying the value by its positive denominator recovers its actual numerator. -/
theorem quittingDiscountedDenominator_mul_liveValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (who : ι) :
    quittingDiscountedDenominator discountComplement root *
      quittingDiscountedLiveValue reward discountComplement root who =
        (1 - discountComplement) * quittingRootAbsorbingContribution reward root who := by
  exact mul_div_cancel₀ _ (ne_of_gt
    (quittingDiscountedDenominator_pos hpositive hdiscount root))

omit [DecidableEq ι] in
/-- Live Bellman consistency holds at every root, before any best-response conditions. -/
theorem quittingDiscountedLiveValue_eq_rootPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (who : ι) :
    quittingDiscountedLiveValue reward discountComplement root who =
      (1 - discountComplement) * quittingRootExpectedPayoff reward
        (quittingDiscountedLiveValue reward discountComplement root) root who := by
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  have h := quittingDiscountedDenominator_mul_liveValue reward hpositive hdiscount root who
  unfold quittingDiscountedDenominator at h
  nlinarith [h]

/-- Exact displacement identity: the excluded reward has coefficient minus one. -/
theorem quittingDiscountedDenominator_mul_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (who : ι) :
    quittingDiscountedDenominator discountComplement root *
      quittingRootEndpointDifference reward
        (quittingDiscountedLiveValue reward discountComplement root) root who =
      quittingDiscountedDisplacement reward discountComplement (hazardOfRoot root) who := by
  rw [quittingRootEndpointDifference, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue]
  have h := quittingDiscountedDenominator_mul_liveValue reward hpositive hdiscount root who
  rw [quittingRootAbsorbingContribution_eq_hazard_mixture] at h
  unfold quittingDiscountedDenominator at h ⊢
  rw [quittingStationaryContinueMass_eq_hazard_split root who] at h ⊢
  unfold gammaValue quittingDiscountedDisplacement
  nlinarith [congrArg (fun value => value * continueMassExcl (hazardOfRoot root) who) h]

omit [DecidableEq ι] in
/-- Bounded actual rewards give bounded discounted values uniformly over the whole cube. -/
theorem abs_quittingDiscountedLiveValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement M : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (root : ι → PMF Bool) (who : ι) :
    |quittingDiscountedLiveValue reward discountComplement root who| ≤ M := by
  have hM : 0 ≤ M := (abs_nonneg (reward ⟨{who}, Finset.singleton_nonempty who⟩ who)).trans
    (hreward _ who)
  have hden := quittingDiscountedDenominator_pos hpositive hdiscount root
  have hbound := abs_quittingRootAbsorbingContribution_le reward root who M hreward
  unfold quittingDiscountedLiveValue
  rw [abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hdiscount), abs_of_pos hden,
    div_le_iff₀ hden, quittingDiscountedDenominator_eq]
  nlinarith [mul_le_mul_of_nonneg_left hbound (sub_nonneg.mpr hdiscount)]

/-- The literal clipped displacement map; no fixed point has been selected. -/
def quittingDiscountedClippedMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (hazard : ι → ℝ) : ι → ℝ :=
  fun who => min 1 (max 0
    (hazard who + quittingDiscountedDisplacement reward discountComplement hazard who))

/-- The literal displacement is jointly continuous in discount and all hazards. -/
theorem continuous_quittingDiscountedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedDisplacement reward point.1 point.2 who := by
  exact ((continuous_const.sub ((continuous_const.sub continuous_fst).mul
    ((continuous_continueMassExcl who).comp continuous_snd))).mul
      ((continuous_sigmaValue (weightOfReward reward) who).comp continuous_snd)).sub
        ((continuous_excludedValue (weightOfReward reward) who).comp continuous_snd)

/-- The clipped map is jointly continuous, with no face-strictness assumption. -/
theorem continuous_quittingDiscountedClippedMap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous fun point : ℝ × (ι → ℝ) =>
      quittingDiscountedClippedMap reward point.1 point.2 := by
  apply continuous_pi
  intro who
  exact continuous_const.min (continuous_const.max
    (((continuous_apply who).comp continuous_snd).add
      (continuous_quittingDiscountedDisplacement reward who)))

/-- Pointwise equivalence for every supplied hazard vector in the closed cube. -/
theorem quittingDiscountedClippedMap_eq_self_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (hazard : ι → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1) :
    quittingDiscountedClippedMap reward discountComplement hazard = hazard ↔
      ∀ who,
        (hazard who = 0 →
          quittingDiscountedDisplacement reward discountComplement hazard who ≤ 0) ∧
        (0 < hazard who → hazard who < 1 →
          quittingDiscountedDisplacement reward discountComplement hazard who = 0) ∧
        (hazard who = 1 →
          0 ≤ quittingDiscountedDisplacement reward discountComplement hazard who) := by
  rw [funext_iff]
  exact forall_congr' fun who =>
    Math.UnitIntervalClip.clipped_unitInterval_add_eq_self_iff (hzero who) (hone who)

end GameTheory
