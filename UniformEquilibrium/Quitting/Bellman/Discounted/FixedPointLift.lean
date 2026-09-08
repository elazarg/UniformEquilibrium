import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement
import UniformEquilibrium.Quitting.Bellman.Discounted.PayoffBridge
import UniformEquilibrium.VanishingDiscount.Bellman.Variety

/-!

# Complete Bellman assignments at each supplied discounted quitting fixed point

The live root, discount complement, and supplied live value are retained literally.
Absorbed-state actions are fixed to Continue and absorbed values are the original
rewards. No fixed point, subsequence, endpoint, or auxiliary reward table is selected.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every fixed point satisfies actual zero-regret root inequalities at its live value. -/
theorem isQuittingRootEndpointNash_of_discountedClippedMap_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool)
    (hfixed : quittingDiscountedClippedMap reward discountComplement (hazardOfRoot root) =
      hazardOfRoot root) :
    IsεQuittingRootEndpointNash reward
      (quittingDiscountedLiveValue reward discountComplement root) 0 root := by
  have hface := (quittingDiscountedClippedMap_eq_self_iff reward discountComplement
    (hazardOfRoot root) (hazardOfRoot_nonneg root) (hazardOfRoot_le_one root)).mp hfixed
  have hden := quittingDiscountedDenominator_pos hpositive hdiscount root
  intro who
  have hid := quittingDiscountedDenominator_mul_endpointDifference
    reward hpositive hdiscount root who
  change (root who false).toReal * _ ≤ 0 ∧ -0 ≤ (root who true).toReal * _
  rw [Math.PMFProduct.pmfBool_false_toReal]
  change (1 - hazardOfRoot root who) * _ ≤ 0 ∧ -0 ≤ hazardOfRoot root who * _
  by_cases hzero : hazardOfRoot root who = 0
  · have hsign := (hface who).1 hzero
    have hgap : quittingRootEndpointDifference reward
        (quittingDiscountedLiveValue reward discountComplement root) root who ≤ 0 := by
      nlinarith
    simpa [hzero] using hgap
  by_cases hone : hazardOfRoot root who = 1
  · have hsign := (hface who).2.2 hone
    have hgap : 0 ≤ quittingRootEndpointDifference reward
        (quittingDiscountedLiveValue reward discountComplement root) root who := by
      nlinarith
    simpa [hone] using hgap
  have hsign := (hface who).2.1
    (lt_of_le_of_ne (hazardOfRoot_nonneg root who) (Ne.symm hzero))
    (lt_of_le_of_ne (hazardOfRoot_le_one root who) hone)
  have hgap : quittingRootEndpointDifference reward
      (quittingDiscountedLiveValue reward discountComplement root) root who = 0 := by
    nlinarith
  simp [hgap]

/-- The supplied live root, with immaterial absorbed actions fixed to Continue. -/
def quittingDiscountedLiftProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) :
    (quittingGame reward).StationaryMixedProfile :=
  fun state => match state with
    | none => root
    | some _ => fun _ => PMF.pure false

/-- The supplied live payoff, completed by the original absorbing rewards. -/
def quittingDiscountedLiftValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (value : Payoff ι) :
    (quittingGame reward).State → Payoff ι :=
  fun state => match state with
    | none => value
    | some terminal => reward terminal

/-- Every supplied fixed point lifts to a full semantic Bellman equilibrium. -/
theorem isDiscountedStationaryBellmanEq_of_quittingClippedMap_eq_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (value : Payoff ι)
    (hvalue : value = quittingDiscountedLiveValue reward discountComplement root)
    (hfixed : quittingDiscountedClippedMap reward discountComplement (hazardOfRoot root) =
      hazardOfRoot root) :
    (quittingGame reward).IsDiscountedStationaryBellmanEq (1 - discountComplement)
      (quittingDiscountedLiftProfile reward root) (quittingDiscountedLiftValue reward value) := by
  subst value
  have hnash := (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
    (quittingDiscountedLiveValue reward discountComplement root) 0 root).mp
      (isQuittingRootEndpointNash_of_discountedClippedMap_eq_self
        reward hpositive hdiscount root hfixed)
  constructor
  · intro state who deviation
    cases state with
    | none =>
        rw [discountedAuxEU_quittingGame_none, discountedAuxEU_quittingGame_none]
        change (1 - discountComplement) * quittingRootExpectedPayoff reward
          (quittingDiscountedLiveValue reward discountComplement root)
          (Function.update root who deviation) who ≤
            (1 - discountComplement) * quittingRootExpectedPayoff reward
              (quittingDiscountedLiveValue reward discountComplement root) root who
        have hdeviation := hnash who deviation
        rw [add_zero] at hdeviation
        exact mul_le_mul_of_nonneg_left hdeviation (sub_nonneg.mpr hdiscount)
    | some terminal =>
        rw [discountedAuxEU_quittingGame_some, discountedAuxEU_quittingGame_some]
  · intro state who
    cases state with
    | none =>
        rw [discountedAuxEU_quittingGame_none]
        exact (quittingDiscountedLiveValue_eq_rootPayoff
          reward hpositive hdiscount root who).symm
    | some terminal =>
        rw [discountedAuxEU_quittingGame_some]
        simp only [quittingDiscountedLiftValue]
        ring

/-- The full polynomial assignment retaining all supplied live coordinates. -/
def quittingDiscountedBellmanAssignment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) (value : Payoff ι) :
    BellmanVar (quittingGame reward) → ℝ :=
  (quittingGame reward).bellmanAssignment
    (quittingDiscountedLiftProfile reward root) (quittingDiscountedLiftValue reward value)
      (1 - discountComplement)

/-- The complete polynomial Bellman system holds at each actual fixed point. -/
theorem isPolynomialBellmanSolution_quittingDiscountedBellmanAssignment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (value : Payoff ι)
    (hvalue : value = quittingDiscountedLiveValue reward discountComplement root)
    (hfixed : quittingDiscountedClippedMap reward discountComplement (hazardOfRoot root) =
      hazardOfRoot root) :
    (quittingGame reward).IsPolynomialBellmanSolution
      (quittingDiscountedBellmanAssignment reward discountComplement root value) :=
  (quittingGame reward).isPolynomialBellmanSolution_bellmanAssignment
    (isDiscountedStationaryBellmanEq_of_quittingClippedMap_eq_self
      reward hpositive hdiscount root value hvalue hfixed)

omit [DecidableEq ι] in
@[simp] theorem quittingDiscountedBellmanAssignment_discount
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) (value : Payoff ι) :
    quittingDiscountedBellmanAssignment reward discountComplement root value .disc =
      discountComplement := by
  change 1 - (1 - discountComplement) = discountComplement
  ring

omit [DecidableEq ι] in
@[simp] theorem quittingDiscountedBellmanAssignment_liveValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) (value : Payoff ι) (who : ι) :
    quittingDiscountedBellmanAssignment reward discountComplement root value (.val none who) =
      value who := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingDiscountedBellmanAssignment_liveQuit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) (value : Payoff ι) (who : ι) :
    quittingDiscountedBellmanAssignment reward discountComplement root value
      (.mix none who true) = hazardOfRoot root who := rfl

omit [DecidableEq ι] in
@[simp] theorem quittingDiscountedBellmanAssignment_absorbedValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (discountComplement : ℝ) (root : ι → PMF Bool) (value : Payoff ι)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    quittingDiscountedBellmanAssignment reward discountComplement root value
      (.val (some terminal) who) = reward terminal who := rfl

omit [DecidableEq ι] in
/-- All state-value coordinates retain the original reward bound. -/
theorem abs_quittingDiscountedLiftValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement M : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (root : ι → PMF Bool) (value : Payoff ι)
    (hvalue : value = quittingDiscountedLiveValue reward discountComplement root)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (state : (quittingGame reward).State) (who : ι) :
    |quittingDiscountedLiftValue reward value state who| ≤ M := by
  cases state with
  | none =>
      subst value
      exact abs_quittingDiscountedLiveValue_le reward hpositive hdiscount hreward root who
  | some terminal => exact hreward terminal who

/-- Literal real-hazard input version: every supplied cube fixed point has the
same discount, same live hazards, same supplied value, and original absorbing values. -/
theorem quittingDiscountedBellmanAssignment_of_hazard_fixedPoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {discountComplement : ℝ} (hpositive : 0 < discountComplement)
    (hdiscount : discountComplement ≤ 1) (hazard : ι → ℝ)
    (hzero : ∀ who, 0 ≤ hazard who) (hone : ∀ who, hazard who ≤ 1)
    (value : Payoff ι)
    (hvalue : value = quittingDiscountedLiveValue reward discountComplement
      (rootOfHazard hazard hzero hone))
    (hfixed : quittingDiscountedClippedMap reward discountComplement hazard = hazard) :
    let assignment := quittingDiscountedBellmanAssignment reward discountComplement
      (rootOfHazard hazard hzero hone) value
    (quittingGame reward).IsPolynomialBellmanSolution assignment ∧
      assignment .disc = discountComplement ∧
      (∀ who, assignment (.mix none who true) = hazard who) ∧
      (∀ who, assignment (.val none who) = value who) ∧
      (∀ terminal who, assignment (.val (some terminal) who) = reward terminal who) := by
  dsimp only
  refine ⟨isPolynomialBellmanSolution_quittingDiscountedBellmanAssignment
    reward hpositive hdiscount (rootOfHazard hazard hzero hone) value hvalue ?_,
    quittingDiscountedBellmanAssignment_discount _ _ _ _, ?_,
    fun _ => rfl, fun _ _ => rfl⟩
  · simpa using hfixed
  · intro who
    simp

end GameTheory
