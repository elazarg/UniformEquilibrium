import MathUE.Analysis.LowerBoxBoundarySmoothDrift
import UniformEquilibrium.Quitting.Classification.NonnegativeProductLowSupportPeelingConverse
import UniformEquilibrium.Quitting.Root.SingletonBoundaryExactRoot
import UniformEquilibrium.Quitting.Root.BoundedEndpoint
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # No differentiable global absorption drift under nonnegative product-low premiums -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Nonnegative product-low own premiums exclude every differentiable
potential with full absorption drift on all absorbing exact Nash edges in
a box strictly larger than the reward bound. Singleton levels may be signed;
continuous differentiability and convexity of the potential are not needed. -/
theorem not_differentiable_absorptionDrift_of_nonnegative_productLow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hlow : HasProductLowQuittingPremium reward)
    (rewardBound bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hbound : rewardBound < bound)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point, (∀ player, |point player| ≤ bound) →
      DifferentiableAt ℝ potential point)
    (hdrift : ∀ point, (∀ player, |point player| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward point 0 root →
        0 < quittingRootAbsorptionMass root →
          quittingRootAbsorptionMass root ≤
            potential point - potential (quittingRootSuccessorPayoff reward point root)) :
    False := by
  let singleton : Payoff ι := fun player => reward (quittingSingletonTerminal player) player
  have hrewardNonneg : 0 ≤ rewardBound :=
    (abs_nonneg (singleton (Classical.arbitrary ι))).trans (hreward _ _)
  have hboundPos : 0 < bound := hrewardNonneg.trans_lt hbound
  have htwo : 0 < 2 * bound := mul_pos (by norm_num) hboundPos
  have hboundReward : ∀ terminal player, |reward terminal player| ≤ bound :=
    fun terminal player => (hreward terminal player).trans hbound.le
  have hsingleton : ∀ player, |singleton player| < bound :=
    fun player => (hreward _ player).trans_lt hbound
  have hboundary : ∀ point, (∀ player, |point player| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward point 0 root →
        0 < quittingRootAbsorptionMass root →
          quittingRootSuccessorPayoff reward point root ∈
            Math.lowerBoxBoundary singleton (fun _ => bound) := by
    intro point hpoint root hnash hpositive
    obtain ⟨hlower, player, _, hbind⟩ :=
      exactRootSuccessor_mem_singletonLowerBoundary hnonnegative hlow point root hnash hpositive
    refine ⟨⟨hlower, fun player => ?_⟩, ⟨player, hbind⟩⟩
    exact (le_abs_self _).trans
      (abs_quittingRootExpectedPayoff_le_bound reward point root player hboundReward hpoint)
  apply Math.not_differentiable_lowerBoxBoundary_drift
    (fun _ => -bound) singleton (fun _ => bound) potential
    (fun player => (abs_lt.mp (hsingleton player)).1)
    (fun player => (abs_lt.mp (hsingleton player)).2)
    (fun point hpoint => hdiff point fun player =>
      abs_le.mpr ⟨hpoint.1 player, hpoint.2 player⟩)
    (1 / (2 * bound)) (div_pos (by norm_num) htwo)
  · intro point hpoint owner honly
    have howner : point owner = singleton owner := by
      obtain ⟨player, hbind⟩ := hpoint.2
      simpa [honly player hbind] using hbind
    have hother : ∀ other, other ≠ owner → singleton other < point other := by
      intro other hne
      apply lt_of_le_of_ne (hpoint.1.1 other)
      intro heq
      exact hne (honly other heq.symm)
    obtain ⟨root, hnash, hpositive⟩ :=
      exists_absorbing_exactRoot_of_unique_singleton_binding reward point owner howner hother
    have hbox : ∀ player, |point player| ≤ bound := by
      intro player
      exact abs_le.mpr ⟨(abs_lt.mp (hsingleton player)).1.le.trans
        (hpoint.1.1 player), hpoint.1.2 player⟩
    refine ⟨quittingRootSuccessorPayoff reward point root,
      hboundary point hbox root hnash hpositive, ?_⟩
    have hdecrease := hdrift point hbox root hnash hpositive
    linarith
  · intro point hpoint player hbelow
    have hbox : ∀ player, |point player| ≤ bound :=
      fun player => abs_le.mpr ⟨hpoint.1 player, hpoint.2 player⟩
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) point
    have hlower : singleton player ≤ quittingRootSuccessorPayoff reward point root player :=
      (quittingSingletonReward_le_rootQuitPayoff_of_nonnegativePremium
        hnonnegative point root player).trans
          (quittingRootQuitPayoff_le_successor_of_isZeroNash reward point root player hnash)
    have hmove := abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
      reward point root player bound hboundReward (hbox player)
    have hchargeBound : singleton player - point player ≤
        2 * bound * quittingRootAbsorptionMass root := by
      have hle := le_abs_self (quittingRootSuccessorPayoff reward point root player - point player)
      linarith
    have hpositive : 0 < quittingRootAbsorptionMass root := by
      have hnonneg := quittingRootAbsorptionMass_nonneg root
      nlinarith
    refine ⟨quittingRootSuccessorPayoff reward point root,
      hboundary point hbox root hnash hpositive, ?_⟩
    calc
      (1 / (2 * bound)) * (singleton player - point player) =
          (singleton player - point player) / (2 * bound) := by ring
      _ ≤ quittingRootAbsorptionMass root := (div_le_iff₀ htwo).mpr (by
        nlinarith [hchargeBound])
      _ ≤ potential point - potential (quittingRootSuccessorPayoff reward point root) :=
        hdrift point hbox root hnash hpositive

/-- The finite weak support-peeling criterion supplies the product-low input
to smooth drift exclusion. This is the signed-singleton auxiliary theorem,
not a restriction on the main signed-premium equilibrium class. -/
theorem not_differentiable_absorptionDrift_of_nonnegative_weakSupportPeeling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnonnegative : HasNonnegativeOwnQuittingPremium reward)
    (hpeeling : HasWeakQuittingPremiumSupportPeeling reward)
    (rewardBound bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ rewardBound)
    (hbound : rewardBound < bound)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point, (∀ player, |point player| ≤ bound) →
      DifferentiableAt ℝ potential point)
    (hdrift : ∀ point, (∀ player, |point player| ≤ bound) →
      ∀ root, IsεQuittingRootNash reward point 0 root →
        0 < quittingRootAbsorptionMass root →
          quittingRootAbsorptionMass root ≤
            potential point - potential (quittingRootSuccessorPayoff reward point root)) :
    False :=
  not_differentiable_absorptionDrift_of_nonnegative_productLow reward hnonnegative
    ((hasProductLowQuittingPremium_iff_weakSupportPeeling_of_nonnegative
      reward hnonnegative).mpr hpeeling)
    rewardBound bound hreward hbound potential hdiff hdrift

end GameTheory
