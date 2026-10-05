import UniformEquilibrium.Quitting.Classification.WeightedQuittingTrapReturn
import UniformEquilibrium.Quitting.Projective.ConvexReturnDomainSmoothDrift

/-! # Global weighted floors supply the canonical convex return theorem

The canonical region is an arbitrary intersection of valid halfspaces, not
asserted to be a finite polytope. Signed singleton levels are allowed in the
analytic theorem; continuity is needed on its sublevel domain and ambient
differentiability only on the singleton lower boundary.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingGlobalWeightedFloorSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Set (Payoff ι) :=
  quittingGlobalWeightedFloorBox reward bound ∩
    {point | ∃ player, point player ≤ quittingSoloReward reward player player}

theorem isClosed_quittingGlobalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) :
    IsClosed (quittingGlobalWeightedFloorBox reward bound) := by
  apply isClosed_Icc.inter
  have hclosed : IsClosed (⋂ weight : {weight // HasGlobalQuittingWeightedFloor reward weight},
      {point : Payoff ι | 0 ≤ ∑ player, weight.val player *
        (point player - reward (quittingSingletonTerminal player) player)}) := by
    apply isClosed_iInter
    intro weight
    apply isClosed_le continuous_const
    exact continuous_finsetSum Finset.univ fun player _ =>
      continuous_const.mul ((continuous_apply player).sub continuous_const)
  have hset : {point : Payoff ι | ∀ weight, HasGlobalQuittingWeightedFloor reward weight →
      0 ≤ ∑ player, weight player *
        (point player - reward (quittingSingletonTerminal player) player)} =
      ⋂ weight : {weight // HasGlobalQuittingWeightedFloor reward weight},
        {point : Payoff ι | 0 ≤ ∑ player, weight.val player *
          (point player - reward (quittingSingletonTerminal player) player)} := by
    ext point
    simp
  rw [← hset] at hclosed
  exact hclosed

theorem convex_quittingGlobalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) :
    Convex ℝ (quittingGlobalWeightedFloorBox reward bound) := by
  intro first hfirst last hlast a b ha hb hab
  refine ⟨(convex_Icc (fun _ : ι => -bound) (fun _ => bound))
    hfirst.1 hlast.1 ha hb hab, ?_⟩
  intro weight hfloor
  have hlinear : (∑ player, weight player *
      ((a • first + b • last) player - reward (quittingSingletonTerminal player) player)) =
      a * (∑ player, weight player *
        (first player - reward (quittingSingletonTerminal player) player)) +
      b * (∑ player, weight player *
        (last player - reward (quittingSingletonTerminal player) player)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro player _
    change weight player * (a * first player + b * last player -
      reward (quittingSingletonTerminal player) player) = _
    calc
      _ = weight player * (a * first player + b * last player -
          (a + b) * reward (quittingSingletonTerminal player) player) := by rw [hab, one_mul]
      _ = _ := by ring
  rw [hlinear]
  exact add_nonneg (mul_nonneg ha (hfirst.2 weight hfloor))
    (mul_nonneg hb (hlast.2 weight hfloor))

/-- The actual raw weighted tests supply both return premises internally.
No region, continuation annotation, strategy, or root selector is supplied. -/
theorem not_isQuittingFullExactRootPotential_of_weightedTrap_strictLeave
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hleavers : HasWeightedQuittingTrapLeavers reward (· < ·))
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential
      (quittingGlobalWeightedFloorSublevelDomain reward bound))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_convexReturnDomain hreward hbound
    (quittingGlobalWeightedFloorBox reward bound)
    (isClosed_quittingGlobalWeightedFloorBox reward bound)
    (convex_quittingGlobalWeightedFloorBox reward bound)
  · exact fun _ hpoint => hpoint.1
  · exact singletonUpperBox_subset_globalWeightedFloorBox reward bound
      (fun terminal player => (hreward terminal player).trans hbound.le)
  · intro tail hbox root hnash
    exact exactRootSuccessor_mem_globalWeightedFloorBox reward bound
      (fun terminal player => (hreward terminal player).trans hbound.le) tail hbox root hnash
  · intro tail htail root hnash hpositive
    exact exists_successor_le_singleton_of_weighted_strictLeave
      reward hleavers bound tail htail root hnash hpositive
  · exact hcontinuous
  · exact hdiff

end GameTheory
