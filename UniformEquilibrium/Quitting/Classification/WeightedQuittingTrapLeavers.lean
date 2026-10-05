import UniformEquilibrium.Quitting.Root.FullCoalitionEndpointIdentities
import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaver

/-! # Global weighted floors and raw trap-leave tests

Each actual trap must admit the same weights for its global floor and leave
tests. The canonical invariant box intersects every globally floor-valid
nonnegative weighted halfspace, without selecting witnesses or strategies.
-/

noncomputable section

namespace GameTheory

open Set Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Inserted participant rewards are tested on every coalition, including
coalitions outside any designated trap and the empty coalition. -/
def quittingWeightedInsertedPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (coalition : Finset ι) : ℝ :=
  ∑ player, weight player *
    (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
      reward (quittingSingletonTerminal player) player)

def HasGlobalQuittingWeightedFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (weight : ι → ℝ) : Prop :=
  (∀ player, 0 ≤ weight player) ∧
    ∀ coalition, 0 ≤ quittingWeightedInsertedPremium reward weight coalition

/-- The nonempty-coalition leave sum uses only players absent from it. -/
def quittingWeightedLeaveSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (weight : ι → ℝ)
    (coalition : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ player ∈ active \ coalition.val, weight player *
    (reward ⟨insert player coalition.val, Finset.insert_nonempty _ _⟩ player -
      reward coalition player)

/-- Positive weights on the actual trap, zero outside, one global floor test,
and the same weights in every nonempty proper-subset leave comparison. -/
def HasWeightedQuittingTrapLeavers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (compare : ℝ → ℝ → Prop) : Prop :=
  ∀ active, IsQuittingPremiumTrap reward active →
    ∃ weight : ι → ℝ,
      (∀ player ∈ active, 0 < weight player) ∧
      (∀ player ∉ active, weight player = 0) ∧
      (∀ coalition, 0 ≤ quittingWeightedInsertedPremium reward weight coalition) ∧
      ∀ (coalition : Finset ι) (hnonempty : coalition.Nonempty),
        coalition ⊂ active → compare
          (quittingWeightedLeaveSum reward active weight ⟨coalition, hnonempty⟩) 0

/-- The invariant region is reward-defined, using all valid nonnegative
weight vectors, not an externally supplied continuation or return certificate. -/
def quittingGlobalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Set (Payoff ι) :=
  Icc (fun _ => -bound) (fun _ => bound) ∩
    {tail | ∀ weight, HasGlobalQuittingWeightedFloor reward weight →
      0 ≤ ∑ player, weight player *
        (tail player - reward (quittingSingletonTerminal player) player)}

/-- Full-product averaging preserves the global inserted-premium test for
arbitrary signed weights, without Nash, support, or normalization assumptions. -/
theorem quittingWeightedQuitPremium_eq_fullCoalitionAverage
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (weight : ι → ℝ) :
    (∑ player, weight player * (quittingRootQuitPayoff reward tail root player -
        reward (quittingSingletonTerminal player) player)) =
      ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
        quittingWeightedInsertedPremium reward weight coalition := by
  have hmass : (∑ coalition : Finset ι, quittingRootCoalitionMass root coalition) = 1 :=
    sum_coalitionMass (quittingRootQuitRates root)
  have hcoordinate : ∀ player,
      quittingRootQuitPayoff reward tail root player -
          reward (quittingSingletonTerminal player) player =
        ∑ coalition : Finset ι, quittingRootCoalitionMass root coalition *
          (reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player -
            reward (quittingSingletonTerminal player) player) := by
    intro player
    rw [quittingRootQuitPayoff_eq_sum_fullCoalitionMass]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
  simp_rw [hcoordinate, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coalition _
  rw [quittingWeightedInsertedPremium, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro player _
  ring

/-- The global floor test yields a weighted forced-Quit floor at all roots
and all continuation annotations, including zero and sure hazards. -/
theorem quittingWeightedQuitPremium_nonneg_of_globalFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (hfloor : HasGlobalQuittingWeightedFloor reward weight)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    0 ≤ ∑ player, weight player * (quittingRootQuitPayoff reward tail root player -
      reward (quittingSingletonTerminal player) player) := by
  rw [quittingWeightedQuitPremium_eq_fullCoalitionAverage]
  exact Finset.sum_nonneg fun coalition _ =>
    mul_nonneg (quittingRootCoalitionMass_nonneg root coalition) (hfloor.2 coalition)

/-- Exact Nash transfers every valid weighted Quit floor to the successor.
No floor at the source is required. -/
theorem exactRootSuccessor_globalWeightedFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (weight : ι → ℝ) (hfloor : HasGlobalQuittingWeightedFloor reward weight)
    (tail : Payoff ι) (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    0 ≤ ∑ player, weight player * (quittingRootSuccessorPayoff reward tail root player -
      reward (quittingSingletonTerminal player) player) := by
  apply (quittingWeightedQuitPremium_nonneg_of_globalFloor reward weight hfloor tail root).trans
  apply Finset.sum_le_sum
  intro player _
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_right
      (quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail root player hnash) _)
    (hfloor.1 player)

/-- Every boxed exact source returns to the canonical weighted-floor box,
even when the source violates its weighted floors. -/
theorem exactRootSuccessor_mem_globalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (tail : Payoff ι) (hbox : ∀ player, |tail player| ≤ bound)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root) :
    quittingRootSuccessorPayoff reward tail root ∈ quittingGlobalWeightedFloorBox reward bound := by
  refine ⟨⟨fun player => ?_, fun player => ?_⟩, ?_⟩
  · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound
      reward tail root player hreward hbox)).1
  · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound
      reward tail root player hreward hbox)).2
  · exact fun weight hfloor => exactRootSuccessor_globalWeightedFloor
      reward weight hfloor tail root hnash

/-- The whole singleton upper box satisfies every canonical weighted floor. -/
theorem singletonUpperBox_subset_globalWeightedFloorBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    Icc (fun player => reward (quittingSingletonTerminal player) player)
        (fun _ => bound) ⊆ quittingGlobalWeightedFloorBox reward bound := by
  intro tail htail
  refine ⟨⟨fun player => ?_, htail.2⟩, ?_⟩
  · exact (abs_le.mp (hreward _ player)).1.trans (htail.1 player)
  · intro weight hfloor
    exact Finset.sum_nonneg fun player _ =>
      mul_nonneg (hfloor.1 player) (sub_nonneg.mpr (htail.1 player))

end GameTheory
