/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.ReachableCarryTelescope

/-!
# State-preserving capacity on zero-boundary exact-D chronologies

This module takes the supremum of literal absorption over finite zero-boundary
exact-D chains. Prepending an exact Nash--Bellman predecessor remains in the
same family and adds exactly that predecessor root's absorption mass.

When the family is bounded above, every positive tolerance admits a finite
chronology with no exact bounded predecessor whose absorption reaches that
tolerance. Compactness is not used to assert that the infinite-horizon
supremum is attained.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {cutoff : ℕ}

/-- Total literal absorption along the preterminal edges of one finite
zero-boundary exact Nash--Bellman chain. -/
def quittingFiniteZeroBoundaryChainCharge
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) : ℝ :=
  ∑ time ∈ Finset.range cutoff,
    quittingRootAbsorptionMass
      (quittingFiniteNashBellmanPathRoots cutoff path time)

omit [DecidableEq ι] in
/-- Finite chain charge is nonnegative. -/
theorem quittingFiniteZeroBoundaryChainCharge_nonneg
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff) :
    0 ≤ quittingFiniteZeroBoundaryChainCharge cutoff path := by
  unfold quittingFiniteZeroBoundaryChainCharge
  apply Finset.sum_nonneg
  intro time _
  unfold quittingRootAbsorptionMass
  exact sub_nonneg.mpr
    (quittingStationaryContinueMass_le_one
      (quittingFiniteNashBellmanPathRoots cutoff path time))

/-- The intrinsic reversed admissible segment has exactly the sum of the
displayed roots' absorption masses on that segment. -/
theorem chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    ∀ (start fuel : ℕ) (hend : start + fuel ≤ cutoff),
      (quittingFiniteDynamicDebtAdmissibleReverseSegment
          path hpath hpunishment start fuel hend).chargeSum =
        ∑ offset ∈ Finset.range fuel,
          quittingRootAbsorptionMass
            (quittingFiniteNashBellmanPathRoots cutoff path (start + offset))
  | start, 0, hend => by
      simp [quittingFiniteDynamicDebtAdmissibleReverseSegment]
  | start, fuel + 1, hend => by
      simp only [quittingFiniteDynamicDebtAdmissibleReverseSegment]
      change quittingRootAbsorptionMass
            (quittingRootOfSimplex
              (quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path
                (start + fuel)).1.2) +
          (quittingFiniteDynamicDebtAdmissibleReverseSegment
            path hpath hpunishment start fuel (by omega)).chargeSum = _
      rw [chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
        path hpath hpunishment start fuel]
      rw [Finset.sum_range_succ]
      have hroot : quittingRootOfSimplex
            (quittingFiniteNashBellmanPathDynamicDebtPoint reward cutoff path
              (start + fuel)).1.2 =
          quittingFiniteNashBellmanPathRoots cutoff path (start + fuel) := by
        unfold quittingFiniteNashBellmanPathDynamicDebtPoint
        rw [dif_pos (by omega)]
        rw [quittingFiniteNashBellmanPathRoots, dif_pos (by omega)]
      rw [hroot]
      ring

/-- A bound on punishment-floor prefixes bounds every zero-boundary exact-D
chronology when the punishment vector is nonpositive. -/
theorem quittingFiniteZeroBoundaryChainCharge_le_prefixChargeBound
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hprefix : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ quittingPunishmentFloorPrefixChargeBound reward)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryChainCharge cutoff path ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  let segment := quittingFiniteDynamicDebtAdmissibleReverseSegment
    path hpath hpunishment 0 cutoff (by omega)
  have hcharge : segment.chargeSum =
      quittingFiniteZeroBoundaryChainCharge cutoff path := by
    simpa [segment, quittingFiniteZeroBoundaryChainCharge] using
      (chargeSum_quittingFiniteDynamicDebtAdmissibleReverseSegment
        path hpath hpunishment 0 cutoff (by omega))
  rw [← hcharge]
  rw [← QuittingPunishmentFloorAdmissibleChargedRelation.pathToFinitePrefix_charge]
  exact hprefix _

/-- The set of charges of all finite zero-boundary exact-D chronologies. -/
def quittingZeroBoundaryChronologyCharges
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Set ℝ :=
  {charge | ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
    path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      charge = quittingFiniteZeroBoundaryChainCharge cutoff path}

/-- State-preserving chronology capacity: the supremum of literal absorption
charges over all finite zero-boundary exact-D chains. -/
def quittingZeroBoundaryChronologyCapacity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ℝ :=
  sSup (quittingZeroBoundaryChronologyCharges reward)

/-- The chronology charge set is nonempty. -/
theorem quittingZeroBoundaryChronologyCharges_nonempty :
    (quittingZeroBoundaryChronologyCharges reward).Nonempty := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer reward 0
  refine ⟨0, 0, path,
    quittingFiniteZeroBoundaryNashBellmanDynamicDebtMinimizer_mem reward 0,
    ?_⟩
  simp [quittingFiniteZeroBoundaryChainCharge]

/-- A uniform punishment-floor prefix bound makes the chronology charge
family bounded above. -/
theorem quittingZeroBoundaryChronologyCharges_bddAbove
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (hprefix : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
      cert.charge ≤ quittingPunishmentFloorPrefixChargeBound reward) :
    BddAbove (quittingZeroBoundaryChronologyCharges reward) := by
  refine ⟨quittingPunishmentFloorPrefixChargeBound reward, ?_⟩
  rintro charge ⟨cutoff, path, hpath, rfl⟩
  exact quittingFiniteZeroBoundaryChainCharge_le_prefixChargeBound
    hpunishment hprefix cutoff path hpath

/-- Every member charge lies below the chronology capacity. -/
theorem quittingFiniteZeroBoundaryChainCharge_le_chronologyCapacity
    (hbounded : BddAbove (quittingZeroBoundaryChronologyCharges reward))
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff) :
    quittingFiniteZeroBoundaryChainCharge cutoff path ≤
      quittingZeroBoundaryChronologyCapacity reward := by
  exact le_csSup hbounded ⟨cutoff, path, hpath, rfl⟩

omit [DecidableEq ι] in
/-- Prepending one bounded exact predecessor adds exactly its root's
absorption mass to the chronology charge. -/
theorem quittingFiniteZeroBoundaryChainCharge_prependPoint
    (cutoff : ℕ) (predecessor : QuittingNashBellmanPoint ι)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    quittingFiniteZeroBoundaryChainCharge (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path) =
      quittingRootAbsorptionMass (quittingRootOfSimplex predecessor.2) +
        quittingFiniteZeroBoundaryChainCharge cutoff path := by
  unfold quittingFiniteZeroBoundaryChainCharge
  have hzero : quittingFiniteNashBellmanPathRoots (cutoff + 1)
        (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path) 0 =
      quittingRootOfSimplex predecessor.2 := by
    unfold quittingFiniteNashBellmanPathRoots
    rw [dif_pos (by omega)]
    rfl
  have hshift : (∑ time ∈ Finset.range cutoff,
        quittingRootAbsorptionMass
          (quittingFiniteNashBellmanPathRoots (cutoff + 1)
            (quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path)
            (time + 1))) =
      ∑ time ∈ Finset.range cutoff,
        quittingRootAbsorptionMass
          (quittingFiniteNashBellmanPathRoots cutoff path time) := by
    apply Finset.sum_congr rfl
    intro time htime
    rw [quittingFiniteNashBellmanPathRoots_prependPoint_shift]
  conv_lhs => rw [Finset.sum_range_succ']
  rw [hzero, hshift]
  ring

/-- Near-maximal chronology leaves less than `ε` absorption capacity for
every literal exact predecessor of its initial state. -/
theorem exists_nearMaximal_zeroBoundaryChronology
    (hbounded : BddAbove (quittingZeroBoundaryChronologyCharges reward))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cutoff : ℕ, ∃ path : QuittingFiniteNashBellmanPath ι cutoff,
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
      quittingZeroBoundaryChronologyCapacity reward - ε <
        quittingFiniteZeroBoundaryChainCharge cutoff path ∧
      ∀ predecessor : QuittingNashBellmanPoint ι,
        predecessor ∈ quittingNashBellmanBox (quittingRewardBound reward) →
        IsQuittingNashBellmanEdge reward predecessor (path 0) →
        quittingRootAbsorptionMass
          (quittingRootOfSimplex predecessor.2) < ε := by
  have hnonempty : (quittingZeroBoundaryChronologyCharges reward).Nonempty :=
    quittingZeroBoundaryChronologyCharges_nonempty
  have hlt : quittingZeroBoundaryChronologyCapacity reward - ε <
      quittingZeroBoundaryChronologyCapacity reward := by
    exact sub_lt_self _ hε
  obtain ⟨charge, ⟨cutoff, path, hpath, rfl⟩, hnear⟩ :=
    (lt_csSup_iff hbounded hnonempty).mp hlt
  refine ⟨cutoff, path, hpath, hnear, ?_⟩
  intro predecessor hpredecessor hedge
  let extended :=
    quittingFiniteNashBellmanPathPrependPoint cutoff predecessor path
  have hextended : extended ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward (cutoff + 1) :=
    quittingFiniteNashBellmanPathPrependPoint_mem reward cutoff path hpath
      predecessor hpredecessor hedge
  have hupper :=
    quittingFiniteZeroBoundaryChainCharge_le_chronologyCapacity
      hbounded (cutoff + 1) extended hextended
  rw [quittingFiniteZeroBoundaryChainCharge_prependPoint] at hupper
  linarith

end GameTheory
