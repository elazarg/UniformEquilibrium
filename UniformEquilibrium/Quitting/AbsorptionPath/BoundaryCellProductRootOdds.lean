/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.IncidentCoalitionOdds
import UniformEquilibrium.Quitting.AbsorptionPath.WeakPathConvergence

/-!
# Product-root odds on absorption-path boundary cells

This module transfers the elementary incident-coalition odds estimate for a
product quitting root to a literal jump lying inside a unit-bounded
absorption-path boundary cell.
-/

noncomputable section

namespace GameTheory.QuittingAbsorptionPath

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A path jump's selected product root has exactly the normalized jump
coalition masses. -/
theorem absorptionPathJumpRoot_coalitionMass_eq_normalizedJump
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path.1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootCoalitionMass (absorptionPathJumpRoot path time) coalition.1 =
      pathJump path.1 time coalition / (1 - time) := by
  exact (absorptionPathJumpRoot_relation path htime coalition).symm

/-- A path jump's selected product root has total absorption equal to the
normalized total path jump. -/
theorem absorptionPathJumpRoot_absorption_eq_normalizedJumpTotal
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path time) =
      (pathTotal path.1 time - pathLeftTotal path.1 time) / (1 - time) := by
  rw [quittingRootAbsorptionMass_eq_sum_nonemptyCoalitionMass]
  simp_rw [absorptionPathJumpRoot_coalitionMass_eq_normalizedJump path htime]
  rw [← Finset.sum_div, ← pathTotal_sub_pathLeftTotal_eq_sum_pathJump]

/-- A jump inside a unit-bounded boundary cell has conditional absorption no
larger than the enclosing cell's conditional absorption. -/
theorem absorptionPathJumpRoot_absorption_le_boundaryCellAbsorption
    (path : AbsorptionPath (ι := ι))
    {start stop time : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1)
    (htime : time ∈ pathJumps path.1)
    (htimeCell : time ∈ Ico start stop) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path time) ≤
      pathCellAbsorption path.1 start stop := by
  have hstopMem : stop ∈ Icc (0 : ℝ) 1 :=
    hstopBoundary.elim And.left And.left
  have htimeOne : time < 1 := htimeCell.2.trans_le hstopMem.2
  have htotalLeStop : pathTotal path.1 time ≤ pathLeftTotal path.1 stop :=
    pathTotal_le_pathLeftTotal_of_lt path.1 htime.1 hstopMem htimeCell.2
  have hleftStart : pathLeftTotal path.1 start = start :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary
  have hleftStop : pathLeftTotal path.1 stop = stop :=
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary
  rw [absorptionPathJumpRoot_absorption_eq_normalizedJumpTotal path htime,
    pathLeftTotal_eq_of_mem_pathJumps path htime]
  unfold pathCellAbsorption
  rw [hleftStart, hleftStop]
  apply (div_le_div_iff₀ (sub_pos.mpr htimeOne)
    (sub_pos.mpr hstartOne)).2
  have hfactor : 0 ≤ (time - start) * (1 - stop) :=
    mul_nonneg (sub_nonneg.mpr htimeCell.1)
      (sub_nonneg.mpr hstopMem.2)
  nlinarith

/-- A product-root jump inside a unit-bounded boundary cell satisfies the
incident singleton estimate with the exact odds of the enclosing cell. -/
theorem pathJump_incidentCoalition_le_boundaryCellOdds_mul_singleton
    (path : AbsorptionPath (ι := ι))
    {start stop time : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1)
    (hcellHalf : pathCellAbsorption path.1 start stop ≤ 1 / 2)
    (htime : time ∈ pathJumps path.1)
    (htimeCell : time ∈ Ico start stop)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    pathJump path.1 time ⟨coalition,
        Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
      (pathCellAbsorption path.1 start stop /
          (1 - pathCellAbsorption path.1 start stop)) *
        pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ := by
  let p := pathCellAbsorption path.1 start stop
  have habsorption :
      quittingRootAbsorptionMass (absorptionPathJumpRoot path time) ≤ p :=
    absorptionPathJumpRoot_absorption_le_boundaryCellAbsorption path
      hstartBoundary hstopBoundary hstartOne htime htimeCell
  have hroot :=
    quittingRootIncidentCoalitionMass_le_absorptionOdds_mul_singleton
      (absorptionPathJumpRoot path time) hcellHalf habsorption
      coalition player hcard hplayer
  have hcoalitionNonempty : coalition.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)
  have hrelationCoalition := absorptionPathJumpRoot_relation path htime
    ⟨coalition, hcoalitionNonempty⟩
  have hrelationSingleton := absorptionPathJumpRoot_relation path htime
    ⟨{player}, Finset.singleton_nonempty player⟩
  have htimeLtOne : time < 1 :=
    htimeCell.2.trans_le (hstopBoundary.elim And.left And.left).2
  have hdiv :
      pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ /
            (1 - time) ≤
        (p / (1 - p)) *
          (pathJump path.1 time
            ⟨{player}, Finset.singleton_nonempty player⟩ /
              (1 - time)) := by
    rw [hrelationCoalition, hrelationSingleton]
    exact hroot
  calc
    pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ =
        (pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ /
          (1 - time)) * (1 - time) := by
      field_simp [ne_of_gt (sub_pos.mpr htimeLtOne)]
    _ ≤ ((p / (1 - p)) *
          (pathJump path.1 time
            ⟨{player}, Finset.singleton_nonempty player⟩ /
              (1 - time))) * (1 - time) :=
      mul_le_mul_of_nonneg_right hdiv (sub_pos.mpr htimeLtOne).le
    _ = (p / (1 - p)) *
        pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ := by
      field_simp [ne_of_gt (sub_pos.mpr htimeLtOne)]

/-- On a sufficiently small unit-bounded boundary cell, every nonsingleton
left-limit increment is bounded by the cell width times its absorption odds. -/
theorem leftValue_incidentCoalitionIncrement_le_boundaryCellWidth_mul_odds
    (path : AbsorptionPath (ι := ι))
    (hbounded : HasUnitBoundedTotalMass path)
    {start stop : ℝ}
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hstopBoundary : stop ∈ partitionBoundaryTimes path)
    (hstartStop : start < stop) (hstopOne : stop < 1)
    (hcellHalf : pathCellAbsorption path.1 start stop ≤ 1 / 2)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    path.1.leftValue stop
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ -
        path.1.leftValue start
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
      (pathCellAbsorption path.1 start stop /
          (1 - pathCellAbsorption path.1 start stop)) * (stop - start) := by
  let p := pathCellAbsorption path.1 start stop
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hstartMem : start ∈ Icc (0 : ℝ) 1 :=
    hstartBoundary.elim And.left And.left
  have hstopMem : stop ∈ Icc (0 : ℝ) 1 :=
    hstopBoundary.elim And.left And.left
  have hpNonneg : 0 ≤ p := by
    unfold p pathCellAbsorption
    exact div_nonneg
      (sub_nonneg.mpr (pathLeftTotal_mono path.1 hstartMem hstopMem
        hstartStop.le))
      (sub_nonneg.mpr (hstartStop.trans hstopOne).le)
  have hpLtOne : p < 1 := hcellHalf.trans_lt (by norm_num)
  have hoddsNonneg : 0 ≤ p / (1 - p) :=
    div_nonneg hpNonneg (sub_nonneg.mpr hpLtOne.le)
  have hjumpBound : ∀ time ∈ Ico start stop,
      pathJump path.1 time
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
        (p / (1 - p)) * pathJump path.1 time singleton := by
    intro time htime
    by_cases hjump : time ∈ pathJumps path.1
    · exact pathJump_incidentCoalition_le_boundaryCellOdds_mul_singleton path
        hstartBoundary hstopBoundary (hstartStop.trans hstopOne)
        hcellHalf hjump htime coalition player hcard hplayer
    · have hcoalitionZero : pathJump path.1 time
          ⟨coalition, Finset.card_pos.mp
            (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ = 0 := by
        by_contra hne
        exact hjump ⟨⟨hstartMem.1.trans htime.1,
          htime.2.le.trans hstopMem.2⟩, _, hne⟩
      rw [hcoalitionZero]
      exact mul_nonneg hoddsNonneg
        (pathJump_nonneg path.1
          ⟨hstartMem.1.trans htime.1, htime.2.le.trans hstopMem.2⟩ singleton)
  have hincident :=
    leftValue_incidentCoalitionIncrement_le_of_pathJump_bounds
      (ε := p / (1 - p)) path hbounded hoddsNonneg hstartMem hstopMem
        hstartStop coalition player hcard hjumpBound
  have hsingletonIncrement :
      path.1.leftValue stop singleton - path.1.leftValue start singleton ≤
        stop - start := by
    have hnonneg (other : {S : Finset ι // S.Nonempty}) :
        0 ≤ path.1.leftValue stop other - path.1.leftValue start other :=
      sub_nonneg.mpr <| path.1.leftValue_mono other hstartMem hstopMem
        hstartStop.le
    have hsingle := Finset.single_le_sum
      (fun other _ ↦ hnonneg other) (Finset.mem_univ singleton)
    calc
      path.1.leftValue stop singleton - path.1.leftValue start singleton ≤
          ∑ other, (path.1.leftValue stop other -
            path.1.leftValue start other) := hsingle
      _ = pathLeftTotal path.1 stop - pathLeftTotal path.1 start := by
        rw [Finset.sum_sub_distrib]
        rfl
      _ = stop - start := by
        rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary,
          pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary]
  exact hincident.trans <|
    mul_le_mul_of_nonneg_left hsingletonIncrement hoddsNonneg

end GameTheory.QuittingAbsorptionPath
