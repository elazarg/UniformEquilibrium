/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.LawTightCapNashSaturationHull

/-!
# Minimum level set of the law-tight cap--Nash saturation hull

This module packages debt minimizers of the law-tight saturation hull and its
minimum equality level set.  The word “face” is only descriptive terminology
for that level set; no convexity or convex-geometric face property is claimed.

Positive minimum debt forces all Continue to be the unique exact root against
the displayed cap at every point of the level set.  Off the level set, exact
cap--Nash absorption is bounded by relative debt excess, and the resulting
finite-chain estimates telescope.

These are carrier-level statements.  They do not supply a Fin4 adapter, a
source chronology, ancestry or timing, a behavioral realization, a strict
chamber consumer, or a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Set
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {origin : QuittingTerminalSemanticLawPoint ι}

/-- A point attaining the least total debt on the law-tight cap--Nash hull. -/
structure IsQuittingLawTightCapNashSaturationMinimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (origin minimum : QuittingTerminalSemanticLawPoint ι) : Prop where
  mem : minimum ∈ quittingLawTightCapNashSaturationHull reward origin
  debt_le : ∀ point ∈
      quittingLawTightCapNashSaturationHull reward origin,
    quittingTerminalSemanticDebtSum minimum.1 ≤
      quittingTerminalSemanticDebtSum point.1

/-- The minimum equality level set of the law-tight cap--Nash hull.  The word
`Face` is terminology only; no convexity is asserted. -/
def quittingLawTightCapNashSaturationMinimumFace
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (origin minimum : QuittingTerminalSemanticLawPoint ι) :
    Set (QuittingTerminalSemanticLawPoint ι) :=
  quittingLawTightCapNashSaturationHull reward origin ∩
    {point | quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalSemanticDebtSum minimum.1}

namespace IsQuittingLawTightCapNashSaturationMinimum

theorem minimum_mem_face
    {minimum : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum) :
    minimum ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum := by
  exact ⟨hminimum.mem, rfl⟩

theorem face_point_is_minimum
    {minimum point : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum) :
    IsQuittingLawTightCapNashSaturationMinimum reward origin point := by
  refine ⟨hpoint.1, ?_⟩
  intro candidate hcandidate
  rw [hpoint.2]
  exact hminimum.debt_le candidate hcandidate

/-- Every point on the minimum level set minimizes debt on its complete
terminal-outcome-law fibre inside the joint carrier. -/
theorem face_point_debt_le_sameLaw
    {minimum point : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum)
    (replacement : QuittingTerminalSemanticPair ι)
    (hreplacement : (replacement, point.2) ∈
      quittingTerminalSemanticLawCarrier reward) :
    quittingTerminalSemanticDebtSum point.1 ≤
      quittingTerminalSemanticDebtSum replacement := by
  by_cases hdebt : quittingTerminalSemanticDebtSum replacement ≤
      quittingTerminalSemanticDebtSum point.1
  · have hreplacementHull :=
      quittingLawTightCapNashSaturationHull_sameLaw_of_debt_le
        reward origin point hpoint.1 replacement hreplacement hdebt
    exact (hminimum.face_point_is_minimum hpoint).debt_le
      (replacement, point.2) hreplacementHull
  · exact le_of_lt (lt_of_not_ge hdebt)

end IsQuittingLawTightCapNashSaturationMinimum

theorem quittingLawTightCapNashSaturationMinimumFace_nonempty
    {minimum : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum) :
    (quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum).Nonempty :=
  ⟨minimum, hminimum.minimum_mem_face⟩

/-- The foundation minimizer packages as a hull minimum while retaining the
reviewed positive finite atom and exact debt-weighted cone. -/
theorem exists_quittingLawTightCapNashSaturationMinimum_retaining_atom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (debtFloor : ℝ) (hfloor_pos : 0 < debtFloor)
    (hfloor : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      debtFloor ≤ quittingTerminalSemanticDebtSum point.1)
    (origin : QuittingTerminalSemanticLawPoint ι)
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward)
    (coalition : {S : Finset ι // S.Nonempty})
    (hatom : 0 < origin.2 (some coalition)) :
    ∃ minimum : QuittingTerminalSemanticLawPoint ι,
      IsQuittingLawTightCapNashSaturationMinimum reward origin minimum ∧
      debtFloor ≤ quittingTerminalSemanticDebtSum minimum.1 ∧
      quittingTerminalSemanticDebtSum minimum.1 *
          origin.2 (some coalition) ≤
        quittingTerminalSemanticDebtSum origin.1 *
          minimum.2 (some coalition) ∧
      0 < minimum.2 (some coalition) := by
  obtain ⟨minimum, hmem, hminimum, hfloorMinimum, hcone, hminimumAtom⟩ :=
    exists_quittingLawTightCapNashSaturationHull_minimum_retaining_atom
      reward debtFloor hfloor_pos hfloor origin horigin coalition hatom
  exact ⟨minimum, ⟨hmem, hminimum⟩, hfloorMinimum, hcone, hminimumAtom⟩

theorem quittingLawTightCapNashSaturationMinimumFace_isClosed
    (minimum : QuittingTerminalSemanticLawPoint ι) :
    IsClosed (quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum) := by
  apply (quittingLawTightCapNashSaturationHull_isClosed reward origin).inter
  exact isClosed_eq
    (continuous_quittingTerminalSemanticDebtSum.comp continuous_fst)
    continuous_const

theorem quittingLawTightCapNashSaturationMinimumFace_isCompact
    (minimum : QuittingTerminalSemanticLawPoint ι)
    (horigin : origin ∈ quittingTerminalSemanticLawCarrier reward) :
    IsCompact (quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum) := by
  have hlevel : IsClosed {point : QuittingTerminalSemanticLawPoint ι |
      quittingTerminalSemanticDebtSum point.1 =
        quittingTerminalSemanticDebtSum minimum.1} :=
    isClosed_eq
      (continuous_quittingTerminalSemanticDebtSum.comp continuous_fst)
      continuous_const
  exact (quittingLawTightCapNashSaturationHull_isCompact
    reward origin horigin).inter_right hlevel

/-- The all-Continue root is the unique exact Nash root against the displayed
cap at every positive-debt point on the hull-minimum level set.  This says
nothing about Nash optimality against the prescribed payoff coordinate. -/
theorem quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue
    {minimum point : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum)
    (root : ι → PMF Bool) :
    IsεQuittingRootNash reward point.1.2 0 root ↔
      root = (quittingAllContinueRoot : ι → PMF Bool) := by
  have root_eq_allContinue
      (candidate : ι → PMF Bool)
      (hnash : IsεQuittingRootNash reward point.1.2 0 candidate) :
      candidate = (quittingAllContinueRoot : ι → PMF Bool) := by
    have hprefixed :=
      quittingLawTightCapNashSaturationHull_prefix_mem
        reward origin point hpoint.1 candidate hnash
    have hminimum_le := hminimum.debt_le _ hprefixed
    have hscale : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward candidate point.1) =
          quittingStationaryContinueMass candidate *
            quittingTerminalSemanticDebtSum point.1 := by
      unfold quittingTerminalSemanticDebtSum
      simp_rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
        point.1 candidate _ hnash]
      exact (Finset.mul_sum ..).symm
    have hpoint_debt : quittingTerminalSemanticDebtSum point.1 =
        quittingTerminalSemanticDebtSum minimum.1 := hpoint.2
    have hcontinue : quittingStationaryContinueMass candidate = 1 := by
      rw [hscale, hpoint_debt] at hminimum_le
      nlinarith [quittingStationaryContinueMass_le_one candidate]
    funext player
    have hpure :=
      eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcontinue player
    simpa only [quittingAllContinueRoot] using hpure
  constructor
  · exact root_eq_allContinue root
  · intro hroot
    obtain ⟨candidate, hnash⟩ :=
      exists_isZeroQuittingRootNash (reward := reward) point.1.2
    have hcandidate := root_eq_allContinue candidate hnash
    rw [hroot, ← hcandidate]
    exact hnash

/-- The unique all-Continue exact cap root fixes both the semantic point and
its time-forgetting terminal-outcome law. -/
theorem quittingLawTightCapNashSaturationMinimumFace_allContinue_prefix_eq
    {minimum point : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (hpoint : point ∈ quittingLawTightCapNashSaturationMinimumFace
      reward origin minimum) :
    (quittingTerminalSemanticPrefix reward quittingAllContinueRoot point.1,
      quittingTerminalOutcomeLawPrefix quittingAllContinueRoot point.2) =
        point := by
  have hnash : IsεQuittingRootNash reward point.1.2 0
      (quittingAllContinueRoot : ι → PMF Bool) :=
    (quittingLawTightCapNashSaturationMinimumFace_rootNash_iff_allContinue
      hminimum hminimum_pos hpoint quittingAllContinueRoot).2 rfl
  apply Prod.ext
  · exact
      (quittingTerminalSemanticPrefix_allContinue_eq_self_iff_isZeroNash_at_cap
        reward point.1).2 hnash
  · funext outcome
    cases outcome with
    | none => simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingAllContinueRoot,
        quittingAllContinueAction]
    | some terminal =>
      have hcard : 0 < terminal.val.card :=
        Finset.card_pos.mpr terminal.property
      simp [quittingTerminalOutcomeLawPrefix,
        quittingStationaryContinueMass, quittingRootCoalitionMass,
        quittingRootQuitRates, quittingAllContinueRoot,
        quittingAllContinueAction, Math.PMFProduct.coalitionMass,
        hcard.ne']

/-- Exact cap--Nash absorption at any hull point is bounded by its relative
debt excess above a supplied positive hull minimum. -/
theorem quittingLawTightCapNashSaturationHull_rootAbsorptionMass_le_debtExcess_div
    {minimum point : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (hpoint : point ∈ quittingLawTightCapNashSaturationHull reward origin)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward point.1.2 0 root) :
    quittingRootAbsorptionMass root ≤
      (quittingTerminalSemanticDebtSum point.1 -
        quittingTerminalSemanticDebtSum minimum.1) /
          quittingTerminalSemanticDebtSum point.1 := by
  have hprefixed := quittingLawTightCapNashSaturationHull_prefix_mem
    reward origin point hpoint root hnash
  have hminimum_le := hminimum.debt_le _ hprefixed
  have hpoint_pos : 0 < quittingTerminalSemanticDebtSum point.1 :=
    hminimum_pos.trans_le (hminimum.debt_le point hpoint)
  have hscale : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward root point.1) =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum point.1 := by
    unfold quittingTerminalSemanticDebtSum
    simp_rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      point.1 root _ hnash]
    exact (Finset.mul_sum ..).symm
  rw [hscale] at hminimum_le
  apply (le_div_iff₀ hpoint_pos).2
  unfold quittingRootAbsorptionMass
  nlinarith

/-- Every point in a finite literal exact cap--Nash prefix chain remains in
the law-tight saturation hull. -/
theorem quittingLawTightCapNashSaturationHull_prefixChain_point_mem
    (points : ℕ → QuittingTerminalSemanticLawPoint ι)
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ)
    (hpoint_zero : points 0 ∈
      quittingLawTightCapNashSaturationHull reward origin)
    (hnash : ∀ time, time < horizon →
      IsεQuittingRootNash reward (points time).1.2 0 (roots time))
    (hstep : ∀ time, time < horizon →
      points (time + 1) =
        (quittingTerminalSemanticPrefix reward (roots time) (points time).1,
          quittingTerminalOutcomeLawPrefix (roots time) (points time).2))
    {time : ℕ} (htime : time ≤ horizon) :
    points time ∈ quittingLawTightCapNashSaturationHull reward origin := by
  induction time with
  | zero => exact hpoint_zero
  | succ time ih =>
      have htime_lt : time < horizon := Nat.lt_of_succ_le htime
      have hprevious : points time ∈
          quittingLawTightCapNashSaturationHull reward origin :=
        ih (Nat.le_trans (Nat.le_succ time) htime)
      have hprefixed :=
        quittingLawTightCapNashSaturationHull_prefix_mem
          reward origin (points time) hprevious (roots time)
            (hnash time htime_lt)
      rw [hstep time htime_lt]
      exact hprefixed

/-- Exact cap--Nash absorption along a finite literal hull-prefix chain is
paid by the telescoping debt drop, with the positive hull minimum as rate. -/
theorem sum_quittingRootAbsorptionMass_le_hullDebtDrop_div_minimum
    {minimum : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (points : ℕ → QuittingTerminalSemanticLawPoint ι)
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ)
    (hpoint_zero : points 0 ∈
      quittingLawTightCapNashSaturationHull reward origin)
    (hnash : ∀ time, time < horizon →
      IsεQuittingRootNash reward (points time).1.2 0 (roots time))
    (hstep : ∀ time, time < horizon →
      points (time + 1) =
        (quittingTerminalSemanticPrefix reward (roots time) (points time).1,
          quittingTerminalOutcomeLawPrefix (roots time) (points time).2)) :
    ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time) ≤
      (quittingTerminalSemanticDebtSum (points 0).1 -
        quittingTerminalSemanticDebtSum (points horizon).1) /
          quittingTerminalSemanticDebtSum minimum.1 := by
  have hweighted : quittingTerminalSemanticDebtSum minimum.1 *
      (∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time)) ≤
      quittingTerminalSemanticDebtSum (points 0).1 -
        quittingTerminalSemanticDebtSum (points horizon).1 := by
    rw [Finset.mul_sum]
    have hpoints : ∀ time, time ≤ horizon →
        points time ∈ quittingLawTightCapNashSaturationHull reward origin :=
      fun _ htime =>
        quittingLawTightCapNashSaturationHull_prefixChain_point_mem
          points roots horizon hpoint_zero hnash hstep htime
    calc
      ∑ time ∈ Finset.range horizon,
          quittingTerminalSemanticDebtSum minimum.1 *
            quittingRootAbsorptionMass (roots time) ≤
        ∑ time ∈ Finset.range horizon,
          (quittingTerminalSemanticDebtSum (points time).1 -
            quittingTerminalSemanticDebtSum (points (time + 1)).1) := by
              apply Finset.sum_le_sum
              intro time htime
              have htime_lt : time < horizon :=
                Finset.mem_range.mp htime
              have hpoint := hpoints time htime_lt.le
              have hminimum_le := hminimum.debt_le (points time) hpoint
              have habsorption_nonneg :=
                quittingRootAbsorptionMass_nonneg (roots time)
              have hscale : quittingTerminalSemanticDebtSum
                  (points (time + 1)).1 =
                    quittingStationaryContinueMass (roots time) *
                      quittingTerminalSemanticDebtSum (points time).1 := by
                rw [hstep time htime_lt]
                unfold quittingTerminalSemanticDebtSum
                simp_rw [
                  quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
                    (points time).1 (roots time) _ (hnash time htime_lt)]
                exact (Finset.mul_sum ..).symm
              rw [hscale]
              unfold quittingRootAbsorptionMass at habsorption_nonneg ⊢
              nlinarith
      _ = quittingTerminalSemanticDebtSum (points 0).1 -
          quittingTerminalSemanticDebtSum (points horizon).1 := by
            exact Finset.sum_range_sub' _ _
  exact (le_div_iff₀ hminimum_pos).2 (by
    simpa [mul_comm] using hweighted)

/-- The finite-chain absorption budget is also bounded by the initial debt
excess above the hull minimum. -/
theorem sum_quittingRootAbsorptionMass_le_initialHullDebtExcess_div_minimum
    {minimum : QuittingTerminalSemanticLawPoint ι}
    (hminimum : IsQuittingLawTightCapNashSaturationMinimum
      reward origin minimum)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum.1)
    (points : ℕ → QuittingTerminalSemanticLawPoint ι)
    (roots : ℕ → ι → PMF Bool) (horizon : ℕ)
    (hpoint_zero : points 0 ∈
      quittingLawTightCapNashSaturationHull reward origin)
    (hnash : ∀ time, time < horizon →
      IsεQuittingRootNash reward (points time).1.2 0 (roots time))
    (hstep : ∀ time, time < horizon →
      points (time + 1) =
        (quittingTerminalSemanticPrefix reward (roots time) (points time).1,
          quittingTerminalOutcomeLawPrefix (roots time) (points time).2)) :
    ∑ time ∈ Finset.range horizon,
        quittingRootAbsorptionMass (roots time) ≤
      (quittingTerminalSemanticDebtSum (points 0).1 -
        quittingTerminalSemanticDebtSum minimum.1) /
          quittingTerminalSemanticDebtSum minimum.1 := by
  have hdrop :=
    sum_quittingRootAbsorptionMass_le_hullDebtDrop_div_minimum
      hminimum hminimum_pos points roots horizon hpoint_zero hnash hstep
  have hpoint_horizon : points horizon ∈
      quittingLawTightCapNashSaturationHull reward origin :=
    quittingLawTightCapNashSaturationHull_prefixChain_point_mem
      points roots horizon hpoint_zero hnash hstep le_rfl
  exact hdrop.trans (div_le_div_of_nonneg_right
    (sub_le_sub_left
      (hminimum.debt_le (points horizon) hpoint_horizon) _)
    hminimum_pos.le)

end GameTheory
