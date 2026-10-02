/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/
import MathUE.ProbabilityMassFunction.BoundedSupportAverage
import UniformEquilibrium.Quitting.Paths.StoppingLawMixture
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle

/-!
# Per-profile core of the unique-debtor minimum-floor repair

Fix an actual quitting profile, one `mover`, a pure plan `target : Option ℕ`,
and a softening `weight` in `[0,1]`.  The softened profile replaces the
mover's coordinate by the canonical behavioral realization of the convex
mixture of the mover's *complete* stopping law with the point mass at
`target`.  That is `quittingStoppingLawMixtureBehaviorStrategy`, not a
pointwise mixture of the two behavioral hazards.

This file records the exact per-profile semantics of that replacement.

* The mover's prescribed payoff moves affinely: it gains exactly `weight`
  times its pure-time gain at `target`.
* The mover's behavioral cap is unchanged, because no opponent changed.
* Every observer's prescribed payoff moves by at most
  `2 * quittingRewardBound reward * weight`, and for a nonmover the same
  bound holds *uniformly over every behavioral deviation of that nonmover*;
  taking suprema transfers it to the nonmover's cap.
* The complete terminal outcome law is the exact convex mixture of the source
  law and the endpoint law.
* A paid pure-time pair of the mover survives the softening verbatim: the
  mover's pure-time deviation values depend only on its opponents.

The packaging theorem converts punishment-floor data, supplied as plain real
hypotheses, into the all-player floor at the softened profile.  Nothing here
builds the sequence-level entrance: `weight` is one arbitrary fixed scalar,
and no convergence is asserted.
-/

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The softened profile -/

/-- The floor-repair softening of `profile`: the `mover`'s coordinate is
replaced by the behavioral realization of the convex mixture of its complete
stopping law with the point mass at the pure plan `target`. -/
def fableFloorRepairSoftenedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    (quittingGame reward).BehaviorProfile :=
  Function.update profile mover
    (quittingStoppingLawMixtureBehaviorStrategy reward mover (profile mover)
      (quittingPureTimeBehaviorStrategy reward mover target) weight hweight0
      hweight1)

/-- Off the mover, the softening changes nothing. -/
theorem fableFloorRepair_softenedProfile_apply_of_ne
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hobserver : observer ≠ mover) :
    fableFloorRepairSoftenedProfile reward profile mover target weight hweight0
        hweight1 observer = profile observer := by
  unfold fableFloorRepairSoftenedProfile
  exact Function.update_of_ne hobserver _ profile

/-! ## K5 preliminary: the mover's pure-time values see only its opponents -/

/-- The mover's pure-time deviation values are unchanged by the softening:
overwriting the mover's own coordinate twice keeps only the last write. -/
theorem fableFloorRepair_pureTimeDeviationPayoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (fableFloorRepairSoftenedProfile reward profile mover target weight
          hweight0 hweight1) mover choice =
      quittingPureTimeDeviationPayoff reward profile mover choice := by
  unfold quittingPureTimeDeviationPayoff fableFloorRepairSoftenedProfile
  rw [Function.update_idem]

/-! ## K1: the mover's prescribed payoff moves affinely -/

/-- **K1.**  The mover's prescribed payoff at the softened profile is its
prescribed payoff plus `weight` times its pure-time gain at `target`.  This
is exact, with no window or cutoff error. -/
theorem fableFloorRepair_mover_payoff_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    quittingTerminalPayoff reward
        (fableFloorRepairSoftenedProfile reward profile mover target weight
          hweight0 hweight1) mover =
      quittingTerminalPayoff reward profile mover +
        weight * (quittingPureTimeDeviationPayoff reward profile mover target -
          quittingTerminalPayoff reward profile mover) := by
  have hsub := quittingTerminalPayoff_stoppingLawMixture_sub_eq reward profile
    mover (quittingPureTimeBehaviorStrategy reward mover target) weight
    hweight0 hweight1
  unfold fableFloorRepairSoftenedProfile quittingPureTimeDeviationPayoff
  linarith [hsub]

/-! ## K2: the mover's cap is exactly unchanged -/

/-- **K2.**  The mover's behavioral best-response envelope is unchanged by the
softening: the cap depends only on the opponents, and no opponent moved. -/
theorem fableFloorRepair_mover_cap_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    quittingContinuationBestResponseValue reward
        (fableFloorRepairSoftenedProfile reward profile mover target weight
          hweight0 hweight1) mover =
      quittingContinuationBestResponseValue reward profile mover := by
  unfold fableFloorRepairSoftenedProfile
  exact quittingContinuationBestResponseValue_update_self reward profile mover _

/-! ## K3: uniform nonmover control -/

/-- Every observer's prescribed payoff moves by at most `2 * M * weight`. -/
theorem fableFloorRepair_abs_payoff_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    |quittingTerminalPayoff reward
          (fableFloorRepairSoftenedProfile reward profile mover target weight
            hweight0 hweight1) observer -
        quittingTerminalPayoff reward profile observer| ≤
      2 * quittingRewardBound reward * weight := by
  unfold fableFloorRepairSoftenedProfile
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq reward profile
    mover observer (profile mover)
    (quittingPureTimeBehaviorStrategy reward mover target) weight hweight0
    hweight1
  rw [Function.update_eq_self] at haffine
  have hsource := abs_le.mp
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward profile observer)
  have htarget := abs_le.mp
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover target)) observer)
  set bound := quittingRewardBound reward with hboundDef
  set base := quittingTerminalPayoff reward profile observer with hbaseDef
  set endpoint := quittingTerminalPayoff reward
    (Function.update profile mover
      (quittingPureTimeBehaviorStrategy reward mover target)) observer
    with hendpointDef
  rw [haffine]
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(2 * bound * weight) = weight * -(2 * bound) := by ring
      _ ≤ weight * (endpoint - base) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight0
      _ = (1 - weight) * base + weight * endpoint - base := by ring
  · calc (1 - weight) * base + weight * endpoint - base
        = weight * (endpoint - base) := by ring
      _ ≤ weight * (2 * bound) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight0
      _ = 2 * bound * weight := by ring

/-- **K3, pointwise.**  For a nonmover, *every* behavioral deviation sees the
softening as a payoff change of at most `2 * M * weight`.  The bound does not
depend on the deviation. -/
theorem fableFloorRepair_abs_deviation_payoff_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hobserver : observer ≠ mover)
    (deviation : (quittingGame reward).BehaviorStrategy observer) :
    |quittingTerminalPayoff reward
          (Function.update
            (fableFloorRepairSoftenedProfile reward profile mover target weight
              hweight0 hweight1) observer deviation) observer -
        quittingTerminalPayoff reward
          (Function.update profile observer deviation) observer| ≤
      2 * quittingRewardBound reward * weight := by
  unfold fableFloorRepairSoftenedProfile
  have hcommuteMixed :
      Function.update (Function.update profile observer deviation) mover
          (quittingStoppingLawMixtureBehaviorStrategy reward mover
            (profile mover)
            (quittingPureTimeBehaviorStrategy reward mover target) weight
            hweight0 hweight1) =
        Function.update
          (Function.update profile mover
            (quittingStoppingLawMixtureBehaviorStrategy reward mover
              (profile mover)
              (quittingPureTimeBehaviorStrategy reward mover target) weight
              hweight0 hweight1)) observer deviation :=
    Function.update_comm hobserver deviation _ profile
  have hcommuteTarget :
      Function.update (Function.update profile observer deviation) mover
          (quittingPureTimeBehaviorStrategy reward mover target) =
        Function.update
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover target)) observer
          deviation :=
    Function.update_comm hobserver deviation _ profile
  have hsourceValue :
      Function.update (Function.update profile observer deviation) mover
          (profile mover) = Function.update profile observer deviation := by
    have hvalue : profile mover =
        (Function.update profile observer deviation) mover :=
      (Function.update_of_ne (Ne.symm hobserver) deviation profile).symm
    rw [hvalue, Function.update_eq_self]
  have haffine := quittingTerminalPayoff_stoppingLawMixture_eq reward
    (Function.update profile observer deviation) mover observer (profile mover)
    (quittingPureTimeBehaviorStrategy reward mover target) weight hweight0
    hweight1
  rw [hcommuteMixed, hsourceValue, hcommuteTarget] at haffine
  have hsource := abs_le.mp
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward
      (Function.update profile observer deviation) observer)
  have htarget := abs_le.mp
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward
      (Function.update
        (Function.update profile mover
          (quittingPureTimeBehaviorStrategy reward mover target)) observer
        deviation) observer)
  set bound := quittingRewardBound reward with hboundDef
  set base := quittingTerminalPayoff reward
    (Function.update profile observer deviation) observer with hbaseDef
  set endpoint := quittingTerminalPayoff reward
    (Function.update
      (Function.update profile mover
        (quittingPureTimeBehaviorStrategy reward mover target)) observer
      deviation) observer with hendpointDef
  rw [haffine]
  refine abs_le.mpr ⟨?_, ?_⟩
  · calc -(2 * bound * weight) = weight * -(2 * bound) := by ring
      _ ≤ weight * (endpoint - base) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight0
      _ = (1 - weight) * base + weight * endpoint - base := by ring
  · calc (1 - weight) * base + weight * endpoint - base
        = weight * (endpoint - base) := by ring
      _ ≤ weight * (2 * bound) :=
          mul_le_mul_of_nonneg_left (by linarith) hweight0
      _ = 2 * bound * weight := by ring

/-- The pure-time specialization of the pointwise nonmover bound. -/
theorem fableFloorRepair_abs_pureTimeDeviationPayoff_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hobserver : observer ≠ mover) (choice : Option ℕ) :
    |quittingPureTimeDeviationPayoff reward
          (fableFloorRepairSoftenedProfile reward profile mover target weight
            hweight0 hweight1) observer choice -
        quittingPureTimeDeviationPayoff reward profile observer choice| ≤
      2 * quittingRewardBound reward * weight := by
  unfold quittingPureTimeDeviationPayoff
  exact fableFloorRepair_abs_deviation_payoff_sub_le reward profile mover
    observer target weight hweight0 hweight1 hobserver _

/-- A uniform pointwise bound between two families transfers to their suprema
whenever both ranges are bounded above and the index type is inhabited. -/
theorem fableFloorRepair_abs_sSup_range_sub_le
    {α : Type*} [Nonempty α] (left right : α → ℝ) (gap : ℝ)
    (hleft : BddAbove (Set.range left)) (hright : BddAbove (Set.range right))
    (hgap : ∀ point, |left point - right point| ≤ gap) :
    |sSup (Set.range left) - sSup (Set.range right)| ≤ gap := by
  have hforward : sSup (Set.range left) ≤ sSup (Set.range right) + gap := by
    refine csSup_le (Set.range_nonempty left) ?_
    rintro value ⟨point, rfl⟩
    have hpoint := abs_le.mp (hgap point)
    have hle : right point ≤ sSup (Set.range right) :=
      le_csSup hright ⟨point, rfl⟩
    linarith [hpoint.2]
  have hbackward : sSup (Set.range right) ≤ sSup (Set.range left) + gap := by
    refine csSup_le (Set.range_nonempty right) ?_
    rintro value ⟨point, rfl⟩
    have hpoint := abs_le.mp (hgap point)
    have hle : left point ≤ sSup (Set.range left) :=
      le_csSup hleft ⟨point, rfl⟩
    linarith [hpoint.1]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The behavioral deviation payoffs of one player are bounded above by the
absolute reward bound. -/
theorem fableFloorRepair_bddAbove_range_deviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (observer : ι) :
    BddAbove (Set.range
      fun deviation : (quittingGame reward).BehaviorStrategy observer =>
        quittingTerminalPayoff reward
          (Function.update profile observer deviation) observer) := by
  refine ⟨quittingRewardBound reward, ?_⟩
  rintro value ⟨deviation, rfl⟩
  exact (abs_le.mp (abs_quittingTerminalPayoff_le_quittingRewardBound reward
    (Function.update profile observer deviation) observer)).2

/-- **K3, cap form.**  Taking suprema over the uniformly controlled family of
behavioral deviations transfers the estimate to a nonmover's cap. -/
theorem fableFloorRepair_abs_cap_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover observer : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (hobserver : observer ≠ mover) :
    |quittingContinuationBestResponseValue reward
          (fableFloorRepairSoftenedProfile reward profile mover target weight
            hweight0 hweight1) observer -
        quittingContinuationBestResponseValue reward profile observer| ≤
      2 * quittingRewardBound reward * weight := by
  unfold quittingContinuationBestResponseValue
  refine fableFloorRepair_abs_sSup_range_sub_le _ _ _
    (fableFloorRepair_bddAbove_range_deviationPayoff reward _ observer)
    (fableFloorRepair_bddAbove_range_deviationPayoff reward profile observer)
    ?_
  intro deviation
  exact fableFloorRepair_abs_deviation_payoff_sub_le reward profile mover
    observer target weight hweight0 hweight1 hobserver deviation

/-! ## K4: the complete terminal law is the exact convex mixture -/

/-- **K4.**  Every terminal outcome mass, including `Never`, of the softened
profile is the convex mixture of the source mass and the endpoint mass. -/
theorem fableFloorRepair_terminalOutcomeMass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward
        (fableFloorRepairSoftenedProfile reward profile mover target weight
          hweight0 hweight1) outcome =
      (1 - weight) * quittingTerminalOutcomeMass reward profile outcome +
        weight * quittingTerminalOutcomeMass reward
          (Function.update profile mover
            (quittingPureTimeBehaviorStrategy reward mover target)) outcome := by
  unfold fableFloorRepairSoftenedProfile
  have hmixture := quittingTerminalOutcomeMass_stoppingLawMixture_eq reward
    profile mover (profile mover)
    (quittingPureTimeBehaviorStrategy reward mover target) weight hweight0
    hweight1 outcome
  rwa [Function.update_eq_self] at hmixture

/-! ## K5: a retained paid pure-time pair -/

/-- The mover's prescribed payoff is the average of its pure-time deviation
values under its own complete stopping law. -/
theorem fableFloorRepair_expect_stoppingLaw_pureTimeDeviationPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι) :
    expect (quittingBehaviorStoppingLaw reward (profile mover))
        (quittingPureTimeDeviationPayoff reward profile mover) =
      quittingTerminalPayoff reward profile mover := by
  have hexpect := quittingTerminalPayoff_update_eq_expect_stoppingLaw_pureTime
    reward profile mover (profile mover)
  rw [Function.update_eq_self] at hexpect
  exact hexpect.symm

/-- Support averaging: some pure time in the support of the mover's own
stopping law has value at most the mover's prescribed payoff. -/
theorem fableFloorRepair_exists_support_pureTime_le_payoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover : ι) :
    ∃ source ∈ (quittingBehaviorStoppingLaw reward (profile mover)).support,
      quittingPureTimeDeviationPayoff reward profile mover source ≤
        quittingTerminalPayoff reward profile mover := by
  have hbound : ∀ choice : Option ℕ,
      |quittingPureTimeDeviationPayoff reward profile mover choice| ≤
        quittingRewardBound reward := by
    intro choice
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ mover
  obtain ⟨source, hsource, hle⟩ := exists_mem_support_le_expect
    (quittingBehaviorStoppingLaw reward (profile mover))
    (quittingPureTimeDeviationPayoff reward profile mover) hbound
  refine ⟨source, hsource, ?_⟩
  rwa [fableFloorRepair_expect_stoppingLaw_pureTimeDeviationPayoff] at hle

/-- **K5.**  The softening retains a paid pure-time pair for the mover.  Some
pure time in the support of the mover's *original* stopping law has value at
most the mover's prescribed payoff, and at the softened profile the pure-time
spread between `target` and that source witness is at least the mover's
original pure-time gain. -/
theorem fableFloorRepair_exists_retained_paidPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1) :
    ∃ source ∈ (quittingBehaviorStoppingLaw reward (profile mover)).support,
      quittingPureTimeDeviationPayoff reward profile mover source ≤
          quittingTerminalPayoff reward profile mover ∧
        quittingPureTimeDeviationPayoff reward profile mover target -
            quittingTerminalPayoff reward profile mover ≤
          quittingPureTimeDeviationPayoff reward
              (fableFloorRepairSoftenedProfile reward profile mover target
                weight hweight0 hweight1) mover target -
            quittingPureTimeDeviationPayoff reward
              (fableFloorRepairSoftenedProfile reward profile mover target
                weight hweight0 hweight1) mover source := by
  obtain ⟨source, hsource, hle⟩ :=
    fableFloorRepair_exists_support_pureTime_le_payoff reward profile mover
  refine ⟨source, hsource, hle, ?_⟩
  rw [fableFloorRepair_pureTimeDeviationPayoff_eq reward profile mover target
      weight hweight0 hweight1 target,
    fableFloorRepair_pureTimeDeviationPayoff_eq reward profile mover target
      weight hweight0 hweight1 source]
  linarith

/-- Approximate cap optimality of the mover's plan is retained exactly: the
cap does not move and the pure-time value does not move. -/
theorem fableFloorRepair_retained_cap_optimality
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (accuracy : ℝ)
    (hoptimal : quittingContinuationBestResponseValue reward profile mover -
      accuracy ≤ quittingPureTimeDeviationPayoff reward profile mover target) :
    quittingContinuationBestResponseValue reward
          (fableFloorRepairSoftenedProfile reward profile mover target weight
            hweight0 hweight1) mover -
        accuracy ≤
      quittingPureTimeDeviationPayoff reward
        (fableFloorRepairSoftenedProfile reward profile mover target weight
          hweight0 hweight1) mover target := by
  rw [fableFloorRepair_mover_cap_eq reward profile mover target weight hweight0
      hweight1,
    fableFloorRepair_pureTimeDeviationPayoff_eq reward profile mover target
      weight hweight0 hweight1 target]
  exact hoptimal

/-! ## K6: the packaged punishment floor at the softened profile -/

/-- **K6.**  Floor repair, packaged per profile.  The mover's floor is met by
the exact affine gain, and every other player's floor is met with the uniform
`2 * M * weight` margin.  The note's choice `weight = 2 f / a` arrives here as
the mover hypothesis; the statement itself is sequence-free. -/
theorem fableFloorRepair_punishmentFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (mover : ι) (target : Option ℕ)
    (weight : ℝ) (hweight0 : 0 ≤ weight) (hweight1 : weight ≤ 1)
    (punishment : ι → ℝ)
    (hmover : punishment mover ≤ quittingTerminalPayoff reward profile mover +
      weight * (quittingPureTimeDeviationPayoff reward profile mover target -
        quittingTerminalPayoff reward profile mover))
    (hothers : ∀ observer, observer ≠ mover →
      punishment observer ≤ quittingTerminalPayoff reward profile observer -
        2 * quittingRewardBound reward * weight) :
    ∀ observer, punishment observer ≤ quittingTerminalPayoff reward
      (fableFloorRepairSoftenedProfile reward profile mover target weight
        hweight0 hweight1) observer := by
  intro observer
  by_cases hobserver : observer = mover
  · subst hobserver
    rw [fableFloorRepair_mover_payoff_eq reward profile observer target weight
      hweight0 hweight1]
    exact hmover
  · have hshift := abs_le.mp (fableFloorRepair_abs_payoff_sub_le reward profile
      mover observer target weight hweight0 hweight1)
    linarith [hothers observer hobserver, hshift.1]

end GameTheory
