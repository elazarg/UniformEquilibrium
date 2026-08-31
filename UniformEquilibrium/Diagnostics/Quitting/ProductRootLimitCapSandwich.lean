/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

/-
Semantic realization at the product base.

A coordinatewise limit of ordinary behavioral quitting laws whose Never and
singleton coordinates vanish is the box law of a limiting quit-rate vector
carrying two sure quitters.  This file upgrades that law statement to a full
semantic realization: the one-date-then-Never profile at the limiting root
reproduces *both* coordinates of the limiting terminal semantic pair, provided
each limiting cap coordinate strictly exceeds its own solo quitting reward.

The route is entirely pure-time.  Every deterministic quit plan against a
source profile is compared, at the selected efficient date, with one of three
closed-form values: the solo reward for an early quit, the zero-tail Quit
endpoint of the selected live root for a quit exactly at that date, and the
zero-tail Continue endpoint for any later quit or for Never.  Each comparison
costs the pre-date absorbed mass and, in the late branch, the opponents'
all-Continue mass at the selected row.  Taking suprema turns the three
estimates into one sandwich for the cap, and the sandwich collapses at the
limit because both defects vanish along the selection.

The strict margin removes the solo argument, leaving the cap equal to the
maximum of the two endpoints of the limiting root; that is exactly the cap of
the unpadded one-date-then-Never profile, whose sure quitter erases the late
branch.  The prescribed coordinate and the law are then the reward moment and
the box law of the same root.
-/
import UniformEquilibrium.Diagnostics.Quitting.OneDateProductRootCaps
import UniformEquilibrium.Diagnostics.Quitting.ZeroSingletonProductBaseLaw
import UniformEquilibrium.Quitting.Bellman.Finite.BooleanMobiusAdapter
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Row moments -/

/-- The reward moment of one product row: the exact-coalition average of the
terminal rewards prescribed at that row. -/
def productRootRowMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  ∑ S : {S : Finset ι // S.Nonempty},
    quittingRootCoalitionMass root S.val * reward S who

/-- A row moment is the zero-tail expected payoff of that row. -/
theorem productRootRowMoment_eq_rootExpectedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    productRootRowMoment reward root who =
      quittingRootExpectedPayoff reward (0 : Payoff ι) root who :=
  (quittingRootAbsorbingContribution_eq_sum_nonemptyCoalitionMass
    reward root who).symm

/-- The zero-tail Quit endpoint is the row moment of the row with the observer
forced to quit. -/
theorem oneDateProductQuitEndpoint_eq_rowMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductQuitEndpoint reward root who =
      productRootRowMoment reward (Function.update root who (PMF.pure true)) who := by
  rw [productRootRowMoment_eq_rootExpectedPayoff]
  rfl

/-- The zero-tail Continue endpoint is the row moment of the row with the
observer forced to continue. -/
theorem oneDateProductContinueEndpoint_eq_rowMoment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductContinueEndpoint reward root who =
      productRootRowMoment reward (Function.update root who (PMF.pure false)) who := by
  rw [productRootRowMoment_eq_rootExpectedPayoff]
  rfl

/-! ## Total nonempty coalition mass of a row -/

/-- The nonempty exact coalitions of a product row are indexed by the erased
powerset. -/
private theorem productRoot_sum_subtype_eq_sum_erase
    (f : Finset ι → ℝ) :
    ∑ S : {S : Finset ι // S.Nonempty}, f S.val =
      ∑ S ∈ Finset.univ.erase (∅ : Finset ι), f S := by
  classical
  refine (Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι)) ?_ f).symm
  intro S
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  exact Finset.nonempty_iff_ne_empty.symm

/-- The total nonempty exact-coalition mass of a product row is its absorption
mass. -/
theorem productRoot_sum_rootCoalitionMass_eq_absorptionMass
    (root : ι → PMF Bool) :
    ∑ S : {S : Finset ι // S.Nonempty}, quittingRootCoalitionMass root S.val =
      quittingRootAbsorptionMass root := by
  rw [productRoot_sum_subtype_eq_sum_erase, quittingRootCoalitionMass_sum_nonempty]
  rfl

/-- A row moment is bounded by any uniform reward bound. -/
theorem productRoot_abs_rowMoment_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (root : ι → PMF Bool) (who : ι) :
    |productRootRowMoment reward root who| ≤ bound := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hterm : ∀ S : {S : Finset ι // S.Nonempty},
      |quittingRootCoalitionMass root S.val * reward S who| ≤
        quittingRootCoalitionMass root S.val * bound := by
    intro S
    rw [abs_mul, abs_of_nonneg (quittingRootCoalitionMass_nonneg root S.val)]
    exact mul_le_mul_of_nonneg_left (hreward S who)
      (quittingRootCoalitionMass_nonneg root S.val)
  have hsum : |productRootRowMoment reward root who| ≤
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass root S.val * bound :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun S _ => hterm S)
  rw [← Finset.sum_mul, productRoot_sum_rootCoalitionMass_eq_absorptionMass] at hsum
  have habs : quittingRootAbsorptionMass root ≤ 1 :=
    quittingRootAbsorptionMass_le_one root
  have habs0 : 0 ≤ quittingRootAbsorptionMass root :=
    quittingRootAbsorptionMass_nonneg root
  nlinarith

/-! ## Box forms of the two endpoints -/

/-- The zero-tail endpoint of a product root read as a polynomial in the
quit-rate vector, with the observer's own rate replaced by `bit`. -/
def productRootEndpointBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (w : ι → ℝ) (who : ι) (bit : ℝ) : ℝ :=
  ∑ S : {S : Finset ι // S.Nonempty},
    zeroSingletonProductBaseBoxCoalition (Function.update w who bit) S.val * reward S who

omit [Fintype ι] in
/-- Overwriting one coordinate of a quit-rate vector is continuous. -/
private theorem productRoot_continuous_update (who : ι) (bit : ℝ) :
    Continuous fun w : ι → ℝ => Function.update w who bit := by
  refine continuous_pi fun i => ?_
  by_cases h : i = who
  · subst h
    simpa only [Function.update_self] using
      (continuous_const : Continuous fun _ : ι → ℝ => bit)
  · simpa only [Function.update_of_ne h] using continuous_apply i

/-- The endpoint polynomial is continuous in the quit-rate vector. -/
theorem productRoot_continuous_endpointBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (bit : ℝ) :
    Continuous fun w : ι → ℝ => productRootEndpointBox reward w who bit := by
  refine continuous_finsetSum _ fun S _ => ?_
  exact ((zeroSingletonProductBase_continuous_boxCoalition S.val).comp
    (productRoot_continuous_update who bit)).mul continuous_const

omit [Fintype ι] in
/-- Forcing one root marginal to a pure Boolean overwrites exactly that
coordinate of the quit-rate vector. -/
private theorem productRoot_quitRates_update
    (root : ι → PMF Bool) (who : ι) (bit : Bool) :
    (fun player => ((Function.update root who (PMF.pure bit)) player true).toReal) =
      Function.update (fun player => (root player true).toReal) who
        (if bit then (1 : ℝ) else 0) := by
  funext player
  by_cases h : player = who
  · subst h
    cases bit <;> simp
  · simp [Function.update_of_ne h]

/-- **Box form of the Quit endpoint.** -/
theorem oneDateProductQuitEndpoint_eq_endpointBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductQuitEndpoint reward root who =
      productRootEndpointBox reward (fun player => (root player true).toReal) who 1 := by
  rw [oneDateProductQuitEndpoint_eq_rowMoment]
  unfold productRootRowMoment productRootEndpointBox
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zeroSingletonProductBase_coalitionMass_eq_boxCoalition,
    productRoot_quitRates_update root who true]
  norm_num

/-- **Box form of the Continue endpoint.** -/
theorem oneDateProductContinueEndpoint_eq_endpointBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    oneDateProductContinueEndpoint reward root who =
      productRootEndpointBox reward (fun player => (root player true).toReal) who 0 := by
  rw [oneDateProductContinueEndpoint_eq_rowMoment]
  unfold productRootRowMoment productRootEndpointBox
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [zeroSingletonProductBase_coalitionMass_eq_boxCoalition,
    productRoot_quitRates_update root who false]
  norm_num

/-! ## The deleted live mass -/

/-- The survival product of one observer's opponents along the profile's
canonical live rows. -/
def productRootDeletedLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (time : ℕ) : ℝ :=
  ∏ t ∈ Finset.range time,
    oneDateProductOppContinue (quittingProfileLiveRoot reward profile t) who

@[simp] theorem productRootDeletedLiveMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    productRootDeletedLiveMass reward profile who 0 = 1 := by
  simp [productRootDeletedLiveMass]

theorem productRootDeletedLiveMass_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    productRootDeletedLiveMass reward profile who (time + 1) =
      productRootDeletedLiveMass reward profile who time *
        oneDateProductOppContinue (quittingProfileLiveRoot reward profile time) who := by
  simp [productRootDeletedLiveMass, Finset.prod_range_succ]

theorem productRootDeletedLiveMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    0 ≤ productRootDeletedLiveMass reward profile who time :=
  Finset.prod_nonneg fun _ _ => oneDateProductOppContinue_nonneg _ who

theorem productRootDeletedLiveMass_le_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (time : ℕ) :
    productRootDeletedLiveMass reward profile who time ≤ 1 :=
  Finset.prod_le_one (fun _ _ => oneDateProductOppContinue_nonneg _ who)
    (fun _ _ => oneDateProductOppContinue_le_one _ who)

theorem productRootDeletedLiveMass_antitone
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    Antitone (productRootDeletedLiveMass reward profile who) := by
  refine antitone_nat_of_succ_le fun time => ?_
  rw [productRootDeletedLiveMass_succ]
  exact mul_le_of_le_one_right (productRootDeletedLiveMass_nonneg reward profile who time)
    (oneDateProductOppContinue_le_one _ who)

/-! ## Joint continuation under a unilateral update -/

/-- The opponents' all-Continue mass is the product of their displayed
Continue probabilities. -/
theorem oneDateProductOppContinue_eq_prod_erase (root : ι → PMF Bool) (who : ι) :
    oneDateProductOppContinue root who =
      ∏ other ∈ Finset.univ.erase who, (root other false).toReal := by
  classical
  rw [oneDateProductOppContinue_eq]
  unfold quittingRootOpponentContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    ← Finset.mul_prod_erase Finset.univ
      (fun player => ((Function.update root who (PMF.pure false))
        player false).toReal) (Finset.mem_univ who), Function.update_self]
  simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul]
  refine Finset.prod_congr rfl fun other hother => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]

/-- The joint all-Continue mass of an updated profile splits into the
deviator's own Continue probability and the opponents' survival factor. -/
theorem productRoot_jointContinueMass_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (str : (quittingGame reward).BehaviorStrategy who) (time : ℕ) :
    quittingJointContinueMass reward (Function.update profile who str) time =
      (str time (quittingLiveHist reward time) false).toReal *
        oneDateProductOppContinue (quittingProfileLiveRoot reward profile time) who := by
  classical
  have hopp : oneDateProductOppContinue (quittingProfileLiveRoot reward profile time) who =
      ∏ player ∈ Finset.univ.erase who,
        ((profile player time (quittingLiveHist reward time)) false).toReal :=
    oneDateProductOppContinue_eq_prod_erase _ who
  rw [quittingJointContinueMass_eq_product, hopp,
    ← Finset.mul_prod_erase Finset.univ
      (fun player => ((Function.update profile who str) player time
        (quittingLiveHist reward time) false).toReal) (Finset.mem_univ who),
    Function.update_self]
  refine congrArg _ (Finset.prod_congr rfl fun other hother => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]

/-- While the deviator continues, the updated profile's live mass is exactly
the opponents' survival product. -/
theorem productRoot_liveMass_update_eq_deletedLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (str : (quittingGame reward).BehaviorStrategy who) (cutoff : ℕ)
    (hcont : ∀ t, t < cutoff →
      (str t (quittingLiveHist reward t) false).toReal = 1) :
    quittingLiveMass reward (Function.update profile who str) cutoff =
      productRootDeletedLiveMass reward profile who cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [quittingLiveMass_succ, ih (fun t ht => hcont t (by omega)),
        productRoot_jointContinueMass_update, hcont cutoff (by omega), one_mul,
        productRootDeletedLiveMass_succ]

/-- Once the deviator quits surely, the updated profile leaves no live mass. -/
theorem productRoot_liveMass_update_succ_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (str : (quittingGame reward).BehaviorStrategy who) (cutoff : ℕ)
    (hquit : (str cutoff (quittingLiveHist reward cutoff) false).toReal = 0) :
    quittingLiveMass reward (Function.update profile who str) (cutoff + 1) = 0 := by
  rw [quittingLiveMass_succ, productRoot_jointContinueMass_update, hquit, zero_mul,
    mul_zero]

/-- The joint live mass never exceeds the opponents' survival product. -/
theorem productRoot_liveMass_le_deletedLiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ) :
    quittingLiveMass reward profile cutoff ≤
      productRootDeletedLiveMass reward profile who cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      have hstep : quittingJointContinueMass reward profile cutoff ≤
          oneDateProductOppContinue (quittingProfileLiveRoot reward profile cutoff) who := by
        have hjoint : quittingJointContinueMass reward profile cutoff =
            quittingStationaryContinueMass
              (quittingProfileLiveRoot reward profile cutoff) := by
          rw [quittingJointContinueMass_eq_product,
            quittingStationaryContinueMass_eq_prod_continueProbability]
          rfl
        rw [hjoint, oneDateProductOppContinue_eq]
        exact quittingStationaryContinueMass_le_update_pure_false _ who
      rw [quittingLiveMass_succ, productRootDeletedLiveMass_succ]
      exact mul_le_mul ih hstep (quittingJointContinueMass_nonneg reward profile cutoff)
        (productRootDeletedLiveMass_nonneg reward profile who cutoff)

/-! ## Prefix approximation of a terminal payoff -/

omit [DecidableEq ι] in
/-- Every prefix sum of the survival-weighted absorption series is the
complement of the survival probability at the cutoff. -/
private theorem productRoot_prefix_absorption_telescope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
        quittingRootAbsorptionMass (quittingProfileLiveRoot reward profile time) =
      1 - quittingLiveMass reward profile cutoff := by
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      have hjoint : quittingJointContinueMass reward profile cutoff =
          quittingStationaryContinueMass
            (quittingProfileLiveRoot reward profile cutoff) := by
        rw [quittingJointContinueMass_eq_product,
          quittingStationaryContinueMass_eq_prod_continueProbability]
        rfl
      have hsucc : quittingLiveMass reward profile (cutoff + 1) =
          quittingLiveMass reward profile cutoff *
            quittingStationaryContinueMass
              (quittingProfileLiveRoot reward profile cutoff) := by
        rw [quittingLiveMass_succ, hjoint]
      rw [Finset.sum_range_succ, ih, hsucc, quittingRootAbsorptionMass]
      ring

/-- The total absorbed mass before a cutoff is the complement of the survival
probability there. -/
theorem productRoot_sum_range_stage_eq_one_sub_liveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ) :
    ∑ time ∈ Finset.range cutoff, ∑ S : {S : Finset ι // S.Nonempty},
        quittingStageCoalitionMass reward profile time S =
      1 - quittingLiveMass reward profile cutoff := by
  rw [← productRoot_prefix_absorption_telescope reward profile cutoff]
  refine Finset.sum_congr rfl fun time _ => ?_
  rw [← productRoot_sum_rootCoalitionMass_eq_absorptionMass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ =>
    quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass reward profile time S

omit [DecidableEq ι] in
/-- A terminal payoff is the sum of its coalition coordinates against the
reward table. -/
theorem productRoot_terminalPayoff_eq_sum_outcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward profile who =
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingTerminalOutcomeMass reward profile (some S) * reward S who := by
  have hmoment := congrFun (quittingTerminalRewardMoment_outcomeMass reward profile) who
  rw [← hmoment, quittingTerminalRewardMoment, Fintype.sum_option]
  simp [quittingTerminalOutcomeReward]

/-- **Prefix approximation.**  A terminal payoff differs from its
chronological prefix of survival-weighted row moments by at most the reward
bound times the survival mass at the cutoff. -/
theorem productRoot_terminalPayoff_sub_prefix_abs_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (cutoff : ℕ) :
    |quittingTerminalPayoff reward profile who -
        ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
          productRootRowMoment reward
            (quittingProfileLiveRoot reward profile time) who| ≤
      bound * quittingLiveMass reward profile cutoff := by
  classical
  obtain ⟨resid, hresid⟩ : ∃ f : {S : Finset ι // S.Nonempty} → ℝ, ∀ S, f S =
      quittingTerminalOutcomeMass reward profile (some S) -
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S := ⟨_, fun _ => rfl⟩
  have hresidNonneg : ∀ S, 0 ≤ resid S := by
    intro S
    have hsum :=
      terminalOutcomeChronology_hasSum_stageCoalitionMass_absorbedMassLimit
        reward profile S
    have hle := sum_le_hasSum (Finset.range cutoff)
      (fun time _ => quittingStageCoalitionMass_nonneg reward profile time S) hsum
    have hlaw : quittingTerminalOutcomeMass reward profile (some S) =
        quittingAbsorbedMassLimit reward profile S := rfl
    rw [hresid S, hlaw]
    linarith
  have hprefix : ∑ S : {S : Finset ι // S.Nonempty},
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time S =
      1 - quittingLiveMass reward profile cutoff := by
    rw [Finset.sum_comm]
    exact productRoot_sum_range_stage_eq_one_sub_liveMass reward profile cutoff
  have htotal : ∑ S : {S : Finset ι // S.Nonempty},
      quittingTerminalOutcomeMass reward profile (some S) =
      1 - quittingTerminalOutcomeMass reward profile none := by
    have hcons := quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
    have hnone : quittingTerminalOutcomeMass reward profile none =
        quittingLiveMassLimit reward profile := rfl
    have hsome : ∀ S : {S : Finset ι // S.Nonempty},
        quittingTerminalOutcomeMass reward profile (some S) =
          quittingAbsorbedMassLimit reward profile S := fun _ => rfl
    rw [hnone]
    simp only [hsome]
    linarith
  have hresidSum : ∑ S : {S : Finset ι // S.Nonempty}, resid S =
      quittingLiveMass reward profile cutoff -
        quittingTerminalOutcomeMass reward profile none := by
    rw [Finset.sum_congr rfl fun S (_ : S ∈ Finset.univ) => hresid S,
      Finset.sum_sub_distrib, htotal, hprefix]
    ring
  have hleft : ∀ time, quittingLiveMass reward profile time *
      productRootRowMoment reward (quittingProfileLiveRoot reward profile time) who =
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingStageCoalitionMass reward profile time S * reward S who := by
    intro time
    rw [productRootRowMoment, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass]
    ring
  have hright : ∀ S : {S : Finset ι // S.Nonempty},
      (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S) * reward S who =
        ∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S * reward S who := by
    intro S
    rw [Finset.sum_mul]
  have hswap : ∑ time ∈ Finset.range cutoff,
      quittingLiveMass reward profile time *
        productRootRowMoment reward
          (quittingProfileLiveRoot reward profile time) who =
      ∑ S : {S : Finset ι // S.Nonempty},
        (∑ time ∈ Finset.range cutoff,
          quittingStageCoalitionMass reward profile time S) * reward S who := by
    rw [Finset.sum_congr rfl (fun time (_ : time ∈ Finset.range cutoff) => hleft time),
      Finset.sum_congr rfl (fun S (_ : S ∈ Finset.univ) => hright S), Finset.sum_comm]
  have hpoint : ∀ S : {S : Finset ι // S.Nonempty},
      quittingTerminalOutcomeMass reward profile (some S) * reward S who =
        resid S * reward S who +
          (∑ time ∈ Finset.range cutoff,
            quittingStageCoalitionMass reward profile time S) * reward S who := by
    intro S
    rw [hresid S]
    ring
  have hdiff : quittingTerminalPayoff reward profile who -
      ∑ time ∈ Finset.range cutoff, quittingLiveMass reward profile time *
        productRootRowMoment reward
          (quittingProfileLiveRoot reward profile time) who =
      ∑ S : {S : Finset ι // S.Nonempty}, resid S * reward S who := by
    rw [productRoot_terminalPayoff_eq_sum_outcomeMass,
      Finset.sum_congr rfl (fun S (_ : S ∈ Finset.univ) => hpoint S),
      Finset.sum_add_distrib, hswap]
    ring
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hterm : ∀ S : {S : Finset ι // S.Nonempty},
      |resid S * reward S who| ≤ resid S * bound := by
    intro S
    rw [abs_mul, abs_of_nonneg (hresidNonneg S)]
    exact mul_le_mul_of_nonneg_left (hreward S who) (hresidNonneg S)
  have hfinal : |∑ S : {S : Finset ι // S.Nonempty}, resid S * reward S who| ≤
      (∑ S : {S : Finset ι // S.Nonempty}, resid S) * bound := by
    have hsum : (∑ S : {S : Finset ι // S.Nonempty}, resid S) * bound =
        ∑ S : {S : Finset ι // S.Nonempty}, resid S * bound := by
      rw [Finset.sum_mul]
    rw [hsum]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum fun S _ => hterm S)
  rw [hdiff]
  refine le_trans hfinal ?_
  rw [hresidSum]
  have hnever : 0 ≤ quittingTerminalOutcomeMass reward profile none :=
    quittingLiveMassLimit_nonneg reward profile
  nlinarith

/-! ## Sharpened row-moment bound -/

/-- A row moment is bounded by the row's absorption mass times the reward
bound. -/
theorem productRoot_abs_rowMoment_le_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (root : ι → PMF Bool) (who : ι) :
    |productRootRowMoment reward root who| ≤ quittingRootAbsorptionMass root * bound := by
  have hterm : ∀ S : {S : Finset ι // S.Nonempty},
      |quittingRootCoalitionMass root S.val * reward S who| ≤
        quittingRootCoalitionMass root S.val * bound := by
    intro S
    rw [abs_mul, abs_of_nonneg (quittingRootCoalitionMass_nonneg root S.val)]
    exact mul_le_mul_of_nonneg_left (hreward S who)
      (quittingRootCoalitionMass_nonneg root S.val)
  have hsum : |productRootRowMoment reward root who| ≤
      ∑ S : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass root S.val * bound :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun S _ => hterm S)
  rwa [← Finset.sum_mul, productRoot_sum_rootCoalitionMass_eq_absorptionMass] at hsum

/-! ## Pure-time rows -/

omit [DecidableEq ι] in
/-- The canonical live row of a pure-time behavior strategy is its hazard. -/
theorem productRoot_pureTimeBehaviorStrategy_row
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (quitTime : Option ℕ) (time : ℕ) :
    quittingPureTimeBehaviorStrategy reward who quitTime time
        (quittingLiveHist reward time) = quittingPureTimeHazard quitTime time :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Away from its quit date a pure-time hazard continues surely. -/
theorem productRoot_pureTimeHazard_of_ne {quitTime : Option ℕ} {time : ℕ}
    (hne : quitTime ≠ some time) :
    quittingPureTimeHazard quitTime time = PMF.pure false := by
  cases quitTime with
  | none => rfl
  | some q =>
      refine quittingPureTimeHazard_some_of_ne ?_
      intro hq
      exact hne (by rw [hq])

omit [DecidableEq ι] in
/-- Away from its quit date a pure-time deviator's displayed Continue
probability is one. -/
theorem productRoot_pureTimeRow_continue_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    {quitTime : Option ℕ} {time : ℕ} (hne : quitTime ≠ some time) :
    (quittingPureTimeBehaviorStrategy reward who quitTime time
      (quittingLiveHist reward time) false).toReal = 1 := by
  show ((quittingPureTimeHazard quitTime time) false).toReal = 1
  rw [productRoot_pureTimeHazard_of_ne hne]
  simp

omit [DecidableEq ι] in
/-- At its quit date a pure-time deviator's displayed Continue probability is
zero. -/
theorem productRoot_pureTimeRow_quit_toReal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (time : ℕ) :
    (quittingPureTimeBehaviorStrategy reward who (some time) time
      (quittingLiveHist reward time) false).toReal = 0 := by
  show ((quittingPureTimeHazard (some time) time) false).toReal = 0
  rw [quittingPureTimeHazard_some_self]
  simp

/-- Updating one behavior strategy updates exactly that coordinate of the
canonical live row. -/
theorem productRoot_liveRoot_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (str : (quittingGame reward).BehaviorStrategy who) (time : ℕ) :
    quittingProfileLiveRoot reward (Function.update profile who str) time =
      Function.update (quittingProfileLiveRoot reward profile time) who
        (str time (quittingLiveHist reward time)) :=
  congrFun (quittingProfileLiveRoot_update_eq_rootSequenceUpdate reward profile
    who str) time

/-! ## The one-date decomposition of a pure-time deviation value -/

/-- **Decomposition.**  If the deviator continues at every date strictly
before `cutoff`, its terminal payoff is the survival-weighted row moment of
the updated row at `cutoff`, up to the mass absorbed before `cutoff` and the
mass surviving past it. -/
theorem productRoot_pureTimeDeviationPayoff_sub_row_abs_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (quitTime : Option ℕ) (cutoff : ℕ)
    (hearly : ∀ t, t < cutoff → quitTime ≠ some t) :
    |quittingPureTimeDeviationPayoff reward profile who quitTime -
        productRootDeletedLiveMass reward profile who cutoff *
          productRootRowMoment reward
            (Function.update (quittingProfileLiveRoot reward profile cutoff) who
              (quittingPureTimeHazard quitTime cutoff)) who| ≤
      bound * (1 - productRootDeletedLiveMass reward profile who cutoff) +
        bound * quittingLiveMass reward (Function.update profile who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) (cutoff + 1) := by
  classical
  obtain ⟨dev, hdev⟩ : ∃ p : (quittingGame reward).BehaviorProfile,
      p = Function.update profile who
        (quittingPureTimeBehaviorStrategy reward who quitTime) := ⟨_, rfl⟩
  have hvalue : quittingPureTimeDeviationPayoff reward profile who quitTime =
      quittingTerminalPayoff reward dev who := by rw [hdev]; rfl
  have hlive : quittingLiveMass reward dev cutoff =
      productRootDeletedLiveMass reward profile who cutoff := by
    rw [hdev]
    exact productRoot_liveMass_update_eq_deletedLiveMass reward profile who _ cutoff
      fun t ht => productRoot_pureTimeRow_continue_toReal reward who (hearly t ht)
  have hrow : quittingProfileLiveRoot reward dev cutoff =
      Function.update (quittingProfileLiveRoot reward profile cutoff) who
        (quittingPureTimeHazard quitTime cutoff) := by
    rw [hdev, productRoot_liveRoot_update, productRoot_pureTimeBehaviorStrategy_row]
  have hprefix := productRoot_terminalPayoff_sub_prefix_abs_le reward hreward dev who
    (cutoff + 1)
  rw [Finset.sum_range_succ, hlive, hrow] at hprefix
  have hpre : |∑ time ∈ Finset.range cutoff, quittingLiveMass reward dev time *
      productRootRowMoment reward (quittingProfileLiveRoot reward dev time) who| ≤
      bound * (1 - productRootDeletedLiveMass reward profile who cutoff) := by
    have hstep : ∀ time ∈ Finset.range cutoff,
        |quittingLiveMass reward dev time *
          productRootRowMoment reward (quittingProfileLiveRoot reward dev time) who| ≤
          quittingLiveMass reward dev time *
            quittingRootAbsorptionMass
              (quittingProfileLiveRoot reward dev time) * bound := by
      intro time _
      rw [abs_mul, abs_of_nonneg (quittingLiveMass_nonneg reward dev time),
        mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (productRoot_abs_rowMoment_le_absorption reward hreward _ who)
        (quittingLiveMass_nonneg reward dev time)
    have hsum := le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum hstep)
    have hcollapse : ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward dev time *
          quittingRootAbsorptionMass
            (quittingProfileLiveRoot reward dev time) * bound =
        (1 - quittingLiveMass reward dev cutoff) * bound := by
      rw [← Finset.sum_mul, productRoot_prefix_absorption_telescope]
    rw [hcollapse, hlive] at hsum
    linarith [hsum]
  have hlast : quittingLiveMass reward (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who quitTime)) (cutoff + 1) =
      quittingLiveMass reward dev (cutoff + 1) := by rw [hdev]
  rw [hvalue, hlast]
  have hsplit : quittingTerminalPayoff reward dev who -
      productRootDeletedLiveMass reward profile who cutoff *
        productRootRowMoment reward
          (Function.update (quittingProfileLiveRoot reward profile cutoff) who
            (quittingPureTimeHazard quitTime cutoff)) who =
      (quittingTerminalPayoff reward dev who -
        ((∑ time ∈ Finset.range cutoff, quittingLiveMass reward dev time *
          productRootRowMoment reward (quittingProfileLiveRoot reward dev time) who) +
          productRootDeletedLiveMass reward profile who cutoff *
            productRootRowMoment reward
              (Function.update (quittingProfileLiveRoot reward profile cutoff) who
                (quittingPureTimeHazard quitTime cutoff)) who)) +
        ∑ time ∈ Finset.range cutoff, quittingLiveMass reward dev time *
          productRootRowMoment reward
            (quittingProfileLiveRoot reward dev time) who := by ring
  rw [hsplit, abs_le]
  have h1 := abs_le.mp hprefix
  have h2 := abs_le.mp hpre
  constructor
  · linarith [h1.1, h2.1]
  · linarith [h1.2, h2.2]

/-! ## The exact solo atom of a forced-quit row -/

/-- At a row with the observer forced to quit, the exact solo coalition has
the opponents' all-Continue mass. -/
theorem productRoot_coalitionMass_sureQuit_singleton (root : ι → PMF Bool) (who : ι) :
    quittingRootCoalitionMass (Function.update root who (PMF.pure true))
        (quittingSingletonTerminal who).val = oneDateProductOppContinue root who := by
  classical
  rw [oneDateProductOppContinue_eq_prod_erase, quittingRootCoalitionMass]
  unfold coalitionMass quittingRootQuitRates
  rw [show (quittingSingletonTerminal who).val = ({who} : Finset ι) from rfl,
    Finset.prod_singleton, Function.update_self, Finset.compl_singleton]
  simp only [PMF.pure_apply, if_true, ENNReal.toReal_one, one_mul]
  refine Finset.prod_congr rfl fun other hother => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hother)]
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  linarith

/-- **Near-solo Quit endpoint.**  When the observer's opponents almost surely
continue, the zero-tail Quit endpoint is almost the solo reward. -/
theorem productRoot_abs_quitEndpoint_sub_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (root : ι → PMF Bool) (who : ι) :
    |oneDateProductQuitEndpoint reward root who -
        reward (quittingSingletonTerminal who) who| ≤
      2 * bound * (1 - oneDateProductOppContinue root who) := by
  classical
  obtain ⟨forced, hforced⟩ : ∃ r : ι → PMF Bool,
      r = Function.update root who (PMF.pure true) := ⟨_, rfl⟩
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have htotal : ∑ S : {S : Finset ι // S.Nonempty},
      quittingRootCoalitionMass forced S.val = 1 := by
    have hzero : quittingStationaryContinueMass forced = 0 := by
      refine quittingStationaryContinueMass_of_sureQuitter (quitter := who) ?_
      rw [hforced, Function.update_self]
    rw [productRoot_sum_rootCoalitionMass_eq_absorptionMass, quittingRootAbsorptionMass,
      hzero]
    ring
  have hsingle : quittingRootCoalitionMass forced
      (quittingSingletonTerminal who).val = oneDateProductOppContinue root who := by
    rw [hforced]
    exact productRoot_coalitionMass_sureQuit_singleton root who
  have hpeelMass := Finset.add_sum_erase Finset.univ
    (fun S : {S : Finset ι // S.Nonempty} => quittingRootCoalitionMass forced S.val)
    (Finset.mem_univ (quittingSingletonTerminal who))
  have hrestMass : ∑ S ∈ Finset.univ.erase (quittingSingletonTerminal who),
      quittingRootCoalitionMass forced S.val = 1 - oneDateProductOppContinue root who := by
    rw [htotal] at hpeelMass
    rw [hsingle] at hpeelMass
    linarith
  have hpeel := Finset.add_sum_erase Finset.univ
    (fun S : {S : Finset ι // S.Nonempty} =>
      quittingRootCoalitionMass forced S.val * reward S who)
    (Finset.mem_univ (quittingSingletonTerminal who))
  have hvalue : oneDateProductQuitEndpoint reward root who =
      oneDateProductOppContinue root who * reward (quittingSingletonTerminal who) who +
        ∑ S ∈ Finset.univ.erase (quittingSingletonTerminal who),
          quittingRootCoalitionMass forced S.val * reward S who := by
    rw [oneDateProductQuitEndpoint_eq_rowMoment, ← hforced, productRootRowMoment, ← hpeel, hsingle]
  have hrestBound : |∑ S ∈ Finset.univ.erase (quittingSingletonTerminal who),
      quittingRootCoalitionMass forced S.val * reward S who| ≤
      (1 - oneDateProductOppContinue root who) * bound := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← hrestMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [abs_mul, abs_of_nonneg (quittingRootCoalitionMass_nonneg forced S.val)]
    exact mul_le_mul_of_nonneg_left (hreward S who)
      (quittingRootCoalitionMass_nonneg forced S.val)
  have hmass0 : 0 ≤ 1 - oneDateProductOppContinue root who := by
    linarith [oneDateProductOppContinue_le_one root who]
  have hsolo := abs_le.mp (hreward (quittingSingletonTerminal who) who)
  have hrest := abs_le.mp hrestBound
  have hup : (1 - oneDateProductOppContinue root who) *
      reward (quittingSingletonTerminal who) who ≤
      (1 - oneDateProductOppContinue root who) * bound :=
    mul_le_mul_of_nonneg_left hsolo.2 hmass0
  have hlo : (1 - oneDateProductOppContinue root who) * (-bound) ≤
      (1 - oneDateProductOppContinue root who) * reward (quittingSingletonTerminal who) who :=
    mul_le_mul_of_nonneg_left hsolo.1 hmass0
  rw [hvalue, abs_le]
  constructor <;> nlinarith [hrest.1, hrest.2, hup, hlo]

/-! ## Transfer of a scaled estimate -/

omit [Fintype ι] [DecidableEq ι] in
/-- Turning a survival-scaled estimate into a plain one costs one more reward
bound times the scaling defect. -/
private theorem productRoot_abs_sub_of_scaled
    {value target scale defect bound slack : ℝ}
    (hscale1 : scale ≤ 1) (hdefect : 1 - scale ≤ defect) (hbound : 0 ≤ bound)
    (htarget : |target| ≤ bound)
    (hclose : |value - scale * target| ≤ bound * (1 - scale) + slack) :
    |value - target| ≤ 2 * bound * defect + slack := by
  have h1 := abs_le.mp hclose
  have h2 := abs_le.mp htarget
  have hd0 : (0 : ℝ) ≤ 1 - scale := by linarith
  have hup : (1 - scale) * target ≤ (1 - scale) * bound :=
    mul_le_mul_of_nonneg_left h2.2 hd0
  have hlo : (1 - scale) * (-bound) ≤ (1 - scale) * target :=
    mul_le_mul_of_nonneg_left h2.1 hd0
  have hb : (1 - scale) * bound ≤ defect * bound :=
    mul_le_mul_of_nonneg_right (by linarith) hbound
  have hexp : value - target = (value - scale * target) - (1 - scale) * target := by
    ring
  rw [abs_le, hexp]
  constructor <;> nlinarith [h1.1, h1.2, hup, hlo, hb]

/-! ## Uniform bounds on the two endpoints -/

/-- The zero-tail Quit endpoint is bounded by any uniform reward bound. -/
theorem productRoot_abs_quitEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (root : ι → PMF Bool) (who : ι) :
    |oneDateProductQuitEndpoint reward root who| ≤ bound := by
  rw [oneDateProductQuitEndpoint_eq_rowMoment]
  exact productRoot_abs_rowMoment_le reward hreward _ who

/-- The zero-tail Continue endpoint is bounded by any uniform reward bound. -/
theorem productRoot_abs_continueEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (root : ι → PMF Bool) (who : ι) :
    |oneDateProductContinueEndpoint reward root who| ≤ bound := by
  rw [oneDateProductContinueEndpoint_eq_rowMoment]
  exact productRoot_abs_rowMoment_le reward hreward _ who

/-! ## The three pure-time regimes at a marked date -/

/-- **Root date.**  Quitting exactly at the marked date is worth the Quit
endpoint of the marked row, up to twice the reward bound times the mass
absorbed before the mark. -/
theorem productRoot_abs_pureTimeDeviation_root_sub_quitEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (mark : ℕ) :
    |quittingPureTimeDeviationPayoff reward profile who (some mark) -
        oneDateProductQuitEndpoint reward
          (quittingProfileLiveRoot reward profile mark) who| ≤
      2 * bound * (1 - quittingLiveMass reward profile mark) := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hne : ∀ t, t < mark → (some mark : Option ℕ) ≠ some t := by
    intro t ht hcontra
    exact absurd (Option.some_injective ℕ hcontra) (by omega)
  have hdec := productRoot_pureTimeDeviationPayoff_sub_row_abs_le reward hreward profile
    who (some mark) mark hne
  have hzero : quittingLiveMass reward (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who (some mark))) (mark + 1) = 0 :=
    productRoot_liveMass_update_succ_eq_zero reward profile who
      (quittingPureTimeBehaviorStrategy reward who (some mark)) mark
      (productRoot_pureTimeRow_quit_toReal reward who mark)
  have hrow : productRootRowMoment reward
      (Function.update (quittingProfileLiveRoot reward profile mark) who
        (quittingPureTimeHazard (some mark) mark)) who =
      oneDateProductQuitEndpoint reward
        (quittingProfileLiveRoot reward profile mark) who := by
    rw [quittingPureTimeHazard_some_self, oneDateProductQuitEndpoint_eq_rowMoment]
  rw [hrow, hzero, mul_zero, add_zero] at hdec
  have hfinal := productRoot_abs_sub_of_scaled
    (value := quittingPureTimeDeviationPayoff reward profile who (some mark))
    (target := oneDateProductQuitEndpoint reward
      (quittingProfileLiveRoot reward profile mark) who)
    (scale := productRootDeletedLiveMass reward profile who mark)
    (defect := 1 - quittingLiveMass reward profile mark) (slack := 0)
    (productRootDeletedLiveMass_le_one reward profile who mark)
    (by linarith [productRoot_liveMass_le_deletedLiveMass reward profile who mark])
    hbound (productRoot_abs_quitEndpoint_le reward hreward _ who) (by linarith)
  linarith [hfinal]

/-- **Late dates and Never.**  A quit plan that continues through the marked
date is worth the Continue endpoint of the marked row, up to twice the reward
bound times the mass absorbed before the mark plus the reward bound times the
opponents' all-Continue mass there. -/
theorem productRoot_abs_pureTimeDeviation_late_sub_continueEndpoint_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (mark : ℕ)
    (quitTime : Option ℕ) (hlate : ∀ t, t ≤ mark → quitTime ≠ some t) :
    |quittingPureTimeDeviationPayoff reward profile who quitTime -
        oneDateProductContinueEndpoint reward
          (quittingProfileLiveRoot reward profile mark) who| ≤
      2 * bound * (1 - quittingLiveMass reward profile mark) +
        bound * oneDateProductOppContinue
          (quittingProfileLiveRoot reward profile mark) who := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hdec := productRoot_pureTimeDeviationPayoff_sub_row_abs_le reward hreward profile
    who quitTime mark (fun t ht => hlate t (by omega))
  have hrow : productRootRowMoment reward
      (Function.update (quittingProfileLiveRoot reward profile mark) who
        (quittingPureTimeHazard quitTime mark)) who =
      oneDateProductContinueEndpoint reward
        (quittingProfileLiveRoot reward profile mark) who := by
    rw [productRoot_pureTimeHazard_of_ne (hlate mark le_rfl),
      oneDateProductContinueEndpoint_eq_rowMoment]
  have htail : quittingLiveMass reward (Function.update profile who
      (quittingPureTimeBehaviorStrategy reward who quitTime)) (mark + 1) =
      productRootDeletedLiveMass reward profile who mark *
        oneDateProductOppContinue (quittingProfileLiveRoot reward profile mark) who := by
    rw [productRoot_liveMass_update_eq_deletedLiveMass reward profile who
      (quittingPureTimeBehaviorStrategy reward who quitTime) (mark + 1)
      (fun t ht => productRoot_pureTimeRow_continue_toReal reward who
        (hlate t (by omega))), productRootDeletedLiveMass_succ]
  rw [hrow, htail] at hdec
  have hslack : bound * (productRootDeletedLiveMass reward profile who mark *
      oneDateProductOppContinue (quittingProfileLiveRoot reward profile mark) who) ≤
      bound * oneDateProductOppContinue
        (quittingProfileLiveRoot reward profile mark) who := by
    refine mul_le_mul_of_nonneg_left ?_ hbound
    exact mul_le_of_le_one_left (oneDateProductOppContinue_nonneg _ who)
      (productRootDeletedLiveMass_le_one reward profile who mark)
  have hstep : |quittingPureTimeDeviationPayoff reward profile who quitTime -
      productRootDeletedLiveMass reward profile who mark *
        oneDateProductContinueEndpoint reward
          (quittingProfileLiveRoot reward profile mark) who| ≤
      bound * (1 - productRootDeletedLiveMass reward profile who mark) +
        bound * oneDateProductOppContinue
          (quittingProfileLiveRoot reward profile mark) who :=
    le_trans hdec (by linarith)
  exact productRoot_abs_sub_of_scaled
    (productRootDeletedLiveMass_le_one reward profile who mark)
    (by linarith [productRoot_liveMass_le_deletedLiveMass reward profile who mark])
    hbound (productRoot_abs_continueEndpoint_le reward hreward _ who) hstep

/-- **Early dates.**  Quitting strictly before the marked date is worth the
solo reward, up to four times the reward bound times the mass absorbed before
the mark. -/
theorem productRoot_abs_pureTimeDeviation_early_sub_solo_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (mark : ℕ)
    {early : ℕ} (hearly : early < mark) :
    |quittingPureTimeDeviationPayoff reward profile who (some early) -
        reward (quittingSingletonTerminal who) who| ≤
      4 * bound * (1 - quittingLiveMass reward profile mark) := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have hroot := productRoot_abs_pureTimeDeviation_root_sub_quitEndpoint_le reward hreward
    profile who early
  have hsolo := productRoot_abs_quitEndpoint_sub_solo_le reward hreward
    (quittingProfileLiveRoot reward profile early) who
  have hlive : quittingLiveMass reward profile mark ≤
      quittingLiveMass reward profile early :=
    quittingLiveMass_antitone reward profile (by omega)
  have hopp : quittingLiveMass reward profile mark ≤
      oneDateProductOppContinue (quittingProfileLiveRoot reward profile early) who := by
    have hstep : productRootDeletedLiveMass reward profile who (early + 1) ≤
        oneDateProductOppContinue (quittingProfileLiveRoot reward profile early) who := by
      rw [productRootDeletedLiveMass_succ]
      exact mul_le_of_le_one_left (oneDateProductOppContinue_nonneg _ who)
        (productRootDeletedLiveMass_le_one reward profile who early)
    have hchain : quittingLiveMass reward profile mark ≤
        productRootDeletedLiveMass reward profile who (early + 1) :=
      le_trans (quittingLiveMass_antitone reward profile (by omega))
        (productRoot_liveMass_le_deletedLiveMass reward profile who (early + 1))
    linarith
  have h1 := abs_le.mp hroot
  have h2 := abs_le.mp hsolo
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-! ## The cap sandwich at a marked date -/

/-- **Lower cap bound.**  The behavioral best-response cap dominates the
maximum of the two endpoints of the marked row, up to the marked defect. -/
theorem productRoot_max_endpoints_sub_defect_le_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (mark : ℕ) :
    max (oneDateProductQuitEndpoint reward
          (quittingProfileLiveRoot reward profile mark) who)
        (oneDateProductContinueEndpoint reward
          (quittingProfileLiveRoot reward profile mark) who) -
        (4 * bound * (1 - quittingLiveMass reward profile mark) +
          bound * oneDateProductOppContinue
            (quittingProfileLiveRoot reward profile mark) who) ≤
      quittingContinuationBestResponseValue reward profile who := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have habsorb : 0 ≤ 1 - quittingLiveMass reward profile mark := by
    linarith [quittingLiveMass_le_one reward profile mark]
  have hopp : 0 ≤ oneDateProductOppContinue
      (quittingProfileLiveRoot reward profile mark) who :=
    oneDateProductOppContinue_nonneg _ who
  have hbdd := bddAbove_range_quittingPureTimeDeviationPayoff reward profile who
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  have hQ : quittingPureTimeDeviationPayoff reward profile who (some mark) ≤
      sSup (Set.range (quittingPureTimeDeviationPayoff reward profile who)) :=
    le_csSup hbdd ⟨some mark, rfl⟩
  have hC : quittingPureTimeDeviationPayoff reward profile who none ≤
      sSup (Set.range (quittingPureTimeDeviationPayoff reward profile who)) :=
    le_csSup hbdd ⟨none, rfl⟩
  have hroot := abs_le.mp
    (productRoot_abs_pureTimeDeviation_root_sub_quitEndpoint_le reward hreward profile
      who mark)
  have hlate := abs_le.mp
    (productRoot_abs_pureTimeDeviation_late_sub_continueEndpoint_le reward hreward
      profile who mark none (fun t _ => by simp))
  refine sub_le_iff_le_add.mpr (max_le ?_ ?_)
  · nlinarith [hroot.1, hroot.2]
  · nlinarith [hlate.1, hlate.2]

/-- **Upper cap bound.**  The behavioral best-response cap is dominated by the
maximum of the solo reward and the two endpoints of the marked row, up to the
marked defect. -/
theorem productRoot_cap_le_max_solo_endpoints_add_defect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {bound : ℝ}
    (hreward : ∀ S player, |reward S player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) (mark : ℕ) :
    quittingContinuationBestResponseValue reward profile who ≤
      max (reward (quittingSingletonTerminal who) who)
          (max (oneDateProductQuitEndpoint reward
              (quittingProfileLiveRoot reward profile mark) who)
            (oneDateProductContinueEndpoint reward
              (quittingProfileLiveRoot reward profile mark) who)) +
        (4 * bound * (1 - quittingLiveMass reward profile mark) +
          bound * oneDateProductOppContinue
            (quittingProfileLiveRoot reward profile mark) who) := by
  have hbound : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hreward (quittingSingletonTerminal who) who)
  have habsorb : 0 ≤ 1 - quittingLiveMass reward profile mark := by
    linarith [quittingLiveMass_le_one reward profile mark]
  have hopp : 0 ≤ oneDateProductOppContinue
      (quittingProfileLiveRoot reward profile mark) who :=
    oneDateProductOppContinue_nonneg _ who
  have hsolo : reward (quittingSingletonTerminal who) who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)
          (oneDateProductContinueEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)) := le_max_left _ _
  have hquit : oneDateProductQuitEndpoint reward
      (quittingProfileLiveRoot reward profile mark) who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)
          (oneDateProductContinueEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hcont : oneDateProductContinueEndpoint reward
      (quittingProfileLiveRoot reward profile mark) who ≤
      max (reward (quittingSingletonTerminal who) who)
        (max (oneDateProductQuitEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)
          (oneDateProductContinueEndpoint reward
            (quittingProfileLiveRoot reward profile mark) who)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro value ⟨quitTime, rfl⟩
  cases quitTime with
  | none =>
      have hlate := abs_le.mp
        (productRoot_abs_pureTimeDeviation_late_sub_continueEndpoint_le reward hreward
          profile who mark none (fun t _ => by simp))
      nlinarith [hlate.1, hlate.2]
  | some q =>
      rcases lt_trichotomy q mark with hq | hq | hq
      · have hearly := abs_le.mp
          (productRoot_abs_pureTimeDeviation_early_sub_solo_le reward hreward profile
            who mark hq)
        nlinarith [hearly.1, hearly.2]
      · subst hq
        have hroot := abs_le.mp
          (productRoot_abs_pureTimeDeviation_root_sub_quitEndpoint_le reward hreward
            profile who q)
        nlinarith [hroot.1, hroot.2]
      · have hne : ∀ t, t ≤ mark → (some q : Option ℕ) ≠ some t := by
          intro t ht hcontra
          exact absurd (Option.some_injective ℕ hcontra) (by omega)
        have hlate := abs_le.mp
          (productRoot_abs_pureTimeDeviation_late_sub_continueEndpoint_le reward hreward
            profile who mark (some q) hne)
        nlinarith [hlate.1, hlate.2]

/-! ## Box form of the opponents' all-Continue mass -/

/-- The opponents' all-Continue mass read as a polynomial in the quit-rate
vector. -/
def productRootBoxOppContinue (w : ι → ℝ) (who : ι) : ℝ :=
  ∏ other ∈ Finset.univ.erase who, (1 - w other)

/-- The opponent survival polynomial is continuous. -/
theorem productRoot_continuous_boxOppContinue (who : ι) :
    Continuous fun w : ι → ℝ => productRootBoxOppContinue w who :=
  continuous_finsetProd _ fun other _ => continuous_const.sub (continuous_apply other)

/-- **Bridge.**  The opponents' all-Continue mass is the opponent survival
polynomial at the row's quit rates. -/
theorem oneDateProductOppContinue_eq_boxOppContinue (root : ι → PMF Bool) (who : ι) :
    oneDateProductOppContinue root who =
      productRootBoxOppContinue (fun k => (root k true).toReal) who := by
  rw [oneDateProductOppContinue_eq_prod_erase, productRootBoxOppContinue]
  refine Finset.prod_congr rfl fun other _ => ?_
  have hsum := quittingRoot_continueProbability_add_quitProbability root other
  linarith

/-! ## The law of an unpadded one-date profile with a sure quitter -/

omit [DecidableEq ι] in
/-- With a sure quitter at the root, a one-date-then-Never profile leaves no
live mass after its first stage. -/
theorem productRoot_liveMass_oneDateThenNever_succ_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {quitter : ι} (hsure : (root quitter true).toReal = 1)
    (time : ℕ) :
    quittingLiveMass reward (quittingOneDateThenNeverProfile reward root)
      (time + 1) = 0 := by
  have hone : quittingLiveMass reward
      (quittingOneDateThenNeverProfile reward root) 1 = 0 := by
    rw [quittingLiveMass_succ, quittingLiveMass_zero, one_mul,
      quittingJointContinueMass_eq_product]
    have hfactor : ((quittingOneDateThenNeverProfile reward root) quitter 0
        (quittingLiveHist reward 0) false).toReal = 0 := by
      show ((root quitter) false).toReal = 0
      have hsum := quittingRoot_continueProbability_add_quitProbability root quitter
      linarith
    exact Finset.prod_eq_zero (Finset.mem_univ quitter) hfactor
  have hle := quittingLiveMass_antitone reward
    (quittingOneDateThenNeverProfile reward root) (show 1 ≤ time + 1 by omega)
  have hnn := quittingLiveMass_nonneg reward
    (quittingOneDateThenNeverProfile reward root) (time + 1)
  linarith

/-- **Coalition law.**  With a sure quitter at the root, every coalition
coordinate of the one-date-then-Never law is the root's exact coalition
mass. -/
theorem productRoot_terminalOutcomeMass_oneDateThenNever_some
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {quitter : ι} (hsure : (root quitter true).toReal = 1)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward
        (quittingOneDateThenNeverProfile reward root) (some terminal) =
      quittingRootCoalitionMass root terminal.val := by
  rw [terminalOutcomeChronology_terminalOutcomeMass_some_eq_tsum_stage,
    tsum_eq_single 0 (fun time htime => ?_)]
  · rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingLiveMass_zero, one_mul]
    rfl
  · obtain ⟨past, rfl⟩ := Nat.exists_eq_succ_of_ne_zero htime
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      productRoot_liveMass_oneDateThenNever_succ_eq_zero reward root hsure past,
      zero_mul]

omit [DecidableEq ι] in
/-- **Never coordinate.**  With a sure quitter at the root, the
one-date-then-Never law leaves no mass on Never. -/
theorem productRoot_terminalOutcomeMass_oneDateThenNever_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) {quitter : ι}
    (hsure : (root quitter true).toReal = 1) :
    quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward root) none = 0 := by
  have hnone : quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward root) none =
      quittingLiveMassLimit reward
        (quittingOneDateThenNeverProfile reward root) := rfl
  have hle := quittingLiveMassLimit_le reward
    (quittingOneDateThenNeverProfile reward root) 1
  have hzero := productRoot_liveMass_oneDateThenNever_succ_eq_zero reward root hsure 0
  have hnn := quittingLiveMassLimit_nonneg reward
    (quittingOneDateThenNeverProfile reward root)
  rw [hnone]
  linarith

/-! ## Semantic realization at the product base -/

/-- The common cap sandwich behind strict and padded product-base realization.
Zero Never and singleton mass produce one product root with two sure quitters.
Its prescribed payoff is the limiting prescribed payoff, while each limiting
deviation cap lies between the root endpoint maximum and the maximum of that
quantity with the corresponding singleton reward. -/
theorem exists_twoSureProductRoot_limitCapSandwich
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hlaw : ∀ outcome, Filter.Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      Filter.atTop (nhds (mu outcome)))
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) {R : ℝ}
    (hR : ∀ S player, |reward S player| ≤ R)
    (z : QuittingTerminalSemanticPair ι)
    (hsem : Filter.Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      Filter.atTop (nhds z)) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalPayoff reward
        (quittingOneDateThenNeverProfile reward root) = z.1 ∧
      (∀ k,
        max (oneDateProductQuitEndpoint reward root k)
            (oneDateProductContinueEndpoint reward root k) ≤ z.2 k ∧
        z.2 k ≤ max (reward (quittingSingletonTerminal k) k)
          (max (oneDateProductQuitEndpoint reward root k)
            (oneDateProductContinueEndpoint reward root k))) ∧
      ∀ outcome, quittingTerminalOutcomeMass reward
        (quittingOneDateThenNeverProfile reward root) outcome = mu outcome := by
  classical
  obtain ⟨w, i, j, phi, date, hij, hphi, hw0, hw1, hwi, hwj, hlaweq, hrootconv,
    hEzero⟩ := zeroSingletonProductBase_zeroNever_zeroSingleton_exists_selectionData reward profiles
      mu hlaw hNever hsingleton hcard
  obtain ⟨root, hrootdef⟩ : ∃ r : ι → PMF Bool,
      r = fun k => quittingHazardCoin (w k) (hw0 k) (hw1 k) := ⟨_, rfl⟩
  have hrates : (fun k => (root k true).toReal) = w := by
    funext k
    rw [hrootdef]
    exact quittingHazardCoin_true_toReal (w k) (hw0 k) (hw1 k)
  have hratek : ∀ k, (root k true).toReal = w k := fun k => congrFun hrates k
  have hsurei : (root i true).toReal = 1 := by rw [hratek i, hwi]
  have hsurej : (root j true).toReal = 1 := by rw [hratek j, hwj]
  have hquitter : ∀ k : ι, ∃ q : ι, q ≠ k ∧ (root q true).toReal = 1 := by
    intro k
    by_cases hik : i = k
    · refine ⟨j, ?_, hsurej⟩
      rw [← hik]
      exact Ne.symm hij
    · exact ⟨i, hik, hsurei⟩
  -- Step A: the terminal outcome law of the one-date-then-Never profile.
  have hlawAll : ∀ outcome, quittingTerminalOutcomeMass reward
      (quittingOneDateThenNeverProfile reward root) outcome = mu outcome := by
    intro outcome
    cases outcome with
    | none =>
        rw [productRoot_terminalOutcomeMass_oneDateThenNever_none reward root hsurei,
          hNever]
    | some S =>
        rw [productRoot_terminalOutcomeMass_oneDateThenNever_some reward root hsurei S,
          zeroSingletonProductBase_coalitionMass_eq_boxCoalition, hrates]
        exact (hlaweq S).symm
  -- Step B: the prescribed coordinate.
  have hmomentEq : quittingTerminalPayoff reward
      (quittingOneDateThenNeverProfile reward root) =
      quittingTerminalRewardMoment reward mu := by
    rw [← quittingTerminalRewardMoment_outcomeMass reward
      (quittingOneDateThenNeverProfile reward root)]
    exact congrArg (quittingTerminalRewardMoment reward) (funext hlawAll)
  have hz1 : z.1 = quittingTerminalRewardMoment reward mu := by
    have hfst : Tendsto
        (fun n => (quittingTerminalSemanticPair reward (profiles n)).1) atTop
        (nhds z.1) := (continuous_fst.tendsto z).comp hsem
    have hmom : Tendsto (fun n => quittingTerminalRewardMoment reward
        (quittingTerminalOutcomeMass reward (profiles n))) atTop
        (nhds (quittingTerminalRewardMoment reward mu)) :=
      ((continuous_quittingTerminalRewardMoment reward).tendsto mu).comp
        (tendsto_pi_nhds.mpr hlaw)
    refine tendsto_nhds_unique hfst (hmom.congr fun n => ?_)
    exact quittingTerminalRewardMoment_outcomeMass reward (profiles n)
  -- Step C: the cap coordinate.
  obtain ⟨rows, hrows⟩ : ∃ f : ℕ → ι → PMF Bool, ∀ m, f m =
      quittingProfileLiveRoot reward (profiles (phi m)) (date (phi m)) :=
    ⟨_, fun _ => rfl⟩
  have hratesconv : Tendsto (fun m => fun who => (rows m who true).toReal) atTop
      (nhds w) := by
    refine tendsto_pi_nhds.mpr fun who => ?_
    simpa only [hrows] using hrootconv who
  have hQconv : ∀ k, Tendsto (fun m => oneDateProductQuitEndpoint reward (rows m) k) atTop
      (nhds (oneDateProductQuitEndpoint reward root k)) := by
    intro k
    have hbox := ((productRoot_continuous_endpointBox reward k 1).tendsto w).comp
      hratesconv
    rw [oneDateProductQuitEndpoint_eq_endpointBox reward root k, hrates]
    exact hbox.congr fun m => (oneDateProductQuitEndpoint_eq_endpointBox reward (rows m) k).symm
  have hCconv : ∀ k, Tendsto (fun m => oneDateProductContinueEndpoint reward (rows m) k)
      atTop (nhds (oneDateProductContinueEndpoint reward root k)) := by
    intro k
    have hbox := ((productRoot_continuous_endpointBox reward k 0).tendsto w).comp
      hratesconv
    rw [oneDateProductContinueEndpoint_eq_endpointBox reward root k, hrates]
    exact hbox.congr fun m =>
      (oneDateProductContinueEndpoint_eq_endpointBox reward (rows m) k).symm
  have hoppconv : ∀ k, Tendsto (fun m => oneDateProductOppContinue (rows m) k) atTop
      (nhds 0) := by
    intro k
    obtain ⟨q, hqne, hqsure⟩ := hquitter k
    have hzero : productRootBoxOppContinue w k = 0 := by
      rw [← hrates, ← oneDateProductOppContinue_eq_boxOppContinue]
      exact oneDateProductOppContinue_eq_zero_of_sureQuitter root k hqne hqsure
    have hbox := ((productRoot_continuous_boxOppContinue k).tendsto w).comp hratesconv
    rw [hzero] at hbox
    exact hbox.congr fun m => (oneDateProductOppContinue_eq_boxOppContinue (rows m) k).symm
  have hBconv : ∀ k, Tendsto (fun m =>
      quittingContinuationBestResponseValue reward (profiles (phi m)) k) atTop
      (nhds (z.2 k)) := by
    intro k
    have hsnd : Tendsto
        (fun n => (quittingTerminalSemanticPair reward (profiles n)).2) atTop
        (nhds z.2) := (continuous_snd.tendsto z).comp hsem
    exact (tendsto_pi_nhds.mp (hsnd.comp hphi.tendsto_atTop)) k
  obtain ⟨err, herr⟩ : ∃ f : ℕ → ι → ℝ, ∀ m k, f m k =
      4 * R * (1 - quittingLiveMass reward (profiles (phi m)) (date (phi m))) +
        R * oneDateProductOppContinue (rows m) k := ⟨_, fun _ _ => rfl⟩
  have herrconv : ∀ k, Tendsto (fun m => err m k) atTop (nhds 0) := by
    intro k
    have h1 : Tendsto (fun m => 4 * R *
        (1 - quittingLiveMass reward (profiles (phi m)) (date (phi m)))) atTop
        (nhds 0) := by
      simpa using hEzero.const_mul (4 * R)
    have h2 : Tendsto (fun m => R * oneDateProductOppContinue (rows m) k) atTop (nhds 0) := by
      simpa using (hoppconv k).const_mul R
    have h3 := h1.add h2
    rw [add_zero] at h3
    simpa only [herr] using h3
  have hcapSandwich : ∀ k,
      max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k) ≤ z.2 k ∧
      z.2 k ≤ max (reward (quittingSingletonTerminal k) k)
        (max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k)) := by
    intro k
    have hlowerSeq : ∀ m, max (oneDateProductQuitEndpoint reward (rows m) k)
        (oneDateProductContinueEndpoint reward (rows m) k) - err m k ≤
        quittingContinuationBestResponseValue reward (profiles (phi m)) k := by
      intro m
      rw [herr, hrows]
      exact productRoot_max_endpoints_sub_defect_le_cap reward hR (profiles (phi m)) k
        (date (phi m))
    have hlowerLim : Tendsto (fun m => max (oneDateProductQuitEndpoint reward (rows m) k)
        (oneDateProductContinueEndpoint reward (rows m) k) - err m k) atTop
        (nhds (max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k))) := by
      simpa using ((hQconv k).max (hCconv k)).sub (herrconv k)
    have hlower := le_of_tendsto_of_tendsto' hlowerLim (hBconv k) hlowerSeq
    have hupperSeq : ∀ m,
        quittingContinuationBestResponseValue reward (profiles (phi m)) k ≤
        max (reward (quittingSingletonTerminal k) k)
          (max (oneDateProductQuitEndpoint reward (rows m) k)
            (oneDateProductContinueEndpoint reward (rows m) k)) + err m k := by
      intro m
      rw [herr, hrows]
      exact productRoot_cap_le_max_solo_endpoints_add_defect reward hR
        (profiles (phi m)) k (date (phi m))
    have hupperLim : Tendsto (fun m =>
        max (reward (quittingSingletonTerminal k) k)
          (max (oneDateProductQuitEndpoint reward (rows m) k)
            (oneDateProductContinueEndpoint reward (rows m) k)) + err m k) atTop
        (nhds (max (reward (quittingSingletonTerminal k) k)
          (max (oneDateProductQuitEndpoint reward root k)
            (oneDateProductContinueEndpoint reward root k)))) := by
      simpa using
        (tendsto_const_nhds.max ((hQconv k).max (hCconv k))).add (herrconv k)
    have hupper := le_of_tendsto_of_tendsto' (hBconv k) hupperLim hupperSeq
    exact ⟨hlower, hupper⟩
  refine ⟨root, i, j, hij, hsurei, hsurej, ?_, hcapSandwich, hlawAll⟩
  exact hmomentEq.trans hz1.symm

/-- Strict singleton margins collapse the common cap sandwich to the endpoint
maximum, so the unpadded root-then-Never profile realizes the semantic pair. -/
theorem exists_twoSureProductRootThenNever_realizing_semantics_of_strictSingletonMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hlaw : ∀ outcome, Filter.Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      Filter.atTop (nhds (mu outcome)))
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) {R : ℝ}
    (hR : ∀ S player, |reward S player| ≤ R)
    (z : QuittingTerminalSemanticPair ι)
    (hsem : Filter.Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      Filter.atTop (nhds z))
    (hstrict : ∀ k, reward (quittingSingletonTerminal k) k < z.2 k) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
        (quittingOneDateThenNeverProfile reward root) = z ∧
      ∀ outcome, quittingTerminalOutcomeMass reward
        (quittingOneDateThenNeverProfile reward root) outcome = mu outcome := by
  classical
  obtain ⟨root, i, j, hij, hsurei, hsurej, hpayoff, hcapSandwich, hlawRoot⟩ :=
    exists_twoSureProductRoot_limitCapSandwich reward profiles mu hlaw hNever
      hsingleton hcard hR z hsem
  have hquitter : ∀ k : ι, ∃ q : ι, q ≠ k ∧ (root q true).toReal = 1 := by
    intro k
    by_cases hik : i = k
    · refine ⟨j, ?_, hsurej⟩
      rw [← hik]
      exact Ne.symm hij
    · exact ⟨i, hik, hsurei⟩
  have hcapRoot : ∀ k, quittingContinuationBestResponseValue reward
      (quittingOneDateThenNeverProfile reward root) k =
      max (oneDateProductQuitEndpoint reward root k)
        (oneDateProductContinueEndpoint reward root k) := by
    intro k
    obtain ⟨q, hqne, hqsure⟩ := hquitter k
    exact oneDateProductQuittingContinuationBestResponseValue_oneDateThenNever_sureQuitter
      reward root k hqne hqsure
  have hcapLimit : ∀ k,
      z.2 k = max (oneDateProductQuitEndpoint reward root k)
        (oneDateProductContinueEndpoint reward root k) := by
    intro k
    obtain ⟨hlower, hupper⟩ := hcapSandwich k
    apply le_antisymm ?_ hlower
    by_contra hnot
    have hendpoint : max (oneDateProductQuitEndpoint reward root k)
        (oneDateProductContinueEndpoint reward root k) < z.2 k :=
      lt_of_not_ge hnot
    have hmaximum : max (reward (quittingSingletonTerminal k) k)
        (max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k)) < z.2 k :=
      max_lt (hstrict k) hendpoint
    exact (not_lt_of_ge hupper) hmaximum
  refine ⟨root, i, j, hij, hsurei, hsurej, ?_, hlawRoot⟩
  apply Prod.ext hpayoff
  funext k
  change quittingContinuationBestResponseValue reward
      (quittingOneDateThenNeverProfile reward root) k = z.2 k
  rw [hcapRoot k, hcapLimit k]

/-- Nonstrict singleton margins collapse the common cap sandwich after one
all-Continue padding row.  The padding preserves the terminal outcome law and
prescribed payoff while making the singleton deviation an explicit cap arm. -/
theorem exists_twoSurePaddedProductRoot_realizing_semantics_of_singletonMargin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (mu : QuittingTerminalOutcome ι → ℝ)
    (hlaw : ∀ outcome, Filter.Tendsto
      (fun n => quittingTerminalOutcomeMass reward (profiles n) outcome)
      Filter.atTop (nhds (mu outcome)))
    (hNever : mu none = 0)
    (hsingleton : ∀ who, mu (some (quittingSingletonTerminal who)) = 0)
    (hcard : 1 < Fintype.card ι) {R : ℝ}
    (hR : ∀ S player, |reward S player| ≤ R)
    (z : QuittingTerminalSemanticPair ι)
    (hsem : Filter.Tendsto
      (fun n => quittingTerminalSemanticPair reward (profiles n))
      Filter.atTop (nhds z))
    (hmargin : ∀ k, reward (quittingSingletonTerminal k) k ≤ z.2 k) :
    ∃ (root : ι → PMF Bool) (i j : ι), i ≠ j ∧
      (root i true).toReal = 1 ∧ (root j true).toReal = 1 ∧
      quittingTerminalSemanticPair reward
        (oneDateProductPaddedOneDateProfile reward 1 root) = z ∧
      ∀ outcome, quittingTerminalOutcomeMass reward
        (oneDateProductPaddedOneDateProfile reward 1 root) outcome = mu outcome := by
  classical
  obtain ⟨root, i, j, hij, hsurei, hsurej, hpayoff, hcapSandwich, hlawRoot⟩ :=
    exists_twoSureProductRoot_limitCapSandwich reward profiles mu hlaw hNever
      hsingleton hcard hR z hsem
  have hquitter : ∀ k : ι, ∃ q : ι, q ≠ k ∧ (root q true).toReal = 1 := by
    intro k
    by_cases hik : i = k
    · refine ⟨j, ?_, hsurej⟩
      rw [← hik]
      exact Ne.symm hij
    · exact ⟨i, hik, hsurei⟩
  have hlawPadded : ∀ outcome, quittingTerminalOutcomeMass reward
      (oneDateProductPaddedOneDateProfile reward 1 root) outcome = mu outcome := by
    intro outcome
    have hlawPrefix := congrFun
      (quittingTerminalOutcomeMass_allContinuePrefix_eq reward
        (quittingOneDateThenNeverProfile reward root) 1) outcome
    rw [← oneDateProductPaddedOneDateProfile_eq] at hlawPrefix
    exact hlawPrefix.trans (hlawRoot outcome)
  have hpayoffPadded : quittingTerminalPayoff reward
      (oneDateProductPaddedOneDateProfile reward 1 root) = z.1 := by
    calc
      quittingTerminalPayoff reward
          (oneDateProductPaddedOneDateProfile reward 1 root) =
          quittingTerminalRewardMoment reward mu := by
        rw [← quittingTerminalRewardMoment_outcomeMass reward
          (oneDateProductPaddedOneDateProfile reward 1 root)]
        exact congrArg (quittingTerminalRewardMoment reward) (funext hlawPadded)
      _ = quittingTerminalPayoff reward
          (quittingOneDateThenNeverProfile reward root) := by
        rw [← quittingTerminalRewardMoment_outcomeMass reward
          (quittingOneDateThenNeverProfile reward root)]
        exact congrArg (quittingTerminalRewardMoment reward) (funext hlawRoot).symm
      _ = z.1 := hpayoff
  have hcapLimit : ∀ k, z.2 k =
      max (reward (quittingSingletonTerminal k) k)
        (max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k)) := by
    intro k
    obtain ⟨hlower, hupper⟩ := hcapSandwich k
    exact le_antisymm hupper (max_le (hmargin k) hlower)
  have hcapPadded : ∀ k, quittingContinuationBestResponseValue reward
      (oneDateProductPaddedOneDateProfile reward 1 root) k =
      max (reward (quittingSingletonTerminal k) k)
        (max (oneDateProductQuitEndpoint reward root k)
          (oneDateProductContinueEndpoint reward root k)) := by
    intro k
    obtain ⟨q, hqne, hqsure⟩ := hquitter k
    have hzero : oneDateProductOppContinue root k = 0 :=
      oneDateProductOppContinue_eq_zero_of_sureQuitter root k hqne hqsure
    rw [oneDateProductQuittingContinuationBestResponseValue_paddedOneDateProfile
      reward (by omega : 0 < 1) root k, hzero, zero_mul, add_zero]
  refine ⟨root, i, j, hij, hsurei, hsurej, ?_, hlawPadded⟩
  apply Prod.ext hpayoffPadded
  funext k
  change quittingContinuationBestResponseValue reward
      (oneDateProductPaddedOneDateProfile reward 1 root) k = z.2 k
  rw [hcapPadded k, hcapLimit k]

end GameTheory
