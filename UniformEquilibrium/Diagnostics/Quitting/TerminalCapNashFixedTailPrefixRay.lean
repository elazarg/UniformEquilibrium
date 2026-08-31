/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw

/-!
# Fixed-tail cap-Nash prefix rays

This module builds one coherent infinite sequence of exact cap-Nash
roots over a fixed executable behavioral tail.  It records exact finite-prefix
debt and survival identities.  It assumes no reward bound, global minimum,
source, or equilibrium consumer.
-/

noncomputable section

open Filter Math.Probability
open scoped Topology

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The actual profile formed by the reverse prefix
`roots (depth - 1), ..., roots 0` over one fixed behavioral tail. -/
def quittingFixedTailCapNashPrefixProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (depth : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingReversePrefixProfile reward roots (fun _ => terminal) depth

omit [DecidableEq ι] in
@[simp]
theorem quittingFixedTailCapNashPrefixProfile_zero
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) :
    quittingFixedTailCapNashPrefixProfile reward terminal roots 0 = terminal := rfl

omit [DecidableEq ι] in
@[simp]
theorem quittingFixedTailCapNashPrefixProfile_succ
    (terminal : (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (depth : ℕ) :
    quittingFixedTailCapNashPrefixProfile reward terminal roots (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (quittingFixedTailCapNashPrefixProfile reward terminal roots depth) := rfl

/-- A coherent infinite root sequence, each root exact Nash against the
unrestricted behavioral cap of the actual prefix built before it. -/
structure QuittingFixedTailCapNashPrefixRay
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) where
  roots : ℕ → ι → PMF Bool
  root_isCapNash : ∀ depth,
    IsεQuittingRootNash reward
      (fun player => quittingContinuationBestResponseValue reward
        (quittingFixedTailCapNashPrefixProfile reward terminal roots depth)
        player)
      0 (roots depth)

namespace QuittingFixedTailCapNashPrefixRay

/-- A coherent fixed-tail exact cap-Nash prefix ray exists over every actual
behavioral tail. -/
theorem exists_quittingFixedTailCapNashPrefixRay
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingFixedTailCapNashPrefixRay reward terminal) := by
  let nextRoot (profile : (quittingGame reward).BehaviorProfile) :
      ι → PMF Bool :=
    Classical.choose (exists_isZeroQuittingRootNash
      (reward := reward)
      (fun player => quittingContinuationBestResponseValue reward profile player))
  have nextRoot_isCapNash (profile : (quittingGame reward).BehaviorProfile) :
      IsεQuittingRootNash reward
        (fun player => quittingContinuationBestResponseValue reward profile player)
        0 (nextRoot profile) :=
    Classical.choose_spec (exists_isZeroQuittingRootNash
      (reward := reward)
      (fun player => quittingContinuationBestResponseValue reward profile player))
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    Nat.rec terminal (fun _ profile =>
      quittingRootThenContinuationProfile reward (nextRoot profile) profile)
  let roots : ℕ → ι → PMF Bool := fun depth => nextRoot (profiles depth)
  have profile_eq (depth : ℕ) :
      quittingFixedTailCapNashPrefixProfile reward terminal roots depth =
        profiles depth := by
    induction depth with
    | zero => rfl
    | succ depth ih =>
        rw [quittingFixedTailCapNashPrefixProfile_succ, ih]
  refine ⟨⟨roots, ?_⟩⟩
  intro depth
  rw [profile_eq]
  exact nextRoot_isCapNash (profiles depth)

variable {terminal : (quittingGame reward).BehaviorProfile}
variable (ray : QuittingFixedTailCapNashPrefixRay reward terminal)

/-- The finite root word underlying the depth-`depth` ray profile. -/
def rootStack (depth : ℕ) : List (ι → PMF Bool) :=
  quittingReversePrefixRootStack ray.roots depth

/-- Joint Continue product of the depth-`depth` ray prefix. -/
def continueProduct (depth : ℕ) : ℝ :=
  quittingCapNashStackContinueProduct (ray.rootStack depth)

@[simp]
theorem rootStack_zero : ray.rootStack 0 = [] := rfl

@[simp]
theorem rootStack_succ (depth : ℕ) :
    ray.rootStack (depth + 1) = ray.roots depth :: ray.rootStack depth := rfl

@[simp]
theorem rootStack_length (depth : ℕ) :
    (ray.rootStack depth).length = depth :=
  quittingReversePrefixRootStack_length ray.roots depth

@[simp]
theorem continueProduct_zero : ray.continueProduct 0 = 1 := rfl

@[simp]
theorem continueProduct_succ (depth : ℕ) :
    ray.continueProduct (depth + 1) =
      quittingStationaryContinueMass (ray.roots depth) *
        ray.continueProduct depth := rfl

/-- Every finite word of the coherent ray is a cap-Nash root stack over the
same fixed tail. -/
theorem isCapNashRootStack (depth : ℕ) :
    IsQuittingCapNashRootStack reward (ray.rootStack depth) terminal := by
  induction depth with
  | zero => exact isQuittingCapNashRootStack_nil reward terminal
  | succ depth ih =>
      rw [rootStack_succ, isQuittingCapNashRootStack_cons_iff]
      exact ⟨ray.root_isCapNash depth, ih⟩

/-- Exact playerwise debt recursion along the coherent ray. -/
theorem deviationDebt_succ (depth : ℕ) (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingFixedTailCapNashPrefixProfile
          reward terminal ray.roots (depth + 1)) who =
      quittingStationaryContinueMass (ray.roots depth) *
        quittingTerminalDeviationDebt reward
          (quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) who := by
  rw [quittingFixedTailCapNashPrefixProfile_succ]
  exact
    quittingTerminalDeviationDebt_rootThenContinuation_eq_continueMass_mul_of_capNash
      (reward := reward) (ray.roots depth)
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)
      who (ray.root_isCapNash depth)

/-- Exact total-debt recursion along the coherent ray. -/
theorem debtSum_succ (depth : ℕ) :
    quittingTerminalDebtSum reward
        (quittingFixedTailCapNashPrefixProfile
          reward terminal ray.roots (depth + 1)) =
      quittingStationaryContinueMass (ray.roots depth) *
        quittingTerminalDebtSum reward
          (quittingFixedTailCapNashPrefixProfile
            reward terminal ray.roots depth) := by
  rw [quittingFixedTailCapNashPrefixProfile_succ]
  exact quittingTerminalDebtSum_rootThenContinuation_eq_continueMass_mul_of_capNash
    (reward := reward) (ray.roots depth)
    (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)
    (ray.root_isCapNash depth)

/-- Exact folded playerwise debt identity. -/
theorem deviationDebt_eq_continueProduct_mul (depth : ℕ) (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth) who =
      ray.continueProduct depth *
        quittingTerminalDeviationDebt reward terminal who := by
  exact quittingTerminalDeviationDebt_capNashRootStack_eq
    (reward := reward) (ray.rootStack depth) terminal who
    (ray.isCapNashRootStack depth)

/-- Exact folded total-debt identity. -/
theorem debtSum_eq_continueProduct_mul (depth : ℕ) :
    quittingTerminalDebtSum reward
        (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth) =
      ray.continueProduct depth * quittingTerminalDebtSum reward terminal := by
  exact quittingTerminalDebtSum_capNashRootStack_eq
    (reward := reward) (ray.rootStack depth) terminal
    (ray.isCapNashRootStack depth)

theorem continueProduct_nonneg (depth : ℕ) :
    0 ≤ ray.continueProduct depth :=
  quittingCapNashStackContinueProduct_nonneg (ray.rootStack depth)

theorem continueProduct_le_one (depth : ℕ) :
    ray.continueProduct depth ≤ 1 :=
  quittingCapNashStackContinueProduct_le_one (ray.rootStack depth)

theorem continueProduct_antitone : Antitone ray.continueProduct := by
  apply antitone_nat_of_succ_le
  intro depth
  rw [ray.continueProduct_succ]
  exact mul_le_of_le_one_left (ray.continueProduct_nonneg depth)
    (quittingStationaryContinueMass_le_one (ray.roots depth))

/-- The decreasing joint Continue products have a canonical limit. -/
def continueProductLimit : ℝ := ⨅ depth, ray.continueProduct depth

theorem continueProduct_tendsto_limit :
    Tendsto ray.continueProduct atTop (nhds ray.continueProductLimit) := by
  apply tendsto_atTop_ciInf ray.continueProduct_antitone
  refine ⟨0, ?_⟩
  rintro _ ⟨depth, rfl⟩
  exact ray.continueProduct_nonneg depth

theorem continueProductLimit_le (depth : ℕ) :
    ray.continueProductLimit ≤ ray.continueProduct depth := by
  exact ciInf_le (by
    refine ⟨0, ?_⟩
    rintro _ ⟨index, rfl⟩
    exact ray.continueProduct_nonneg index) depth

/-- A positive uniform debt floor yields the sharp joint-survival floor. -/
theorem debtFloor_div_tailDebt_le_continueProduct
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth))
    (depth : ℕ) :
    Dstar / quittingTerminalDebtSum reward terminal ≤
      ray.continueProduct depth := by
  have htailPos : 0 < quittingTerminalDebtSum reward terminal := by
    simpa using hDstar.trans_le (hfloor 0)
  have hfloorDepth := hfloor depth
  rw [ray.debtSum_eq_continueProduct_mul depth] at hfloorDepth
  exact (div_le_iff₀ htailPos).2 (by simpa [mul_comm] using hfloorDepth)

theorem debtFloor_div_tailDebt_le_continueProductLimit
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    Dstar / quittingTerminalDebtSum reward terminal ≤
      ray.continueProductLimit := by
  apply le_ciInf
  exact ray.debtFloor_div_tailDebt_le_continueProduct hDstar hfloor

theorem continueProductLimit_pos
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    0 < ray.continueProductLimit := by
  have htailPos : 0 < quittingTerminalDebtSum reward terminal := by
    simpa using hDstar.trans_le (hfloor 0)
  exact (div_pos hDstar htailPos).trans_le
    (ray.debtFloor_div_tailDebt_le_continueProductLimit hDstar hfloor)

/-- Positive limiting joint survival forces each newly prepended root's joint
Continue mass to tend to one. -/
theorem rootContinueMass_tendsto_one
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    Tendsto (fun depth => quittingStationaryContinueMass (ray.roots depth))
      atTop (nhds 1) := by
  have hlimit := ray.continueProduct_tendsto_limit
  have hlimitPos := ray.continueProductLimit_pos hDstar hfloor
  have hshift : Tendsto (fun depth => ray.continueProduct (depth + 1))
      atTop (nhds ray.continueProductLimit) := by
    convert hlimit.comp (tendsto_add_atTop_nat 1) using 1
    funext depth
    simp
  have hratio := hshift.div hlimit hlimitPos.ne'
  have hratioFunction :
      (fun depth => ray.continueProduct (depth + 1) /
        ray.continueProduct depth) =
      fun depth => quittingStationaryContinueMass (ray.roots depth) := by
    funext depth
    rw [ray.continueProduct_succ]
    have hcurrent : ray.continueProduct depth ≠ 0 := by
      exact ne_of_gt ((ray.continueProductLimit_pos hDstar hfloor).trans_le
        (ray.continueProductLimit_le depth))
    field_simp [hcurrent]
  rw [show ((fun depth => ray.continueProduct (depth + 1)) /
      ray.continueProduct) =
      (fun depth => ray.continueProduct (depth + 1) /
        ray.continueProduct depth) by rfl,
    hratioFunction, div_self hlimitPos.ne'] at hratio
  exact hratio

/-- Hence the one-stage absorption masses of the coherent roots vanish. -/
theorem rootAbsorptionMass_tendsto_zero
    {Dstar : ℝ} (hDstar : 0 < Dstar)
    (hfloor : ∀ depth, Dstar ≤ quittingTerminalDebtSum reward
      (quittingFixedTailCapNashPrefixProfile reward terminal ray.roots depth)) :
    Tendsto (fun depth => quittingRootAbsorptionMass (ray.roots depth))
      atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  simpa only [quittingRootAbsorptionMass, sub_self] using
    hone.sub (ray.rootContinueMass_tendsto_one hDstar hfloor)

end QuittingFixedTailCapNashPrefixRay

end GameTheory
