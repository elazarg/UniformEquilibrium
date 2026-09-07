import UniformEquilibrium.Quitting.Paths.InfiniteJointSurvivalDebt
import UniformEquilibrium.Quitting.Root.ExactCapClockTransport
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # Actual exact-prefix rays from arbitrary executable sources -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- One literal infinite genealogy obtained by repeatedly choosing an exact
product root against the actual current profile payoff. -/
structure QuittingActualExactPrefixRay
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) where
  profiles : ℕ → (quittingGame reward).BehaviorProfile
  roots : ℕ → ι → PMF Bool
  profiles_zero : profiles 0 = source
  profiles_succ : ∀ depth, profiles (depth + 1) =
    quittingRootThenContinuationProfile reward (roots depth) (profiles depth)
  roots_exact : ∀ depth, IsεQuittingRootNash reward
    (fun player ↦ quittingTerminalPayoff reward (profiles depth) player)
    0 (roots depth)

/-- Exact mixed-root existence recursively produces an actual exact-prefix
ray from every executable profile. -/
theorem exists_quittingActualExactPrefixRay
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) :
    Nonempty (QuittingActualExactPrefixRay reward source) := by
  let nextRoot (profile : (quittingGame reward).BehaviorProfile) :
      ι → PMF Bool :=
    Classical.choose (exists_isZeroQuittingRootNash
      (reward := reward)
      (fun player ↦ quittingTerminalPayoff reward profile player))
  have nextRoot_exact (profile : (quittingGame reward).BehaviorProfile) :
      IsεQuittingRootNash reward
        (fun player ↦ quittingTerminalPayoff reward profile player)
        0 (nextRoot profile) :=
    Classical.choose_spec (exists_isZeroQuittingRootNash
      (reward := reward)
      (fun player ↦ quittingTerminalPayoff reward profile player))
  let profiles : ℕ → (quittingGame reward).BehaviorProfile :=
    Nat.rec source (fun _ profile ↦
      quittingRootThenContinuationProfile reward (nextRoot profile) profile)
  let roots : ℕ → ι → PMF Bool := fun depth ↦ nextRoot (profiles depth)
  exact ⟨⟨profiles, roots, rfl, fun _ ↦ rfl,
    fun depth ↦ nextRoot_exact (profiles depth)⟩⟩

namespace QuittingActualExactPrefixRay

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {source : (quittingGame reward).BehaviorProfile}

/-- Along an actual exact-prefix ray, either every root has positive joint
survival or one literal finite root has zero joint survival. -/
theorem positiveSurvival_or_exists_zeroSurvival
    (ray : QuittingActualExactPrefixRay reward source) :
    (∀ depth, 0 < quittingStationaryContinueMass (ray.roots depth)) ∨
      ∃ depth, quittingStationaryContinueMass (ray.roots depth) = 0 := by
  by_cases hpositive :
      ∀ depth, 0 < quittingStationaryContinueMass (ray.roots depth)
  · exact Or.inl hpositive
  · right
    push Not at hpositive
    obtain ⟨depth, hdepth⟩ := hpositive
    exact ⟨depth, le_antisymm hdepth
      (quittingStationaryContinueMass_nonneg (ray.roots depth))⟩

/-- The pure-time choice obtained by shifting a finite choice by `shift`
dates; `Never` remains `Never`. -/
def shiftedPureTimeChoice (choice : Option ℕ) (shift : ℕ) : Option ℕ :=
  choice.map (fun time => time + shift)

@[simp] theorem shiftedPureTimeChoice_zero (choice : Option ℕ) :
    shiftedPureTimeChoice choice 0 = choice := by
  cases choice <;> simp [shiftedPureTimeChoice]

theorem shiftedPureTimeChoice_succ (choice : Option ℕ) (shift : ℕ) :
    shiftedPureTimeChoice choice (shift + 1) =
      (shiftedPureTimeChoice choice shift).map Nat.succ := by
  cases choice <;> simp [shiftedPureTimeChoice, Nat.add_assoc]

/-- A cap carried by one actual descendant ray.  The source is the literal
profile at `start`, the same finite time (or `Never`) shifts at each later
root, and the carrier debt has one common positive lower bound. -/
structure ShiftedCapTail
    (ray : QuittingActualExactPrefixRay reward source) where
  start : ℕ
  owner : ι
  initialChoice : Option ℕ
  debtFloor : ℝ
  debtFloor_pos : 0 < debtFloor
  roots_positive : ∀ fuel,
    0 < quittingStationaryContinueMass (ray.roots (start + fuel))
  cap_attains : ∀ fuel,
    quittingTerminalPayoff reward
        (Function.update (ray.profiles (start + fuel)) owner
          (quittingPureTimeBehaviorStrategy reward owner
            (shiftedPureTimeChoice initialChoice fuel))) owner =
      quittingContinuationBestResponseValue reward
        (ray.profiles (start + fuel)) owner
  debt_ge : ∀ fuel, debtFloor ≤
    quittingTerminalDeviationDebt reward (ray.profiles (start + fuel)) owner

/-- An attained finite-or-Never cap of positive debt at one point of an
actual ray shifts through every later positive-survival root.  Summable
marginal hazards give a single positive debt floor for the entire tail. -/
theorem nonempty_shiftedCapTail_of_attainedCap
    (ray : QuittingActualExactPrefixRay reward source)
    (start : ℕ) (owner : ι) (choice : Option ℕ)
    (hcap : quittingTerminalPayoff reward
        (Function.update (ray.profiles start) owner
          (quittingPureTimeBehaviorStrategy reward owner choice)) owner =
      quittingContinuationBestResponseValue reward (ray.profiles start) owner)
    (hdebt : 0 < quittingTerminalDeviationDebt reward
      (ray.profiles start) owner)
    (hpositive : ∀ fuel,
      0 < quittingStationaryContinueMass (ray.roots (start + fuel)))
    (hsummable : Summable (fun depth =>
      ∑ player, (ray.roots depth player true).toReal)) :
    ∃ tail : ShiftedCapTail ray,
      tail.start = start ∧ tail.owner = owner ∧ tail.initialChoice = choice := by
  let shiftedRoots : ℕ → ι → PMF Bool := fun fuel => ray.roots (start + fuel)
  have hshiftedSummable : Summable (fun fuel =>
      ∑ player, (shiftedRoots fuel player true).toReal) := by
    exact hsummable.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hinfinite : 0 < quittingInfiniteJointSurvival shiftedRoots :=
    quittingInfiniteJointSurvival_pos_of_summable_marginalHazard
      shiftedRoots hshiftedSummable hpositive
  let floor := quittingInfiniteJointSurvival shiftedRoots *
    quittingTerminalDeviationDebt reward (ray.profiles start) owner
  have hfloor : 0 < floor := mul_pos hinfinite hdebt
  have htransportAll : ∀ fuel,
      quittingTerminalPayoff reward
          (Function.update (ray.profiles (start + fuel)) owner
            (quittingPureTimeBehaviorStrategy reward owner
              (shiftedPureTimeChoice choice fuel))) owner =
        quittingContinuationBestResponseValue reward
          (ray.profiles (start + fuel)) owner ∧
      quittingTerminalDeviationDebt reward
          (ray.profiles (start + fuel)) owner =
        (∏ depth ∈ Finset.range fuel,
          quittingRootOpponentContinueMass (shiftedRoots depth) owner) *
            quittingTerminalDeviationDebt reward (ray.profiles start) owner := by
    intro fuel
    induction fuel with
    | zero => exact ⟨by simpa using hcap, by simp⟩
    | succ fuel ih =>
        have hcontinue : 0 < (ray.roots (start + fuel) owner false).toReal :=
          (hpositive fuel).trans_le
            (quittingStationaryContinueMass_le_ownContinueProbability
              (ray.roots (start + fuel)) owner)
        have htransport := quitting_exactCapAttainer_rootThen_continue_transport
          reward (ray.roots (start + fuel)) (ray.profiles (start + fuel)) owner
            (quittingPureTimeBehaviorStrategy reward owner
              (shiftedPureTimeChoice choice fuel))
            (ray.roots_exact (start + fuel)) hcontinue ih.1
        constructor
        · rw [show ray.profiles (start + (fuel + 1)) =
              quittingRootThenContinuationProfile reward
                (ray.roots (start + fuel)) (ray.profiles (start + fuel)) by
              simpa only [Nat.add_assoc] using ray.profiles_succ (start + fuel),
            shiftedPureTimeChoice_succ]
          rw [quittingPureTimeBehaviorStrategy_optionMap_succ_eq]
          exact htransport.1
        · rw [show ray.profiles (start + (fuel + 1)) =
              quittingRootThenContinuationProfile reward
                (ray.roots (start + fuel)) (ray.profiles (start + fuel)) by
              simpa only [Nat.add_assoc] using ray.profiles_succ (start + fuel),
            htransport.2, ih.2, Finset.prod_range_succ]
          ring
  refine ⟨⟨start, owner, choice, floor, hfloor, hpositive,
    fun fuel => (htransportAll fuel).1, ?_⟩, rfl, rfl, rfl⟩
  intro fuel
  rw [(htransportAll fuel).2]
  have hjoint := quittingInfiniteJointSurvival_le_prefix shiftedRoots fuel
  have hopponent := quittingJointSurvivalPrefix_le_opponentSurvivalPrefix
    shiftedRoots owner fuel
  have hsourceDebt := quittingTerminalDeviationDebt_nonneg
    reward (ray.profiles start) owner
  exact mul_le_mul_of_nonneg_right (hjoint.trans hopponent) hsourceDebt

/-- A finite sure-Quit anchor moves one date to the right at every literal
prefix of the ray. -/
theorem anchor_sureQuit_at_shiftedDeadline
    (ray : QuittingActualExactPrefixRay reward source)
    (anchor : ι) (deadline : ℕ)
    (hsure : quittingProfileLiveRoot reward source deadline anchor =
      PMF.pure true) :
    ∀ depth, quittingProfileLiveRoot reward (ray.profiles depth)
        (deadline + depth) anchor = PMF.pure true := by
  intro depth
  induction depth with
  | zero => simpa [ray.profiles_zero] using hsure
  | succ depth ih =>
      rw [show ray.profiles (depth + 1) =
          quittingRootThenContinuationProfile reward (ray.roots depth)
            (ray.profiles depth) from ray.profiles_succ depth]
      rw [show deadline + (depth + 1) = (deadline + depth) + 1 by omega]
      change quittingProfileLiveRoot reward (ray.profiles depth)
        (deadline + depth) anchor = PMF.pure true
      exact ih

/-- A zero-debt anchor remains zero-debt under every exact literal prefix. -/
theorem anchor_debt_eq_zero
    (ray : QuittingActualExactPrefixRay reward source)
    (anchor : ι)
    (hzero : quittingTerminalDeviationDebt reward source anchor = 0) :
    ∀ depth,
      quittingTerminalDeviationDebt reward (ray.profiles depth) anchor = 0 := by
  intro depth
  induction depth with
  | zero => simpa [ray.profiles_zero] using hzero
  | succ depth ih =>
      rw [show ray.profiles (depth + 1) =
          quittingRootThenContinuationProfile reward (ray.roots depth)
            (ray.profiles depth) from ray.profiles_succ depth]
      apply le_antisymm
      · have hle := quittingTerminalDeviationDebt_rootThenContinuation_le
          reward (ray.roots depth) (ray.profiles depth) anchor
            (ray.roots_exact depth)
        rw [ih, mul_zero] at hle
        exact hle
      · exact quittingTerminalDeviationDebt_nonneg reward _ anchor


end QuittingActualExactPrefixRay

end GameTheory
