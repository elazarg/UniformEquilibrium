import UniformEquilibrium.Quitting.Bellman.Finite.LiteralExactPrefixBoxPath
import UniformEquilibrium.Quitting.Bellman.Finite.UnboundedExactBlockHazardCapacity
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw

/-! # Finite exact blocks from literal nested behavioral prefixes -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The canonical reverse word executes to the supplied actual profile. -/
theorem quittingReversePrefixProfile_eq_of_nested
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n)) :
    ∀ n, quittingReversePrefixProfile reward roots (fun _ => profiles 0) n =
      profiles n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [quittingReversePrefixProfile,
        quittingReversePrefixRootStack_succ,
        quittingLiteralRootStackProfile_cons]
      change quittingRootThenContinuationProfile reward (roots n)
        (quittingReversePrefixProfile reward roots (fun _ => profiles 0) n) = _
      rw [ih, ← hnested n]

/-- A finite actual prefix, indexed from newest to oldest, is a literal exact
root word over the actual initial profile. -/
theorem isQuittingLiteralExactRootStack_reversePrefix_of_nested
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (hexact : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles n) player)
      0 (roots n)) :
    ∀ n, IsQuittingLiteralExactRootStack reward
      (quittingReversePrefixRootStack roots n) (profiles 0) := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [quittingReversePrefixRootStack_succ,
        isQuittingLiteralExactRootStack_cons_iff]
      refine ⟨?_, ih⟩
      change IsεQuittingRootEndpointNash reward
        (fun player => quittingTerminalPayoff reward
          (quittingReversePrefixProfile reward roots (fun _ => profiles 0) n)
          player) 0 (roots n)
      rw [quittingReversePrefixProfile_eq_of_nested reward profiles roots hnested n]
      exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward _ 0 (roots n)).mpr (hexact n)

/-- The finite exact block indexed in chronological reverse-prefix order. -/
def quittingActualPrefixHazardBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (hexact : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles n) player)
      0 (roots n))
    (horizon : ℕ) (hpositive : 0 < horizon) :
    QuittingFiniteExactNashBellmanBlock reward
      (quittingNashBellmanBox (quittingRewardBound reward)) where
  horizon := horizon
  horizon_pos := hpositive
  state time := quittingActualProfileBoxState
    (profiles (horizon - time))
    (quittingSimplexOfRoot (roots (horizon - time - 1)))
  state_mem _ _ := (quittingActualProfileBoxState _ _).2
  edge time htime := by
    let index := horizon - time - 1
    have hcurrent : horizon - time = index + 1 := by
      dsimp [index]
      omega
    have hnext : horizon - (time + 1) = index := by
      dsimp [index]
      omega
    unfold IsQuittingNashBellmanEdge
    simp only [quittingActualProfileBoxState_payoff,
      quittingActualProfileBoxState_decoration,
      quittingRootOfSimplex_simplexOfRoot]
    change (fun player => quittingTerminalPayoff reward
          (profiles (horizon - time)) player) =
        quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward
            (profiles (horizon - (time + 1))) player)
          (roots (horizon - time - 1)) ∧
      IsεQuittingRootEndpointNash reward
        (fun player => quittingTerminalPayoff reward
          (profiles (horizon - (time + 1))) player)
        0 (roots (horizon - time - 1))
    rw [hcurrent, hnext]
    constructor
    · funext player
      rw [hnested index, quittingTerminalPayoff_rootThenContinuation_eq]
      rfl
    · exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
        reward _ 0 (roots index)).mpr (hexact index)

/-- The direct actual-prefix block carries exactly the reversed finite sum of
the supplied marginal Quit hazards. -/
theorem quittingActualPrefixHazardBlock_hazardCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool)
    (hnested : ∀ n, profiles (n + 1) =
      quittingRootThenContinuationProfile reward (roots n) (profiles n))
    (hexact : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles n) player)
      0 (roots n))
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (quittingActualPrefixHazardBlock reward profiles roots hnested hexact
        horizon hpositive).hazardCharge =
      ∑ time ∈ Finset.range horizon,
        ∑ player, (roots time player true).toReal := by
  unfold QuittingFiniteExactNashBellmanBlock.hazardCharge
    QuittingFiniteExactNashBellmanBlock.stageHazardCharge
    QuittingFiniteExactNashBellmanBlock.marginalQuitHazard
    QuittingFiniteExactNashBellmanBlock.root
  simp only [quittingActualPrefixHazardBlock,
    quittingActualProfileBoxState_decoration,
    quittingRootOfSimplex_simplexOfRoot]
  calc
    (∑ time ∈ Finset.range horizon,
        ∑ player, (roots (horizon - time - 1) player true).toReal) =
        ∑ time ∈ Finset.range horizon,
          ∑ player, (roots (horizon - 1 - time) player true).toReal := by
      apply Finset.sum_congr rfl
      intro time htime
      have htime' := Finset.mem_range.mp htime
      have hindex : horizon - time - 1 = horizon - 1 - time := by omega
      rw [hindex]
    _ = _ := Finset.sum_range_reflect
      (fun time => ∑ player, (roots time player true).toReal) horizon

end GameTheory
