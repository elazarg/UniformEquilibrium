import UniformEquilibrium.Quitting.Root.LiteralPrefixDeviationTransport
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection
import UniformEquilibrium.Quitting.Paths.ReversePrefixStoppingLaw

/-!
# Exact cap-clock transport through literal product roots

One-step exact transport and its finite literal iteration.  Every cap equality is derived from an actual suffix attainer.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Positive own Continue support at an exact root makes Continue weakly
better than Quit against the literal continuation payoff. -/
theorem quittingRootQuitPayoff_le_continuePayoff_of_isZeroNash_of_continue_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hcontinue : 0 < (root who false).toReal) :
    quittingRootQuitPayoff reward tail root who ≤
      quittingRootContinuePayoff reward tail root who := by
  have hendpoint :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 root).mpr hnash who
  unfold quittingRootEndpointDifference at hendpoint
  exact sub_nonpos.mp <|
    nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hendpoint.1) hcontinue

/-- An actual suffix cap attainer, prefixed by sure Continue for its owner,
attains the new unrestricted behavioral cap.  The new literal debt is exactly
opponent survival times the old debt.  No positive joint survival is needed. -/
theorem quitting_exactCapAttainer_rootThen_continue_transport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who)
    (hnash : IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward continuation player) 0 root)
    (hcontinue : 0 < (root who false).toReal)
    (hattains : quittingTerminalPayoff reward
        (Function.update continuation who strategy) who =
      quittingContinuationBestResponseValue reward continuation who) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who
            (quittingRootAndContinuationDeviation reward (PMF.pure false)
              strategy)) who =
        quittingContinuationBestResponseValue reward
          (quittingRootThenContinuationProfile reward root continuation) who ∧
      quittingTerminalDeviationDebt reward
          (quittingRootThenContinuationProfile reward root continuation) who =
        quittingRootOpponentContinueMass root who *
          quittingTerminalDeviationDebt reward continuation who := by
  let tail : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let debt := quittingTerminalDeviationDebt reward continuation who
  have hdebt : 0 ≤ debt :=
    quittingTerminalDeviationDebt_nonneg reward continuation who
  have hbase : quittingRootQuitPayoff reward tail root who ≤
      quittingRootContinuePayoff reward tail root who :=
    quittingRootQuitPayoff_le_continuePayoff_of_isZeroNash_of_continue_pos
      reward tail root who hnash hcontinue
  have hbest : quittingContinuationBestResponseValue reward continuation who =
      tail who + debt := by
    dsimp [tail, debt, quittingTerminalDeviationDebt]
    ring
  have hmass : 0 ≤ quittingRootOpponentContinueMass root who :=
    quittingRootOpponentContinueMass_nonneg root who
  have hraised : quittingRootQuitPayoff reward tail root who ≤
      quittingRootContinuePayoff reward tail root who +
        quittingRootOpponentContinueMass root who * debt :=
    hbase.trans (le_add_of_nonneg_right (mul_nonneg hmass hdebt))
  constructor
  · rw [quittingTerminalPayoff_update_rootAndContinuationDeviation_eq,
      quittingContinuationBestResponseValue_rootThenContinuation_eq_max,
      hattains, hbest, quittingRootContinuePayoff_update_add,
      max_eq_right hraised]
    change quittingRootContinuePayoff reward
      (Function.update tail who (tail who + debt)) root who = _
    exact quittingRootContinuePayoff_update_add reward tail root who debt
  · rw [quittingTerminalDeviationDebt_rootThenContinuation_eq
      reward root continuation who hnash,
      max_eq_right hbase, max_eq_right hraised]
    ring

/-- Copying the prescribed root marginal and changing only the reached suffix
multiplies the suffix gain by the root's joint survival. -/
theorem quitting_copiedRootResponse_gain_eq_jointSurvival_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward root continuation)
            who (quittingRootAndContinuationDeviation reward (root who)
              strategy)) who -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root continuation) who =
      quittingStationaryContinueMass root *
        (quittingTerminalPayoff reward
            (Function.update continuation who strategy) who -
          quittingTerminalPayoff reward continuation who) := by
  simpa [quittingLiteralRootStackProfile,
    quittingLiteralRootStackJointSurvival,
    quittingCopyLiteralRootStackThenDeviation] using
    quittingTerminalPayoff_copyLiteralRootStackThenDeviation_sub_eq
      reward [root] continuation who strategy

/-- Starting from a literal `Quit0` cap, repeated exact roots with positive
owner Continue support produce the literal cap clock `Quit n`.  Its debt is
the product of the owner-deleted survival factors times the initial debt.
The updated profiles have the corresponding literal child genealogy. -/
theorem quitting_pureTimeCap_literalPrefix_transport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool)
    (terminal : (quittingGame reward).BehaviorProfile)
    (owner : ι)
    (hbase : quittingTerminalPayoff reward
        (Function.update terminal owner
          (quittingPureTimeBehaviorStrategy reward owner (some 0))) owner =
      quittingContinuationBestResponseValue reward terminal owner)
    (hnash : ∀ n, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward
        (quittingReversePrefixProfile reward roots (fun _ => terminal) n) player)
      0 (roots n))
    (hcontinue : ∀ n, 0 < (roots n owner false).toReal) :
    ∀ n,
      quittingTerminalPayoff reward
          (Function.update
            (quittingReversePrefixProfile reward roots (fun _ => terminal) n)
            owner
            (quittingPureTimeBehaviorStrategy reward owner (some n))) owner =
        quittingContinuationBestResponseValue reward
          (quittingReversePrefixProfile reward roots (fun _ => terminal) n) owner ∧
      quittingTerminalDeviationDebt reward
          (quittingReversePrefixProfile reward roots (fun _ => terminal) n) owner =
        (∏ k ∈ Finset.range n,
          quittingRootOpponentContinueMass (roots k) owner) *
          quittingTerminalDeviationDebt reward terminal owner ∧
      Function.update
          (quittingReversePrefixProfile reward roots (fun _ => terminal) (n + 1))
          owner
          (quittingPureTimeBehaviorStrategy reward owner (some (n + 1))) =
        quittingRootThenContinuationProfile reward
          (Function.update (roots n) owner (PMF.pure false))
          (Function.update
            (quittingReversePrefixProfile reward roots (fun _ => terminal) n)
            owner
            (quittingPureTimeBehaviorStrategy reward owner (some n))) := by
  intro n
  induction n with
  | zero =>
      refine ⟨hbase, ?_, ?_⟩
      · simp [quittingReversePrefixProfile]
      · simpa [quittingReversePrefixProfile] using
          update_quittingRootThenContinuationProfile_pureTime_succ_eq
            reward (roots 0) terminal owner 0
  | succ n ih =>
      let profile := quittingReversePrefixProfile reward roots (fun _ => terminal) n
      have hstep := quitting_exactCapAttainer_rootThen_continue_transport
        reward (roots n) profile owner
          (quittingPureTimeBehaviorStrategy reward owner (some n))
          (hnash n) (hcontinue n) ih.1
      have hattains : quittingTerminalPayoff reward
            (Function.update
              (quittingReversePrefixProfile reward roots (fun _ => terminal) (n + 1))
              owner
              (quittingPureTimeBehaviorStrategy reward owner (some (n + 1))))
            owner =
          quittingContinuationBestResponseValue reward
            (quittingReversePrefixProfile reward roots (fun _ => terminal) (n + 1))
            owner := by
        change quittingTerminalPayoff reward
            (Function.update
              (quittingRootThenContinuationProfile reward (roots n) profile)
              owner
              (quittingPureTimeBehaviorStrategy reward owner (some (n + 1))))
            owner = _
        have hshift := quittingPureTimeBehaviorStrategy_optionMap_succ_eq
          reward owner (some n)
        simp only [Option.map_some, Nat.succ_eq_add_one] at hshift
        rw [hshift]
        exact hstep.1
      refine ⟨hattains, ?_, ?_⟩
      · rw [show quittingReversePrefixProfile reward roots (fun _ => terminal) (n + 1) =
            quittingRootThenContinuationProfile reward (roots n) profile by
            rfl,
          hstep.2, ih.2.1]
        simp only [Finset.prod_range_succ]
        ring
      · simpa [quittingReversePrefixProfile] using
          update_quittingRootThenContinuationProfile_pureTime_succ_eq
            reward (roots (n + 1))
              (quittingReversePrefixProfile reward roots (fun _ => terminal) (n + 1))
              owner (n + 1)

end GameTheory
