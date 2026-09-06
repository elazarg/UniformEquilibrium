import UniformEquilibrium.Quitting.Root.CofinalImmediateQuitCapDisplacementLimit
import UniformEquilibrium.Quitting.Root.CoherentPureTimeCapClock
import UniformEquilibrium.Quitting.Root.NestedCapChildFixedDebtor
import UniformEquilibrium.Quitting.Paths.SummableRootSurvival

/-! # Coherent cap-clock dichotomy for literal nested children -/

noncomputable section
namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal nested cap children admit a coherent outsider cap clock.  It
either shifts forever after a cutoff, or resets cofinally and forces the
limiting child-minus-source payoff displacement to be at most the negative
of the fixed debt floor. -/
theorem quittingNestedCapChild_eventuallyShift_or_negativeHolonomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    {debtFloor M : ℝ} (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hnested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hexact : ∀ depth, IsεQuittingRootNash reward
      (fun player => quittingTerminalPayoff reward (profiles depth) player)
      0 (roots depth))
    (hhazard : Summable (fun depth =>
      ∑ player, (roots depth player true).toReal))
    (R : ℕ)
    (hdebt : ∀ depth, R ≤ depth → debtFloor ≤
      quittingTerminalDeviationDebt reward
        (quittingPureTimeCapChild reward (profiles depth) owner depth) who) :
    ∃ (choices : ℕ → Option ℕ) (limit : ℝ),
      (∀ depth, quittingTerminalPayoff reward
          (Function.update
            (quittingPureTimeCapChild reward (profiles depth) owner depth) who
            (quittingPureTimeBehaviorStrategy reward who (choices depth))) who =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth) who) ∧
      (∀ depth, choices (depth + 1) = some 0 ∨
        choices (depth + 1) = (choices depth).map Nat.succ) ∧
      Tendsto (fun depth =>
        quittingTerminalPayoff reward
              (quittingPureTimeCapChild reward (profiles depth) owner depth) who -
          quittingTerminalPayoff reward (profiles depth) who)
        atTop (nhds limit) ∧
      ((∃ cutoff, ∀ depth, cutoff ≤ depth →
          choices (depth + 1) = (choices depth).map Nat.succ) ∨
        ((∀ cutoff, ∃ depth, cutoff ≤ depth ∧
            choices (depth + 1) = some 0) ∧
          limit ≤ -debtFloor)) := by
  obtain ⟨choices, _, hcaps, hsteps⟩ :=
    exists_coherentOutsiderCapClock_on_pureTimeCapChildren
      reward profiles roots hne hnested
  have hforced :=
    summable_forcedContinue_absorption_of_summable_marginalHazard roots owner hhazard
  have howner :=
    summable_coordinateHazard_of_summable_marginalHazard roots owner hhazard
  have hsourceNext : ∀ depth,
      (fun player => quittingTerminalPayoff reward (profiles (depth + 1)) player) =
        quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward (profiles depth) player)
          (roots depth) := by
    intro depth
    funext player
    rw [hnested depth]
    simpa [quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_rootThenContinuation_eq
        reward (roots depth) (profiles depth) player
  have hchildNested : ∀ depth,
      quittingPureTimeCapChild reward (profiles (depth + 1)) owner (depth + 1) =
        quittingRootThenContinuationProfile reward
          (Function.update (roots depth) owner (PMF.pure false))
          (quittingPureTimeCapChild reward (profiles depth) owner depth) := by
    intro depth
    rw [hnested depth]
    exact update_quittingRootThenContinuationProfile_pureTime_succ_eq
      reward (roots depth) (profiles depth) owner depth
  have hchildNext : ∀ depth,
      (fun player => quittingTerminalPayoff reward
        (quittingPureTimeCapChild reward (profiles (depth + 1)) owner
          (depth + 1)) player) =
        quittingRootSuccessorPayoff reward
          (fun player => quittingTerminalPayoff reward
            (quittingPureTimeCapChild reward (profiles depth) owner depth) player)
          (Function.update (roots depth) owner (PMF.pure false)) := by
    intro depth
    funext player
    rw [hchildNested depth]
    simpa [quittingRootSuccessorPayoff] using
      quittingTerminalPayoff_rootThenContinuation_eq reward
        (Function.update (roots depth) owner (PMF.pure false))
        (quittingPureTimeCapChild reward (profiles depth) owner depth) player
  rcases quittingCapClock_eventually_shift_or_cofinally_reset choices hsteps with
    hshift | hreset
  · obtain ⟨limit, hlimit⟩ :=
      exists_tendsto_terminalChildPayoffDisplacement
        reward
        (fun depth player => quittingTerminalPayoff reward (profiles depth) player)
        (fun depth player => quittingTerminalPayoff reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth) player)
        roots owner who hreward
        (fun depth player => abs_quittingTerminalPayoff_le
          reward (profiles depth) player hreward)
        (fun depth player => abs_quittingTerminalPayoff_le reward
          (quittingPureTimeCapChild reward (profiles depth) owner depth)
          player hreward)
        hsourceNext hchildNext
        hforced howner
    exact ⟨choices, limit, hcaps, hsteps, hlimit, Or.inl hshift⟩
  · have hfrequent : ∃ᶠ depth in atTop,
        choices (depth + 1) = some 0 := by
      rw [frequently_atTop]
      exact hreset
    obtain ⟨limit, hlimit, hlimitLe⟩ :=
      exists_terminalChildPayoffDisplacement_limit_le_neg_of_frequently_quitZeroCap
        reward
        (fun depth player => quittingTerminalPayoff reward (profiles depth) player)
        (fun depth => quittingPureTimeCapChild reward
          (profiles depth) owner depth)
        roots hne hdebtFloor hreward
        (fun depth player => abs_quittingTerminalPayoff_le
          reward (profiles depth) player hreward)
        hsourceNext hchildNested
        (Eventually.of_forall hexact)
        hforced howner
        (eventually_atTop.2 ⟨R, fun depth hR => by
          simpa [quittingPureTimeCapChild, hnested depth,
            update_quittingRootThenContinuationProfile_pureTime_succ_eq]
            using hdebt (depth + 1) (Nat.le_add_right_of_le hR)⟩)
        (hfrequent.mono fun depth hresetDepth => by
          simpa [quittingPureTimeCapChild, hnested depth,
            update_quittingRootThenContinuationProfile_pureTime_succ_eq,
            hresetDepth] using hcaps (depth + 1))
    exact ⟨choices, limit, hcaps, hsteps, hlimit,
      Or.inr ⟨hreset, hlimitLe⟩⟩

end GameTheory
