/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.ImmediateQuitCapDisplacement
import UniformEquilibrium.Quitting.Root.TerminalChildPayoffDisplacementSequence

/-!
# Negative displacement from cofinal immediate-Quit cap resets

Along literal source and owner-forced child Bellman sequences, summable
forced-root absorption and owner hazard make the payoff displacement converge.
If one outsider retains a positive debt floor and immediate Quit attains its
complete cap cofinally, then the limiting child-minus-source displacement in
that coordinate is at most minus half the debt floor.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Cofinal immediate-Quit cap attainment forces a fixed negative limiting
payoff displacement.  Eventually the source roots are exact Nash, the
outsider has positive Continue probability, and the child carries the fixed
debt floor.  No Nash claim is made for the owner-forced child roots. -/
theorem exists_terminalChildPayoffDisplacement_limit_le_neg_half_of_frequently_quitZeroCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ℕ → Payoff ι)
    (childProfile : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    {debtFloor M : ℝ} (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ time player, |source time player| ≤ M)
    (hsourceNext : ∀ time, source (time + 1) =
      quittingRootSuccessorPayoff reward (source time) (roots time))
    (hchildNext : ∀ time, childProfile (time + 1) =
      quittingRootThenContinuationProfile reward
        (Function.update (roots time) owner (PMF.pure false))
        (childProfile time))
    (hroot : ∀ᶠ time in atTop,
      IsεQuittingRootNash reward (source time) 0 (roots time))
    (hcontinue : ∀ᶠ time in atTop,
      0 < ((roots time who) false).toReal)
    (hforcedAbsorption : Summable (fun time =>
      quittingRootAbsorptionMass
        (Function.update (roots time) owner (PMF.pure false))))
    (hownerHazard : Summable (fun time =>
      ((roots time owner) true).toReal))
    (hdebt : ∀ᶠ time in atTop,
      debtFloor ≤ quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward
          (Function.update (roots time) owner (PMF.pure false))
          (childProfile time)) who)
    (hreset : ∃ᶠ time in atTop,
      quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward
              (Function.update (roots time) owner (PMF.pure false))
              (childProfile time))
            who (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
        quittingContinuationBestResponseValue reward
          (quittingRootThenContinuationProfile reward
            (Function.update (roots time) owner (PMF.pure false))
            (childProfile time)) who) :
    ∃ limit : ℝ,
      Tendsto (fun time =>
        quittingTerminalPayoff reward (childProfile time) who -
          source time who) atTop (nhds limit) ∧
      limit ≤ -debtFloor / 2 := by
  let child : ℕ → Payoff ι := fun time player =>
    quittingTerminalPayoff reward (childProfile time) player
  have hchildValueNext : ∀ time, child (time + 1) =
      quittingRootSuccessorPayoff reward (child time)
        (Function.update (roots time) owner (PMF.pure false)) := by
    intro time
    funext player
    simp only [child, hchildNext time,
      quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  obtain ⟨limit, hlimit⟩ :=
    exists_tendsto_terminalChildPayoffDisplacement
      reward source child roots owner who hreward hsource
        (fun time player =>
          abs_quittingTerminalPayoff_le reward (childProfile time) player
            hreward)
        hsourceNext hchildValueNext hforcedAbsorption hownerHazard
  have hownerZero : Tendsto (fun time =>
      ((roots time owner) true).toReal) atTop (nhds 0) :=
    hownerHazard.tendsto_atTop_zero
  have herrorZero : Tendsto (fun time =>
      4 * M * ((roots time owner) true).toReal) atTop (nhds 0) := by
    simpa using hownerZero.const_mul (4 * M)
  have hsmall : ∀ᶠ time in atTop,
      4 * M * ((roots time owner) true).toReal < debtFloor / 2 :=
    (tendsto_order.1 herrorZero).2 (debtFloor / 2) (by linarith)
  have hnegativeAtReset : ∀ᶠ time in atTop,
      (quittingTerminalPayoff reward
          (Function.update
            (quittingRootThenContinuationProfile reward
              (Function.update (roots time) owner (PMF.pure false))
              (childProfile time))
            who (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
          quittingContinuationBestResponseValue reward
            (quittingRootThenContinuationProfile reward
              (Function.update (roots time) owner (PMF.pure false))
              (childProfile time)) who) →
        child time who - source time who ≤ -debtFloor / 2 := by
    filter_upwards [hsmall, hroot, hcontinue, hdebt] with time hsmallTime
      hrootTime hcontinueTime hdebtTime
    intro hcap
    have hstep :=
      debtFloor_sub_ownerHazardError_le_neg_payoffDisplacement_of_quitZeroCap
        reward (source time) (roots time) (childProfile time) hne hdebtFloor
          hreward (hsource time) hrootTime hcontinueTime hcap hdebtTime
    let survival := quittingRootOpponentContinueMass
      (Function.update (roots time) owner (PMF.pure false)) who
    let displacement := child time who - source time who
    have hlower : debtFloor / 2 ≤ -survival * displacement := by
      change debtFloor - 4 * M * ((roots time owner) true).toReal ≤
        -survival * displacement at hstep
      linarith
    have hsurvivalNonneg : 0 ≤ survival :=
      quittingRootOpponentContinueMass_nonneg _ _
    have hsurvivalLe : survival ≤ 1 :=
      quittingRootOpponentContinueMass_le_one _ _
    let drop := -displacement
    have hlowerDrop : debtFloor / 2 ≤ survival * drop := by
      dsimp only [drop]
      linarith
    have hdropNonneg : 0 ≤ drop := by
      by_contra hdrop
      have hproductNonpos : survival * drop ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hsurvivalNonneg
          (le_of_not_ge hdrop)
      linarith
    have hproductLe : survival * drop ≤ drop := by
      have hcharge := mul_nonneg (sub_nonneg.mpr hsurvivalLe) hdropNonneg
      nlinarith
    change displacement ≤ -debtFloor / 2
    dsimp only [drop] at hdropNonneg hproductLe hlowerDrop
    linarith
  have hfrequentNegative : ∃ᶠ time in atTop,
      child time who - source time who ≤ -debtFloor / 2 :=
    (hreset.and_eventually hnegativeAtReset).mono fun time hboth =>
      hboth.2 hboth.1
  have hlimitLe : limit ≤ -debtFloor / 2 := by
    by_contra hnot
    have hstrict : -debtFloor / 2 < limit := lt_of_not_ge hnot
    have heventuallyGreater : ∀ᶠ time in atTop,
        -debtFloor / 2 < child time who - source time who :=
      (tendsto_order.1 hlimit).1 (-debtFloor / 2) hstrict
    obtain ⟨time, hle, hlt⟩ :=
      (hfrequentNegative.and_eventually heventuallyGreater).exists
    linarith
  exact ⟨limit, hlimit, hlimitLe⟩

end GameTheory
