/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.CoordinateMarginalMixture
import UniformEquilibrium.Quitting.Root.PureTimeCapPrefixSelection

/-!
# Payoff displacement forced by an immediate-Quit cap reset

For an outsider, forcing one owner to Continue changes the root endpoint gap
by an exact continuation-displacement term plus a root-local remainder.  The
remainder is at most four times the payoff bound times the removed owner's
Quit probability.  If immediate Quit attains the outsider's complete cap,
the outsider's literal debt is its Continue probability times the new
endpoint gap.  These are the exact ingredients of the negative-displacement
consequence below.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The root-local change in an outsider's Quit-minus-Continue gap when
`owner` is forced to Continue, written so each term is a one-coordinate
mixture perturbation. -/
def quittingForcedContinueEndpointRemainder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) : ℝ :=
  (quittingRootExpectedPayoff reward source
        (Function.update (Function.update root who (PMF.pure true))
          owner (PMF.pure false)) who -
      quittingRootExpectedPayoff reward source
        (Function.update root who (PMF.pure true)) who) -
    (quittingRootExpectedPayoff reward source
        (Function.update (Function.update root who (PMF.pure false))
          owner (PMF.pure false)) who -
      quittingRootExpectedPayoff reward source
        (Function.update root who (PMF.pure false)) who)

/-- For distinct owner and outsider, the explicit perturbation remainder is
exactly the change of the source-tail endpoint gap. -/
theorem quittingForcedContinueEndpointRemainder_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    {owner who : ι} (hne : who ≠ owner) :
    quittingForcedContinueEndpointRemainder reward source root owner who =
      quittingRootEndpointDifference reward source
          (Function.update root owner (PMF.pure false)) who -
        quittingRootEndpointDifference reward source root who := by
  unfold quittingForcedContinueEndpointRemainder
    quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  rw [Function.update_comm hne, Function.update_comm hne]
  ring

/-- Changing only the continuation coordinate changes the endpoint gap by
minus opponent survival times that coordinate change. -/
theorem quittingRootEndpointDifference_sub_eq_neg_opponentContinueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference reward first root who -
        quittingRootEndpointDifference reward second root who =
      -quittingRootOpponentContinueMass root who *
        (first who - second who) := by
  have hquit := quittingRootQuitPayoff_continuation_invariant
    reward first second root who
  have hcontinue := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward first second (Function.update root who (PMF.pure false)) who
  change quittingRootContinuePayoff reward first root who -
      quittingRootContinuePayoff reward second root who =
        quittingRootOpponentContinueMass root who *
          (first who - second who) at hcontinue
  unfold quittingRootEndpointDifference
  rw [hquit]
  linarith

/-- Exact endpoint comparison between a source root and the root obtained by
forcing one distinct owner to Continue. -/
theorem quittingRootEndpointDifference_forcedContinue_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child : Payoff ι) (root : ι → PMF Bool)
    {owner who : ι} (hne : who ≠ owner) :
    quittingRootEndpointDifference reward child
          (Function.update root owner (PMF.pure false)) who -
        quittingRootEndpointDifference reward source root who =
      -quittingRootOpponentContinueMass
          (Function.update root owner (PMF.pure false)) who *
          (child who - source who) +
        quittingForcedContinueEndpointRemainder
          reward source root owner who := by
  have htail :=
    quittingRootEndpointDifference_sub_eq_neg_opponentContinueMass_mul
      reward child source
        (Function.update root owner (PMF.pure false)) who
  have hremainder :=
    quittingForcedContinueEndpointRemainder_eq reward source root hne
  linarith

/-- The endpoint remainder is bounded by `4 * M` times the removed owner's
Quit probability. -/
theorem abs_quittingForcedContinueEndpointRemainder_le_four_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    {owner who : ι} (hne : who ≠ owner) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ player, |source player| ≤ M) :
    |quittingForcedContinueEndpointRemainder reward source root owner who| ≤
      4 * M * (root owner true).toReal := by
  let quitRoot := Function.update root who (PMF.pure true)
  let continueRoot := Function.update root who (PMF.pure false)
  have hquit := abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    reward source quitRoot owner who (PMF.pure false) hreward hsource
  have hcontinue := abs_quittingRootExpectedPayoff_update_coord_sub_self_le
    reward source continueRoot owner who (PMF.pure false) hreward hsource
  have hquit' :
      |quittingRootExpectedPayoff reward source
          (Function.update quitRoot owner (PMF.pure false)) who -
        quittingRootExpectedPayoff reward source quitRoot who| ≤
        (root owner true).toReal * (2 * M) := by
    simpa [quitRoot, Function.update_of_ne hne.symm] using hquit
  have hcontinue' :
      |quittingRootExpectedPayoff reward source
          (Function.update continueRoot owner (PMF.pure false)) who -
        quittingRootExpectedPayoff reward source continueRoot who| ≤
        (root owner true).toReal * (2 * M) := by
    simpa [continueRoot, Function.update_of_ne hne.symm] using hcontinue
  unfold quittingForcedContinueEndpointRemainder
  calc
    |(quittingRootExpectedPayoff reward source
          (Function.update quitRoot owner (PMF.pure false)) who -
        quittingRootExpectedPayoff reward source quitRoot who) -
      (quittingRootExpectedPayoff reward source
          (Function.update continueRoot owner (PMF.pure false)) who -
        quittingRootExpectedPayoff reward source continueRoot who)| ≤
        |quittingRootExpectedPayoff reward source
            (Function.update quitRoot owner (PMF.pure false)) who -
          quittingRootExpectedPayoff reward source quitRoot who| +
        |quittingRootExpectedPayoff reward source
            (Function.update continueRoot owner (PMF.pure false)) who -
          quittingRootExpectedPayoff reward source continueRoot who| :=
      abs_sub _ _
    _ ≤ (root owner true).toReal * (2 * M) +
        (root owner true).toReal * (2 * M) :=
      add_le_add hquit' hcontinue'
    _ = 4 * M * (root owner true).toReal := by ring

/-- If immediate Quit attains the complete cap after one root, the literal
terminal debt is the prescribed Continue probability times the root endpoint
gap. -/
theorem quittingTerminalDeviationDebt_rootThen_eq_continue_mul_endpointDifference_of_quitZeroCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι)
    (hcap : quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward root continuation) who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward root continuation) who) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      (root who false).toReal *
        quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward continuation player)
          root who := by
  have hquit :=
    quittingTerminalPayoff_rootThen_pureTime_zero_eq_quitPayoff
      reward root continuation who
  unfold quittingTerminalDeviationDebt
  rw [← hcap, hquit, quittingTerminalPayoff_rootThenContinuation_eq]
  exact quittingRootQuitPayoff_sub_successorPayoff
    reward
      (fun player => quittingTerminalPayoff reward continuation player)
      root who

/-- At an exact source root, a positive debt attained by immediate Quit in
the owner-forced child forces a quantitatively negative source-to-child
payoff displacement, up to the explicit root-local remainder. -/
theorem debtFloor_sub_ownerHazardError_le_neg_payoffDisplacement_of_quitZeroCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    {owner who : ι} (hne : who ≠ owner) {debtFloor M : ℝ}
    (hdebtFloor : 0 < debtFloor)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ player, |source player| ≤ M)
    (hroot : IsεQuittingRootNash reward source 0 root)
    (hcap : quittingTerminalPayoff reward
        (Function.update
          (quittingRootThenContinuationProfile reward
            (Function.update root owner (PMF.pure false)) continuation)
          who (quittingPureTimeBehaviorStrategy reward who (some 0))) who =
      quittingContinuationBestResponseValue reward
        (quittingRootThenContinuationProfile reward
          (Function.update root owner (PMF.pure false)) continuation) who)
    (hdebt : debtFloor ≤ quittingTerminalDeviationDebt reward
      (quittingRootThenContinuationProfile reward
        (Function.update root owner (PMF.pure false)) continuation) who) :
    debtFloor - 4 * M * (root owner true).toReal ≤
      -quittingRootOpponentContinueMass
          (Function.update root owner (PMF.pure false)) who *
        (quittingTerminalPayoff reward continuation who - source who) := by
  let forced := Function.update root owner (PMF.pure false)
  let child : Payoff ι :=
    fun player => quittingTerminalPayoff reward continuation player
  let newGap := quittingRootEndpointDifference reward child forced who
  let oldGap := quittingRootEndpointDifference reward source root who
  let remainder :=
    quittingForcedContinueEndpointRemainder reward source root owner who
  have hdebtIdentity :=
    quittingTerminalDeviationDebt_rootThen_eq_continue_mul_endpointDifference_of_quitZeroCap
      reward forced continuation who hcap
  have hcontinueForced : (forced who false).toReal =
      (root who false).toReal := by
    simp [forced, Function.update_of_ne hne]
  have hcontinue : 0 < (root who false).toReal := by
    by_contra hnot
    have hzero : (root who false).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    rw [hcontinueForced, hzero, zero_mul] at hdebtIdentity
    linarith
  have hnewGap : debtFloor ≤ newGap := by
    have hcontinueLe : (root who false).toReal ≤ 1 := by
      exact ENNReal.toReal_mono ENNReal.one_ne_top
        ((root who).coe_le_one false)
    have hcontinueNonneg : 0 ≤ (root who false).toReal :=
      ENNReal.toReal_nonneg
    rw [hcontinueForced] at hdebtIdentity
    change quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward forced continuation) who =
      (root who false).toReal * newGap at hdebtIdentity
    have hproduct : debtFloor ≤ (root who false).toReal * newGap := by
      linarith
    have hgapNonneg : 0 ≤ newGap := by
      by_contra hnegative
      have hproductNonpos :=
        mul_nonpos_of_nonneg_of_nonpos hcontinueNonneg
          (le_of_not_ge hnegative)
      linarith
    exact hproduct.trans
      (by simpa using mul_le_mul_of_nonneg_right hcontinueLe hgapNonneg)
  have holdGap : oldGap ≤ 0 := by
    have hendpoint :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward source root).2 hroot
    have hweighted := (hendpoint who).1
    exact nonpos_of_mul_nonpos_left
      (by simpa [mul_comm] using hweighted) hcontinue
  have hcomparison :=
    quittingRootEndpointDifference_forcedContinue_sub_eq
      reward source child root hne
  have hremainder :=
    abs_quittingForcedContinueEndpointRemainder_le_four_mul
      reward source root hne hreward hsource
  have hremainderUpper := (abs_le.mp hremainder).2
  change newGap - oldGap =
      -quittingRootOpponentContinueMass forced who *
          (child who - source who) + remainder at hcomparison
  change |remainder| ≤ 4 * M * (root owner true).toReal at hremainder
  change remainder ≤ 4 * M * (root owner true).toReal at hremainderUpper
  change debtFloor - 4 * M * (root owner true).toReal ≤
      -quittingRootOpponentContinueMass forced who *
        (child who - source who)
  linarith

end GameTheory
