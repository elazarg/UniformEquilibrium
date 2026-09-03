/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.CoordinateMarginalMixture

/-!
# Payoff displacement after forcing one root coordinate to Continue

Replacing one root marginal by pure Continue and changing the continuation
payoff has an exact affine decomposition.  The continuation displacement is
multiplied by the forced root's joint survival; the remaining correction is
the original owner's Quit-versus-Continue effect.  These identities are
valid for every finite player type and require no Nash hypothesis.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The source-tail payoff change caused by replacing `owner`'s root
marginal by Continue instead of Quit, observed in coordinate `who`. -/
def quittingForcedContinueOwnerCorrection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) : ℝ :=
  quittingRootSuccessorPayoff reward source
      (Function.update root owner (PMF.pure false)) who -
    quittingRootSuccessorPayoff reward source
      (Function.update root owner (PMF.pure true)) who

/-- Exact affine displacement after forcing one root coordinate to Continue.
The coefficient of the tail displacement is the full joint survival of the
forced root. -/
theorem quittingRootSuccessorPayoff_forcedContinue_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) :
    quittingRootSuccessorPayoff reward child
          (Function.update root owner (PMF.pure false)) who -
        quittingRootSuccessorPayoff reward source root who =
      quittingStationaryContinueMass
          (Function.update root owner (PMF.pure false)) *
          (child who - source who) +
        (root owner true).toReal *
          quittingForcedContinueOwnerCorrection reward source root owner who := by
  let forced := Function.update root owner (PMF.pure false)
  let quit := Function.update root owner (PMF.pure true)
  have htail := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward child source forced who
  have hmix := quittingRootExpectedPayoff_update_coord_eq_mix
    reward source root owner (root owner) who
  rw [Function.update_eq_self] at hmix
  have hsum : (root owner false).toReal +
      (root owner true).toReal = 1 := by
    simpa [Fintype.sum_bool, add_comm] using
      pmf_toReal_sum_one (root owner)
  change quittingRootSuccessorPayoff reward source root who =
      (root owner true).toReal *
          quittingRootSuccessorPayoff reward source quit who +
        (root owner false).toReal *
          quittingRootSuccessorPayoff reward source forced who at hmix
  change
    quittingRootSuccessorPayoff reward child forced who -
        quittingRootSuccessorPayoff reward source root who =
      quittingStationaryContinueMass forced * (child who - source who) +
        (root owner true).toReal *
          quittingForcedContinueOwnerCorrection reward source root owner who
  rw [show quittingForcedContinueOwnerCorrection reward source root owner who =
      quittingRootSuccessorPayoff reward source forced who -
        quittingRootSuccessorPayoff reward source quit who by rfl]
  have hcontinue : (root owner false).toReal =
      1 - (root owner true).toReal := by linarith
  rw [← htail, hmix, hcontinue]
  ring

/-- Under a common reward-box bound, the owner correction has absolute value
at most `2 * M`. -/
theorem abs_quittingForcedContinueOwnerCorrection_le_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : Payoff ι) (root : ι → PMF Bool)
    (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ player, |source player| ≤ M) :
    |quittingForcedContinueOwnerCorrection reward source root owner who| ≤
      2 * M := by
  have hcontinue := abs_quittingRootExpectedPayoff_le_bound reward source
    (Function.update root owner (PMF.pure false)) who hreward hsource
  have hquit := abs_quittingRootExpectedPayoff_le_bound reward source
    (Function.update root owner (PMF.pure true)) who hreward hsource
  unfold quittingForcedContinueOwnerCorrection quittingRootSuccessorPayoff
  rw [abs_le]
  have hcontinue' := abs_le.mp hcontinue
  have hquit' := abs_le.mp hquit
  constructor <;> linarith

omit [Fintype ι] [DecidableEq ι] in
private theorem abs_payoffCoordinate_sub_le_two_mul
    (first second : Payoff ι) (who : ι) {M : ℝ}
    (hfirst : |first who| ≤ M) (hsecond : |second who| ≤ M) :
    |first who - second who| ≤ 2 * M := by
  rw [abs_le]
  have hfirst' := abs_le.mp hfirst
  have hsecond' := abs_le.mp hsecond
  constructor <;> linarith

/-- Literal Bellman equations for a source root and its owner-forced-Continue
child give the exact successor displacement recurrence. -/
theorem terminalChildPayoffDisplacement_next_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child sourceNext childNext : Payoff ι)
    (root : ι → PMF Bool) (owner who : ι)
    (hsourceNext : sourceNext =
      quittingRootSuccessorPayoff reward source root)
    (hchildNext : childNext =
      quittingRootSuccessorPayoff reward child
        (Function.update root owner (PMF.pure false))) :
    childNext who - sourceNext who =
      quittingStationaryContinueMass
          (Function.update root owner (PMF.pure false)) *
          (child who - source who) +
        (root owner true).toReal *
          quittingForcedContinueOwnerCorrection reward source root owner who := by
  rw [hsourceNext, hchildNext]
  exact quittingRootSuccessorPayoff_forcedContinue_sub_eq
    reward source child root owner who

/-- The adjacent displacement increment is charged only to absorption of the
forced root and the removed owner's Quit probability.  The sharp owner
correction constant is `2 * M`. -/
theorem abs_terminalChildPayoffDisplacement_next_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source child sourceNext childNext : Payoff ι)
    (root : ι → PMF Bool) (owner who : ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hsource : ∀ player, |source player| ≤ M)
    (hchild : ∀ player, |child player| ≤ M)
    (hsourceNext : sourceNext =
      quittingRootSuccessorPayoff reward source root)
    (hchildNext : childNext =
      quittingRootSuccessorPayoff reward child
        (Function.update root owner (PMF.pure false))) :
    |(childNext who - sourceNext who) - (child who - source who)| ≤
      2 * M * quittingRootAbsorptionMass
          (Function.update root owner (PMF.pure false)) +
        2 * M * (root owner true).toReal := by
  let forced := Function.update root owner (PMF.pure false)
  let displacement := child who - source who
  let correction :=
    quittingForcedContinueOwnerCorrection reward source root owner who
  have hrecurrence := terminalChildPayoffDisplacement_next_eq
    reward source child sourceNext childNext root owner who
      hsourceNext hchildNext
  have hdisplacement : |displacement| ≤ 2 * M :=
    abs_payoffCoordinate_sub_le_two_mul child source who
      (hchild who) (hsource who)
  have hcorrection : |correction| ≤ 2 * M :=
    abs_quittingForcedContinueOwnerCorrection_le_two_mul
      reward source root owner who hreward hsource
  have habsorption : 0 ≤ quittingRootAbsorptionMass forced :=
    quittingRootAbsorptionMass_nonneg forced
  have howner : 0 ≤ (root owner true).toReal := ENNReal.toReal_nonneg
  have hmass : quittingStationaryContinueMass forced - 1 =
      -quittingRootAbsorptionMass forced := by
    unfold quittingRootAbsorptionMass
    ring
  rw [hrecurrence]
  change |quittingStationaryContinueMass forced * displacement +
      (root owner true).toReal * correction - displacement| ≤ _
  rw [show quittingStationaryContinueMass forced * displacement +
          (root owner true).toReal * correction - displacement =
        (quittingStationaryContinueMass forced - 1) * displacement +
          (root owner true).toReal * correction by ring,
    hmass]
  calc
    |(-quittingRootAbsorptionMass forced) * displacement +
        (root owner true).toReal * correction| ≤
        |(-quittingRootAbsorptionMass forced) * displacement| +
          |(root owner true).toReal * correction| := abs_add_le _ _
    _ = quittingRootAbsorptionMass forced * |displacement| +
        (root owner true).toReal * |correction| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg habsorption,
        abs_of_nonneg howner]
    _ ≤ quittingRootAbsorptionMass forced * (2 * M) +
        (root owner true).toReal * (2 * M) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hdisplacement habsorption)
        (mul_le_mul_of_nonneg_left hcorrection howner)
    _ = 2 * M * quittingRootAbsorptionMass forced +
        2 * M * (root owner true).toReal := by ring

end GameTheory
