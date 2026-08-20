/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLiteralSourceReturnNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# Paid own-strategy transport of terminal debt

Changing one player's behavior while keeping every opponent fixed preserves
that player's all-behavior best-response envelope.  Consequently the change
in prescribed payoff is exactly the decrease in that player's terminal debt.
This gives the bounded potential underlying changed-root and changed-tail
transport: a positive reached-row ticket can be paid only by a decrease of
the marked debt or by the transported profile's residual best-response error.

The second part records the exact one-row decomposition of that residual.
For an arbitrary semantic pair and root, prefixed debt is the cap-coordinate
Nash defect of the root plus joint survival times the tail debt.  No Nash
hypothesis is used.

The opponent-aware surcharge identities localize best-response-envelope
drift as hidden continuation-option debt. The surcharge is at most opponent
survival times tail debt, yielding a sharp lower bound on the literal defect
in terms of the cap defect and the marked player's Quit probability. This
closes the conversion whenever the cap defect exceeds that explicit budget;
it does not prove that every returned cap-defect charge does so. At a global
minimum of total semantic debt, the aggregate cap inequality does dominate
the sum of all option budgets. Strict domination—and hence a positive literal
defect—follows whenever one positive-debt coordinate's own singleton option
mass is strictly below total root absorption.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- For an arbitrary profile transport, debt plus prescribed-payoff gain
equals old debt plus best-response-envelope drift.  This is the exact signed
term that disappears under a fixed-opponent own-strategy update. -/
theorem quittingTerminalSemanticDebt_add_payoffGain_eq_add_envelopeDrift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) who +
        (quittingTerminalPayoff reward target who -
          quittingTerminalPayoff reward source who) =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) who +
        (quittingContinuationBestResponseValue reward target who -
          quittingContinuationBestResponseValue reward source who) := by
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
  ring

/-- The hidden continuation-option surcharge at one semantic prefix row:
the increase in the best pure endpoint when the literal prescribed tail is
replaced by the coordinatewise behavioral cap. -/
def quittingRootContinuationOptionSurcharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) : ℝ :=
  max (quittingRootQuitPayoff reward pair.2 root who)
      (quittingRootContinuePayoff reward pair.2 root who) -
    max (quittingRootQuitPayoff reward pair.1 root who)
      (quittingRootContinuePayoff reward pair.1 root who)

/-- Replacing a literal continuation by its semantic cap cannot decrease the
best pure endpoint. -/
theorem quittingRootContinuationOptionSurcharge_nonneg_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    0 ≤ quittingRootContinuationOptionSurcharge reward pair root who := by
  have hdebt := quittingTerminalSemanticDebt_nonneg_of_mem_carrier
    reward hpair who
  have htail : pair.1 who ≤ pair.2 who := by
    unfold quittingTerminalSemanticDebt at hdebt
    linarith
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue : quittingRootContinuePayoff reward pair.1 root who ≤
      quittingRootContinuePayoff reward pair.2 root who := by
    let roots : ℕ → ι → PMF Bool := fun _ => root
    rw [show root = roots 0 by rfl,
      quittingRootContinuePayoff_eq_fixedOpponents,
      quittingRootContinuePayoff_eq_fixedOpponents]
    have hmul := mul_le_mul_of_nonneg_left htail
      (quittingFixedOpponentsContinueMass_nonneg roots who 0)
    linarith
  unfold quittingRootContinuationOptionSurcharge
  rw [hquit]
  exact sub_nonneg.mpr (max_le (le_max_left _ _) (hcontinue.trans (le_max_right _ _)))

/-- Raising the literal continuation coordinate to its behavioral cap raises
the pure-Continue endpoint by opponent survival times terminal debt. -/
theorem quittingRootContinuePayoff_cap_eq_literal_add_opponentMass_mul_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuePayoff reward pair.2 root who =
      quittingRootContinuePayoff reward pair.1 root who +
        quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who := by
  have hcongr : quittingRootContinuePayoff reward
      (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  have hcoordinate : pair.2 who =
      pair.1 who + quittingTerminalSemanticDebt pair who := by
    unfold quittingTerminalSemanticDebt
    ring
  rw [← hcongr, hcoordinate, quittingRootContinuePayoff_update_add]

/-- Exact max-increment formula for the continuation-option surcharge. -/
theorem quittingRootContinuationOptionSurcharge_eq_max_increment
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootContinuationOptionSurcharge reward pair root who =
      max (quittingRootQuitPayoff reward pair.1 root who)
          (quittingRootContinuePayoff reward pair.1 root who +
            quittingRootOpponentContinueMass root who *
              quittingTerminalSemanticDebt pair who) -
        max (quittingRootQuitPayoff reward pair.1 root who)
          (quittingRootContinuePayoff reward pair.1 root who) := by
  have hquit := quittingRootQuitPayoff_continuation_invariant
    reward pair.1 pair.2 root who
  unfold quittingRootContinuationOptionSurcharge
  rw [← hquit,
    quittingRootContinuePayoff_cap_eq_literal_add_opponentMass_mul_debt]

/-- The option surcharge is at most opponent survival times tail debt. This
is the sharp one-stage budget for converting a cap defect into a literal
best-endpoint defect. -/
theorem quittingRootContinuationOptionSurcharge_le_opponentMass_mul_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingRootContinuationOptionSurcharge reward pair root who ≤
      quittingRootOpponentContinueMass root who *
        quittingTerminalSemanticDebt pair who := by
  rw [quittingRootContinuationOptionSurcharge_eq_max_increment]
  have hdebt : 0 ≤ quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  have hmass : 0 ≤ quittingRootOpponentContinueMass root who :=
    quittingRootOpponentContinueMass_nonneg root who
  have hdelta : 0 ≤ quittingRootOpponentContinueMass root who *
      quittingTerminalSemanticDebt pair who := mul_nonneg hmass hdebt
  rw [sub_le_iff_le_add]
  apply max_le
  · have hfloor := le_max_left
      (quittingRootQuitPayoff reward pair.1 root who)
      (quittingRootContinuePayoff reward pair.1 root who)
    linarith
  · have haffine := le_max_right
      (quittingRootQuitPayoff reward pair.1 root who)
      (quittingRootContinuePayoff reward pair.1 root who)
    linarith

/-- Exact literal-error plus hidden-surcharge decomposition.  This is a
localization of the opponent-change obstruction, not a bound on it. -/
theorem quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootCoordinateNashDefect reward pair.1 root who +
        quittingRootContinuationOptionSurcharge reward pair root who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue : quittingRootContinuePayoff reward
      (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
    quittingRootContinuationOptionSurcharge
  dsimp only
  rw [hquit, hcontinue]
  ring

/-- **Exact arbitrary-root cap decomposition.** Prefix debt is the root's
coordinate Nash defect against the tail cap plus joint Continue mass times
the tail debt. No Nash hypothesis is used. -/
theorem quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who =
      quittingRootCoordinateNashDefect reward pair.2 root who +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  have hsuccessor := quittingRootSuccessorPayoff_sub_eq_continueMass_mul
    reward pair.2 pair.1 root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
    quittingRootCoordinateNashDefect
  dsimp only
  rw [hquit, hcontinue]
  linarith

/-- Exact reconciliation of the literal-defect and cap-defect accounts. -/
theorem quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootCoordinateNashDefect reward pair.1 root who +
        quittingRootContinuationOptionSurcharge reward pair root who =
      quittingRootCoordinateNashDefect reward pair.2 root who +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
  have hliteral := quittingTerminalSemanticDebt_prefix_eq_literalDefect_add_surcharge
    reward pair root who
  have hcap := quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
    reward pair root who
  linarith

/-- A cap defect controls the literal best-endpoint defect after subtracting
the precise own-Quit option budget. -/
theorem quittingRootCapDefect_sub_quitOptionBudget_le_literalDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingRootCoordinateNashDefect reward pair.2 root who -
        quittingRootOpponentContinueMass root who *
          (root who true).toReal * quittingTerminalSemanticDebt pair who ≤
      quittingRootCoordinateNashDefect reward pair.1 root who := by
  have hid := quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt
    reward pair root who
  have hsurcharge :=
    quittingRootContinuationOptionSurcharge_le_opponentMass_mul_debt
      reward pair root who hpair
  have hfactor := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    root who
  change quittingStationaryContinueMass root =
    quittingRootOpponentContinueMass root who * (root who false).toReal at hfactor
  have hprobability := quittingRoot_continueProbability_add_quitProbability
    root who
  have hquitProbability : 1 - (root who false).toReal =
      (root who true).toReal := by
    linarith
  have hbudget :
      quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who -
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who =
      quittingRootOpponentContinueMass root who * (root who true).toReal *
        quittingTerminalSemanticDebt pair who := by
    rw [hfactor]
    rw [show quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who -
        (quittingRootOpponentContinueMass root who * (root who false).toReal) *
          quittingTerminalSemanticDebt pair who =
        quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt pair who *
            (1 - (root who false).toReal) by ring,
      hquitProbability]
    ring
  rw [← hbudget]
  linarith

/-- The own-Quit option coefficient is the singleton-absorption probability
and is bounded by total one-stage absorption. -/
theorem quittingRootOpponentContinue_mul_quit_le_absorption
    (root : ι → PMF Bool) (who : ι) :
    quittingRootOpponentContinueMass root who * (root who true).toReal ≤
      quittingRootAbsorptionMass root := by
  have hfactor := quittingStationaryContinueMass_eq_forcedContinue_mul_own
    root who
  change quittingStationaryContinueMass root =
    quittingRootOpponentContinueMass root who * (root who false).toReal at hfactor
  have hprobability := quittingRoot_continueProbability_add_quitProbability
    root who
  have hquitProbability : (root who true).toReal =
      1 - (root who false).toReal := by
    linarith
  have hmass := quittingRootOpponentContinueMass_le_one root who
  unfold quittingRootAbsorptionMass
  rw [hfactor, hquitProbability]
  nlinarith

/-- The sum of all players' option budgets is bounded by absorption times
total semantic debt. -/
theorem quittingRootQuitOptionBudgetSum_le_absorption_mul_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    (∑ who : ι, quittingRootOpponentContinueMass root who *
        (root who true).toReal * quittingTerminalSemanticDebt pair who) ≤
      quittingRootAbsorptionMass root *
        quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro who _
  exact mul_le_mul_of_nonneg_right
    (quittingRootOpponentContinue_mul_quit_le_absorption root who)
    (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who)

/-- The aggregate option budget is strictly below absorption-weighted debt
as soon as one positive-debt coordinate has non-singleton absorption mass
outside its own option coefficient. -/
theorem quittingRootQuitOptionBudgetSum_lt_absorption_mul_debtSum_of_exists
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (who : ι) (hdebt : 0 < quittingTerminalSemanticDebt pair who)
    (hmass : quittingRootOpponentContinueMass root who *
        (root who true).toReal < quittingRootAbsorptionMass root) :
    (∑ player : ι, quittingRootOpponentContinueMass root player *
        (root player true).toReal *
          quittingTerminalSemanticDebt pair player) <
      quittingRootAbsorptionMass root *
        quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro player _
    exact mul_le_mul_of_nonneg_right
      (quittingRootOpponentContinue_mul_quit_le_absorption root player)
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hpair player)
  · refine ⟨who, Finset.mem_univ who, ?_⟩
    exact mul_lt_mul_of_pos_right hmass hdebt

/-- A cap defect exceeding the own-Quit option budget is already a positive
literal best-endpoint defect. -/
theorem quittingRootLiteralDefect_pos_of_capDefect_gt_quitOptionBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hstrict : quittingRootOpponentContinueMass root who *
        (root who true).toReal * quittingTerminalSemanticDebt pair who <
      quittingRootCoordinateNashDefect reward pair.2 root who) :
    0 < quittingRootCoordinateNashDefect reward pair.1 root who := by
  have hlower := quittingRootCapDefect_sub_quitOptionBudget_le_literalDefect
    reward pair root who hpair
  linarith

/-- At a reached literal row, the cap-defect criterion gives an actual
positive unilateral behavioral gain by switching to the better pure
endpoint. -/
theorem quittingLiteralActualRowBestEndpointGain_pos_of_capDefect_gt_quitOptionBudget
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (stage : ℕ)
    (hlive : 0 < quittingLiveMass reward profile stage)
    (hstrict :
      let pair := quittingLiteralActualRowTail reward profile stage
      let root := quittingLiteralActualRowRoot reward profile stage
      quittingRootOpponentContinueMass root who * (root who true).toReal *
          quittingTerminalSemanticDebt pair who <
        quittingRootCoordinateNashDefect reward pair.2 root who) :
    0 < quittingLiteralActualRowBestEndpointGain reward profile who stage := by
  let pair := quittingLiteralActualRowTail reward profile stage
  let root := quittingLiteralActualRowRoot reward profile stage
  have hpair : pair ∈ quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPair_mem_carrier reward _
  have hliteral : 0 <
      quittingRootCoordinateNashDefect reward pair.1 root who :=
    quittingRootLiteralDefect_pos_of_capDefect_gt_quitOptionBudget
      reward pair root who hpair hstrict
  have hgain :=
    quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
      reward profile who stage
  change quittingLiteralActualRowBestEndpointGain reward profile who stage =
    quittingLiveMass reward profile stage *
      quittingRootCoordinateNashDefect reward pair.1 root who at hgain
  rw [hgain]
  exact mul_pos hlive hliteral

/-- For the debt potential and the displayed row-error account, the residual
reserve hypothesis is exactly equivalent to the desired paid-transport
inequality. -/
theorem gain_le_potentialDrop_add_error_iff_residual_le_reserve
    (gain sourcePotential targetPotential error residual : ℝ)
    (hsplit : targetPotential = error + residual) :
    gain ≤ sourcePotential - targetPotential + error ↔
      residual ≤ sourcePotential - gain := by
  rw [hsplit]
  constructor <;> intro h <;> linarith

/-- **Minimum-fiber barrier for paid residuals.**  If the source potential is
globally minimal among admissible outputs, an exact `target = error + residual`
account together with the paid-residual condition can only hold after the
row-error account has already spent the whole gain.  In particular, this is
an obstruction theorem: it does not produce the paid-residual hypothesis. -/
theorem gain_le_error_of_minimumFiber_and_paid_residual
    (gain minimum sourcePotential targetPotential error residual : ℝ)
    (hsource : sourcePotential = minimum)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual)
    (hpaid : residual ≤ sourcePotential - gain) :
    gain ≤ error := by
  linarith

/-- The fundamental minimum-fiber invariant behind the preceding gain
statement: residual debt can decrease below the minimum only by at most the
amount entered in the explicit error ledger.  This uses no proposed gain or
paid-transport condition. -/
theorem residualDischarge_le_error_of_minimumFiber
    (minimum targetPotential error residual : ℝ)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual) :
    minimum - residual ≤ error := by
  linarith

/-- An exact target on or above the minimum fiber cannot discharge any
strictly positive charge from its residual ledger.  This is the direct
operation-class no-go obtained by specializing the error ledger to zero. -/
theorem not_residual_le_minimum_sub_charge_of_exact_minimumFiber
    (minimum targetPotential residual charge : ℝ)
    (hcharge : 0 < charge)
    (htarget : minimum ≤ targetPotential)
    (hexact : targetPotential = residual) :
    ¬ residual ≤ minimum - charge := by
  intro hpaid
  linarith

/-- Exact slack identity for a claimed residual discharge `charge`.  If the
target is above the minimum or the claimed residual bound has positive
slack, the error ledger exceeds the charge by exactly those two slacks. -/
theorem error_sub_charge_eq_minimumExcess_add_residualSlack
    (minimum targetPotential error residual charge : ℝ)
    (hsplit : targetPotential = error + residual) :
    error - charge =
      (targetPotential - minimum) + (minimum - charge - residual) := by
  rw [hsplit]
  ring

/-- Near the minimum fiber, a paid residual reduction can spend at most the
source's pre-existing excess before the rest of its charge becomes error. -/
theorem charge_sub_excess_le_error_of_nearMinimum_paid_residual
    (minimum sourcePotential targetPotential error residual charge excess : ℝ)
    (hsource : sourcePotential = minimum + excess)
    (htarget : minimum ≤ targetPotential)
    (hsplit : targetPotential = error + residual)
    (hpaid : residual ≤ sourcePotential - charge) :
    charge - excess ≤ error := by
  linarith

/-- A decrease of a proper-subset debt potential at a globally minimal
total-debt source is paid by an equal increase in the complementary debt.
Thus changing the tracked subset can move debt between players but cannot
create a decrease of total debt. -/
theorem complementPotential_increase_of_totalMinimum_and_subsetDrop
    (sourceSelected sourceComplement targetSelected targetComplement charge : ℝ)
    (htotal : sourceSelected + sourceComplement ≤
      targetSelected + targetComplement)
    (hdrop : targetSelected ≤ sourceSelected - charge) :
    sourceComplement + charge ≤ targetComplement := by
  linarith

/-- Updating only `who` changes terminal debt by exactly the negative of the
prescribed-payoff change.  This is the fixed-opponent potential identity. -/
theorem quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (Function.update profile who strategy)) who =
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        (quittingTerminalPayoff reward
            (Function.update profile who strategy) who -
          quittingTerminalPayoff reward profile who) := by
  change quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who -
        quittingTerminalPayoff reward
          (Function.update profile who strategy) who =
      (quittingContinuationBestResponseValue reward profile who -
        quittingTerminalPayoff reward profile who) -
      (quittingTerminalPayoff reward
          (Function.update profile who strategy) who -
        quittingTerminalPayoff reward profile who)
  rw [quittingContinuationBestResponseValue_update_self]
  ring

/-- Equivalent telescoping form of fixed-opponent debt transport. -/
theorem quittingTerminalSemanticDebt_update_self_add_payoffGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who) :
    quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who +
        (quittingTerminalPayoff reward
            (Function.update profile who strategy) who -
          quittingTerminalPayoff reward profile who) =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  rw [quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain]
  ring

/-- A source ticket bounded by the marked player's source debt is paid by
the marked debt drop plus the transported profile's residual debt.  The
transport may replace the player's entire behavior strategy, hence includes
root-only, tail-only, and simultaneous root-and-tail changes, while every
opponent stays literal. -/
theorem gain_le_debtDrop_add_residual_of_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who)
    (gain : ℝ)
    (hgain : gain ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who) :
    gain ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who +
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who := by
  linarith

/-- If the transported own strategy is within `error` of the unchanged
best-response envelope, the only unpaid amount in the potential account is
at most `error`. -/
theorem gain_le_debtDrop_add_error_of_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (strategy : (quittingGame reward).BehaviorStrategy who)
    (gain error : ℝ)
    (hgain : gain ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hcap : quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward
        (Function.update profile who strategy) who + error) :
    gain ≤
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (Function.update profile who strategy)) who + error := by
  have hresidual : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (Function.update profile who strategy)) who ≤ error := by
    change quittingContinuationBestResponseValue reward
        (Function.update profile who strategy) who -
          quittingTerminalPayoff reward
            (Function.update profile who strategy) who ≤ error
    rw [quittingContinuationBestResponseValue_update_self]
    linarith
  have hpaid := gain_le_debtDrop_add_residual_of_update_self
    reward profile who strategy gain hgain
  linarith

/-- Under a uniform reward bound, the marked debt is a bounded nonnegative
potential, with range contained in `[0, 2M]`. -/
theorem quittingTerminalSemanticDebt_mem_Icc_zero_two_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who ∈
      Set.Icc 0 (2 * M) := by
  constructor
  · exact quittingTerminalDeviationDebt_nonneg reward profile who
  · unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    have hbest := abs_quittingContinuationBestResponseValue_le
      reward profile who hreward
    have hpayoff := abs_quittingTerminalPayoff_le
      reward profile who hreward
    have hbestUpper := le_of_abs_le hbest
    have hpayoffLower := neg_le_of_abs_le hpayoff
    linarith

/-- At a global minimum of total semantic debt, every root pays for its
absorption mass through total cap Nash defect. -/
theorem minimumTerminalSemantic_absorption_mul_debtSum_le_capDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingRootAbsorptionMass root *
        quittingTerminalSemanticDebtSum pair ≤
      quittingRootTotalNashDefect reward pair.2 root := by
  let prefixed := quittingTerminalSemanticPrefix reward root pair
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root pair hpair
  have hminPrefix : quittingTerminalSemanticDebtSum pair ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixed
  have hsum : quittingTerminalSemanticDebtSum prefixed =
      quittingRootTotalNashDefect reward pair.2 root +
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum pair := by
    dsimp only [prefixed]
    unfold quittingTerminalSemanticDebtSum quittingRootTotalNashDefect
    simp_rw [quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward pair root]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  unfold quittingRootAbsorptionMass
  rw [hsum] at hminPrefix
  nlinarith

/-- At a minimum-total-debt semantic pair, absorption-weighted debt after
subtracting every player's option budget is paid by literal root defects. -/
theorem minimumTerminalSemantic_absorptionDebt_sub_quitOptionBudget_le_literalDefectSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingRootAbsorptionMass root *
          quittingTerminalSemanticDebtSum pair -
        (∑ who : ι, quittingRootOpponentContinueMass root who *
          (root who true).toReal * quittingTerminalSemanticDebt pair who) ≤
      quittingRootTotalNashDefect reward pair.1 root := by
  have hcap := minimumTerminalSemantic_absorption_mul_debtSum_le_capDefect
    reward pair root hpair hminimum
  have hcoordinate :
      (∑ who : ι,
        (quittingRootCoordinateNashDefect reward pair.2 root who -
          quittingRootOpponentContinueMass root who *
            (root who true).toReal * quittingTerminalSemanticDebt pair who)) ≤
      ∑ who : ι, quittingRootCoordinateNashDefect reward pair.1 root who := by
    apply Finset.sum_le_sum
    intro who _
    exact quittingRootCapDefect_sub_quitOptionBudget_le_literalDefect
      reward pair root who hpair
  rw [Finset.sum_sub_distrib] at hcoordinate
  unfold quittingRootTotalNashDefect at hcap ⊢
  linarith

/-- Strict aggregate slack beyond the option budgets forces a positive
literal root defect at a minimum-total-debt semantic pair. -/
theorem exists_literalDefect_pos_of_minimum_of_quitOptionBudgetSum_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hstrict :
      (∑ who : ι, quittingRootOpponentContinueMass root who *
          (root who true).toReal * quittingTerminalSemanticDebt pair who) <
        quittingRootAbsorptionMass root *
          quittingTerminalSemanticDebtSum pair) :
    ∃ who : ι,
      0 < quittingRootCoordinateNashDefect reward pair.1 root who := by
  have hlower :=
    minimumTerminalSemantic_absorptionDebt_sub_quitOptionBudget_le_literalDefectSum
      reward pair root hpair hminimum
  have htotal : 0 < quittingRootTotalNashDefect reward pair.1 root := by
    linarith
  unfold quittingRootTotalNashDefect at htotal
  obtain ⟨who, _, hwho⟩ := (Finset.sum_pos_iff_of_nonneg fun player _ ↦
    quittingRootCoordinateNashDefect_nonneg reward pair.1 root player).mp htotal
  exact ⟨who, hwho⟩

/-- A concrete sufficient condition: one positive-debt coordinate whose own
singleton option mass is strictly below total absorption forces a positive
literal defect somewhere at a minimum-total-debt pair. -/
theorem exists_literalDefect_pos_of_minimum_of_debt_pos_of_optionMass_lt_absorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (who : ι) (hdebt : 0 < quittingTerminalSemanticDebt pair who)
    (hmass : quittingRootOpponentContinueMass root who *
        (root who true).toReal < quittingRootAbsorptionMass root) :
    ∃ player : ι,
      0 < quittingRootCoordinateNashDefect reward pair.1 root player := by
  apply exists_literalDefect_pos_of_minimum_of_quitOptionBudgetSum_lt
    reward pair root hpair hminimum
  exact quittingRootQuitOptionBudgetSum_lt_absorption_mul_debtSum_of_exists
    reward pair root hpair who hdebt hmass

/-- Equality regime of the aggregate conversion. If every literal root
defect vanishes at a minimum-total-debt pair, each positive-debt coordinate's
own singleton option mass equals the entire absorption mass. -/
theorem quittingRootOptionMass_eq_absorption_of_minimum_of_literalDefects_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair ≤
        quittingTerminalSemanticDebtSum candidate)
    (hdefect : ∀ player,
      quittingRootCoordinateNashDefect reward pair.1 root player = 0)
    (who : ι) (hdebt : 0 < quittingTerminalSemanticDebt pair who) :
    quittingRootOpponentContinueMass root who * (root who true).toReal =
      quittingRootAbsorptionMass root := by
  apply le_antisymm
  · exact quittingRootOpponentContinue_mul_quit_le_absorption root who
  · by_contra hnot
    have hstrict : quittingRootOpponentContinueMass root who *
        (root who true).toReal < quittingRootAbsorptionMass root :=
      lt_of_not_ge hnot
    obtain ⟨player, hpositive⟩ :=
      exists_literalDefect_pos_of_minimum_of_debt_pos_of_optionMass_lt_absorption
        reward pair root hpair hminimum who hdebt hstrict
    rw [hdefect player] at hpositive
    exact (lt_irrefl 0) hpositive

/-- **Maximal one-step transport/prefix account.**  Relative to an arbitrary
source semantic state, a changed root and changed tail pay through prescribed
payoff gain, minus cap-envelope drift, plus the changed root's cap defect and
survival-weighted tail debt.  Fixed-opponent own-strategy transport is the
special case in which the envelope-drift term vanishes. -/
theorem quittingTerminalSemanticDebt_eq_payoffGain_sub_envelopeDrift_add_capDefect_add_liveTail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source tail : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingTerminalSemanticDebt source who =
      ((quittingTerminalSemanticPrefix reward root tail).1 who -
          source.1 who) -
        ((quittingTerminalSemanticPrefix reward root tail).2 who -
          source.2 who) +
      quittingRootCoordinateNashDefect reward tail.2 root who +
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt tail who := by
  have hprefix :=
    quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward tail root who
  unfold quittingTerminalSemanticDebt at hprefix ⊢
  linarith

/-- Literal specialization of the exact cap-error recursion. -/
theorem quittingTerminalDeviationDebt_rootThenContinuation_eq_capDefect_add_continueMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool)
    (continuation : (quittingGame reward).BehaviorProfile)
    (who : ι) :
    quittingTerminalDeviationDebt reward
        (quittingRootThenContinuationProfile reward root continuation) who =
      quittingRootCoordinateNashDefect reward
          (fun player =>
            quittingContinuationBestResponseValue reward continuation player)
          root who +
        quittingStationaryContinueMass root *
          quittingTerminalDeviationDebt reward continuation who := by
  have hpair := quittingTerminalSemanticPair_rootThenContinuation
    reward root continuation
  have hdecomp :=
    quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
      reward (quittingTerminalSemanticPair reward continuation) root who
  rw [← hpair] at hdecomp
  exact hdecomp

end GameTheory
