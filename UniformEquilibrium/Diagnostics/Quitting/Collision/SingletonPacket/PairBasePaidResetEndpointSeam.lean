/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBasePaidResetPayoffAlignment
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport

/-!
# The endpoint seam after a fixed-law paid reset

An exact Nash root against a terminal semantic envelope need not be exact
Nash against the prescribed payoff.  The precise discrepancy is already
present in the own-strategy transport account: the continuation-option
surcharge must consume exactly the survival-weighted tail debt in every
coordinate.

This file records that equality as an if-and-only-if and gives a useful exact
converter when opponent survival kills every debt coordinate.  The final
trichotomy applies the equality of prescribed payoffs in a fixed-law reset:
the dynamic root is either such a positive endpoint root, has a concrete
positive literal Nash defect, or the dispatch is on its all-Continue cap
face.

No floor dominance or chronological return of the pair-base target is
asserted.  Those remain separate data.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} -> Payoff iota}

/-- For a cap--Nash root, exact Nash at the prescribed payoff is equivalent
to exact exhaustion of survival-weighted debt by the continuation-option
surcharge, coordinate by coordinate. -/
theorem capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt
    (pair : QuittingTerminalSemanticPair iota) (root : iota -> PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    IsεQuittingRootNash reward pair.1 0 root <->
      forall who,
        quittingRootContinuationOptionSurcharge reward pair root who =
          quittingStationaryContinueMass root *
            quittingTerminalSemanticDebt pair who := by
  have hcap : forall who,
      quittingRootCoordinateNashDefect reward pair.2 root who = 0 :=
    (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward pair.2 root).mp hnash
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  constructor
  · intro hliteral who
    have haccount := quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt
      reward pair root who
    rw [hliteral who, hcap who, zero_add] at haccount
    simpa using haccount
  · intro haccount who
    have hreconcile :=
      quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt
        reward pair root who
    rw [hcap who, haccount who] at hreconcile
    linarith

/-- A concrete exact converter.  If forcing each player to Continue leaves
zero opponent-survival-weighted debt, then cap--Nash is already exact Nash
against the prescribed payoff. -/
theorem isZeroQuittingRootNash_at_prescribed_of_capNash_of_killedDebt
    (pair : QuittingTerminalSemanticPair iota) (root : iota -> PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.2 0 root)
    (hkilled : forall who,
      quittingRootOpponentContinueMass root who *
        quittingTerminalSemanticDebt pair who = 0) :
    IsεQuittingRootNash reward pair.1 0 root := by
  apply (capNash_isZeroNash_at_prescribed_iff_surcharge_eq_liveDebt
    pair root hnash).mpr
  intro who
  have hsurchargeNonneg : 0 <=
      quittingRootContinuationOptionSurcharge reward pair root who :=
    quittingRootContinuationOptionSurcharge_nonneg_of_mem_carrier
      reward pair root who hpair
  have hsurchargeLe :
      quittingRootContinuationOptionSurcharge reward pair root who <= 0 := by
    have hupper :=
      quittingRootContinuationOptionSurcharge_le_opponentMass_mul_debt
        reward pair root who hpair
    rw [hkilled who] at hupper
    exact hupper
  have hsurcharge :
      quittingRootContinuationOptionSurcharge reward pair root who = 0 :=
    le_antisymm hsurchargeLe hsurchargeNonneg
  have hlive : quittingStationaryContinueMass root *
      quittingTerminalSemanticDebt pair who = 0 := by
    rw [quittingStationaryContinueMass_eq_forcedContinue_mul_own]
    change (quittingRootOpponentContinueMass root who *
          (root who false).toReal) *
        quittingTerminalSemanticDebt pair who = 0
    calc
      (quittingRootOpponentContinueMass root who *
            (root who false).toReal) *
          quittingTerminalSemanticDebt pair who =
        (root who false).toReal *
          (quittingRootOpponentContinueMass root who *
            quittingTerminalSemanticDebt pair who) := by ring
      _ = 0 := by rw [hkilled who, mul_zero]
  rw [hsurcharge, hlive]

/-- Quantitative fallback: an exact cap--Nash root is Nash against the
prescribed payoff with error at most the tail's total semantic debt.  This
does not make the error small; it identifies the exact correction budget
which any limiting use must drive to zero. -/
theorem isQuittingRootNash_at_prescribed_with_debtSumError_of_capNash
    (pair : QuittingTerminalSemanticPair iota) (root : iota -> PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    IsεQuittingRootNash reward pair.1
      (quittingTerminalSemanticDebtSum pair) root := by
  apply (isεQuittingRootNash_iff_coordinateNashDefect_le
    reward pair.1 (quittingTerminalSemanticDebtSum pair) root).mpr
  intro who
  have hcap :
      quittingRootCoordinateNashDefect reward pair.2 root who = 0 :=
    (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
      reward pair.2 root).mp hnash who
  have hsurcharge : 0 <=
      quittingRootContinuationOptionSurcharge reward pair root who :=
    quittingRootContinuationOptionSurcharge_nonneg_of_mem_carrier
      reward pair root who hpair
  have haccount :=
    quittingRootLiteralDefect_add_surcharge_eq_capDefect_add_liveDebt
      reward pair root who
  have hlive :
      quittingRootCoordinateNashDefect reward pair.1 root who <=
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt pair who := by
    rw [hcap, zero_add] at haccount
    linarith
  have hdebtNonneg : 0 <= quittingTerminalSemanticDebt pair who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hpair who
  have hliveLe : quittingStationaryContinueMass root *
      quittingTerminalSemanticDebt pair who <=
        quittingTerminalSemanticDebt pair who := by
    nlinarith [quittingStationaryContinueMass_nonneg root,
      quittingStationaryContinueMass_le_one root]
  have hcoordinateLe : quittingTerminalSemanticDebt pair who <=
      quittingTerminalSemanticDebtSum pair := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.single_le_sum
      (fun player _ =>
        quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward hpair player)
      (Finset.mem_univ who)
  exact hlive.trans (hliveLe.trans hcoordinateLe)

/-- Positive joint survival and positive total debt force one coordinate to
retain strictly positive opponent-survival-weighted debt.  Thus the
support-killing exact converter above cannot apply on such a root. -/
theorem exists_positive_opponentSurvival_mul_debt
    (pair : QuittingTerminalSemanticPair iota) (root : iota -> PMF Bool)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hdebt : 0 < quittingTerminalSemanticDebtSum pair)
    (hcontinue : 0 < quittingStationaryContinueMass root) :
    ∃ who, 0 < quittingRootOpponentContinueMass root who *
      quittingTerminalSemanticDebt pair who := by
  have hnonneg : ∀ who ∈ (Finset.univ : Finset iota),
      0 <= quittingTerminalSemanticDebt pair who := by
    intro who _
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hpair who
  unfold quittingTerminalSemanticDebtSum at hdebt
  obtain ⟨who, _hwho, hwho⟩ :=
    (Finset.sum_pos_iff_of_nonneg hnonneg).mp hdebt
  have hopponent : 0 < quittingRootOpponentContinueMass root who := by
    have hle := quittingStationaryContinueMass_le_update_pure_false root who
    exact hcontinue.trans_le (by
      simpa [quittingRootOpponentContinueMass] using hle)
  exact ⟨who, mul_pos hopponent hwho⟩

/-- The actual positive-survival branch of a fixed-law reset dispatch has a
strictly positive approximation budget and cannot satisfy coordinatewise
support-killing.  Any exact cap-to-prescribed conversion there must instead
prove the sharp surcharge equality above. -/
theorem QuittingFixedLawResetDispatch.positiveError_and_not_killedDebt
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota -> ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (hsource : 0 < quittingTerminalSemanticDebtSum source)
    (root : iota -> PMF Bool)
    (hcontinue : 0 < quittingStationaryContinueMass root) :
    0 < quittingTerminalSemanticDebtSum returned ∧
      ¬ ∀ who,
        quittingRootOpponentContinueMass root who *
          quittingTerminalSemanticDebt returned who = 0 := by
  have hreturned : returned ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (point := (returned, mass)) dispatch.joint
  have hreturnedPositive : 0 < quittingTerminalSemanticDebtSum returned :=
    hsource.trans_le dispatch.source_le
  refine ⟨hreturnedPositive, ?_⟩
  obtain ⟨who, hwho⟩ := exists_positive_opponentSurvival_mul_debt
    returned root hreturned hreturnedPositive hcontinue
  intro hkilled
  rw [hkilled who] at hwho
  exact (lt_irrefl 0) hwho

/-- Exact payoff alignment sharpens the fixed-law dynamic dispatch.  In the
absorbing branch, either the chosen cap root is already exact Nash at the
pair-base prescribed payoff, or one named coordinate has a positive literal
Nash defect.  The third branch is the original all-Continue cap stall. -/
theorem QuittingFixedLawResetDispatch.endpointRoot_or_literalDefect_or_stall
    {source target : QuittingTerminalSemanticPair iota}
    {mass : QuittingTerminalOutcome iota -> ℝ}
    {owner other : iota} {returned : QuittingTerminalSemanticPair iota}
    (dispatch : QuittingFixedLawResetDispatch (reward := reward)
      source target mass owner other returned)
    (htarget : (target, mass) ∈ quittingTerminalSemanticLawCarrier reward) :
    (∃ root : iota -> PMF Bool,
        IsεQuittingRootNash reward target.1 0 root ∧
          0 < quittingRootAbsorptionMass root ∧
          0 < quittingStationaryContinueMass root) ∨
      (∃ root : iota -> PMF Bool, ∃ who,
        IsεQuittingRootNash reward returned.2 0 root ∧
          0 < quittingRootAbsorptionMass root ∧
          0 < quittingStationaryContinueMass root ∧
          0 < quittingRootCoordinateNashDefect reward target.1 root who) ∨
      (IsεQuittingRootNash reward returned.2 0
          (quittingAllContinueRoot : iota -> PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot
          returned = returned) := by
  have hpayoff : returned.1 = target.1 :=
    dispatch.prescribed_eq_target htarget
  rcases dispatch.dynamic_exit with hdynamic | hstall
  · obtain ⟨root, hcap, habsorption, hcontinue, _hlower, _hjoint,
        _hreset, _hincidence⟩ := hdynamic
    by_cases hliteral : IsεQuittingRootNash reward returned.1 0 root
    · exact Or.inl ⟨root, hpayoff ▸ hliteral, habsorption, hcontinue⟩
    · right
      left
      have hexists : ∃ who, 0 <
          quittingRootCoordinateNashDefect reward returned.1 root who := by
        by_contra hnone
        have hnone' : ∀ who, ¬ 0 <
            quittingRootCoordinateNashDefect reward returned.1 root who :=
          not_exists.mp hnone
        apply hliteral
        apply (isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero
          reward returned.1 root).mpr
        intro who
        exact le_antisymm (le_of_not_gt (hnone' who))
          (quittingRootCoordinateNashDefect_nonneg
            reward returned.1 root who)
      obtain ⟨who, hpositive⟩ := hexists
      rw [hpayoff] at hpositive
      exact ⟨root, who, hcap, habsorption, hcontinue, hpositive⟩
  · exact Or.inr (Or.inr hstall)

end GameTheory
