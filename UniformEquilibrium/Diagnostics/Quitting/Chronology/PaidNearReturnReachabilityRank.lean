/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.ChargedPathReachabilityRank
import UniformEquilibrium.Quitting.Projective.PunishmentFloorNearReturn

/-!
# Reachability rank for failed admissible payoff near-returns

Fix a finite labelling of exact punishment-floor admissible states whose cells
have payoff diameter at most `endpointError`.  If there is no exact path with
endpoints in one cell and containing an edge of charge at least `threshold`,
the generic reachable-label cardinality is a finite Lyapunov rank for the
literal admissible relation.  It weakly decreases across every exact edge and
strictly decreases across every threshold-charged edge.

This is the exact well-founded obstruction obtained by negating the paid
payoff-near-return output.  It uses only paths in the checked admissible
relation.  It does not assert that a paid first-disagreement row itself is an
admissible edge; producing a threshold-charged edge or eliminating the
zero-charge/all-Continue obstruction remains a separate strategic step.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleState :=
  QuittingPunishmentFloorAdmissibleState reward

private abbrev AdmissibleEdge :=
  QuittingPunishmentFloorAdmissibleEdge reward

private abbrev AdmissibleRelation :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-- A finite partition/cover labelling of admissible states whose fibres have
coordinatewise payoff diameter at most `endpointError`. -/
structure QuittingAdmissiblePayoffCellLabelling
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (endpointError : ℝ) where
  Label : Type
  labelFintype : Fintype Label
  labelDecidableEq : DecidableEq Label
  label : QuittingPunishmentFloorAdmissibleState reward → Label
  payoff_close_of_label_eq :
    ∀ source target, label source = label target → ∀ who,
      |source.1.1.1 who - target.1.1.1 who| ≤ endpointError

/-- A fixed-threshold payoff near-return at one prescribed tolerance. -/
def HasQuittingAdmissiblePayoffNearReturnAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (threshold endpointError : ℝ) : Prop :=
  ∃ (source target : QuittingPunishmentFloorAdmissibleState reward)
    (path : (quittingPunishmentFloorAdmissibleChargedRelation reward).Path
      source target),
    (∀ who, |source.1.1.1 who - target.1.1.1 who| ≤ endpointError) ∧
      0 < path.highChargeCount threshold

namespace QuittingAdmissiblePayoffCellLabelling

variable {endpointError threshold : ℝ}

/-- Failure of a payoff near-return implies failure of a same-cell charged
return for every payoff-cell labelling at that tolerance. -/
theorem hasNoHighChargeLabelReturn_of_not_nearReturn
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (hfailure : ¬HasQuittingAdmissiblePayoffNearReturnAt
      reward threshold endpointError) :
    letI := cells.labelFintype
    letI := cells.labelDecidableEq
    AdmissibleRelation.HasNoHighChargeLabelReturn cells.label threshold := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  intro source target path hlabel
  by_contra hcount
  have hpositive : 0 < path.highChargeCount threshold :=
    Nat.pos_of_ne_zero hcount
  apply hfailure
  exact ⟨source, target, path,
    cells.payoff_close_of_label_eq source target hlabel, hpositive⟩

/-- The finite reachable-cell rank attached to a failed near-return. -/
noncomputable def failureRank
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (state : AdmissibleState) : ℕ := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  exact AdmissibleRelation.reachableLabelRank cells.label state

/-- The failure rank weakly decreases across every exact floor-admissible
edge. -/
theorem failureRank_tgt_le_src
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (edge : AdmissibleEdge) :
    cells.failureRank edge.current ≤ cells.failureRank edge.tail := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  exact AdmissibleRelation.reachableLabelRank_tgt_le_src cells.label edge

/-- Under failure at `(threshold, endpointError)`, every edge carrying the
threshold strictly decreases the finite reachable-cell rank. -/
theorem failureRank_tgt_lt_src_of_highCharge
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (hfailure : ¬HasQuittingAdmissiblePayoffNearReturnAt
      reward threshold endpointError)
    (edge : AdmissibleEdge)
    (hhigh : threshold ≤ edge.toBoxEdge.absorptionCharge) :
    cells.failureRank edge.current < cells.failureRank edge.tail := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  exact AdmissibleRelation.reachableLabelRank_tgt_lt_src
    cells.label threshold
      (cells.hasNoHighChargeLabelReturn_of_not_nearReturn hfailure)
      edge hhigh

/-- Quantitative path form: the number of threshold-charged edges plus the
terminal rank is bounded by the initial rank. -/
theorem highChargeCount_add_failureRank_le
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (hfailure : ¬HasQuittingAdmissiblePayoffNearReturnAt
      reward threshold endpointError)
    {source target : AdmissibleState}
    (path : AdmissibleRelation.Path source target) :
    path.highChargeCount threshold + cells.failureRank target ≤
      cells.failureRank source := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  exact AdmissibleRelation.highChargeCount_add_reachableLabelRank_le
    cells.label threshold
      (cells.hasNoHighChargeLabelReturn_of_not_nearReturn hfailure) path

/-- Consequently every literal exact admissible path contains at most the
number of payoff cells many threshold-charged edges. -/
theorem highChargeCount_le_card
    (cells : QuittingAdmissiblePayoffCellLabelling reward endpointError)
    (hfailure : ¬HasQuittingAdmissiblePayoffNearReturnAt
      reward threshold endpointError)
    {source target : AdmissibleState}
    (path : AdmissibleRelation.Path source target) :
    path.highChargeCount threshold ≤ Fintype.card cells.Label := by
  letI := cells.labelFintype
  letI := cells.labelDecidableEq
  exact AdmissibleRelation.highChargeCount_le_card_label
    cells.label threshold
      (cells.hasNoHighChargeLabelReturn_of_not_nearReturn hfailure) path

end QuittingAdmissiblePayoffCellLabelling

end GameTheory
