/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.NormalizedPassportMinimizer
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.LiteralRootStackSurvival

/-!
# Chronological weighted cap-defect ledger for a finite literal word

At each row the cap vector is recomputed from the complete actual suffix.
The recursive ledger weights its total product-root Nash defect by survival
through every preceding row.  Iterating the checked one-step debt identity
gives an exact equality, not an estimate.

This aggregate diagnostic is not a prescribed-payoff edge sum: a root defect
may be carried by an unrestricted suffix best response and may diffuse over
many rows.  No paid chronology or downstream return is produced here.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact cap defect at the first row, evaluated against the actual
literal suffix after that row. -/
def quittingFiniteWordHeadCapDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (suffixRoots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) : ℝ :=
  quittingRootTotalNashDefect reward
    (quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward suffixRoots terminal)).2 root

/-- Chronological aggregate cap charge.  Recursion multiplies every later
charge by the current joint Continue probability, hence by the full prefix
survival accumulated before its row. -/
def quittingFiniteWordWeightedCapDefectLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    List (ι → PMF Bool) → (quittingGame reward).BehaviorProfile → ℝ
  | [], _ => 0
  | root :: roots, terminal =>
      quittingFiniteWordHeadCapDefect reward root roots terminal +
        quittingStationaryContinueMass root *
          quittingFiniteWordWeightedCapDefectLedger reward roots terminal

@[simp] theorem quittingFiniteWordWeightedCapDefectLedger_nil
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingFiniteWordWeightedCapDefectLedger reward [] terminal = 0 := rfl

@[simp] theorem quittingFiniteWordWeightedCapDefectLedger_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingFiniteWordWeightedCapDefectLedger reward (root :: roots) terminal =
      quittingFiniteWordHeadCapDefect reward root roots terminal +
        quittingStationaryContinueMass root *
          quittingFiniteWordWeightedCapDefectLedger reward roots terminal := rfl

/-- Every aggregate charge is nonnegative. -/
theorem quittingFiniteWordWeightedCapDefectLedger_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    0 ≤ quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
  induction roots with
  | nil => simp
  | cons root roots ih =>
      rw [quittingFiniteWordWeightedCapDefectLedger_cons]
      exact add_nonneg
        (quittingRootTotalNashDefect_nonneg reward _ root)
        (mul_nonneg (quittingStationaryContinueMass_nonneg root) ih)

/-- Prefix/suffix decomposition: the second word's ledger is transported by
the first word's exact joint survival. -/
theorem quittingFiniteWordWeightedCapDefectLedger_append
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingFiniteWordWeightedCapDefectLedger reward (first ++ second) terminal =
      quittingFiniteWordWeightedCapDefectLedger reward first
          (quittingLiteralRootStackProfile reward second terminal) +
        quittingCapNashStackContinueProduct first *
          quittingFiniteWordWeightedCapDefectLedger reward second terminal := by
  induction first with
  | nil => simp [quittingCapNashStackContinueProduct]
  | cons root first ih =>
      rw [List.cons_append,
        quittingFiniteWordWeightedCapDefectLedger_cons,
        quittingFiniteWordWeightedCapDefectLedger_cons,
        quittingCapNashStackContinueProduct_cons, ih]
      unfold quittingFiniteWordHeadCapDefect
      rw [quittingLiteralRootStackProfile_append reward first second terminal]
      ring

/-- Exact chronological telescope against the complete terminal semantic
debt of the actual suffix. -/
theorem quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots terminal)) =
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal +
        quittingCapNashStackContinueProduct roots *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) := by
  induction roots with
  | nil => simp [quittingCapNashStackContinueProduct]
  | cons root roots ih =>
      let suffix := quittingLiteralRootStackProfile reward roots terminal
      have hstep :=
        quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_add_capDefect
          reward (quittingTerminalSemanticPair reward suffix) root
      rw [← quittingTerminalSemanticPair_rootThenContinuation] at hstep
      rw [quittingLiteralRootStackProfile_cons, hstep, ih,
        quittingFiniteWordWeightedCapDefectLedger_cons,
        quittingCapNashStackContinueProduct_cons]
      unfold quittingFiniteWordHeadCapDefect
      ring

/-- Rearranged exact telescope.  The ledger is literally whole debt minus the
joint-survival transport of the terminal suffix debt. -/
theorem quittingFiniteWordWeightedCapDefectLedger_eq_debt_sub_transport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingFiniteWordWeightedCapDefectLedger reward roots terminal =
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots terminal)) -
        quittingCapNashStackContinueProduct roots *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) := by
  rw [quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add]
  ring

/-- The exact minimum-minus-transport lower bound, before choosing a fixed
fraction such as one half. -/
theorem minimum_sub_transport_le_weightedLedger
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    quittingTerminalSemanticDebtSum minimum -
        quittingCapNashStackContinueProduct roots *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) ≤
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
  have hwhole := hminimum
    (quittingTerminalSemanticPair reward
      (quittingLiteralRootStackProfile reward roots terminal))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  rw [quittingTerminalSemanticDebtSum_literalRootStack_eq_weightedLedger_add]
    at hwhole
  linarith

/-- Half-minimum ledger consequence from a direct bound on the transported
terminal debt. -/
theorem half_minimum_le_weightedLedger_of_transport_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htransport : quittingCapNashStackContinueProduct roots *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) ≤
      quittingTerminalSemanticDebtSum minimum / 2) :
      quittingTerminalSemanticDebtSum minimum / 2 ≤
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
  have hledger := minimum_sub_transport_le_weightedLedger
    reward minimum roots terminal hminimum
  linarith

/-- Bounded-tail specialization.  A sufficiently small full prefix survival
forces at least half of the positive minimum debt into aggregate suffix-cap
defect on the same literal word. -/
theorem half_minimum_le_weightedLedger_of_prefixSurvival_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (maximumDebt : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hmaximum_pos : 0 < maximumDebt)
    (htail : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) ≤ maximumDebt)
    (hsurvival : quittingCapNashStackContinueProduct roots ≤
      quittingTerminalSemanticDebtSum minimum / (2 * maximumDebt)) :
    quittingTerminalSemanticDebtSum minimum / 2 ≤
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
  apply half_minimum_le_weightedLedger_of_transport_le
    reward minimum roots terminal hminimum
  have htail0 : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward terminal) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
        (quittingTerminalSemanticPair_mem_carrier reward terminal) who
  have hbound0 : 0 ≤ quittingTerminalSemanticDebtSum minimum /
      (2 * maximumDebt) :=
    div_nonneg hminimum_pos.le (mul_nonneg (by norm_num) hmaximum_pos.le)
  calc
    quittingCapNashStackContinueProduct roots *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) ≤
        (quittingTerminalSemanticDebtSum minimum / (2 * maximumDebt)) *
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) :=
      mul_le_mul_of_nonneg_right hsurvival htail0
    _ ≤ (quittingTerminalSemanticDebtSum minimum / (2 * maximumDebt)) *
          maximumDebt := mul_le_mul_of_nonneg_left htail hbound0
    _ = quittingTerminalSemanticDebtSum minimum / 2 := by
      field_simp [ne_of_gt hmaximum_pos]

/-- One row carrying strictly positive cap defect and reached with strictly
positive joint survival through its literal prefix.  The cap defect still
uses an unrestricted best response against the complete actual suffix; this
is not a prescribed-payoff edge certificate. -/
structure QuittingFiniteWordReachedPositiveCapDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile) where
  prefixRoots : List (ι → PMF Bool)
  selectedRoot : ι → PMF Bool
  suffixRoots : List (ι → PMF Bool)
  roots_eq : roots = prefixRoots ++ selectedRoot :: suffixRoots
  prefixSurvival_pos :
    0 < quittingCapNashStackContinueProduct prefixRoots
  capDefect_pos : 0 <
    quittingFiniteWordHeadCapDefect reward selectedRoot suffixRoots terminal

namespace QuittingFiniteWordReachedPositiveCapDefect

/-- The selected row therefore has a strictly positive chronological weighted
cap charge. -/
theorem weightedCapDefect_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {terminal : (quittingGame reward).BehaviorProfile}
    (row : QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) :
    0 < quittingCapNashStackContinueProduct row.prefixRoots *
      quittingFiniteWordHeadCapDefect reward row.selectedRoot row.suffixRoots
        terminal :=
  mul_pos row.prefixSurvival_pos row.capDefect_pos

/-- Some player coordinate carries positive Nash defect at the selected row.
This identifies a profitable best endpoint only; it still does not choose a
prescribed chronological action or close its continuation seam. -/
theorem exists_positiveCoordinateNashDefect
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {roots : List (ι → PMF Bool)}
    {terminal : (quittingGame reward).BehaviorProfile}
    (row : QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) :
    ∃ who, 0 < quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward row.suffixRoots terminal)).2
      row.selectedRoot who := by
  have htotal := row.capDefect_pos
  unfold quittingFiniteWordHeadCapDefect quittingRootTotalNashDefect at htotal
  obtain ⟨who, -, hwho⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun candidate _ =>
      quittingRootCoordinateNashDefect_nonneg reward _ row.selectedRoot
        candidate).mp htotal
  exact ⟨who, hwho⟩

end QuittingFiniteWordReachedPositiveCapDefect

/-- Every strictly positive finite aggregate ledger contains an actually
reached row with strictly positive cap defect. -/
theorem nonempty_reachedPositiveCapDefect_of_weightedLedger_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hledger : 0 <
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal) :
    Nonempty
      (QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) := by
  induction roots with
  | nil => simp at hledger
  | cons root roots ih =>
      have hhead0 : 0 ≤
          quittingFiniteWordHeadCapDefect reward root roots terminal := by
        unfold quittingFiniteWordHeadCapDefect
        exact quittingRootTotalNashDefect_nonneg reward _ root
      have hcontinue0 : 0 ≤ quittingStationaryContinueMass root :=
        quittingStationaryContinueMass_nonneg root
      have htail0 : 0 ≤
          quittingFiniteWordWeightedCapDefectLedger reward roots terminal :=
        quittingFiniteWordWeightedCapDefectLedger_nonneg reward roots terminal
      rw [quittingFiniteWordWeightedCapDefectLedger_cons] at hledger
      by_cases hhead : 0 <
          quittingFiniteWordHeadCapDefect reward root roots terminal
      · exact ⟨{
          prefixRoots := []
          selectedRoot := root
          suffixRoots := roots
          roots_eq := rfl
          prefixSurvival_pos := by
            simp [quittingCapNashStackContinueProduct]
          capDefect_pos := hhead
        }⟩
      · have hheadEq :
            quittingFiniteWordHeadCapDefect reward root roots terminal = 0 :=
          le_antisymm (le_of_not_gt hhead) hhead0
        have hweightedTail : 0 < quittingStationaryContinueMass root *
            quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
          rw [hheadEq, zero_add] at hledger
          exact hledger
        have hcontinue : 0 < quittingStationaryContinueMass root := by
          nlinarith
        have htail : 0 <
            quittingFiniteWordWeightedCapDefectLedger reward roots terminal := by
          nlinarith
        obtain ⟨row⟩ := ih htail
        exact ⟨{
          prefixRoots := root :: row.prefixRoots
          selectedRoot := row.selectedRoot
          suffixRoots := row.suffixRoots
          roots_eq := by simp [row.roots_eq]
          prefixSurvival_pos := by
            rw [quittingCapNashStackContinueProduct_cons]
            exact mul_pos hcontinue row.prefixSurvival_pos
          capDefect_pos := row.capDefect_pos
        }⟩

/-- A strict gap between the minimum debt and transported terminal debt
selects an actually reached positive cap-defect row. -/
theorem nonempty_reachedPositiveCapDefect_of_transport_lt_minimum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (htransport : quittingCapNashStackContinueProduct roots *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) <
      quittingTerminalSemanticDebtSum minimum) :
    Nonempty
      (QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) := by
  apply nonempty_reachedPositiveCapDefect_of_weightedLedger_pos
  have hledger := minimum_sub_transport_le_weightedLedger
    reward minimum roots terminal hminimum
  linarith

/-- The half-minimum aggregate charge likewise selects an actually reached
positive cap-defect row. -/
theorem nonempty_reachedPositiveCapDefect_of_half_minimum_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hledger : quittingTerminalSemanticDebtSum minimum / 2 ≤
      quittingFiniteWordWeightedCapDefectLedger reward roots terminal) :
    Nonempty
      (QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) := by
  apply nonempty_reachedPositiveCapDefect_of_weightedLedger_pos
  linarith

/-- Bounded terminal debt and sufficiently small prefix survival directly
select an actually reached positive cap-defect row. -/
theorem nonempty_reachedPositiveCapDefect_of_prefixSurvival_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (roots : List (ι → PMF Bool))
    (terminal : (quittingGame reward).BehaviorProfile)
    (maximumDebt : ℝ)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimum_pos : 0 < quittingTerminalSemanticDebtSum minimum)
    (hmaximum_pos : 0 < maximumDebt)
    (htail : quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) ≤ maximumDebt)
    (hsurvival : quittingCapNashStackContinueProduct roots ≤
      quittingTerminalSemanticDebtSum minimum / (2 * maximumDebt)) :
    Nonempty
      (QuittingFiniteWordReachedPositiveCapDefect reward roots terminal) := by
  apply nonempty_reachedPositiveCapDefect_of_half_minimum_le
    reward minimum roots terminal hminimum_pos
  exact half_minimum_le_weightedLedger_of_prefixSurvival_le
    reward minimum roots terminal maximumDebt hminimum hminimum_pos
      hmaximum_pos htail hsurvival

/-- One surviving deleted-survival host on an actual word sequence. -/
def HasQuittingFiniteWordVisibleHost
    (words : ℕ → List (ι → PMF Bool)) : Prop :=
  ∃ host threshold, 0 < threshold ∧
    ∀ᶠ rank in atTop,
      threshold ≤ quittingLiteralRootStackOpponentSurvival (words rank) host

/-- Full screening means that every player-deleted survival tends to zero. -/
def IsQuittingFiniteWordFullyScreened
    (words : ℕ → List (ι → PMF Bool)) : Prop :=
  ∀ who, Tendsto
    (fun rank => quittingLiteralRootStackOpponentSurvival (words rank) who)
      atTop (nhds 0)

/-- Honest named boundary alternatives.  This type packages a proved branch;
it does not assert the compact subsequence producer needed to obtain one. -/
inductive QuittingFiniteWordHostOrFullScreening
    (words : ℕ → List (ι → PMF Bool)) : Prop
  | visibleHost (hhost : HasQuittingFiniteWordVisibleHost words)
  | fullScreening (hscreened : IsQuittingFiniteWordFullyScreened words)

end GameTheory
