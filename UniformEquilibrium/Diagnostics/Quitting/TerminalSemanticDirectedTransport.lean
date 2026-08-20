/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.MaxAffine.Basic
import MathUE.Probability.SurvivalWeightedReachedHistoryAccount
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticOwnStrategyTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence

/-!
# Directed transport of terminal semantic debt

An exact terminal-semantic prefix chain records a semantic pair at each time
and a product root whose prefix action carries the next pair to the current
pair.  For each player, its best-response debt then obeys

`debt t = defect t + survival t * debt (t + 1)`.

Thus the debt is an exact section of the backward-time path graph.  The edge
label has no floor, shift equal to the root coordinate Nash defect, and slope
equal to the root's joint Continue mass.  Literal behavioral profiles define
such chains through their all-Continue semantic spines.

Besides the exact section and finite telescope, the main results describe a
return of the debt coordinate.  Any survival loss on a positive-debt return
must be paid by a positive reached Nash defect.  If every intervening defect
vanishes, a positive-debt return forces every intervening root to have joint
Continue mass one. The positive reached charge either gives an actual
best-endpoint behavioral gain or is covered by the exact continuation-option
budget isolated in `TerminalSemanticOwnStrategyTransport`.
-/

noncomputable section

namespace GameTheory

open Finset Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A sequence of terminal-semantic pairs related by exact root prefixing. -/
structure QuittingTerminalSemanticPrefixChain
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota) where
  /-- The terminal-semantic pair at each time. -/
  pair : ℕ → QuittingTerminalSemanticPair iota
  /-- The product root prefixing the next pair. -/
  root : ℕ → iota → PMF Bool
  /-- Exact compatibility of the pair sequence and the roots. -/
  prefix_eq : ∀ time,
    pair time = quittingTerminalSemanticPrefix reward (root time) (pair (time + 1))

omit [DecidableEq iota] in
/-- The reached-history weight of literal live roots equals the profile's live
mass at the displayed row. -/
theorem reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∀ time,
      reachedHistoryWeight
          (fun stage ↦ quittingStationaryContinueMass
            (quittingProfileLiveRoot reward profile stage)) time =
        quittingLiveMass reward profile time := by
  intro time
  induction time with
  | zero => simp
  | succ time ih =>
      rw [reachedHistoryWeight_succ, quittingLiveMass_succ, ih]
      congr 1

namespace QuittingTerminalSemanticPrefixChain

variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- The exact prefix chain induced by the all-Continue spine of a behavioral
profile. -/
def ofProfile (profile : (quittingGame reward).BehaviorProfile) :
    QuittingTerminalSemanticPrefixChain reward where
  pair time := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile time)
  root time := quittingProfileLiveRoot reward profile time
  prefix_eq := quittingTerminalSemanticPair_spine_eq_prefix reward profile

variable (chain : QuittingTerminalSemanticPrefixChain reward)

/-- Playerwise best-response debt along the chain. -/
def debt (who : iota) (time : ℕ) : ℝ :=
  quittingTerminalSemanticDebt (chain.pair time) who

/-- One-stage coordinate Nash defect against the next envelope cap. -/
def defect (who : iota) (time : ℕ) : ℝ :=
  quittingRootCoordinateNashDefect reward (chain.pair (time + 1)).2
    (chain.root time) who

/-- Joint Continue mass, interpreted as the slope of debt transport. -/
def survival (time : ℕ) : ℝ :=
  quittingStationaryContinueMass (chain.root time)

/-- The affine edge label carrying next-period debt to current debt. -/
def label (who : iota) (time : ℕ) : Math.MaxAffineTransport.Label :=
  ⟨⊥, chain.defect who time, chain.survival time⟩

@[simp] theorem label_floor (who : iota) (time : ℕ) :
    (chain.label who time).floor = ⊥ := rfl

@[simp] theorem label_shift (who : iota) (time : ℕ) :
    (chain.label who time).shift = chain.defect who time := rfl

@[simp] theorem label_slope (who : iota) (time : ℕ) :
    (chain.label who time).slope = chain.survival time := rfl

theorem survival_nonneg (time : ℕ) : 0 ≤ chain.survival time :=
  quittingStationaryContinueMass_nonneg (chain.root time)

theorem survival_le_one (time : ℕ) : chain.survival time ≤ 1 :=
  quittingStationaryContinueMass_le_one (chain.root time)

theorem defect_nonneg (who : iota) (time : ℕ) : 0 ≤ chain.defect who time :=
  quittingRootCoordinateNashDefect_nonneg reward (chain.pair (time + 1)).2
    (chain.root time) who

/-- The terminal-semantic prefix formula as an exact scalar debt account. -/
theorem debt_account (who : iota) (time : ℕ) :
    chain.debt who time =
      chain.defect who time + chain.survival time * chain.debt who (time + 1) := by
  rw [debt, chain.prefix_eq time]
  exact quittingTerminalSemanticDebt_prefix_eq_capDefect_add_continueMass_mul
    reward (chain.pair (time + 1)) (chain.root time) who

/-- The edge label transports next-period debt exactly to current debt. -/
theorem label_apply_next_debt (who : iota) (time : ℕ) :
    (chain.label who time).apply (chain.debt who (time + 1)) =
      chain.debt who time := by
  rw [label, Math.MaxAffineTransport.Label.apply_mk_bot]
  exact (chain.debt_account who time).symm

/-- The path graph oriented from the next time back to the current time. -/
def backwardTimeGraph : Math.EdgeGraph ℕ ℕ where
  source time := time + 1
  target time := time

/-- The constant-fiber transport defined by the debt labels. -/
def directedTransport (who : iota) :=
  Math.MaxAffineTransport.toTransport backwardTimeGraph (chain.label who)

/-- Debt is an exact section of its backward-time directed transport. -/
theorem debt_isSection (who : iota) :
    (chain.directedTransport who).IsSection (chain.debt who) := by
  intro time
  exact chain.label_apply_next_debt who time

/-- Exact finite account for every abstract prefix chain. -/
theorem debt_zero_eq_sum_reached_defect_add_tail
    (who : iota) (cutoff : ℕ) :
    chain.debt who 0 =
      (∑ time ∈ Finset.range cutoff,
        reachedHistoryWeight chain.survival time * chain.defect who time) +
      reachedHistoryWeight chain.survival cutoff * chain.debt who cutoff := by
  exact debt_zero_eq_sum_reachedHistoryWeight_mul_defect_add
    chain.survival (chain.defect who) (chain.debt who) (chain.debt_account who) cutoff

/-- On a return of the debt coordinate, survival loss is exactly paid by
reached coordinate Nash defects. -/
theorem debt_mul_one_sub_reachedWeight_eq_sum_reached_defect_of_return
    (who : iota) (cutoff : ℕ)
    (hreturn : chain.debt who cutoff = chain.debt who 0) :
    chain.debt who 0 * (1 - reachedHistoryWeight chain.survival cutoff) =
      ∑ time ∈ Finset.range cutoff,
        reachedHistoryWeight chain.survival time * chain.defect who time := by
  have haccount := floor_mul_one_sub_reachedHistoryWeight_eq
    chain.survival (chain.defect who) (chain.debt who)
      (chain.debt_account who) (chain.debt who 0) 0 0 cutoff
      (by ring) (by rw [hreturn]; ring)
  simpa using haccount

/-- A positive-debt return with strict survival loss contains a reached row
with strictly positive defect charge. -/
theorem exists_reached_defect_pos_of_return_of_reachedWeight_lt_one
    (who : iota) (cutoff : ℕ) (hdebt : 0 < chain.debt who 0)
    (hreturn : chain.debt who cutoff = chain.debt who 0)
    (hweight : reachedHistoryWeight chain.survival cutoff < 1) :
    ∃ time ∈ Finset.range cutoff,
      0 < reachedHistoryWeight chain.survival time * chain.defect who time := by
  have hbudget :=
    chain.debt_mul_one_sub_reachedWeight_eq_sum_reached_defect_of_return
      who cutoff hreturn
  have hsum : 0 < ∑ time ∈ Finset.range cutoff,
      reachedHistoryWeight chain.survival time * chain.defect who time := by
    rw [← hbudget]
    positivity
  exact (Finset.sum_pos_iff_of_nonneg fun time _ ↦
    mul_nonneg (reachedHistoryWeight_nonneg chain.survival_nonneg time)
      (chain.defect_nonneg who time)).mp hsum

/-- If all intervening root defects vanish, a positive-debt return has no
survival loss. -/
theorem reachedWeight_eq_one_of_return_of_defect_eq_zero
    (who : iota) (cutoff : ℕ) (hdebt : 0 < chain.debt who 0)
    (hreturn : chain.debt who cutoff = chain.debt who 0)
    (hdefect : ∀ time < cutoff, chain.defect who time = 0) :
    reachedHistoryWeight chain.survival cutoff = 1 := by
  have hbudget :=
    chain.debt_mul_one_sub_reachedWeight_eq_sum_reached_defect_of_return
      who cutoff hreturn
  have hsum : (∑ time ∈ Finset.range cutoff,
      reachedHistoryWeight chain.survival time * chain.defect who time) = 0 := by
    apply Finset.sum_eq_zero
    intro time htime
    rw [hdefect time (Finset.mem_range.mp htime), mul_zero]
  rw [hsum] at hbudget
  have hweightLe := reachedHistoryWeight_le_one
    chain.survival_nonneg chain.survival_le_one cutoff
  nlinarith

/-- If all intervening root defects vanish, a positive-debt return forces
every intervening product root to Continue jointly with probability one. -/
theorem survival_eq_one_of_return_of_defect_eq_zero
    (who : iota) (cutoff : ℕ) (hdebt : 0 < chain.debt who 0)
    (hreturn : chain.debt who cutoff = chain.debt who 0)
    (hdefect : ∀ time < cutoff, chain.defect who time = 0) :
    ∀ time < cutoff, chain.survival time = 1 := by
  apply survival_eq_one_of_lt_of_reachedHistoryWeight_eq_one
    chain.survival_nonneg chain.survival_le_one
  exact chain.reachedWeight_eq_one_of_return_of_defect_eq_zero
    who cutoff hdebt hreturn hdefect

/-! ## Literal-profile consequences -/

/-- On a literal-spine return of one player's debt, its survival loss is paid
exactly by live-mass-weighted coordinate Nash defects. -/
theorem quittingTerminalSemanticDebt_mul_one_sub_liveMass_eq_sum_capDefect_of_return
    (profile : (quittingGame reward).BehaviorProfile) (who : iota) (cutoff : ℕ)
    (hreturn : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile cutoff)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who *
          (1 - quittingLiveMass reward profile cutoff) =
      ∑ time ∈ Finset.range cutoff,
        quittingLiveMass reward profile time *
          quittingRootCoordinateNashDefect reward
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile (time + 1))).2
            (quittingProfileLiveRoot reward profile time) who := by
  let literalChain := ofProfile profile
  have hreturn' : literalChain.debt who cutoff = literalChain.debt who 0 := by
    simpa only [literalChain, ofProfile, debt, quittingAllContinueProfileSpine] using hreturn
  have hbudget :=
    literalChain.debt_mul_one_sub_reachedWeight_eq_sum_reached_defect_of_return
      who cutoff hreturn'
  have hweight : ∀ time,
      reachedHistoryWeight literalChain.survival time =
        quittingLiveMass reward profile time := by
    intro time
    exact reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
      reward profile time
  simp_rw [hweight] at hbudget
  simpa only [literalChain, ofProfile, debt, defect,
    quittingAllContinueProfileSpine] using hbudget

/-- If a positive literal-spine debt returns after strict absorption, some
reached row has a strictly positive cap-defect charge. -/
theorem exists_liveMass_mul_capDefect_pos_of_terminalSemanticDebt_return
    (profile : (quittingGame reward).BehaviorProfile) (who : iota) (cutoff : ℕ)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hreturn : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile cutoff)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who)
    (hlive : quittingLiveMass reward profile cutoff < 1) :
    ∃ time ∈ Finset.range cutoff,
      0 < quittingLiveMass reward profile time *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).2
          (quittingProfileLiveRoot reward profile time) who := by
  let literalChain := ofProfile profile
  have hreturn' : literalChain.debt who cutoff = literalChain.debt who 0 := by
    simpa only [literalChain, ofProfile, debt, quittingAllContinueProfileSpine] using hreturn
  have hdebt' : 0 < literalChain.debt who 0 := by
    simpa only [literalChain, ofProfile, debt, quittingAllContinueProfileSpine] using hdebt
  have hweight : ∀ time,
      reachedHistoryWeight literalChain.survival time =
        quittingLiveMass reward profile time := by
    intro time
    exact reachedHistoryWeight_stationaryContinueMass_eq_quittingLiveMass
      reward profile time
  have hlive' : reachedHistoryWeight literalChain.survival cutoff < 1 := by
    rw [hweight]
    exact hlive
  have hwitness :=
    literalChain.exists_reached_defect_pos_of_return_of_reachedWeight_lt_one
      who cutoff hdebt' hreturn' hlive'
  simp_rw [hweight] at hwitness
  simpa only [literalChain, ofProfile, defect,
    quittingAllContinueProfileSpine] using hwitness

/-- A positive-debt return with survival loss yields either an actual reached
best-endpoint gain or a positively charged row whose cap defect is entirely
covered by the explicit continuation-option budget. -/
theorem exists_actualRowGain_pos_or_capDefect_le_quitOptionBudget_of_return
    (profile : (quittingGame reward).BehaviorProfile) (who : iota) (cutoff : ℕ)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hreturn : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile cutoff)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who)
    (hlive : quittingLiveMass reward profile cutoff < 1) :
    ∃ time ∈ Finset.range cutoff,
      let pair := quittingLiteralActualRowTail reward profile time
      let root := quittingLiteralActualRowRoot reward profile time
      0 < quittingLiteralActualRowBestEndpointGain reward profile who time ∨
        (0 < quittingLiveMass reward profile time *
            quittingRootCoordinateNashDefect reward pair.2 root who ∧
          quittingRootCoordinateNashDefect reward pair.2 root who ≤
            quittingRootOpponentContinueMass root who *
              (root who true).toReal *
                quittingTerminalSemanticDebt pair who) := by
  obtain ⟨time, htime, hcharge⟩ :=
    exists_liveMass_mul_capDefect_pos_of_terminalSemanticDebt_return
      profile who cutoff hdebt hreturn hlive
  refine ⟨time, htime, ?_⟩
  let pair := quittingLiteralActualRowTail reward profile time
  let root := quittingLiteralActualRowRoot reward profile time
  change 0 < quittingLiveMass reward profile time *
    quittingRootCoordinateNashDefect reward pair.2 root who at hcharge
  have hliveNonneg : 0 ≤ quittingLiveMass reward profile time :=
    quittingLiveMass_nonneg reward profile time
  have hlivePos : 0 < quittingLiveMass reward profile time := by
    rcases (mul_pos_iff.mp hcharge) with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hliveNonneg hneg.1).elim
  by_cases hstrict : quittingRootOpponentContinueMass root who *
      (root who true).toReal * quittingTerminalSemanticDebt pair who <
        quittingRootCoordinateNashDefect reward pair.2 root who
  · left
    exact quittingLiteralActualRowBestEndpointGain_pos_of_capDefect_gt_quitOptionBudget
      reward profile who time hlivePos hstrict
  · right
    exact ⟨hcharge, le_of_not_gt hstrict⟩

/-- On a positive literal-spine debt return, zero intervening cap defects
force every intervening root to Continue jointly with probability one. -/
theorem stationaryContinueMass_eq_one_of_terminalSemanticDebt_return_of_capDefect_eq_zero
    (profile : (quittingGame reward).BehaviorProfile) (who : iota) (cutoff : ℕ)
    (hdebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who)
    (hreturn : quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile cutoff)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who)
    (hdefect : ∀ time < cutoff,
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward profile (time + 1))).2
        (quittingProfileLiveRoot reward profile time) who = 0) :
    ∀ time < cutoff,
      quittingStationaryContinueMass
        (quittingProfileLiveRoot reward profile time) = 1 := by
  let literalChain := ofProfile profile
  have hreturn' : literalChain.debt who cutoff = literalChain.debt who 0 := by
    simpa only [literalChain, ofProfile, debt, quittingAllContinueProfileSpine] using hreturn
  have hdebt' : 0 < literalChain.debt who 0 := by
    simpa only [literalChain, ofProfile, debt, quittingAllContinueProfileSpine] using hdebt
  have hdefect' : ∀ time < cutoff, literalChain.defect who time = 0 := by
    intro time htime
    simpa only [literalChain, ofProfile, defect,
      quittingAllContinueProfileSpine] using hdefect time htime
  simpa only [literalChain, ofProfile, survival] using
    literalChain.survival_eq_one_of_return_of_defect_eq_zero
      who cutoff hdebt' hreturn' hdefect'

end QuittingTerminalSemanticPrefixChain

end GameTheory
