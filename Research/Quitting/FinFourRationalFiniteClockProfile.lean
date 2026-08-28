/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.FiniteClockPolynomialCenter
import Mathlib.Data.Rat.Encodable

/-!
# Exact rational finite-clock profile codes for Fin4

This module separates the executable upper-certificate payload from its real
game semantics.  A code is only a clock bound and four lists of rational
masses.  The Boolean checker recomputes the literal finite product payoff,
the complete pure-date/Never menu, and maximum exploitability using rational
arithmetic.  It does not trust stored payoff or cap coordinates.

The semantic adapter casts a valid code to four finite-clock stopping laws.
The auxiliary after-support date is an explicit zero coordinate and `Never`
is a separate final coordinate.  No interval-tree or search-completeness
claim is made here.
-/

namespace GameTheory

open Math.ProbabilityMassFunction
open scoped BigOperators

/-- Proof-free exact encoding of the sixty Fin4 reward coordinates.

Rows are indexed by the nonzero four-bit coalition mask minus one, and each
row is indexed by the observer.  Malformed rows read as zero; the executable
well-formedness predicate excludes that fallback from checked inputs. -/
structure RationalFinFourRewardCode where
  rows : List (List ℚ)
deriving DecidableEq, Repr

namespace RationalFinFourRewardCode

/-- Four-bit mask of a Fin4 terminal coalition. -/
def terminalMask (terminal : Finset (Fin 4)) : ℕ :=
  ∑ player ∈ terminal, 2 ^ player.val

/-- Exact reward coordinate, with zero as the total fallback for malformed
codes. -/
def value (reward : RationalFinFourRewardCode)
    (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (observer : Fin 4) : ℚ :=
  ((reward.rows[(terminalMask terminal.1 - 1)]?).bind
      fun row ↦ row[observer.val]?).getD 0

/-- The game reward obtained by casting the exact code. -/
def realReward (reward : RationalFinFourRewardCode) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal observer ↦ reward.value terminal observer

/-- Exact structural validity of a sixty-coordinate reward table. -/
def WellFormed (reward : RationalFinFourRewardCode) : Prop :=
  reward.rows.length = 15 ∧ ∀ row ∈ reward.rows, row.length = 4

/-- Unit normalization of every stored reward coordinate. -/
def Normalized (reward : RationalFinFourRewardCode) : Prop :=
  reward.WellFormed ∧
    ∀ row ∈ reward.rows, ∀ entry ∈ row, |entry| ≤ 1

instance (reward : RationalFinFourRewardCode) : Decidable reward.WellFormed :=
  by
    unfold WellFormed
    infer_instance

instance (reward : RationalFinFourRewardCode) : Decidable reward.Normalized :=
  by
    unfold Normalized WellFormed
    infer_instance

/-- Executable normalized-table checker. -/
def normalized (reward : RationalFinFourRewardCode) : Bool :=
  decide reward.Normalized

theorem normalized_eq_true_iff (reward : RationalFinFourRewardCode) :
    reward.normalized = true ↔ reward.Normalized := by
  simp [normalized]

end RationalFinFourRewardCode

/-- Proof-free rational product-law payload.

For clock bound `T`, each row has `T + 2` coordinates: finite dates
`0, ..., T`, followed by `Never`.  Date `T` is the auxiliary after-support
date and must have zero mass in a valid code. -/
structure RationalFinFourFiniteClockProfileCode where
  clockBound : ℕ
  rows : Fin 4 → List ℚ
deriving DecidableEq, Repr

namespace RationalFinFourFiniteClockProfileCode

/-- List index of a finite-clock atom. -/
def atomIndex (code : RationalFinFourFiniteClockProfileCode) :
    FiniteClockAtom code.clockBound → ℕ
  | none => code.clockBound + 1
  | some time => time.val

/-- Rational mass of one atom, with zero as a total malformed-code fallback. -/
def mass (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4)
    (atom : FiniteClockAtom code.clockBound) : ℚ :=
  (code.rows player)[code.atomIndex atom]?.getD 0

/-- Exact structural and simplex validity of the four rational laws. -/
def Valid (code : RationalFinFourFiniteClockProfileCode) : Prop :=
  0 < code.clockBound ∧
    ∀ player,
      (code.rows player).length = code.clockBound + 2 ∧
      (∀ atom : FiniteClockAtom code.clockBound,
        0 ≤ code.mass player atom) ∧
      code.mass player (finiteClockAuxAtom code.clockBound) = 0 ∧
      (∑ atom : FiniteClockAtom code.clockBound,
        code.mass player atom) = 1

instance (code : RationalFinFourFiniteClockProfileCode) : Decidable code.Valid :=
  by
    unfold Valid
    infer_instance

/-- Executable exact validity checker. -/
def valid (code : RationalFinFourFiniteClockProfileCode) : Bool :=
  decide code.Valid

theorem valid_eq_true_iff (code : RationalFinFourFiniteClockProfileCode) :
    code.valid = true ↔ code.Valid := by
  simp [valid]

/-- Finite dates at which at least one player stops in one pure atom tuple. -/
def activeTimes (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound) :
    Finset (Fin (code.clockBound + 1)) :=
  Finset.univ.filter fun time ↦ ∃ player, choices player = some time

/-- Executable rational value of one pure stopping-time tuple. -/
def outcomeValue (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound)
    (observer : Fin 4) : ℚ :=
  let times := code.activeTimes choices
  if htimes : times.Nonempty then
    let first := times.min' htimes
    let terminal := Finset.univ.filter fun player ↦
      choices player = some first
    if hterminal : terminal.Nonempty then
      reward.value ⟨terminal, hterminal⟩ observer
    else 0
  else 0

theorem activeTimes_nonempty_iff
    (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound) :
    (code.activeTimes choices).Nonempty ↔
      ∃ time, ∃ player,
        finiteClockJointStoppingTimes code.clockBound choices player =
          some time := by
  constructor
  · rintro ⟨time, htime⟩
    obtain ⟨-, ⟨player, hplayer⟩⟩ := Finset.mem_filter.mp htime
    exact ⟨time.val, player, by
      simp [finiteClockJointStoppingTimes, hplayer]⟩
  · rintro ⟨time, player, hplayer⟩
    cases hchoice : choices player with
    | none =>
        simp [finiteClockJointStoppingTimes, hchoice] at hplayer
    | some selected =>
        refine ⟨selected, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact ⟨player, hchoice⟩

theorem min_activeTime_val_eq_natFind
    (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound)
    (htimes : (code.activeTimes choices).Nonempty) :
    ((code.activeTimes choices).min' htimes).val =
      @Nat.find
        (fun time : ℕ ↦ ∃ player : Fin 4,
          finiteClockJointStoppingTimes code.clockBound choices player =
            some time)
        (fun _ ↦ Fintype.decidableExistsFintype)
        ((code.activeTimes_nonempty_iff choices).mp htimes) := by
  letI : DecidablePred (fun time : ℕ ↦ ∃ player : Fin 4,
      finiteClockJointStoppingTimes code.clockBound choices player =
        some time) :=
    fun _ ↦ Fintype.decidableExistsFintype
  let first := (code.activeTimes choices).min' htimes
  let hfinite := (code.activeTimes_nonempty_iff choices).mp htimes
  have hfirstMem : first ∈ code.activeTimes choices :=
    Finset.min'_mem _ _
  obtain ⟨-, ⟨firstPlayer, hfirstPlayer⟩⟩ :=
    Finset.mem_filter.mp hfirstMem
  have hfind_le : Nat.find hfinite ≤ first.val := by
    apply Nat.find_min'
    exact ⟨firstPlayer, by
      simp [finiteClockJointStoppingTimes, hfirstPlayer]⟩
  obtain ⟨findPlayer, hfindPlayer⟩ := Nat.find_spec hfinite
  cases hchoice : choices findPlayer with
  | none =>
      have htime :
          finiteClockJointStoppingTimes code.clockBound choices findPlayer =
            none := by
        simp [finiteClockJointStoppingTimes, hchoice]
      rw [htime] at hfindPlayer
      cases hfindPlayer
  | some selected =>
      have hvalue : selected.val = Nat.find hfinite := by
        have htime :
            finiteClockJointStoppingTimes code.clockBound choices findPlayer =
              some selected.val := by
          simp [finiteClockJointStoppingTimes, hchoice]
        rw [htime] at hfindPlayer
        exact Option.some.inj hfindPlayer
      have hselectedMem : selected ∈ code.activeTimes choices := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨findPlayer, hchoice⟩⟩
      have hfirst_le : first.val ≤ Nat.find hfinite := by
        rw [← hvalue]
        exact Finset.min'_le _ _ hselectedMem
      exact Nat.le_antisymm hfirst_le hfind_le

theorem outcomeValue_eq_finiteStoppingTimesOutcomeValue
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound)
    (observer : Fin 4) :
    code.outcomeValue reward choices observer =
      finiteStoppingTimesOutcomeValue reward.value
        (finiteClockJointStoppingTimes code.clockBound choices) observer := by
  classical
  letI : DecidablePred (fun time : ℕ ↦ ∃ player : Fin 4,
      finiteClockJointStoppingTimes code.clockBound choices player =
        some time) :=
    fun _ ↦ Fintype.decidableExistsFintype
  by_cases htimes : (code.activeTimes choices).Nonempty
  · let first := (code.activeTimes choices).min' htimes
    let hfinite := (code.activeTimes_nonempty_iff choices).mp htimes
    have hfirstMem : first ∈ code.activeTimes choices :=
      Finset.min'_mem _ _
    obtain ⟨-, ⟨player, hplayer⟩⟩ :=
      Finset.mem_filter.mp hfirstMem
    have hterminal :
        (Finset.univ.filter fun who ↦ choices who = some first).Nonempty :=
      ⟨player, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplayer⟩⟩
    have hfirst : first.val = Nat.find hfinite :=
      code.min_activeTime_val_eq_natFind choices htimes
    have hcoalition :
        (Finset.univ.filter fun who ↦ choices who = some first) =
          Finset.univ.filter fun who ↦
            finiteClockJointStoppingTimes code.clockBound choices who =
              some (Nat.find hfinite) := by
      ext who
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases hchoice : choices who with
      | none =>
          have htime :
              finiteClockJointStoppingTimes code.clockBound choices who =
                none := by
            simp [finiteClockJointStoppingTimes, hchoice]
          simp [htime]
      | some selected =>
          have htime :
              finiteClockJointStoppingTimes code.clockBound choices who =
                some selected.val := by
            simp [finiteClockJointStoppingTimes, hchoice]
          simp only [htime, Option.some.injEq]
          constructor
          · intro hselected
            exact congrArg Fin.val hselected |>.trans hfirst
          · intro hselected
            exact Fin.ext (hselected.trans hfirst.symm)
    have hterminalRaw :
        (Finset.univ.filter fun who ↦ choices who =
          some ((code.activeTimes choices).min' htimes)).Nonempty := by
      simpa only [first] using hterminal
    simp only [outcomeValue, htimes, hterminalRaw, dif_pos]
    simp only [finiteStoppingTimesOutcomeValue, hfinite, dif_pos]
    apply congrArg (fun terminal : {S : Finset (Fin 4) // S.Nonempty} ↦
      reward.value terminal observer)
    apply Subtype.ext
    simpa only [first] using hcoalition
  · have hfinite : ¬ ∃ time, ∃ player,
        finiteClockJointStoppingTimes code.clockBound choices player =
          some time := by
      exact fun h ↦ htimes
        ((code.activeTimes_nonempty_iff choices).mpr h)
    simp [outcomeValue, htimes, finiteStoppingTimesOutcomeValue, hfinite]

/-- Exact product-profile prescribed payoff. -/
def payoff (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode)
    (observer : Fin 4) : ℚ :=
  ∑ choices : Fin 4 → FiniteClockAtom code.clockBound,
    (∏ player, code.mass player (choices player)) *
      code.outcomeValue reward choices observer

/-- Exact payoff of one pure date or Never deviation. -/
def deviationPayoff (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode)
    (player : Fin 4) (candidate : FiniteClockAtom code.clockBound) : ℚ :=
  ∑ choices : Fin 4 → FiniteClockAtom code.clockBound,
    (∏ opponent ∈ Finset.univ.erase player,
      code.mass opponent (choices opponent)) *
        (if choices player = candidate then
          code.outcomeValue reward choices player
        else 0)

/-- Exact finite pure-time/Never cap. -/
def cap (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun candidate =>
    code.deviationPayoff reward player candidate

theorem deviationPayoff_le_cap (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4)
    (candidate : FiniteClockAtom code.clockBound) :
    code.deviationPayoff reward player candidate ≤ code.cap reward player := by
  exact Finset.le_sup' _ (Finset.mem_univ candidate)

theorem exists_deviationPayoff_eq_cap (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4) :
    ∃ candidate : FiniteClockAtom code.clockBound,
      code.deviationPayoff reward player candidate = code.cap reward player := by
  obtain ⟨candidate, -, hcandidate⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty fun candidate =>
      code.deviationPayoff reward player candidate
  exact ⟨candidate, hcandidate.symm⟩

/-- Exact unrestricted exploitability claimed by an upper certificate. -/
def exploitability (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun player =>
    max 0 (code.cap reward player - code.payoff reward player)

theorem playerGap_le_exploitability (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (player : Fin 4) :
    max 0 (code.cap reward player - code.payoff reward player) ≤
      code.exploitability reward := by
  exact Finset.le_sup'
    (fun who ↦ max 0 (code.cap reward who - code.payoff reward who))
    (Finset.mem_univ player)

/-- The complete executable upper-certificate checker. -/
def verifiesUpper (reward : RationalFinFourRewardCode) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode) : Bool :=
  code.valid && decide (code.exploitability reward < target)

theorem verifiesUpper_eq_true_iff
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode) :
    code.verifiesUpper reward target = true ↔
      code.Valid ∧ code.exploitability reward < target := by
  simp [verifiesUpper, valid_eq_true_iff]

/-! ## Fair raw-code enumeration -/

deriving instance Encodable for RationalFinFourRewardCode
deriving instance Encodable for RationalFinFourFiniteClockProfileCode

/-- The `n`th proof-free rational profile candidate. -/
def candidateAt (n : ℕ) : Option RationalFinFourFiniteClockProfileCode :=
  Encodable.decode n

/-- Every proof-free rational profile code occurs at a finite candidate
index. -/
theorem candidateAt_surjective
    (code : RationalFinFourFiniteClockProfileCode) :
    ∃ n, candidateAt n = some code := by
  exact ⟨Encodable.encode code, Encodable.encodek code⟩

/-- The `n`th rational profile candidate, retained exactly when it passes the
upper-certificate checker. -/
def checkedCandidateAt (reward : RationalFinFourRewardCode) (target : ℚ)
    (n : ℕ) : Option RationalFinFourFiniteClockProfileCode :=
  match candidateAt n with
  | none => none
  | some code =>
      if code.verifiesUpper reward target then some code else none

theorem checkedCandidateAt_eq_some_iff
    (reward : RationalFinFourRewardCode) (target : ℚ) (n : ℕ)
    (code : RationalFinFourFiniteClockProfileCode) :
    checkedCandidateAt reward target n = some code ↔
      candidateAt n = some code ∧ code.verifiesUpper reward target = true := by
  cases hcandidate : candidateAt n with
  | none => simp [checkedCandidateAt, hcandidate]
  | some candidate =>
      by_cases hverified : candidate.verifiesUpper reward target = true
      · constructor
        · intro hout
          have heq : candidate = code := by
            simpa [checkedCandidateAt, hcandidate, hverified] using hout
          subst code
          exact ⟨rfl, hverified⟩
        · rintro ⟨hcode, -⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          simp [checkedCandidateAt, hcandidate, hverified]
      · have hfalse : candidate.verifiesUpper reward target = false :=
          Bool.eq_false_of_not_eq_true hverified
        constructor
        · intro hout
          simp [checkedCandidateAt, hcandidate, hfalse] at hout
        · rintro ⟨hcode, hcodeVerified⟩
          have heq : candidate = code := Option.some.inj hcode
          subst code
          exact (hverified hcodeVerified).elim

/-- A checked rational upper witness is discovered at a finite enumeration
index.  This is the finite-stage fact used by an outer dovetail. -/
theorem exists_checkedCandidateAt_of_verifiesUpper
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode)
    (hcode : code.verifiesUpper reward target = true) :
    ∃ n, checkedCandidateAt reward target n = some code := by
  obtain ⟨n, hn⟩ := candidateAt_surjective code
  exact ⟨n, checkedCandidateAt_eq_some_iff reward target n code |>.2
    ⟨hn, hcode⟩⟩

/-! ## Semantic decoding -/

section Semantic

noncomputable section

/-- Real simplex coordinates represented by a rational code. -/
def realMass (code : RationalFinFourFiniteClockProfileCode)
    (player : Fin 4) (atom : FiniteClockAtom code.clockBound) : ℝ :=
  code.mass player atom

theorem realMass_nonneg (code : RationalFinFourFiniteClockProfileCode)
    (hvalid : code.Valid) (player : Fin 4)
    (atom : FiniteClockAtom code.clockBound) :
    0 ≤ code.realMass player atom := by
  change (0 : ℝ) ≤ (code.mass player atom : ℝ)
  exact_mod_cast hvalid.2 player |>.2.1 atom

theorem realMass_sum_eq_one (code : RationalFinFourFiniteClockProfileCode)
    (hvalid : code.Valid) (player : Fin 4) :
    ∑ atom : FiniteClockAtom code.clockBound, code.realMass player atom = 1 := by
  change ∑ atom : FiniteClockAtom code.clockBound,
    (code.mass player atom : ℝ) = 1
  exact_mod_cast hvalid.2 player |>.2.2.2

theorem realMass_mem_stdSimplex
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (player : Fin 4) :
    code.realMass player ∈ stdSimplex ℝ (FiniteClockAtom code.clockBound) := by
  exact ⟨code.realMass_nonneg hvalid player,
    code.realMass_sum_eq_one hvalid player⟩

theorem realMass_aux_eq_zero
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (player : Fin 4) :
    code.realMass player (finiteClockAuxAtom code.clockBound) = 0 := by
  change (code.mass player (finiteClockAuxAtom code.clockBound) : ℝ) = 0
  exact_mod_cast hvalid.2 player |>.2.2.1

theorem cast_outcomeValue_eq_finiteStoppingTimesOutcomeValue
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode)
    (choices : Fin 4 → FiniteClockAtom code.clockBound)
    (observer : Fin 4) :
    (code.outcomeValue reward choices observer : ℝ) =
      finiteStoppingTimesOutcomeValue reward.realReward
        (finiteClockJointStoppingTimes code.clockBound choices) observer := by
  calc
    (code.outcomeValue reward choices observer : ℝ) =
        Rat.castHom ℝ
          (finiteStoppingTimesOutcomeValue reward.value
            (finiteClockJointStoppingTimes code.clockBound choices)
            observer) := by
      exact congrArg (Rat.castHom ℝ)
        (code.outcomeValue_eq_finiteStoppingTimesOutcomeValue
          reward choices observer)
    _ = finiteStoppingTimesOutcomeValue
        (fun terminal player ↦ Rat.castHom ℝ (reward.value terminal player))
        (finiteClockJointStoppingTimes code.clockBound choices) observer :=
      map_finiteStoppingTimesOutcomeValue (Rat.castHom ℝ) reward.value
        (finiteClockJointStoppingTimes code.clockBound choices) observer
    _ = finiteStoppingTimesOutcomeValue reward.realReward
        (finiteClockJointStoppingTimes code.clockBound choices) observer := rfl

/-- Literal behavioral profile decoded from a valid rational certificate. -/
def toBehaviorProfile (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid) :
    (quittingGame reward.realReward).BehaviorProfile :=
  finiteClockDecodedProfile reward.realReward code.clockBound code.realMass
    (code.realMass_mem_stdSimplex hvalid)

theorem cast_payoff_eq_quittingTerminalPayoff
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (observer : Fin 4) :
    (code.payoff reward observer : ℝ) =
      quittingTerminalPayoff reward.realReward
        (code.toBehaviorProfile reward hvalid) observer := by
  rw [toBehaviorProfile,
    quittingTerminalPayoff_finiteClockDecodedProfile_eq_sum]
  simp only [payoff]
  push_cast
  refine Finset.sum_congr rfl fun choices _ ↦ ?_
  rw [code.cast_outcomeValue_eq_finiteStoppingTimesOutcomeValue]
  rfl

theorem cast_deviationPayoff_eq_quittingTerminalPayoff_update
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (player : Fin 4) (candidate : FiniteClockAtom code.clockBound) :
    (code.deviationPayoff reward player candidate : ℝ) =
      quittingTerminalPayoff reward.realReward
        (Function.update (code.toBehaviorProfile reward hvalid) player
          (quittingPureTimeBehaviorStrategy reward.realReward player
            (finiteClockAtomToStoppingTime code.clockBound candidate)))
        player := by
  rw [toBehaviorProfile,
    quittingTerminalPayoff_finiteClockDecodedProfile_update_eq_sum]
  simp only [deviationPayoff]
  push_cast
  refine Finset.sum_congr rfl fun choices _ ↦ ?_
  by_cases hchoice : choices player = candidate
  · simp only [hchoice, if_pos]
    rw [code.cast_outcomeValue_eq_finiteStoppingTimesOutcomeValue]
    simp [realMass]
  · simp [hchoice]

theorem cast_cap_eq_quittingContinuationBestResponseValue
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (player : Fin 4) :
    (code.cap reward player : ℝ) =
      quittingContinuationBestResponseValue reward.realReward
        (code.toBehaviorProfile reward hvalid) player := by
  apply le_antisymm
  · obtain ⟨candidate, hcandidate⟩ :=
      code.exists_deviationPayoff_eq_cap reward player
    rw [← hcandidate,
      code.cast_deviationPayoff_eq_quittingTerminalPayoff_update]
    exact quittingTerminalPayoff_update_pureTime_le_continuationBestResponseValue
      reward.realReward (code.toBehaviorProfile reward hvalid) player
      (finiteClockAtomToStoppingTime code.clockBound candidate)
  · obtain ⟨candidate, hcandidate⟩ :=
      exists_finiteClockCandidate_payoff_eq_continuationBestResponseValue
        reward.realReward code.clockBound code.realMass
        (code.realMass_mem_stdSimplex hvalid)
        (code.realMass_aux_eq_zero hvalid) player
    have hcandidate' :
        quittingTerminalPayoff reward.realReward
            (Function.update (code.toBehaviorProfile reward hvalid) player
              (quittingPureTimeBehaviorStrategy reward.realReward player
                (finiteClockAtomToStoppingTime code.clockBound candidate)))
            player =
          quittingContinuationBestResponseValue reward.realReward
            (code.toBehaviorProfile reward hvalid) player := by
      simpa only [toBehaviorProfile] using hcandidate
    rw [← hcandidate',
      ← code.cast_deviationPayoff_eq_quittingTerminalPayoff_update]
    exact_mod_cast code.deviationPayoff_le_cap reward player candidate

theorem cast_playerGap_eq_terminalPlayerGap
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid)
    (player : Fin 4) :
    ((max 0 (code.cap reward player - code.payoff reward player) : ℚ) : ℝ) =
        max 0
          (quittingContinuationBestResponseValue reward.realReward
              (code.toBehaviorProfile reward hvalid) player -
            quittingTerminalPayoff reward.realReward
              (code.toBehaviorProfile reward hvalid) player) := by
  push_cast
  rw [code.cast_cap_eq_quittingContinuationBestResponseValue,
    code.cast_payoff_eq_quittingTerminalPayoff]

theorem cast_exploitability_eq_quittingTerminalExploitability
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid) :
    (code.exploitability reward : ℝ) =
      quittingTerminalExploitability reward.realReward
        (code.toBehaviorProfile reward hvalid) := by
  unfold exploitability quittingTerminalExploitability
  apply le_antisymm
  · obtain ⟨player, -, hplayer⟩ :=
      Finset.exists_mem_eq_sup' Finset.univ_nonempty fun player : Fin 4 =>
        max 0 (code.cap reward player - code.payoff reward player)
    rw [hplayer]
    calc
      ((max 0 (code.cap reward player - code.payoff reward player) : ℚ) : ℝ) =
          max 0
            (quittingContinuationBestResponseValue reward.realReward
                (code.toBehaviorProfile reward hvalid) player -
              quittingTerminalPayoff reward.realReward
                (code.toBehaviorProfile reward hvalid) player) :=
        code.cast_playerGap_eq_terminalPlayerGap reward hvalid player
      _ ≤ QuittingBoundaryHolonomy.finitePlayerMax (fun who ↦
          max 0
            (quittingContinuationBestResponseValue reward.realReward
                (code.toBehaviorProfile reward hvalid) who -
              quittingTerminalPayoff reward.realReward
                (code.toBehaviorProfile reward hvalid) who)) :=
        QuittingBoundaryHolonomy.le_finitePlayerMax
          (fun who : Fin 4 ↦
            max 0
              (quittingContinuationBestResponseValue reward.realReward
                  (code.toBehaviorProfile reward hvalid) who -
                quittingTerminalPayoff reward.realReward
                  (code.toBehaviorProfile reward hvalid) who)) player
  · apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro player
    rw [← code.cast_playerGap_eq_terminalPlayerGap]
    exact_mod_cast code.playerGap_le_exploitability reward player

theorem toBehaviorProfile_finiteClock
    (reward : RationalFinFourRewardCode)
    (code : RationalFinFourFiniteClockProfileCode) (hvalid : code.Valid) :
    ∃ laws : Fin 4 → PMF (Option ℕ),
      (∀ player, IsFiniteClockStoppingLaw code.clockBound (laws player)) ∧
      code.toBehaviorProfile reward hvalid =
        quittingStoppingLawProfile reward.realReward laws := by
  let laws := finiteClockDecodedLaws code.clockBound code.realMass
    (code.realMass_mem_stdSimplex hvalid)
  refine ⟨laws, ?_, rfl⟩
  intro player choice hchoice
  exact finiteClockDecodeLaw_support code.clockBound
    (code.realMass player) (code.realMass_mem_stdSimplex hvalid player)
    (code.realMass_aux_eq_zero hvalid player) choice hchoice

/-- A successful executable check decodes to an actual finite-clock profile
whose literal unrestricted behavioral exploitability is below the target. -/
theorem verifiesUpper_sound
    (reward : RationalFinFourRewardCode) (target : ℚ)
    (code : RationalFinFourFiniteClockProfileCode)
    (hchecked : code.verifiesUpper reward target = true) :
    ∃ hvalid : code.Valid,
      quittingTerminalExploitability reward.realReward
          (code.toBehaviorProfile reward hvalid) < (target : ℝ) ∧
        ∃ laws : Fin 4 → PMF (Option ℕ),
          (∀ player,
            IsFiniteClockStoppingLaw code.clockBound (laws player)) ∧
          code.toBehaviorProfile reward hvalid =
            quittingStoppingLawProfile reward.realReward laws := by
  obtain ⟨hvalid, htarget⟩ :=
    (code.verifiesUpper_eq_true_iff reward target).mp hchecked
  refine ⟨hvalid, ?_, code.toBehaviorProfile_finiteClock reward hvalid⟩
  rw [← code.cast_exploitability_eq_quittingTerminalExploitability]
  exact_mod_cast htarget

/-- Every emitted upper-search row carries an actual finite-clock behavioral
profile with the checked unrestricted exploitability bound. -/
theorem checkedCandidateAt_sound
    (reward : RationalFinFourRewardCode) (target : ℚ) (n : ℕ)
    (code : RationalFinFourFiniteClockProfileCode)
    (hrow : checkedCandidateAt reward target n = some code) :
    ∃ hvalid : code.Valid,
      quittingTerminalExploitability reward.realReward
          (code.toBehaviorProfile reward hvalid) < (target : ℝ) ∧
        ∃ laws : Fin 4 → PMF (Option ℕ),
          (∀ player,
            IsFiniteClockStoppingLaw code.clockBound (laws player)) ∧
          code.toBehaviorProfile reward hvalid =
            quittingStoppingLawProfile reward.realReward laws := by
  exact code.verifiesUpper_sound reward target
    ((checkedCandidateAt_eq_some_iff reward target n code).mp hrow).2

end

end Semantic

end RationalFinFourFiniteClockProfileCode

end GameTheory
