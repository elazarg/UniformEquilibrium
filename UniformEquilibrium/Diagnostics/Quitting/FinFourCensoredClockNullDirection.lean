/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.FiniteFubini
import UniformEquilibrium.Diagnostics.Quitting.CensoredFiniteClockOperationalEffect
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-!
# A Fin4 censored-clock null direction

This file realizes the concrete calendar-reshuffling regression from the
censored-clock packet.  A large old-clock total-variation displacement is
invisible to every hard payoff and pure timing gain, hence to every retained
tail semantic pair.  The result records reward-, coalition-, and
terminal-semantic nullity only: it does not erase the stage label of the
calendar atom and does not provide a positive-minimum source or a uniform-
equilibrium conclusion.
-/

noncomputable section

namespace GameTheory
namespace FinFourCensoredClockNullDirection

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

abbrev Player := Fin 4

private noncomputable def realPMF {α : Type} [Fintype α]
    (weight : α → ℝ) (hnonneg : ∀ action, 0 ≤ weight action)
    (hsum : ∑ action, weight action = 1) : PMF α :=
  PMF.ofFintype (fun action ↦ ENNReal.ofReal (weight action)) (by
    rw [← ENNReal.ofReal_one, ← hsum]
    exact (ENNReal.ofReal_sum_of_nonneg fun action _ ↦ hnonneg action).symm)

private theorem realPMF_apply {α : Type} [Fintype α]
    (weight : α → ℝ) (hnonneg : ∀ action, 0 ≤ weight action)
    (hsum : ∑ action, weight action = 1) (action : α) :
    (realPMF weight hnonneg hsum action).toReal = weight action := by
  rw [realPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (hnonneg action)]

/-- The four-player reward table.  The coalition `{0,3}` is the unique
override at which players `1,2,3` receive a nonzero reward. -/
def reward (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : ℝ :=
  if terminal.1 = {0, 3} then
    ![(2 : ℝ), 1, 1, 1] who
  else if who = 0 then
    if 1 ∈ terminal.1 then
      if 0 ∈ terminal.1 then 0 else 2
    else if 2 ∈ terminal.1 then 1
    else if 0 ∈ terminal.1 then 1 else 0
  else 0

/-- Every entry of the regression table has absolute value at most two. -/
theorem abs_reward_le_two (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 2 := by
  fin_cases who <;> simp only [reward] <;> split_ifs <;> norm_num

@[simp] theorem reward_singleton (who : Player) :
    reward (quittingSingletonTerminal who) who =
      if who = 0 then 1 else 0 := by
  fin_cases who <;>
    simp [reward, quittingSingletonTerminal,
      show ({0} : Finset Player) ≠ {0, 3} by decide,
      show ({1} : Finset Player) ≠ {0, 3} by decide,
      show ({2} : Finset Player) ≠ {0, 3} by decide,
      show ({3} : Finset Player) ≠ {0, 3} by decide]

def oldLate (N : ℕ) (hN : 3 ≤ N) : Fin N := ⟨N - 1, by omega⟩

def oldZero (N : ℕ) (_hN : 3 ≤ N) : Fin N := ⟨0, by omega⟩

def oldOne (N : ℕ) (hN : 3 ≤ N) : Fin N := ⟨1, by omega⟩

def newLate (N : ℕ) (hN : 3 ≤ N) : Fin (N + 1) := ⟨N - 1, by omega⟩

def newBoundary (N : ℕ) (_hN : 3 ≤ N) : Fin (N + 1) := ⟨N, by omega⟩

def newOne (N : ℕ) (hN : 3 ≤ N) : Fin (N + 1) := ⟨1, by omega⟩

/-- Weight function of the old deadline-`N` law. -/
def oldWeight (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (who : Player) (action : QuittingFiniteDeadlineTimingAction N) : ℝ :=
  if who = 0 ∨ who = 3 then
    if action = none then 1 else 0
  else if who = 1 then
    if action = some (oldLate N hN) then 1 / 2
    else if action = none then 1 / 2 else 0
  else if action = some (oldZero N hN) then c
  else if action = none then 1 - c else 0

theorem oldWeight_nonneg (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction N) :
    0 ≤ oldWeight N c hN who action := by
  unfold oldWeight
  split_ifs <;> norm_num <;> linarith

theorem oldWeight_sum (N : ℕ) (c : ℝ) (hN : 3 ≤ N) (who : Player) :
    ∑ action, oldWeight N c hN who action = 1 := by
  fin_cases who <;>
    simp [oldWeight, Fintype.sum_option]
  all_goals norm_num

/-- The old deadline-`N` product timing law `p`. -/
def oldLaw (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Player → PMF (QuittingFiniteDeadlineTimingAction N) :=
  fun who ↦ realPMF (oldWeight N c hN who)
    (oldWeight_nonneg N c hN hc0 hc1 who) (oldWeight_sum N c hN who)

@[simp] theorem oldLaw_apply (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction N) :
    (oldLaw N c hN hc0 hc1 who action).toReal =
      oldWeight N c hN who action := by
  exact realPMF_apply _ _ _ _

/-- Weight function of the adjacent deadline-`N+1` law. -/
def newWeight (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (who : Player)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) : ℝ :=
  if who = 0 ∨ who = 3 then
    if action = none then 1 else 0
  else if who = 1 then
    if action = some (newLate N hN) then 1 / 2
    else if action = some (newBoundary N hN) then 1 / 6
    else if action = none then 1 / 3 else 0
  else if action = some (newOne N hN) then c
  else if action = none then 1 - c else 0

theorem newWeight_nonneg (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) :
    0 ≤ newWeight N c hN who action := by
  unfold newWeight
  split_ifs <;> norm_num <;> linarith

theorem newWeight_sum (N : ℕ) (c : ℝ) (hN : 3 ≤ N) (who : Player) :
    ∑ action, newWeight N c hN who action = 1 := by
  have hne : newLate N hN ≠ newBoundary N hN := by
    change (⟨N - 1, by omega⟩ : Fin (N + 1)) ≠ ⟨N, by omega⟩
    intro heq
    have : N - 1 = N := congrArg Fin.val heq
    omega
  have hsum :
      (∑ x : Fin (N + 1),
          if x = newLate N hN then (2 : ℝ)⁻¹
          else if x = newBoundary N hN then (6 : ℝ)⁻¹ else 0) =
        (2 : ℝ)⁻¹ + (6 : ℝ)⁻¹ := by
    calc
      _ = (∑ x : Fin (N + 1),
              if x = newLate N hN then (2 : ℝ)⁻¹ else 0) +
            ∑ x : Fin (N + 1),
              if x = newBoundary N hN then (6 : ℝ)⁻¹ else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = newLate N hN
          · subst x
            simp [hne]
          · by_cases hy : x = newBoundary N hN <;>
              simp [hx, hy, Ne.symm hne]
      _ = _ := by simp
  fin_cases who <;>
    simp [newWeight, Fintype.sum_option]
  rw [hsum]
  norm_num

/-- The adjacent deadline-`N+1` product timing law `q`. -/
def newLaw (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Player → PMF (QuittingFiniteDeadlineTimingAction (N + 1)) :=
  fun who ↦ realPMF (newWeight N c hN who)
    (newWeight_nonneg N c hN hc0 hc1 who) (newWeight_sum N c hN who)

@[simp] theorem newLaw_apply (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) :
    (newLaw N c hN hc0 hc1 who action).toReal =
      newWeight N c hN who action := by
  exact realPMF_apply _ _ _ _

/-- The explicit old-clock law obtained after censoring `newLaw`. -/
def reshuffledWeight (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (who : Player) (action : QuittingFiniteDeadlineTimingAction N) : ℝ :=
  if who = 2 then
    if action = some (oldOne N hN) then c
    else if action = none then 1 - c else 0
  else oldWeight N c hN who action

theorem reshuffledWeight_nonneg (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction N) :
    0 ≤ reshuffledWeight N c hN who action := by
  unfold reshuffledWeight
  split_ifs
  · exact hc0
  · linarith
  · norm_num
  · exact oldWeight_nonneg N c hN hc0 hc1 who action

theorem reshuffledWeight_sum (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (who : Player) :
    ∑ action, reshuffledWeight N c hN who action = 1 := by
  by_cases hwho : who = 2
  · subst who
    simp [reshuffledWeight, Fintype.sum_option]
  · simp only [reshuffledWeight, hwho, ↓reduceIte]
    exact oldWeight_sum N c hN who

/-- The censored law written directly on the old deadline. -/
def reshuffledLaw (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Player → PMF (QuittingFiniteDeadlineTimingAction N) :=
  fun who ↦ realPMF (reshuffledWeight N c hN who)
    (reshuffledWeight_nonneg N c hN hc0 hc1 who)
    (reshuffledWeight_sum N c hN who)

@[simp] theorem reshuffledLaw_apply (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player)
    (action : QuittingFiniteDeadlineTimingAction N) :
    (reshuffledLaw N c hN hc0 hc1 who action).toReal =
      reshuffledWeight N c hN who action := by
  exact realPMF_apply _ _ _ _

private theorem censor_some_apply
    (N : ℕ) (law : PMF (QuittingFiniteDeadlineTimingAction (N + 1)))
    (time : Fin N) :
    (law.map quittingFiniteDeadlineTimingActionCensor (some time)) =
      law (some time.castSucc) := by
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single (some time.castSucc)]
  · simp [quittingFiniteDeadlineTimingActionCensor, time.isLt]
  · intro action _ hne
    split
    · next heq =>
        exfalso
        apply hne
        cases action with
        | none =>
            simp [quittingFiniteDeadlineTimingActionCensor] at heq
        | some nextTime =>
            simp only [quittingFiniteDeadlineTimingActionCensor] at heq
            split at heq
            · next hlt =>
                have hfin : time = ⟨nextTime.val, hlt⟩ :=
                  Option.some.inj heq
                apply congrArg some
                apply Fin.ext
                simpa using (congrArg Fin.val hfin).symm
            · simp at heq
    · rfl
  · simp

private theorem censor_none_apply
    (N : ℕ) (law : PMF (QuittingFiniteDeadlineTimingAction (N + 1))) :
    ((law.map quittingFiniteDeadlineTimingActionCensor) none).toReal =
      (law none).toReal +
        (law (quittingFiniteDeadlineTimingBoundaryAction N)).toReal := by
  cases N with
  | zero =>
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_option]
      simp [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingBoundaryAction]
      rw [ENNReal.toReal_add (PMF.apply_ne_top law none)
        (PMF.apply_ne_top law (some 0))]
  | succ N =>
      rw [PMF.map_apply, tsum_fintype, Fintype.sum_option,
        Fin.sum_univ_succ]
      simp only [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingBoundaryAction, ↓reduceIte]
      rw [Finset.sum_eq_single (Fin.last N)]
      · simp [Fin.val_last]
        rw [ENNReal.toReal_add (PMF.apply_ne_top law none)
          (PMF.apply_ne_top law _)]
        congr 2
      · intro time _ htime
        have hlt : time.val < N := by
          exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ time.isLt) fun heq ↦
            htime (Fin.ext heq)
        simp [hlt]
      · simp

/-- Censoring the boundary mass of `newLaw` gives exactly the displayed
old-clock reshuffling. -/
theorem censor_newLaw_eq_reshuffledLaw
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingFiniteDeadlineTimingProfileCensor
        (newLaw N c hN hc0 hc1) =
      reshuffledLaw N c hN hc0 hc1 := by
  funext who
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ action) (PMF.apply_ne_top _ action)).mp
  cases action with
  | none =>
      change (((newLaw N c hN hc0 hc1 who).map
        quittingFiniteDeadlineTimingActionCensor) none).toReal = _
      rw [censor_none_apply]
      have hboundary : quittingFiniteDeadlineTimingBoundaryAction N =
          some (newBoundary N hN) := rfl
      have hboundaryNeLate : newBoundary N hN ≠ newLate N hN := by
        intro heq
        have : N = N - 1 := congrArg Fin.val heq
        omega
      have hboundaryNeOne : newBoundary N hN ≠ newOne N hN := by
        intro heq
        have : N = 1 := congrArg Fin.val heq
        omega
      fin_cases who
      all_goals simp [hboundary, newWeight, reshuffledWeight, oldWeight,
        hboundaryNeLate, hboundaryNeOne]
      all_goals norm_num
  | some time =>
      change (((newLaw N c hN hc0 hc1 who).map
        quittingFiniteDeadlineTimingActionCensor) (some time)).toReal = _
      rw [censor_some_apply]
      rw [newLaw_apply, reshuffledLaw_apply]
      have hcastLate :
          time.castSucc = newLate N hN ↔ time = oldLate N hN := by
        constructor <;> intro heq <;> apply Fin.ext
        · simpa [newLate, oldLate] using congrArg Fin.val heq
        · simpa [newLate, oldLate] using congrArg Fin.val heq
      have hcastOne :
          time.castSucc = newOne N hN ↔ time = oldOne N hN := by
        constructor <;> intro heq <;> apply Fin.ext
        · simpa [newOne, oldOne] using congrArg Fin.val heq
        · simpa [newOne, oldOne] using congrArg Fin.val heq
      have hcastBoundary : time.castSucc ≠ newBoundary N hN := by
        intro heq
        have : time.val = N := by
          simpa [newBoundary] using congrArg Fin.val heq
        omega
      fin_cases who <;>
        simp [newWeight, reshuffledWeight, oldWeight, hcastLate, hcastOne,
          hcastBoundary]

theorem reshuffledLaw_eq_oldLaw_of_ne_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player) (hwho : who ≠ 2) :
    reshuffledLaw N c hN hc0 hc1 who = oldLaw N c hN hc0 hc1 who := by
  apply PMF.ext
  intro action
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ action) (PMF.apply_ne_top _ action)).mp
  rw [reshuffledLaw_apply, oldLaw_apply]
  simp [reshuffledWeight, hwho]

/-- The only nonzero censored marginal distance is player `2`'s calendar
move, and that distance is exactly `c`. -/
theorem pmfTV_old_reshuffled_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Math.Probability.pmfTV
        (oldLaw N c hN hc0 hc1 2)
        (reshuffledLaw N c hN hc0 hc1 2) = c := by
  change (∑ action : QuittingFiniteDeadlineTimingAction N,
    max (((oldLaw N c hN hc0 hc1 2) action).toReal -
      ((reshuffledLaw N c hN hc0 hc1 2) action).toReal) 0) = c
  rw [Fintype.sum_option]
  simp only [oldLaw_apply, reshuffledLaw_apply]
  have hzeroOne : oldZero N hN ≠ oldOne N hN := by
    intro heq
    have : 0 = 1 := congrArg Fin.val heq
    omega
  have hsum :
      (∑ time : Fin N,
        max (oldWeight N c hN 2 (some time) -
          reshuffledWeight N c hN 2 (some time)) 0) = c := by
    have hpoint : (fun time : Fin N ↦
        max (oldWeight N c hN 2 (some time) -
          reshuffledWeight N c hN 2 (some time)) 0) =
        fun time ↦ if time = oldZero N hN then c else 0 := by
      funext time
      by_cases hzero : time = oldZero N hN
      · subst time
        simp [oldWeight, reshuffledWeight, hc0, hzeroOne]
      · by_cases hone : time = oldOne N hN
        · subst time
          simp [oldWeight, reshuffledWeight, hzero, hc0]
        · simp [oldWeight, reshuffledWeight, hzero, hone]
    rw [hpoint]
    simp
  rw [hsum]
  simp [oldWeight, reshuffledWeight]

theorem pmfTV_old_reshuffled
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (who : Player) :
    Math.Probability.pmfTV
        (oldLaw N c hN hc0 hc1 who)
        (reshuffledLaw N c hN hc0 hc1 who) =
      if who = 2 then c else 0 := by
  by_cases hwho : who = 2
  · subst who
    simpa using pmfTV_old_reshuffled_two N c hN hc0 hc1
  · rw [if_neg hwho, reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 who hwho,
      Math.Probability.pmfTV_self]

/-- The summed old-clock total variation after censoring is exactly `c`. -/
theorem sum_censoredError_eq_c
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∑ who, quittingFiniteDeadlineCensoredError N
        (oldLaw N c hN hc0 hc1) (newLaw N c hN hc0 hc1) who = c := by
  unfold quittingFiniteDeadlineCensoredError
  rw [censor_newLaw_eq_reshuffledLaw]
  simp_rw [pmfTV_old_reshuffled]
  norm_num

/-- With the packet's operational scale `a = (1-c)/4`, the censor ratio is
exactly `4c/(1-c)`. -/
theorem censoredError_div_boundaryScale_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 < c) (hc1 : c < 1) :
    (∑ who, quittingFiniteDeadlineCensoredError N
        (oldLaw N c hN hc0.le hc1.le) (newLaw N c hN hc0.le hc1.le) who) /
        ((1 - c) / 4) =
      4 * c / (1 - c) := by
  rw [sum_censoredError_eq_c]
  field_simp

/-- Player `1` carries exactly the strategically effective mass `1/6` at
the newly exposed boundary date. -/
theorem new_boundaryParticipation_one_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingFiniteDeadlineBoundaryParticipation N
        (newLaw N c hN hc0 hc1) 1 = 1 / 6 := by
  have hboundaryLate :
      (⟨N, by omega⟩ : Fin (N + 1)) ≠ newLate N hN := by
    intro heq
    have hval := congrArg Fin.val heq
    simp [newLate] at hval
    omega
  unfold quittingFiniteDeadlineBoundaryParticipation
  rw [newLaw_apply]
  simp [newWeight, newBoundary,
    quittingFiniteDeadlineTimingBoundaryAction, hboundaryLate]

/-- The censored displacement can exceed any prescribed multiple of the
normalized boundary-gain scale. -/
theorem exists_censoredError_div_boundaryScale_gt
    (N : ℕ) (hN : 3 ≤ N) (K : ℝ) :
    ∃ (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1),
      K <
        (∑ who, quittingFiniteDeadlineCensoredError N
          (oldLaw N c hN hc0.le hc1.le)
          (newLaw N c hN hc0.le hc1.le) who) /
            ((1 - c) / 4) := by
  let c := (|K| + 1) / (|K| + 2)
  have hc0 : 0 < c := by
    dsimp only [c]
    positivity
  have hc1 : c < 1 := by
    dsimp only [c]
    rw [div_lt_one (by positivity)]
    linarith
  refine ⟨c, hc0, hc1, ?_⟩
  rw [censoredError_div_boundaryScale_eq N c hN hc0 hc1]
  have hden : |K| + 2 ≠ 0 := by positivity
  dsimp only [c]
  rw [show 4 * ((|K| + 1) / (|K| + 2)) /
      (1 - (|K| + 1) / (|K| + 2)) = 4 * (|K| + 1) by
    field_simp
    ring]
  nlinarith [le_abs_self K, abs_nonneg K]

private theorem timingPurePayoff_zero_of_playerZero_never
    (dates : ℕ)
    (choices : Player → QuittingFiniteDeadlineTimingAction dates)
    (who : Player) (hwho : who ≠ 0) (hzero : choices 0 = none) :
    timingPurePayoff reward dates choices who = 0 := by
  induction dates with
  | zero => exact timingPurePayoff_zero reward choices who
  | succ dates ih =>
      rw [timingPurePayoff_succ]
      unfold quittingRootPayoff
      split_ifs with hcurrent
      · have hzeroMem : 0 ∉ quittingQuitters
            (fun player ↦ timingActionCurrent (choices player)) := by
          simp [quittingQuitters, hzero, timingActionCurrent]
        have hterminal : quittingQuitters
            (fun player ↦ timingActionCurrent (choices player)) ≠ {0, 3} := by
          intro heq
          apply hzeroMem
          rw [heq]
          simp
        simp [reward, hterminal, hwho]
      · apply ih
        simp [timingChoicesTail, timingActionTail, hzero]

private theorem timingPurePayoff_eq_reward_of_first
    (table : {S : Finset Player // S.Nonempty} → Payoff Player) :
    ∀ (dates : ℕ)
      (choices : Player → QuittingFiniteDeadlineTimingAction dates)
      (first : Fin dates) (terminal : {S : Finset Player // S.Nonempty}),
      (∀ player time, time.val < first.val → choices player ≠ some time) →
      (∀ player, choices player = some first ↔ player ∈ terminal.1) →
      ∀ who, timingPurePayoff table dates choices who =
        table terminal who := by
  intro dates
  induction dates with
  | zero =>
      intro choices first
      exact Fin.elim0 first
  | succ dates ih =>
      intro choices first terminal hbefore hfirst who
      cases first using Fin.cases with
      | zero =>
          have hquitters : quittingQuitters
              (fun player ↦ timingActionCurrent (choices player)) = terminal.1 := by
            ext player
            simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
              true_and, timingActionCurrent_eq_true_iff, hfirst]
          have hcurrent : (quittingQuitters fun player ↦
              timingActionCurrent (choices player)).Nonempty := by
            rw [hquitters]
            exact terminal.2
          have hpayoff := timingPurePayoff_succ_of_current_nonempty
            table dates choices who hcurrent
          simpa only [hquitters] using hpayoff
      | succ first =>
          rw [timingPurePayoff_succ_of_current_empty]
          · apply ih (timingChoicesTail choices) first terminal
            · intro player time htime heq
              apply hbefore player time.succ (by simpa using htime)
              have hcontinue : timingActionCurrent (choices player) = false := by
                by_contra htrue
                have hzero : choices player = some (0 : Fin (dates + 1)) :=
                  (timingActionCurrent_eq_true_iff _).mp (by simpa using htrue)
                exact hbefore player 0 (by simp) hzero
              rw [← timingAction_lift_tail_of_continue
                (choices player) hcontinue]
              simpa [timingChoicesTail, timingActionLift] using
                congrArg timingActionLift heq
            · intro player
              constructor
              · intro htail
                have hlift := congrArg timingActionLift htail
                unfold timingChoicesTail at hlift
                have hcontinue : timingActionCurrent (choices player) = false := by
                  by_contra htrue
                  have hzero : choices player = some (0 : Fin (dates + 1)) :=
                    (timingActionCurrent_eq_true_iff _).mp (by simpa using htrue)
                  exact hbefore player 0 (by simp) hzero
                rw [timingAction_lift_tail_of_continue
                  (choices player) hcontinue] at hlift
                exact (hfirst player).mp (by
                  simpa [timingActionLift] using hlift)
              · intro hmem
                have horiginal := (hfirst player).mpr hmem
                simp [timingChoicesTail, horiginal, timingActionTail]
          · intro hnonempty
            obtain ⟨player, hplayer⟩ := hnonempty
            have hcurrent := hplayer
            simp only [quittingQuitters, Finset.mem_filter, Finset.mem_univ,
              true_and] at hcurrent
            have hzero : choices player = some (0 : Fin (dates + 1)) :=
              (timingActionCurrent_eq_true_iff _).mp hcurrent
            exact hbefore player 0 (by simp) hzero

private theorem timingPurePayoff_all_none
    (table : {S : Finset Player // S.Nonempty} → Payoff Player)
    (dates : ℕ) (who : Player) :
    timingPurePayoff table dates (fun _ ↦ none) who = 0 := by
  induction dates with
  | zero => exact timingPurePayoff_zero table _ who
  | succ dates ih =>
      rw [timingPurePayoff_succ_of_current_empty]
      · rw [show timingChoicesTail (fun _ : Player ↦ none) =
          (fun _ ↦ none) by
            funext player
            simp [timingChoicesTail, timingActionTail]]
        exact ih
      · simp [quittingQuitters, timingActionCurrent]

private theorem fin_ne_of_val_lt {n : ℕ} {a b : Fin n}
    (h : a.val < b.val) : b ≠ a := by
  intro heq
  have := congrArg Fin.val heq
  omega

private theorem old_two_zero_value
    (N : ℕ) (hN : 3 ≤ N)
    (a b : QuittingFiniteDeadlineTimingAction N)
    (hb : b ≠ some (oldZero N hN)) :
    timingPurePayoff reward N ![a, b, some (oldZero N hN), none] 0 = 1 := by
  by_cases ha : a = some (oldZero N hN)
  · have hfirst := timingPurePayoff_eq_reward_of_first reward N
      ![a, b, some (oldZero N hN), none] (oldZero N hN)
      ⟨{0, 2}, by decide⟩
    rw [hfirst]
    · simp [reward,
        show ({0, 2} : Finset Player) ≠ {0, 3} by decide,
        show (1 : Player) ≠ 2 by decide]
    · intro player time htime
      simp [oldZero] at htime
    · intro player
      fin_cases player <;> simp [ha, hb]
  · have hfirst := timingPurePayoff_eq_reward_of_first reward N
      ![a, b, some (oldZero N hN), none] (oldZero N hN)
      ⟨{2}, by decide⟩
    rw [hfirst]
    · simp [reward,
        show ({2} : Finset Player) ≠ {0, 3} by decide,
        show (1 : Player) ≠ 2 by decide]
    · intro player time htime
      simp [oldZero] at htime
    · intro player
      fin_cases player <;> simp [ha, hb]

private theorem old_one_late_value
    (N : ℕ) (hN : 3 ≤ N)
    (a : QuittingFiniteDeadlineTimingAction N) :
    timingPurePayoff reward N ![a, some (oldLate N hN), none, none] 0 =
      match a with
      | none => 2
      | some time => if time = oldLate N hN then 0 else 1 := by
  cases a with
  | none =>
      have hfirst := timingPurePayoff_eq_reward_of_first reward N
        ![none, some (oldLate N hN), none, none] (oldLate N hN)
        ⟨{1}, by decide⟩
      rw [hfirst]
      · norm_num [reward,
          show ({1} : Finset Player) ≠ {0, 3} by decide]
      · intro player time htime
        fin_cases player
        · simp
        · change some (oldLate N hN) ≠ some time
          exact fun heq ↦ fin_ne_of_val_lt htime (Option.some.inj heq)
        · simp
        · simp
      · intro player
        fin_cases player <;> simp
  | some time =>
      by_cases htime : time = oldLate N hN
      · subst time
        have hfirst := timingPurePayoff_eq_reward_of_first reward N
          ![some (oldLate N hN), some (oldLate N hN), none, none]
          (oldLate N hN) ⟨{0, 1}, by decide⟩
        rw [hfirst]
        · norm_num [reward,
            show ({0, 1} : Finset Player) ≠ {0, 3} by decide]
        · intro player earlier hearlier
          fin_cases player
          · change some (oldLate N hN) ≠ some earlier
            exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
          · change some (oldLate N hN) ≠ some earlier
            exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
          · simp
          · simp
        · intro player
          fin_cases player <;> simp
      · have hlt : time.val < (oldLate N hN).val := by
          change time.val < N - 1
          have hle : time.val ≤ N - 1 := by omega
          have hne : time.val ≠ N - 1 := by
            intro heq
            apply htime
            apply Fin.ext
            exact heq
          omega
        have hfirst := timingPurePayoff_eq_reward_of_first reward N
          ![some time, some (oldLate N hN), none, none] time
          ⟨{0}, by decide⟩
        rw [hfirst]
        · norm_num [reward, htime,
            show ({0} : Finset Player) ≠ {0, 3} by decide]
        · intro player earlier hearlier
          fin_cases player
          · change some time ≠ some earlier
            exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
          · change some (oldLate N hN) ≠ some earlier
            exact fun heq ↦
              fin_ne_of_val_lt (lt_trans hearlier hlt) (Option.some.inj heq)
          · simp
          · simp
        · intro player
          fin_cases player <;> simp [Ne.symm htime]

private theorem old_only_zero_value
    (N : ℕ) (a : QuittingFiniteDeadlineTimingAction N) :
    timingPurePayoff reward N ![a, none, none, none] 0 =
      if a = none then 0 else 1 := by
  cases a with
  | none =>
      rw [show ![none, none, none, none] =
        (fun _ : Player ↦ none) by
          funext player
          fin_cases player <;> rfl]
      exact timingPurePayoff_all_none reward N 0
  | some time =>
      have hfirst := timingPurePayoff_eq_reward_of_first reward N
        ![some time, none, none, none] time ⟨{0}, by decide⟩
      rw [hfirst]
      · simp [reward,
          show ({0} : Finset Player) ≠ {0, 3} by decide]
      · intro player earlier hearlier
        fin_cases player
        · change some time ≠ some earlier
          exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
        · simp
        · simp
        · simp
      · intro player
        fin_cases player <;> simp

private theorem expect_oldLaw_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction N → ℝ) :
    Math.Probability.expect (oldLaw N c hN hc0 hc1 0) f = f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [oldLaw_apply, oldWeight]

private theorem expect_oldLaw_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction N → ℝ) :
    Math.Probability.expect (oldLaw N c hN hc0 hc1 1) f =
      (1 / 2 : ℝ) * f (some (oldLate N hN)) + 1 / 2 * f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [oldLaw_apply, oldWeight]
  ring

private theorem expect_oldLaw_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction N → ℝ) :
    Math.Probability.expect (oldLaw N c hN hc0 hc1 2) f =
      c * f (some (oldZero N hN)) + (1 - c) * f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [oldLaw_apply, oldWeight]
  ring

private theorem expect_oldLaw_three
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction N → ℝ) :
    Math.Probability.expect (oldLaw N c hN hc0 hc1 3) f = f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [oldLaw_apply, oldWeight]

/-- The old law's displayed hard payoff for player `0` is exactly one. -/
theorem old_timingPayoff_zero_eq_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    timingMixedPayoff reward N (oldLaw N c hN hc0 hc1) 0 = 1 := by
  have hlateZero : oldLate N hN ≠ oldZero N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldLate, oldZero] at this
    omega
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  rw [expect_oldLaw_zero]
  simp_rw [expect_oldLaw_one, expect_oldLaw_two, expect_oldLaw_three]
  simp_rw [old_two_zero_value N hN none (some (oldLate N hN)) (by
      intro heq
      exact hlateZero (Option.some.inj heq)),
    old_two_zero_value N hN none none (by intro heq; cases heq),
    old_one_late_value,
    old_only_zero_value]
  simp
  ring

private theorem old_pure_zero_payoff_le_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (oldLaw N c hN hc0 hc1) 0 (PMF.pure action)) 0 ≤ 1 := by
  have hlateZero : oldLate N hN ≠ oldZero N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldLate, oldZero] at this
    omega
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0),
    Math.Probability.expect_pure]
  simp_rw [expect_oldLaw_one, expect_oldLaw_two, expect_oldLaw_three]
  simp_rw [old_two_zero_value N hN action (some (oldLate N hN)) (by
      intro heq
      exact hlateZero (Option.some.inj heq)),
    old_two_zero_value N hN action none (by intro heq; cases heq),
    old_one_late_value,
    old_only_zero_value]
  cases action with
  | none =>
      simp
      ring_nf
      exact le_rfl
  | some time =>
      by_cases htime : time = oldLate N hN
      · simp [htime]
        nlinarith
      · simp [htime]
        ring_nf
        exact le_rfl

private theorem old_pure_other_payoff_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (oldLaw N c hN hc0 hc1) who (PMF.pure action)) who = 0 := by
  have hzeroLaw : oldLaw N c hN hc0 hc1 0 = PMF.pure none := by
    apply PMF.ext
    intro candidate
    apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ candidate) (PMF.apply_ne_top _ candidate)).mp
    rw [oldLaw_apply]
    cases candidate <;> simp [oldWeight]
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  rw [show Function.update (oldLaw N c hN hc0 hc1) who
      (PMF.pure action) 0 = PMF.pure none by
        rw [Function.update_of_ne (Ne.symm hwho), hzeroLaw]]
  simp only [Math.Probability.expect_pure]
  have hpoint (a b d : QuittingFiniteDeadlineTimingAction N) :
      timingPurePayoff reward N ![none, a, b, d] who = 0 :=
    timingPurePayoff_zero_of_playerZero_never N _ who hwho rfl
  simp_rw [hpoint]
  simp

private theorem timingMixedPayoff_eq_zero_of_zeroLaw
    {dates : ℕ}
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction dates))
    (hzero : mixed 0 = PMF.pure none)
    (who : Player) (hwho : who ≠ 0) :
    timingMixedPayoff reward dates mixed who = 0 := by
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4, hzero]
  simp only [Math.Probability.expect_pure]
  have hpoint (a b d : QuittingFiniteDeadlineTimingAction dates) :
      timingPurePayoff reward dates ![none, a, b, d] who = 0 :=
    timingPurePayoff_zero_of_playerZero_never dates _ who hwho rfl
  simp_rw [hpoint]
  simp

theorem old_timingPayoff_other_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0) :
    timingMixedPayoff reward N (oldLaw N c hN hc0 hc1) who = 0 := by
  apply timingMixedPayoff_eq_zero_of_zeroLaw _ _ who hwho
  apply PMF.ext
  intro candidate
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ candidate) (PMF.apply_ne_top _ candidate)).mp
  rw [oldLaw_apply]
  cases candidate <;> simp [oldWeight]

/-- The old finite timing law is an exact Nash equilibrium, including all
finite-date, tie, and Never deviations. -/
theorem oldLaw_isNash
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension.IsNash
      (oldLaw N c hN hc0 hc1) := by
  rw [(quittingFiniteDeadlineTimingGame reward N).isNash_iff_gains_nonpos]
  intro who action
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub]
  by_cases hwho : who = 0
  · subst who
    rw [old_timingPayoff_zero_eq_one]
    linarith [old_pure_zero_payoff_le_one N c hN hc0 hc1 action]
  · rw [old_timingPayoff_other_eq_zero N c hN hc0 hc1 who hwho,
      old_pure_other_payoff_eq_zero N c hN hc0 hc1 who hwho action]
    norm_num

private theorem two_player_zero_value
    (dates : ℕ) (a : QuittingFiniteDeadlineTimingAction dates)
    (stop : Fin dates) :
    timingPurePayoff reward dates ![a, some stop, none, none] 0 =
      match a with
      | none => 2
      | some time =>
          if time.val < stop.val then 1
          else if time = stop then 0 else 2 := by
  cases a with
  | none =>
      have hfirst := timingPurePayoff_eq_reward_of_first reward dates
        ![none, some stop, none, none] stop ⟨{1}, by decide⟩
      rw [hfirst]
      · simp [reward,
          show ({1} : Finset Player) ≠ {0, 3} by decide]
      · intro player earlier hearlier
        fin_cases player
        · simp
        · change some stop ≠ some earlier
          exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
        · simp
        · simp
      · intro player
        fin_cases player <;> simp
  | some time =>
      by_cases hlt : time.val < stop.val
      · have hfirst := timingPurePayoff_eq_reward_of_first reward dates
          ![some time, some stop, none, none] time ⟨{0}, by decide⟩
        rw [hfirst]
        · simp [reward,
            show ({0} : Finset Player) ≠ {0, 3} by decide, hlt]
        · intro player earlier hearlier
          fin_cases player
          · change some time ≠ some earlier
            exact fun heq ↦ fin_ne_of_val_lt hearlier (Option.some.inj heq)
          · change some stop ≠ some earlier
            exact fun heq ↦
              fin_ne_of_val_lt (lt_trans hearlier hlt) (Option.some.inj heq)
          · simp
          · simp
        · intro player
          fin_cases player
          · simp
          · simp [fin_ne_of_val_lt hlt]
          · simp
          · simp
      · by_cases heq : time = stop
        · subst time
          have hfirst := timingPurePayoff_eq_reward_of_first reward dates
            ![some stop, some stop, none, none] stop ⟨{0, 1}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({0, 1} : Finset Player) ≠ {0, 3} by decide]
          · intro player earlier hearlier
            fin_cases player
            · change some stop ≠ some earlier
              exact fun h ↦ fin_ne_of_val_lt hearlier (Option.some.inj h)
            · change some stop ≠ some earlier
              exact fun h ↦ fin_ne_of_val_lt hearlier (Option.some.inj h)
            · simp
            · simp
          · intro player
            fin_cases player <;> simp
        · have hstoplt : stop.val < time.val := by
            have hle : stop.val ≤ time.val := Nat.le_of_not_gt hlt
            omega
          have hfirst := timingPurePayoff_eq_reward_of_first reward dates
            ![some time, some stop, none, none] stop ⟨{1}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({1} : Finset Player) ≠ {0, 3} by decide, hlt, heq]
          · intro player earlier hearlier
            fin_cases player
            · change some time ≠ some earlier
              exact fun h ↦
                fin_ne_of_val_lt (lt_trans hearlier hstoplt) (Option.some.inj h)
            · change some stop ≠ some earlier
              exact fun h ↦ fin_ne_of_val_lt hearlier (Option.some.inj h)
            · simp
            · simp
          · intro player
            fin_cases player <;> simp [heq]

private theorem new_two_one_value
    (N : ℕ) (hN : 3 ≤ N)
    (a b : QuittingFiniteDeadlineTimingAction (N + 1))
    (hb0 : b ≠ some 0) (hb1 : b ≠ some (newOne N hN)) :
    timingPurePayoff reward (N + 1)
      ![a, b, some (newOne N hN), none] 0 = 1 := by
  have honeZero : newOne N hN ≠ (0 : Fin (N + 1)) := by
    intro heq
    have := congrArg Fin.val heq
    simp [newOne] at this
  cases a with
  | none =>
      have hfirst := timingPurePayoff_eq_reward_of_first reward (N + 1)
        ![none, b, some (newOne N hN), none] (newOne N hN)
        ⟨{2}, by decide⟩
      rw [hfirst]
      · simp [reward,
          show ({2} : Finset Player) ≠ {0, 3} by decide,
          show (1 : Player) ≠ 2 by decide]
      · intro player earlier hearlier
        have hearlierZero : earlier = 0 := by
          apply Fin.ext
          simp [newOne] at hearlier ⊢
          omega
        subst earlier
        fin_cases player <;> simp [hb0, honeZero]
      · intro player
        fin_cases player <;> simp [hb1]
  | some time =>
      by_cases hzero : time = 0
      · subst time
        have hfirst := timingPurePayoff_eq_reward_of_first reward (N + 1)
          ![some 0, b, some (newOne N hN), none] 0 ⟨{0}, by decide⟩
        rw [hfirst]
        · simp [reward,
            show ({0} : Finset Player) ≠ {0, 3} by decide]
        · intro player earlier hearlier
          simp at hearlier
        · intro player
          fin_cases player <;> simp [hb0, honeZero]
      · by_cases hone : time = newOne N hN
        · subst time
          have hfirst := timingPurePayoff_eq_reward_of_first reward (N + 1)
            ![some (newOne N hN), b, some (newOne N hN), none]
            (newOne N hN) ⟨{0, 2}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({0, 2} : Finset Player) ≠ {0, 3} by decide,
              show (1 : Player) ≠ 2 by decide]
          · intro player earlier hearlier
            have hearlierZero : earlier = 0 := by
              apply Fin.ext
              simp [newOne] at hearlier ⊢
              omega
            subst earlier
            fin_cases player <;> simp [hb0, honeZero]
          · intro player
            fin_cases player <;> simp [hb1]
        · have htime : 1 < time.val := by
            have hpositive : 0 < time.val := by
              exact Nat.pos_of_ne_zero fun heq ↦ hzero (Fin.ext heq)
            have hneOne : time.val ≠ 1 := by
              intro heq
              apply hone
              apply Fin.ext
              simpa [newOne]
            omega
          have hfirst := timingPurePayoff_eq_reward_of_first reward (N + 1)
            ![some time, b, some (newOne N hN), none] (newOne N hN)
            ⟨{2}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({2} : Finset Player) ≠ {0, 3} by decide,
              show (1 : Player) ≠ 2 by decide]
          · intro player earlier hearlier
            have hearlierZero : earlier = 0 := by
              apply Fin.ext
              simp [newOne] at hearlier ⊢
              omega
            subst earlier
            fin_cases player <;> simp [hb0, hzero, honeZero]
          · intro player
            fin_cases player <;> simp [hb1, hone]

private theorem expect_newLaw_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect (newLaw N c hN hc0 hc1 0) f = f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [newLaw_apply, newWeight]

private theorem expect_newLaw_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect (newLaw N c hN hc0 hc1 1) f =
      (1 / 2 : ℝ) * f (some (newLate N hN)) +
        1 / 6 * f (some (newBoundary N hN)) + 1 / 3 * f none := by
  have hne : newLate N hN ≠ newBoundary N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [newLate, newBoundary] at this
    omega
  have hsum :
      (∑ x : Fin (N + 1),
        (if x = newLate N hN then (1 / 2 : ℝ)
          else if x = newBoundary N hN then 1 / 6 else 0) * f (some x)) =
        1 / 2 * f (some (newLate N hN)) +
          1 / 6 * f (some (newBoundary N hN)) := by
    calc
      _ = (∑ x : Fin (N + 1),
            if x = newLate N hN then 1 / 2 * f (some x) else 0) +
          ∑ x : Fin (N + 1),
            if x = newBoundary N hN then 1 / 6 * f (some x) else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = newLate N hN
        · subst x
          simp [hne]
        · by_cases hy : x = newBoundary N hN <;>
            simp [hx, hy, Ne.symm hne]
      _ = _ := by simp
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp only [newLaw_apply, newWeight]
  simp
  have hsum' :
      (∑ x : Fin (N + 1),
        if x = newLate N hN then 1 / 2 * f (some x)
        else if x = newBoundary N hN then 1 / 6 * f (some x) else 0) =
      1 / 2 * f (some (newLate N hN)) +
        1 / 6 * f (some (newBoundary N hN)) := by
    simpa [ite_mul] using hsum
  have hsumInv :
      (∑ x : Fin (N + 1),
        if x = newLate N hN then (2 : ℝ)⁻¹ * f (some x)
        else if x = newBoundary N hN then (6 : ℝ)⁻¹ * f (some x)
        else 0) =
      (2 : ℝ)⁻¹ * f (some (newLate N hN)) +
        (6 : ℝ)⁻¹ * f (some (newBoundary N hN)) := by
    simpa only [one_div] using hsum'
  rw [hsumInv]
  ring

private theorem expect_newLaw_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect (newLaw N c hN hc0 hc1 2) f =
      c * f (some (newOne N hN)) + (1 - c) * f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [newLaw_apply, newWeight]
  ring

private theorem expect_newLaw_three
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect (newLaw N c hN hc0 hc1 3) f = f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [newLaw_apply, newWeight]

private theorem newLate_ne_zero (N : ℕ) (hN : 3 ≤ N) :
    newLate N hN ≠ (0 : Fin (N + 1)) := by
  intro heq
  have := congrArg Fin.val heq
  simp [newLate] at this
  omega

private theorem newLate_ne_one (N : ℕ) (hN : 3 ≤ N) :
    newLate N hN ≠ newOne N hN := by
  intro heq
  have := congrArg Fin.val heq
  simp [newLate, newOne] at this
  omega

private theorem newBoundary_ne_zero (N : ℕ) (hN : 3 ≤ N) :
    newBoundary N hN ≠ (0 : Fin (N + 1)) := by
  intro heq
  have := congrArg Fin.val heq
  simp [newBoundary] at this
  omega

private theorem newBoundary_ne_one (N : ℕ) (hN : 3 ≤ N) :
    newBoundary N hN ≠ newOne N hN := by
  intro heq
  have := congrArg Fin.val heq
  simp [newBoundary, newOne] at this
  omega

theorem new_timingPayoff_zero_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    timingMixedPayoff reward (N + 1) (newLaw N c hN hc0 hc1) 0 =
      c + (1 - c) * (4 / 3) := by
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4, expect_newLaw_zero]
  simp_rw [expect_newLaw_one, expect_newLaw_two, expect_newLaw_three]
  simp_rw [new_two_one_value N hN none (some (newLate N hN)) (by
      intro heq
      exact newLate_ne_zero N hN (Option.some.inj heq)) (by
      intro heq
      exact newLate_ne_one N hN (Option.some.inj heq)),
    new_two_one_value N hN none (some (newBoundary N hN)) (by
      intro heq
      exact newBoundary_ne_zero N hN (Option.some.inj heq)) (by
      intro heq
      exact newBoundary_ne_one N hN (Option.some.inj heq)),
    new_two_one_value N hN none none (by intro heq; cases heq)
      (by intro heq; cases heq), two_player_zero_value, old_only_zero_value]
  simp
  ring

private theorem new_conditional_zero_payoff_le
    (N : ℕ) (hN : 3 ≤ N)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) :
    (1 / 2 : ℝ) *
          timingPurePayoff reward (N + 1)
            ![action, some (newLate N hN), none, none] 0 +
        1 / 6 * timingPurePayoff reward (N + 1)
          ![action, some (newBoundary N hN), none, none] 0 +
        1 / 3 * timingPurePayoff reward (N + 1)
          ![action, none, none, none] 0 ≤
      4 / 3 := by
  rw [two_player_zero_value, two_player_zero_value, old_only_zero_value]
  cases action with
  | none => norm_num
  | some time =>
      by_cases hlt : time.val < (newLate N hN).val
      · have hltBoundary : time.val < (newBoundary N hN).val := by
          simp [newLate, newBoundary] at hlt ⊢
          omega
        simp [hlt, hltBoundary]
        norm_num
      · by_cases heqLate : time = newLate N hN
        · have hltBoundary : time.val < (newBoundary N hN).val := by
            subst time
            simp [newLate, newBoundary]
            omega
          have hlateBoundary : newLate N hN < newBoundary N hN := by
            simp [newLate, newBoundary]
            omega
          simp [heqLate, hlateBoundary]
          norm_num
        · have hlateLt : (newLate N hN).val < time.val := by
            have hle : (newLate N hN).val ≤ time.val := Nat.le_of_not_gt hlt
            have hne : time.val ≠ (newLate N hN).val := by
              intro h
              apply heqLate
              apply Fin.ext
              exact h
            omega
          have heqBoundary : time = newBoundary N hN := by
            apply Fin.ext
            simp [newLate, newBoundary] at hlateLt ⊢
            omega
          subst time
          have hnotLt : ¬N < N - 1 := by omega
          have hne : N ≠ N - 1 := by omega
          simp [newLate, newBoundary, hnotLt, hne]
          norm_num

private theorem new_pure_zero_payoff_le
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) :
    timingMixedPayoff reward (N + 1)
        (Function.update (newLaw N c hN hc0 hc1) 0 (PMF.pure action)) 0 ≤
      c + (1 - c) * (4 / 3) := by
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  simp only [Function.update_self, Math.Probability.expect_pure,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  simp_rw [expect_newLaw_one, expect_newLaw_two, expect_newLaw_three]
  simp_rw [new_two_one_value N hN action (some (newLate N hN)) (by
      intro heq
      exact newLate_ne_zero N hN (Option.some.inj heq)) (by
      intro heq
      exact newLate_ne_one N hN (Option.some.inj heq)),
    new_two_one_value N hN action (some (newBoundary N hN)) (by
      intro heq
      exact newBoundary_ne_zero N hN (Option.some.inj heq)) (by
      intro heq
      exact newBoundary_ne_one N hN (Option.some.inj heq)),
    new_two_one_value N hN action none (by intro heq; cases heq)
      (by intro heq; cases heq)]
  have hbound := new_conditional_zero_payoff_le N hN action
  nlinarith

theorem new_timingPayoff_other_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0) :
    timingMixedPayoff reward (N + 1) (newLaw N c hN hc0 hc1) who = 0 := by
  apply timingMixedPayoff_eq_zero_of_zeroLaw _ _ who hwho
  apply PMF.ext
  intro candidate
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ candidate) (PMF.apply_ne_top _ candidate)).mp
  rw [newLaw_apply]
  cases candidate <;> simp [newWeight]

private theorem new_pure_other_payoff_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0)
    (action : QuittingFiniteDeadlineTimingAction (N + 1)) :
    timingMixedPayoff reward (N + 1)
        (Function.update (newLaw N c hN hc0 hc1) who (PMF.pure action)) who = 0 := by
  apply timingMixedPayoff_eq_zero_of_zeroLaw _ _ who hwho
  rw [Function.update_of_ne (Ne.symm hwho)]
  apply PMF.ext
  intro candidate
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ candidate) (PMF.apply_ne_top _ candidate)).mp
  rw [newLaw_apply]
  cases candidate <;> simp [newWeight]

/-- The adjacent law is an exact finite timing Nash equilibrium. -/
theorem newLaw_isNash
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedExtension.IsNash
      (newLaw N c hN hc0 hc1) := by
  rw [(quittingFiniteDeadlineTimingGame reward
    (N + 1)).isNash_iff_gains_nonpos]
  intro who action
  rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub]
  by_cases hwho : who = 0
  · subst who
    rw [new_timingPayoff_zero_eq]
    linarith [new_pure_zero_payoff_le N c hN hc0 hc1 action]
  · rw [new_timingPayoff_other_eq_zero N c hN hc0 hc1 who hwho,
      new_pure_other_payoff_eq_zero N c hN hc0 hc1 who hwho action]
    norm_num

private theorem reshuffled_two_one_value
    (N : ℕ) (hN : 3 ≤ N)
    (a b : QuittingFiniteDeadlineTimingAction N)
    (hb0 : b ≠ some (oldZero N hN)) (hb1 : b ≠ some (oldOne N hN)) :
    timingPurePayoff reward N ![a, b, some (oldOne N hN), none] 0 = 1 := by
  have honeZero : oldOne N hN ≠ oldZero N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldOne, oldZero] at this
  cases a with
  | none =>
      have hfirst := timingPurePayoff_eq_reward_of_first reward N
        ![none, b, some (oldOne N hN), none] (oldOne N hN)
        ⟨{2}, by decide⟩
      rw [hfirst]
      · simp [reward,
          show ({2} : Finset Player) ≠ {0, 3} by decide,
          show (1 : Player) ≠ 2 by decide]
      · intro player earlier hearlier
        have hearlierZero : earlier = oldZero N hN := by
          apply Fin.ext
          simp [oldOne, oldZero] at hearlier ⊢
          omega
        subst earlier
        fin_cases player <;> simp [hb0, honeZero]
      · intro player
        fin_cases player <;> simp [hb1]
  | some time =>
      by_cases hzero : time = oldZero N hN
      · subst time
        have hfirst := timingPurePayoff_eq_reward_of_first reward N
          ![some (oldZero N hN), b, some (oldOne N hN), none]
          (oldZero N hN) ⟨{0}, by decide⟩
        rw [hfirst]
        · simp [reward,
            show ({0} : Finset Player) ≠ {0, 3} by decide]
        · intro player earlier hearlier
          simp [oldZero] at hearlier
        · intro player
          fin_cases player <;> simp [hb0, honeZero]
      · by_cases hone : time = oldOne N hN
        · subst time
          have hfirst := timingPurePayoff_eq_reward_of_first reward N
            ![some (oldOne N hN), b, some (oldOne N hN), none]
            (oldOne N hN) ⟨{0, 2}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({0, 2} : Finset Player) ≠ {0, 3} by decide,
              show (1 : Player) ≠ 2 by decide]
          · intro player earlier hearlier
            have hearlierZero : earlier = oldZero N hN := by
              apply Fin.ext
              simp [oldOne, oldZero] at hearlier ⊢
              omega
            subst earlier
            fin_cases player <;> simp [hb0, honeZero]
          · intro player
            fin_cases player <;> simp [hb1]
        · have htime : 1 < time.val := by
            have hpositive : 0 < time.val := by
              exact Nat.pos_of_ne_zero fun heq ↦ hzero (Fin.ext heq)
            have hneOne : time.val ≠ 1 := by
              intro heq
              apply hone
              apply Fin.ext
              simpa [oldOne]
            omega
          have hfirst := timingPurePayoff_eq_reward_of_first reward N
            ![some time, b, some (oldOne N hN), none] (oldOne N hN)
            ⟨{2}, by decide⟩
          rw [hfirst]
          · simp [reward,
              show ({2} : Finset Player) ≠ {0, 3} by decide,
              show (1 : Player) ≠ 2 by decide]
          · intro player earlier hearlier
            have hearlierZero : earlier = oldZero N hN := by
              apply Fin.ext
              simp [oldOne, oldZero] at hearlier ⊢
              omega
            subst earlier
            fin_cases player <;> simp [hb0, hzero, honeZero]
          · intro player
            fin_cases player <;> simp [hb1, hone]

private theorem expect_reshuffledLaw_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction N → ℝ) :
    Math.Probability.expect (reshuffledLaw N c hN hc0 hc1 2) f =
      c * f (some (oldOne N hN)) + (1 - c) * f none := by
  rw [Math.Probability.expect_eq_sum, Fintype.sum_option]
  simp [reshuffledLaw_apply, reshuffledWeight]
  ring

private theorem old_pure_zero_payoff_eq_formula
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (oldLaw N c hN hc0 hc1) 0 (PMF.pure action)) 0 =
      c + (1 - c) *
        (1 / 2 * timingPurePayoff reward N
            ![action, some (oldLate N hN), none, none] 0 +
          1 / 2 * timingPurePayoff reward N ![action, none, none, none] 0) := by
  have hlateZero : oldLate N hN ≠ oldZero N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldLate, oldZero] at this
    omega
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  simp only [Function.update_self, Math.Probability.expect_pure,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  simp_rw [expect_oldLaw_one, expect_oldLaw_two, expect_oldLaw_three]
  simp_rw [old_two_zero_value N hN action (some (oldLate N hN)) (by
      intro heq
      exact hlateZero (Option.some.inj heq)),
    old_two_zero_value N hN action none (by intro heq; cases heq)]
  ring

private theorem reshuffled_pure_zero_payoff_eq_formula
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (reshuffledLaw N c hN hc0 hc1) 0
          (PMF.pure action)) 0 =
      c + (1 - c) *
        (1 / 2 * timingPurePayoff reward N
            ![action, some (oldLate N hN), none, none] 0 +
          1 / 2 * timingPurePayoff reward N ![action, none, none, none] 0) := by
  have hlateZero : oldLate N hN ≠ oldZero N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldLate, oldZero] at this
    omega
  have hlateOne : oldLate N hN ≠ oldOne N hN := by
    intro heq
    have := congrArg Fin.val heq
    simp [oldLate, oldOne] at this
    omega
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  simp only [Function.update_self, Math.Probability.expect_pure,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  rw [reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 1 (by decide)]
  simp_rw [expect_oldLaw_one, expect_reshuffledLaw_two]
  rw [reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 3 (by decide)]
  simp_rw [expect_oldLaw_three]
  simp_rw [reshuffled_two_one_value N hN action (some (oldLate N hN)) (by
      intro heq
      exact hlateZero (Option.some.inj heq)) (by
      intro heq
      exact hlateOne (Option.some.inj heq)),
    reshuffled_two_one_value N hN action none (by intro heq; cases heq)
      (by intro heq; cases heq)]
  ring

theorem old_reshuffled_pure_zero_payoff_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (oldLaw N c hN hc0 hc1) 0 (PMF.pure action)) 0 =
      timingMixedPayoff reward N
        (Function.update (reshuffledLaw N c hN hc0 hc1) 0
          (PMF.pure action)) 0 := by
  rw [old_pure_zero_payoff_eq_formula,
    reshuffled_pure_zero_payoff_eq_formula]

private theorem reshuffled_zeroLaw_eq_pure_none
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    reshuffledLaw N c hN hc0 hc1 0 = PMF.pure none := by
  apply PMF.ext
  intro candidate
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ candidate) (PMF.apply_ne_top _ candidate)).mp
  rw [reshuffledLaw_apply]
  cases candidate <;> simp [reshuffledWeight, oldWeight]

theorem reshuffled_timingPayoff_zero_eq_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    timingMixedPayoff reward N (reshuffledLaw N c hN hc0 hc1) 0 = 1 := by
  have hupdate : Function.update (reshuffledLaw N c hN hc0 hc1) 0
      (PMF.pure none) = reshuffledLaw N c hN hc0 hc1 := by
    funext who
    by_cases hwho : who = 0
    · subst who
      rw [Function.update_self, reshuffled_zeroLaw_eq_pure_none]
    · rw [Function.update_of_ne hwho]
  rw [← hupdate, reshuffled_pure_zero_payoff_eq_formula]
  rw [old_one_late_value, old_only_zero_value]
  norm_num

private theorem reshuffled_timingPayoff_other_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0) :
    timingMixedPayoff reward N (reshuffledLaw N c hN hc0 hc1) who = 0 := by
  exact timingMixedPayoff_eq_zero_of_zeroLaw _
    (reshuffled_zeroLaw_eq_pure_none N c hN hc0 hc1) who hwho

private theorem reshuffled_pure_other_payoff_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (who : Player) (hwho : who ≠ 0)
    (action : QuittingFiniteDeadlineTimingAction N) :
    timingMixedPayoff reward N
        (Function.update (reshuffledLaw N c hN hc0 hc1) who
          (PMF.pure action)) who = 0 := by
  apply timingMixedPayoff_eq_zero_of_zeroLaw _ _ who hwho
  rw [Function.update_of_ne (Ne.symm hwho)]
  exact reshuffled_zeroLaw_eq_pure_none N c hN hc0 hc1

/-- The old law and its censored calendar reshuffling have identical hard
payoff and pure-gain observables, hence operational distance zero. -/
theorem old_reshuffled_operationalEffectDistance_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingFiniteDeadlineOperationalEffectDistance reward 2 N
        (oldLaw N c hN hc0 hc1) (reshuffledLaw N c hN hc0 hc1) = 0 := by
  apply (finiteClockOperationalEffectDistance_eq_zero_iff (by norm_num) _ _).2
  constructor
  · intro player
    change ((oldLaw N c hN hc0 hc1 player none).toReal) =
      (reshuffledLaw N c hN hc0 hc1 player none).toReal
    rw [oldLaw_apply, reshuffledLaw_apply]
    fin_cases player <;> simp [oldWeight, reshuffledWeight]
  constructor
  · intro player
    change (quittingFiniteDeadlineTimingGame reward N).mixedExtension.eu
      (oldLaw N c hN hc0 hc1) player =
        (quittingFiniteDeadlineTimingGame reward N).mixedExtension.eu
          (reshuffledLaw N c hN hc0 hc1) player
    rw [finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff,
      finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff]
    by_cases hplayer : player = 0
    · subst player
      rw [old_timingPayoff_zero_eq_one,
        reshuffled_timingPayoff_zero_eq_one]
    · rw [old_timingPayoff_other_eq_zero N c hN hc0 hc1 player hplayer,
        reshuffled_timingPayoff_other_eq_zero N c hN hc0 hc1 player hplayer]
  · intro player action
    change (quittingFiniteDeadlineTimingGame reward N).mixedGain
      (oldLaw N c hN hc0 hc1) player action =
        (quittingFiniteDeadlineTimingGame reward N).mixedGain
          (reshuffledLaw N c hN hc0 hc1) player action
    rw [finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub,
      finiteDeadlineTimingGame_mixedGain_eq_timingMixedPayoff_sub]
    by_cases hplayer : player = 0
    · subst player
      rw [old_reshuffled_pure_zero_payoff_eq,
        old_timingPayoff_zero_eq_one, reshuffled_timingPayoff_zero_eq_one]
    · rw [old_pure_other_payoff_eq_zero N c hN hc0 hc1 player hplayer,
        reshuffled_pure_other_payoff_eq_zero N c hN hc0 hc1 player hplayer,
        old_timingPayoff_other_eq_zero N c hN hc0 hc1 player hplayer,
        reshuffled_timingPayoff_other_eq_zero N c hN hc0 hc1 player hplayer]

theorem old_censored_new_operationalEffectDistance_eq_zero
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingFiniteDeadlineOperationalEffectDistance reward 2 N
        (oldLaw N c hN hc0 hc1)
        (quittingFiniteDeadlineTimingProfileCensor
          (newLaw N c hN hc0 hc1)) = 0 := by
  rw [censor_newLaw_eq_reshuffledLaw]
  exact old_reshuffled_operationalEffectDistance_eq_zero N c hN hc0 hc1

/-- Every common retained behavioral tail gives exactly the same full
terminal semantic pair at the two censored endpoints. -/
theorem retainedTailSemantic_old_eq_censoredNew
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward N
          (oldLaw N c hN hc0 hc1) tail) =
      quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward N
          (quittingFiniteDeadlineTimingProfileCensor
            (newLaw N c hN hc0 hc1)) tail) := by
  apply quittingFiniteDeadlineOperationalEffectDistance_zero_retainedTailSemantic_eq
    reward (bound := 2) (by norm_num)
  exact old_censored_new_operationalEffectDistance_eq_zero N c hN hc0 hc1

/-! ## Canonical terminal coalition law -/

/-- A reward table whose every coordinate records one selected terminal
coalition. -/
def terminalCoalitionIndicatorReward
    (selected : {S : Finset Player // S.Nonempty}) :
    {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal _ ↦ if terminal = selected then 1 else 0

private theorem terminalOutcomeMass_some_eq_indicatorPayoff
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset Player // S.Nonempty}) :
    quittingTerminalOutcomeMass reward profile (some terminal) =
      quittingTerminalPayoff
        (terminalCoalitionIndicatorReward terminal) profile 0 := by
  change quittingAbsorbedMassLimit reward profile terminal =
    ∑ other, quittingAbsorbedMassLimit
      (terminalCoalitionIndicatorReward terminal) profile other *
        terminalCoalitionIndicatorReward terminal other 0
  rw [Finset.sum_eq_single terminal]
  · simp only [terminalCoalitionIndicatorReward, if_pos, mul_one]
    exact QuittingLCPClassification.quittingAbsorbedMassLimit_congr_reward
      reward (terminalCoalitionIndicatorReward terminal) profile terminal
  · intro other _ hother
    simp [terminalCoalitionIndicatorReward, hother]
  · simp

private theorem indicator_two_first_value
    (N : ℕ) (hN : 3 ≤ N)
    (selected : {S : Finset Player // S.Nonempty})
    (stop : Fin N) (hstop : stop.val < (oldLate N hN).val)
    (clock : QuittingFiniteDeadlineTimingAction N)
    (hclock : clock = some (oldLate N hN) ∨ clock = none) :
    timingPurePayoff (terminalCoalitionIndicatorReward selected) N
        ![none, clock, some stop, none] 0 =
      if (⟨{2}, by simp⟩ : {S : Finset Player // S.Nonempty}) = selected
        then 1 else 0 := by
  have hfirst := timingPurePayoff_eq_reward_of_first
    (terminalCoalitionIndicatorReward selected) N
      ![none, clock, some stop, none] stop ⟨{2}, by simp⟩
  rw [hfirst]
  · simp [terminalCoalitionIndicatorReward]
  · intro player earlier hearlier
    rcases hclock with rfl | rfl
    · fin_cases player
      · simp
      · intro heq
        have hval := congrArg (fun action ↦ Option.map Fin.val action) heq
        simp at hval
        omega
      · intro heq
        have hval := congrArg (fun action ↦ Option.map Fin.val action) heq
        simp at hval
        omega
      · simp
    · fin_cases player
      · simp
      · simp
      · intro heq
        have hval := congrArg (fun action ↦ Option.map Fin.val action) heq
        simp at hval
        omega
      · simp
  · intro player
    rcases hclock with rfl | rfl
    · fin_cases player <;> simp
      intro heq
      have hval := congrArg Fin.val heq
      omega
    · fin_cases player <;> simp

private theorem indicator_one_first_value
    (N : ℕ) (hN : 3 ≤ N)
    (selected : {S : Finset Player // S.Nonempty}) :
    timingPurePayoff (terminalCoalitionIndicatorReward selected) N
        ![none, some (oldLate N hN), none, none] 0 =
      if (⟨{1}, by simp⟩ : {S : Finset Player // S.Nonempty}) = selected
        then 1 else 0 := by
  have hfirst := timingPurePayoff_eq_reward_of_first
    (terminalCoalitionIndicatorReward selected) N
      ![none, some (oldLate N hN), none, none]
        (oldLate N hN) ⟨{1}, by simp⟩
  rw [hfirst]
  · simp [terminalCoalitionIndicatorReward]
  · intro player earlier hearlier
    fin_cases player
    · simp
    · intro heq
      have hval := congrArg Fin.val (Option.some.inj heq)
      omega
    · simp
    · simp
  · intro player
    fin_cases player <;> simp

private theorem indicatorTimingPayoff_old_eq_reshuffled
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (selected : {S : Finset Player // S.Nonempty}) :
    timingMixedPayoff (terminalCoalitionIndicatorReward selected) N
        (oldLaw N c hN hc0 hc1) 0 =
      timingMixedPayoff (terminalCoalitionIndicatorReward selected) N
        (reshuffledLaw N c hN hc0 hc1) 0 := by
  have hzero : reshuffledLaw N c hN hc0 hc1 0 =
      oldLaw N c hN hc0 hc1 0 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 0 (by decide)
  have hone : reshuffledLaw N c hN hc0 hc1 1 =
      oldLaw N c hN hc0 hc1 1 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 1 (by decide)
  have hthree : reshuffledLaw N c hN hc0 hc1 3 =
      oldLaw N c hN hc0 hc1 3 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 3 (by decide)
  have hzeroLate : (oldZero N hN).val < (oldLate N hN).val := by
    simp [oldZero, oldLate]
    omega
  have honeLate : (oldOne N hN).val < (oldLate N hN).val := by
    simp [oldOne, oldLate]
    omega
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4, hzero, hone, hthree]
  rw [expect_oldLaw_zero, expect_oldLaw_zero]
  rw [expect_oldLaw_one, expect_oldLaw_one]
  simp_rw [expect_oldLaw_two, expect_reshuffledLaw_two]
  simp_rw [expect_oldLaw_three]
  rw [indicator_two_first_value N hN selected (oldZero N hN) hzeroLate
      (some (oldLate N hN)) (Or.inl rfl),
    indicator_two_first_value N hN selected (oldZero N hN) hzeroLate
      none (Or.inr rfl),
    indicator_two_first_value N hN selected (oldOne N hN) honeLate
      (some (oldLate N hN)) (Or.inl rfl),
    indicator_two_first_value N hN selected (oldOne N hN) honeLate
      none (Or.inr rfl),
    indicator_one_first_value N hN selected]

/-- The calendar reshuffling preserves the canonical terminal outcome mass,
including `Never` and every nonempty quitting coalition. -/
theorem quittingTerminalOutcomeMass_old_eq_reshuffled
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (oldLaw N c hN hc0 hc1)) =
      quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (reshuffledLaw N c hN hc0 hc1)) := by
  let oldProfile := quittingFiniteDeadlineTimingProfile reward N
    (oldLaw N c hN hc0 hc1)
  let reshuffledProfile := quittingFiniteDeadlineTimingProfile reward N
    (reshuffledLaw N c hN hc0 hc1)
  have hsome : ∀ terminal,
      quittingTerminalOutcomeMass reward oldProfile (some terminal) =
        quittingTerminalOutcomeMass reward reshuffledProfile (some terminal) := by
    intro terminal
    rw [terminalOutcomeMass_some_eq_indicatorPayoff,
      terminalOutcomeMass_some_eq_indicatorPayoff]
    change quittingTerminalPayoff (terminalCoalitionIndicatorReward terminal)
        (quittingFiniteDeadlineTimingProfile
          (terminalCoalitionIndicatorReward terminal) N
            (oldLaw N c hN hc0 hc1)) 0 =
      quittingTerminalPayoff (terminalCoalitionIndicatorReward terminal)
        (quittingFiniteDeadlineTimingProfile
          (terminalCoalitionIndicatorReward terminal) N
            (reshuffledLaw N c hN hc0 hc1)) 0
    rw [quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
      quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU,
      finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff,
      finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff]
    exact indicatorTimingPayoff_old_eq_reshuffled N c hN hc0 hc1 terminal
  funext outcome
  cases outcome with
  | some terminal => exact hsome terminal
  | none =>
      have hold := (quittingTerminalOutcomeMass_mem_stdSimplex
        reward oldProfile).2
      have hreshuffled := (quittingTerminalOutcomeMass_mem_stdSimplex
        reward reshuffledProfile).2
      rw [Fintype.sum_option] at hold hreshuffled
      have hfinite :
          (∑ terminal, quittingTerminalOutcomeMass reward oldProfile
            (some terminal)) =
            ∑ terminal, quittingTerminalOutcomeMass reward reshuffledProfile
              (some terminal) := by
        exact Finset.sum_congr rfl fun terminal _ ↦ hsome terminal
      linarith

/-- The old law and the censoring of the adjacent law preserve the canonical
terminal outcome mass exactly. -/
theorem quittingTerminalOutcomeMass_old_eq_censoredNew
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (oldLaw N c hN hc0 hc1)) =
      quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (quittingFiniteDeadlineTimingProfileCensor
            (newLaw N c hN hc0 hc1))) := by
  rw [censor_newLaw_eq_reshuffledLaw]
  exact quittingTerminalOutcomeMass_old_eq_reshuffled N c hN hc0 hc1

/-! ## Concrete hard terminal coalition law -/

/-- The hard terminal outcome in this chamber.  Players `0,3` use `Never`,
player `2`'s possible finite date precedes player `1`'s, so the first
coalition is `{2}`, then `{1}`, or `Never`. -/
def hardTerminalCoalitionOutcome {deadline : ℕ}
    (choices : Player → QuittingFiniteDeadlineTimingAction deadline) :
    QuittingTerminalOutcome Player :=
  if (choices 2).isSome then
    some ⟨{2}, by simp⟩
  else if (choices 1).isSome then
    some ⟨{1}, by simp⟩
  else none

/-- Concrete terminal coalition law of one product timing profile in this
chamber, written as its finite probability mass function. -/
def hardTerminalCoalitionMass {deadline : ℕ}
    (mixed : Player → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (outcome : QuittingTerminalOutcome Player) : ℝ :=
  Math.Probability.expect (pmfPi mixed) fun choices ↦
    if hardTerminalCoalitionOutcome choices = outcome then 1 else 0

/-- Moving player `2`'s stopping mass from date zero to date one leaves the
complete hard terminal coalition law unchanged. -/
theorem hardTerminalCoalitionMass_old_eq_reshuffled
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    hardTerminalCoalitionMass (oldLaw N c hN hc0 hc1) =
      hardTerminalCoalitionMass (reshuffledLaw N c hN hc0 hc1) := by
  have hzero : reshuffledLaw N c hN hc0 hc1 0 =
      oldLaw N c hN hc0 hc1 0 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 0 (by decide)
  have hone : reshuffledLaw N c hN hc0 hc1 1 =
      oldLaw N c hN hc0 hc1 1 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 1 (by decide)
  have hthree : reshuffledLaw N c hN hc0 hc1 3 =
      oldLaw N c hN hc0 hc1 3 :=
    reshuffledLaw_eq_oldLaw_of_ne_two N c hN hc0 hc1 3 (by decide)
  funext outcome
  unfold hardTerminalCoalitionMass
  rw [expect_pmfPi_fin4, expect_pmfPi_fin4, hzero, hone, hthree]
  rw [expect_oldLaw_zero, expect_oldLaw_zero]
  rw [expect_oldLaw_one, expect_oldLaw_one]
  simp_rw [expect_oldLaw_two, expect_reshuffledLaw_two]
  simp_rw [expect_oldLaw_three]
  simp [hardTerminalCoalitionOutcome]

/-- The original law and the censoring of the adjacent law have exactly the
same concrete hard terminal coalition law. -/
theorem hardTerminalCoalitionMass_old_eq_censoredNew
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    hardTerminalCoalitionMass (oldLaw N c hN hc0 hc1) =
      hardTerminalCoalitionMass
        (quittingFiniteDeadlineTimingProfileCensor
          (newLaw N c hN hc0 hc1)) := by
  rw [censor_newLaw_eq_reshuffledLaw]
  exact hardTerminalCoalitionMass_old_eq_reshuffled N c hN hc0 hc1

private theorem expect_includedOldLaw_one
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 1) f =
      1 / 2 * f (some (newLate N hN)) + 1 / 2 * f none := by
  unfold quittingFiniteDeadlineTimingProfileInclude
  rw [Math.Probability.expect_map, expect_oldLaw_one]
  rfl

private theorem expect_includedOldLaw_two
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 2) f =
      c * f (some 0) + (1 - c) * f none := by
  unfold quittingFiniteDeadlineTimingProfileInclude
  rw [Math.Probability.expect_map, expect_oldLaw_two]
  rfl

private theorem expect_includedOldLaw_three
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (f : QuittingFiniteDeadlineTimingAction (N + 1) → ℝ) :
    Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 3) f = f none := by
  unfold quittingFiniteDeadlineTimingProfileInclude
  rw [Math.Probability.expect_map, expect_oldLaw_three]
  rfl

/-- The newly exposed date `N` against the old law pays exactly
`3/2-c/2`. -/
theorem old_boundaryPayoff_zero_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedExtension.eu
        (Function.update
          (quittingFiniteDeadlineTimingProfileInclude
            (oldLaw N c hN hc0 hc1)) 0
          (PMF.pure (some (newBoundary N hN)))) 0 =
      3 / 2 - c / 2 := by
  rw [finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff]
  unfold timingMixedPayoff
  rw [expect_pmfPi_fin4]
  simp only [Function.update_self,
    Function.update_of_ne (by decide : (1 : Player) ≠ 0),
    Function.update_of_ne (by decide : (2 : Player) ≠ 0),
    Function.update_of_ne (by decide : (3 : Player) ≠ 0)]
  change Math.Probability.expect
      (PMF.pure (some (newBoundary N hN)) :
        PMF (QuittingFiniteDeadlineTimingAction (N + 1))) (fun a ↦
      Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 1) (fun b ↦
      Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 2) (fun cAction ↦
      Math.Probability.expect
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1) 3) (fun d ↦
      timingPurePayoff reward (N + 1) ![a, b, cAction, d] 0)))) =
    3 / 2 - c / 2
  rw [Math.Probability.expect_pure]
  simp_rw [expect_includedOldLaw_one, expect_includedOldLaw_two,
    expect_includedOldLaw_three]
  have hNsucc : 3 ≤ N + 1 := by omega
  have hlateZero : newLate N hN ≠ oldZero (N + 1) hNsucc := by
    intro heq
    have := congrArg Fin.val heq
    simp [newLate, oldZero] at this
    omega
  rw [show (0 : Fin (N + 1)) = oldZero (N + 1) hNsucc by rfl]
  simp_rw [old_two_zero_value (N + 1) hNsucc (some (newBoundary N hN))
      (some (newLate N hN)) (by
        intro heq
        exact hlateZero (Option.some.inj heq)),
    old_two_zero_value (N + 1) hNsucc (some (newBoundary N hN)) none
      (by intro heq; cases heq),
    two_player_zero_value, old_only_zero_value]
  have hnotLt : ¬N < N - 1 := by omega
  have hne : N ≠ N - 1 := by omega
  simp [newLate, newBoundary, hnotLt, hne]
  ring

/-- The old law's pure boundary gain is exactly `(1-c)/2`. -/
theorem old_boundaryGain_zero_eq
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0 hc1)) 0 (some (newBoundary N hN)) =
      (1 - c) / 2 := by
  unfold KernelGame.mixedGain
  rw [old_boundaryPayoff_zero_eq,
    quittingFiniteDeadlineTiming_mixedEU_include_eq,
    finiteDeadlineTimingGame_mixedEU_eq_timingMixedPayoff,
    old_timingPayoff_zero_eq_one]
  ring

/-- Under the packet's strict upper bound on `c`, the displayed boundary
gain is strictly positive. -/
theorem old_boundaryGain_zero_pos
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N)
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 < (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedGain
      (quittingFiniteDeadlineTimingProfileInclude
        (oldLaw N c hN hc0 hc1.le)) 0 (some (newBoundary N hN)) := by
  rw [old_boundaryGain_zero_eq]
  linarith

/-- Pure stationary root of the concrete singleton-separated tail. -/
def separatedTailRoot : Player → PMF Bool :=
  ![PMF.pure true, PMF.pure false, PMF.pure false, PMF.pure true]

/-- Displayed payoff of the concrete tail. -/
def separatedTailValue : Payoff Player := ![(2 : ℝ), 1, 1, 1]

/-- Players `0,3` quit surely at the tail's first date. -/
def separatedTailProfile : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward separatedTailRoot

private theorem separatedTail_quitters :
    quittingQuitters ![true, false, false, true] = ({0, 3} : Finset Player) := by
  decide

private theorem separatedTail_quitters_one_ne :
    quittingQuitters ![true, true, false, true] ≠ ({0, 3} : Finset Player) := by
  decide

private theorem separatedTail_quitters_two_ne :
    quittingQuitters ![true, false, true, true] ≠ ({0, 3} : Finset Player) := by
  decide

private theorem separatedTail_quitters_zero_continue :
    quittingQuitters ![false, false, false, true] = ({3} : Finset Player) := by
  decide

private theorem separatedTail_zero_continue_set_ne :
    ({3} : Finset Player) ≠ ({0, 3} : Finset Player) := by
  decide

private theorem separatedTail_quitters_three_continue_ne :
    quittingQuitters ![true, false, false, false] ≠ ({0, 3} : Finset Player) := by
  decide

private theorem separatedTail_exists_quitter :
    ∃ who : Player, ![true, false, false, true] who = true := by
  exact ⟨0, rfl⟩

private theorem separatedTail_one_deviation_exists_quitter :
    ∃ who : Player, ![true, true, false, true] who = true := by
  exact ⟨0, rfl⟩

private theorem separatedTail_two_deviation_exists_quitter :
    ∃ who : Player, ![true, false, true, true] who = true := by
  exact ⟨0, rfl⟩

private theorem separatedTail_zero_continue_exists_quitter :
    ∃ who : Player, ![false, false, false, true] who = true := by
  exact ⟨3, rfl⟩

private theorem separatedTail_three_continue_exists_quitter :
    ∃ who : Player, ![true, false, false, false] who = true := by
  exact ⟨0, rfl⟩

theorem separatedTail_terminalPayoff_eq :
    quittingTerminalPayoff reward separatedTailProfile = separatedTailValue := by
  funext who
  unfold separatedTailProfile
  rw [quittingTerminalPayoff_stationary_eq_rootExpectedPayoff]
  unfold separatedTailRoot separatedTailValue
    quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [quittingRootPayoff, reward, separatedTail_quitters,
      separatedTail_exists_quitter]

theorem separatedTail_singletonGap_eq_one (who : Player) :
    quittingTerminalPayoff reward separatedTailProfile who -
        reward (quittingSingletonTerminal who) who = 1 := by
  rw [separatedTail_terminalPayoff_eq]
  fin_cases who
  all_goals simp [separatedTailValue]
  all_goals norm_num

private theorem separatedTail_fixedPoint :
    separatedTailValue =
      quittingRootSuccessorPayoff reward separatedTailValue separatedTailRoot := by
  funext who
  unfold quittingRootSuccessorPayoff separatedTailRoot separatedTailValue
    quittingRootExpectedPayoff
  rw [expect_pmfPi_fin4]
  fin_cases who <;>
    simp [quittingRootPayoff, reward,
      separatedTail_quitters]

private theorem separatedTail_endpointNash :
    IsεQuittingRootEndpointNash reward separatedTailValue 0 separatedTailRoot := by
  rw [isεQuittingRootEndpointNash_iff_purePayoff_le]
  intro who
  constructor
  · unfold quittingRootQuitPayoff quittingRootSuccessorPayoff
      quittingRootExpectedPayoff separatedTailRoot separatedTailValue
    rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
    fin_cases who <;>
      simp [quittingRootPayoff, reward,
        separatedTail_quitters, separatedTail_quitters_one_ne,
        separatedTail_quitters_two_ne,
        separatedTail_one_deviation_exists_quitter,
        separatedTail_two_deviation_exists_quitter]
  · unfold quittingRootContinuePayoff quittingRootSuccessorPayoff
      quittingRootExpectedPayoff separatedTailRoot separatedTailValue
    rw [expect_pmfPi_fin4, expect_pmfPi_fin4]
    fin_cases who <;>
      simp [quittingRootPayoff, reward,
        separatedTail_quitters,
        separatedTail_quitters_three_continue_ne,
        separatedTail_quitters_zero_continue,
        separatedTail_zero_continue_set_ne,
        separatedTail_zero_continue_exists_quitter,
        separatedTail_three_continue_exists_quitter]

private theorem separatedTail_absorbs :
    quittingStationaryContinueMass separatedTailRoot < 1 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [separatedTailRoot, Fin.prod_univ_succ]

private theorem separatedTail_contracts (who : Player) :
    quittingStationaryFixedOpponentsContinueMass separatedTailRoot who < 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass
    quittingFixedOpponentsContinueMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  fin_cases who <;>
    simp [separatedTailRoot, Fin.prod_univ_succ, Function.update]

/-- The displayed tail is an exact unrestricted behavioral terminal Nash
profile. -/
theorem separatedTail_isZeroAsymptoticNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 separatedTailProfile := by
  exact isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    reward separatedTailRoot separatedTailValue separatedTail_absorbs
      separatedTail_fixedPoint separatedTail_endpointNash separatedTail_contracts

/-- The concrete exact tail forces the global terminal-debt infimum to
zero. -/
theorem terminalDebtSumInf_eq_zero :
    quittingTerminalDebtSumInf reward = 0 :=
  quittingTerminalDebtSumInf_eq_zero_of_isZeroAsymptoticNash
    separatedTailProfile separatedTail_isZeroAsymptoticNash

/-- Compact literal surface of the complete censored-clock null-direction
regression.  It records no source provenance or uniform-equilibrium claim. -/
structure RegressionCertificate
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N) (hc0 : 0 < c) (hc1 : c < 1) : Prop where
  oldNash :
    (quittingFiniteDeadlineTimingGame reward N).mixedExtension.IsNash
      (oldLaw N c hN hc0.le hc1.le)
  newNash :
    (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedExtension.IsNash
      (newLaw N c hN hc0.le hc1.le)
  boundaryParticipation :
    quittingFiniteDeadlineBoundaryParticipation N
      (newLaw N c hN hc0.le hc1.le) 1 = 1 / 6
  boundaryGain :
    (quittingFiniteDeadlineTimingGame reward (N + 1)).mixedGain
        (quittingFiniteDeadlineTimingProfileInclude
          (oldLaw N c hN hc0.le hc1.le)) 0
        (some (newBoundary N hN)) =
      (1 - c) / 2
  censoredError :
    (∑ who, quittingFiniteDeadlineCensoredError N
      (oldLaw N c hN hc0.le hc1.le)
      (newLaw N c hN hc0.le hc1.le) who) = c
  normalizedRatio :
    (∑ who, quittingFiniteDeadlineCensoredError N
        (oldLaw N c hN hc0.le hc1.le)
        (newLaw N c hN hc0.le hc1.le) who) /
        ((1 - c) / 4) =
      4 * c / (1 - c)
  canonicalTerminalLaw :
    quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (oldLaw N c hN hc0.le hc1.le)) =
      quittingTerminalOutcomeMass reward
        (quittingFiniteDeadlineTimingProfile reward N
          (quittingFiniteDeadlineTimingProfileCensor
            (newLaw N c hN hc0.le hc1.le)))
  operationalNull :
    quittingFiniteDeadlineOperationalEffectDistance reward 2 N
        (oldLaw N c hN hc0.le hc1.le)
        (quittingFiniteDeadlineTimingProfileCensor
          (newLaw N c hN hc0.le hc1.le)) = 0
  graftSemanticNull : ∀ tail : (quittingGame reward).BehaviorProfile,
    quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward N
          (oldLaw N c hN hc0.le hc1.le) tail) =
      quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward N
          (quittingFiniteDeadlineTimingProfileCensor
            (newLaw N c hN hc0.le hc1.le)) tail)
  separatedTailNash :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 separatedTailProfile
  debtInfZero : quittingTerminalDebtSumInf reward = 0

/-- The displayed old/new laws, their canonical coalition law, every common
graft, and the exact separated tail jointly realize the regression. -/
theorem regressionCertificate
    (N : ℕ) (c : ℝ) (hN : 3 ≤ N) (hc0 : 0 < c) (hc1 : c < 1) :
    RegressionCertificate N c hN hc0 hc1 where
  oldNash := oldLaw_isNash N c hN hc0.le hc1.le
  newNash := newLaw_isNash N c hN hc0.le hc1.le
  boundaryParticipation :=
    new_boundaryParticipation_one_eq N c hN hc0.le hc1.le
  boundaryGain := old_boundaryGain_zero_eq N c hN hc0.le hc1.le
  censoredError := sum_censoredError_eq_c N c hN hc0.le hc1.le
  normalizedRatio := censoredError_div_boundaryScale_eq N c hN hc0 hc1
  canonicalTerminalLaw :=
    quittingTerminalOutcomeMass_old_eq_censoredNew N c hN hc0.le hc1.le
  operationalNull :=
    old_censored_new_operationalEffectDistance_eq_zero
      N c hN hc0.le hc1.le
  graftSemanticNull := fun tail ↦
    retainedTailSemantic_old_eq_censoredNew N c hN hc0.le hc1.le tail
  separatedTailNash := separatedTail_isZeroAsymptoticNash
  debtInfZero := terminalDebtSumInf_eq_zero

end FinFourCensoredClockNullDirection
end GameTheory
