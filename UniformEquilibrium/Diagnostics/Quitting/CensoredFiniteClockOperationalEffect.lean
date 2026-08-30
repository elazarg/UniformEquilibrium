/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineAdjacentTotalVariation
import UniformEquilibrium.Diagnostics.Quitting.RetainedTailFiniteTimingRealization

/-!
# Operational quotients for censored finite clocks

This file separates two different pieces of adjacent-deadline data.  The
boundary mass is the mass placed on the newly exposed date.  Censoring moves
that mass back to `Never`; the remaining discrepancy is an old-clock
reshuffle.  The raw total variation of that reshuffle is deliberately not a
strategic progress measure.

The operational effect gauge below instead records the finite family of
observables which controls every literal graft: each player's pass
coefficient, every hard prescribed payoff, and every hard pure-action gain.
Its zero classes are the graft-universal null directions.  No minimum-tail
source, chronological edge, return, or uniform-equilibrium consumer is
asserted here.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Literal censoring -/

/-- Censor the new boundary date of a successor timing action back to
`Never`.  Every older date is retained literally. -/
def quittingFiniteDeadlineTimingActionCensor {deadline : ℕ} :
    QuittingFiniteDeadlineTimingAction (deadline + 1) →
      QuittingFiniteDeadlineTimingAction deadline
  | none => none
  | some time =>
      if htime : time.val < deadline then some ⟨time.val, htime⟩ else none

/-- Censor the newly exposed date in every marginal of a successor timing
law. -/
def quittingFiniteDeadlineTimingProfileCensor {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    ι → PMF (QuittingFiniteDeadlineTimingAction deadline) :=
  fun player => (mixed player).map quittingFiniteDeadlineTimingActionCensor

/-- Real mass carried by the newly exposed boundary date. -/
def quittingFiniteDeadlineBoundaryParticipation (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (player : ι) : ℝ :=
  (mixed player (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal

/-- Old-clock total variation left after the new boundary mass is censored
to `Never`. -/
def quittingFiniteDeadlineCensoredError (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (player : ι) : ℝ :=
  Math.Probability.pmfTV (old player)
    (quittingFiniteDeadlineTimingProfileCensor new player)

/-- The exact `e+b` budget used by the adjacent finite-versus-Never split.
It keeps censored reshuffling and genuine boundary participation as separate
coordinates. -/
def quittingFiniteDeadlineCensorBudget (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) : ℝ :=
  ∑ player,
    (quittingFiniteDeadlineCensoredError deadline old new player +
      quittingFiniteDeadlineBoundaryParticipation deadline new player)

@[simp]
theorem quittingFiniteDeadlineTimingActionCensor_include
    {deadline : ℕ}
    (action : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteDeadlineTimingActionCensor
        (quittingFiniteDeadlineTimingActionInclude action) = action := by
  cases action with
  | none => rfl
  | some time =>
      simp [quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingActionInclude, time.isLt]

/-- Censoring is a literal retraction of the old finite clock from the
successor clock. -/
theorem quittingFiniteDeadlineTimingActionCensor_leftInverse
    {deadline : ℕ} :
    Function.LeftInverse
      (quittingFiniteDeadlineTimingActionCensor (deadline := deadline))
      quittingFiniteDeadlineTimingActionInclude :=
  quittingFiniteDeadlineTimingActionCensor_include

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem quittingFiniteDeadlineTimingProfileCensor_include
    {deadline : ℕ}
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteDeadlineTimingProfileCensor
        (quittingFiniteDeadlineTimingProfileInclude mixed) = mixed := by
  funext player
  rw [quittingFiniteDeadlineTimingProfileCensor,
    quittingFiniteDeadlineTimingProfileInclude, PMF.map_comp]
  have hcomp :
      (quittingFiniteDeadlineTimingActionCensor (deadline := deadline)) ∘
          (quittingFiniteDeadlineTimingActionInclude (deadline := deadline)) =
        id := by
    funext action
    exact quittingFiniteDeadlineTimingActionCensor_include action
  rw [hcomp, PMF.map_id]

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinatewise censoring is a literal retraction of old-clock product
laws. -/
theorem quittingFiniteDeadlineTimingProfileCensor_leftInverse
    {deadline : ℕ} :
    Function.LeftInverse
      (quittingFiniteDeadlineTimingProfileCensor
        (ι := ι) (deadline := deadline))
      quittingFiniteDeadlineTimingProfileInclude :=
  quittingFiniteDeadlineTimingProfileCensor_include

omit [Fintype ι] [DecidableEq ι] in
/-- Censoring is nonexpansive for total variation. -/
theorem pmfTV_quittingFiniteDeadlineTimingActionCensor_le
    {deadline : ℕ}
    (first second :
      PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    Math.Probability.pmfTV
        (first.map quittingFiniteDeadlineTimingActionCensor)
        (second.map quittingFiniteDeadlineTimingActionCensor) ≤
      Math.Probability.pmfTV first second :=
  Math.Probability.pmfTV_map_le
    quittingFiniteDeadlineTimingActionCensor first second

omit [DecidableEq ι] in
/-- Coordinatewise censoring is nonexpansive for summed marginal total
variation. -/
theorem sum_pmfTV_quittingFiniteDeadlineTimingProfileCensor_le
    {deadline : ℕ}
    (first second :
      ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    (∑ player, Math.Probability.pmfTV
        (quittingFiniteDeadlineTimingProfileCensor first player)
        (quittingFiniteDeadlineTimingProfileCensor second player)) ≤
      ∑ player, Math.Probability.pmfTV (first player) (second player) := by
  apply Finset.sum_le_sum
  intro player _
  exact pmfTV_quittingFiniteDeadlineTimingActionCensor_le
    (first player) (second player)

private theorem pmfTV_le_couplingMismatch
    {α : Type} [Fintype α] [DecidableEq α]
    (first second : PMF α) (coupling : PMF (α × α))
    (hfirst : coupling.map Prod.fst = first)
    (hsecond : coupling.map Prod.snd = second) :
    Math.Probability.pmfTV first second ≤
      Math.Probability.expect coupling fun pair =>
        if pair.1 ≠ pair.2 then 1 else 0 := by
  let witness : α → ℝ :=
    Math.Probability.pmfPositiveVariationWitness first second 1
  calc
    Math.Probability.pmfTV first second =
        Math.Probability.expect first witness -
          Math.Probability.expect second witness := by
      symm
      simpa [witness] using
        Math.Probability.expect_sub_pmfPositiveVariationWitness first second 1
    _ = Math.Probability.expect coupling fun pair =>
          witness pair.1 - witness pair.2 := by
      rw [← hfirst, ← hsecond, Math.Probability.expect_map,
        Math.Probability.expect_map, Math.Probability.expect_sub]
    _ ≤ Math.Probability.expect coupling fun pair =>
          if pair.1 ≠ pair.2 then 1 else 0 := by
      apply Math.Probability.expect_mono
      intro pair
      by_cases heq : pair.1 = pair.2
      · simp [heq]
      · rw [if_pos heq]
        have hleft := Math.Probability.pmfPositiveVariationWitness_le
          first second zero_le_one pair.1
        have hright := Math.Probability.pmfPositiveVariationWitness_nonneg
          first second zero_le_one pair.2
        linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Censoring and then lifting a successor marginal changes it by at most the
literal mass of the erased boundary atom. -/
theorem pmfTV_quittingFiniteDeadline_include_censor_le_boundary
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    Math.Probability.pmfTV
        ((law.map quittingFiniteDeadlineTimingActionCensor).map
          quittingFiniteDeadlineTimingActionInclude)
        law ≤
      (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
  classical
  let project : QuittingFiniteDeadlineTimingAction (deadline + 1) →
      QuittingFiniteDeadlineTimingAction (deadline + 1) := fun action =>
    quittingFiniteDeadlineTimingActionInclude
      (quittingFiniteDeadlineTimingActionCensor action)
  let coupling : PMF
      (QuittingFiniteDeadlineTimingAction (deadline + 1) ×
        QuittingFiniteDeadlineTimingAction (deadline + 1)) :=
    law.map fun action => (project action, action)
  have hfirst : coupling.map Prod.fst = law.map project := by
    change (law.map fun action => (project action, action)).map Prod.fst = _
    rw [PMF.map_comp]
    rfl
  have hsecond : coupling.map Prod.snd = law := by
    change (law.map fun action => (project action, action)).map Prod.snd = _
    rw [PMF.map_comp]
    have hcomp : Prod.snd ∘ (fun action => (project action, action)) = id := by
      funext action
      rfl
    rw [hcomp, PMF.map_id]
  have hproject : law.map project =
      (law.map quittingFiniteDeadlineTimingActionCensor).map
        quittingFiniteDeadlineTimingActionInclude := by
    rw [PMF.map_comp]
    rfl
  have hmismatch :
      Math.Probability.expect coupling (fun pair =>
          if pair.1 ≠ pair.2 then 1 else 0) =
        (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
    change Math.Probability.expect
        (law.map fun action => (project action, action)) _ = _
    rw [Math.Probability.expect_map,
      Math.Probability.apply_toReal_eq_expect_indicator]
    congr 1
    funext action
    cases action with
    | none => simp [project, quittingFiniteDeadlineTimingActionCensor,
        quittingFiniteDeadlineTimingActionInclude,
        quittingFiniteDeadlineTimingBoundaryAction]
    | some time =>
        refine Fin.lastCases ?_ (fun oldTime => ?_) time
        · have hlast : (Fin.last deadline : Fin (deadline + 1)) =
              ⟨deadline, Nat.lt_add_one deadline⟩ := Fin.ext rfl
          simp [project, quittingFiniteDeadlineTimingActionCensor,
            quittingFiniteDeadlineTimingActionInclude,
            quittingFiniteDeadlineTimingBoundaryAction, hlast]
        · have hne : oldTime.castSucc ≠ Fin.last deadline := by
            intro heq
            have hval := congrArg Fin.val heq
            simp only [Fin.val_castSucc, Fin.val_last] at hval
            exact (Nat.ne_of_lt oldTime.isLt) hval
          have hboundary : (⟨deadline, Nat.lt_add_one deadline⟩ :
              Fin (deadline + 1)) = Fin.last deadline := Fin.ext rfl
          simp [project, quittingFiniteDeadlineTimingActionCensor,
            quittingFiniteDeadlineTimingActionInclude,
            quittingFiniteDeadlineTimingBoundaryAction, oldTime.isLt,
            hboundary, hne]
  rw [← hproject, ← hmismatch]
  exact pmfTV_le_couplingMismatch _ _ coupling hfirst hsecond

omit [Fintype ι] [DecidableEq ι] in
/-- Moving the new boundary atom to `Never` has total variation exactly its
boundary mass. -/
theorem pmfTV_quittingFiniteDeadline_include_censor_eq_boundary
    (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    Math.Probability.pmfTV
        ((law.map quittingFiniteDeadlineTimingActionCensor).map
          quittingFiniteDeadlineTimingActionInclude)
        law =
      (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
  classical
  let projected :=
    (law.map quittingFiniteDeadlineTimingActionCensor).map
      quittingFiniteDeadlineTimingActionInclude
  have hprojectedBoundary :
      projected (quittingFiniteDeadlineTimingBoundaryAction deadline) = 0 := by
    unfold projected
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro oldAction
    split
    · next heq =>
        exfalso
        cases oldAction with
        | none =>
            simp [quittingFiniteDeadlineTimingActionInclude,
              quittingFiniteDeadlineTimingBoundaryAction] at heq
        | some oldTime =>
            have hfin : oldTime.castSucc = Fin.last deadline := by
              exact Option.some.inj heq.symm
            have hval := congrArg Fin.val hfin
            simp only [Fin.val_castSucc, Fin.val_last] at hval
            exact (Nat.ne_of_lt oldTime.isLt) hval
    · rfl
  have hlower :
      (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal ≤
        Math.Probability.pmfTV projected law := by
    let indicator : QuittingFiniteDeadlineTimingAction (deadline + 1) → ℝ :=
      fun action => if action =
        quittingFiniteDeadlineTimingBoundaryAction deadline then 1 else 0
    have hvariation := Math.Probability.expect_sub_le_mul_pmfPositiveVariation
      law projected indicator (U := 1)
      (fun action => by by_cases h : action =
          quittingFiniteDeadlineTimingBoundaryAction deadline <;>
        simp [indicator, h])
      (fun action => by by_cases h : action =
          quittingFiniteDeadlineTimingBoundaryAction deadline <;>
        simp [indicator, h])
    have hlaw : Math.Probability.expect law indicator =
        (law (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
      symm
      exact Math.Probability.apply_toReal_eq_expect_indicator law _
    have hprojected : Math.Probability.expect projected indicator = 0 := by
      rw [Math.Probability.expect_eq_sum]
      apply Finset.sum_eq_zero
      intro action _
      by_cases haction : action =
          quittingFiniteDeadlineTimingBoundaryAction deadline
      · subst action
        simp [indicator, hprojectedBoundary]
      · simp [indicator, haction]
    rw [hlaw, hprojected, sub_zero, one_mul] at hvariation
    simpa [projected, Math.Probability.pmfTV_symm] using hvariation
  exact le_antisymm
    (pmfTV_quittingFiniteDeadline_include_censor_le_boundary deadline law)
    hlower

omit [DecidableEq ι] in
/-- Summed censor-to-successor total variation is exactly the total erased
boundary participation. -/
theorem sum_pmfTV_quittingFiniteDeadline_include_censor_eq_boundary
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    (∑ player, Math.Probability.pmfTV
        (((mixed player).map quittingFiniteDeadlineTimingActionCensor).map
          quittingFiniteDeadlineTimingActionInclude)
        (mixed player)) =
      ∑ player, quittingFiniteDeadlineBoundaryParticipation
        deadline mixed player := by
  apply Finset.sum_congr rfl
  intro player _
  exact pmfTV_quittingFiniteDeadline_include_censor_eq_boundary
    deadline (mixed player)

omit [DecidableEq ι] in
/-- Literal adjacent distance is bounded by the exact censored-error plus
boundary-participation budget. -/
theorem quittingFiniteDeadlineAdjacentTV_le_censorBudget
    (deadline : ℕ)
    (old : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (new : ι → PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    quittingFiniteDeadlineAdjacentTV deadline old new ≤
      quittingFiniteDeadlineCensorBudget deadline old new := by
  unfold quittingFiniteDeadlineAdjacentTV
    quittingFiniteDeadlineCensorBudget
    quittingFiniteDeadlineCensoredError
    quittingFiniteDeadlineBoundaryParticipation
    quittingFiniteDeadlineTimingProfileInclude
    quittingFiniteDeadlineTimingProfileCensor
  apply Finset.sum_le_sum
  intro player _
  calc
    Math.Probability.pmfTV
        ((old player).map quittingFiniteDeadlineTimingActionInclude)
        (new player) ≤
      Math.Probability.pmfTV
          ((old player).map quittingFiniteDeadlineTimingActionInclude)
          (((new player).map quittingFiniteDeadlineTimingActionCensor).map
            quittingFiniteDeadlineTimingActionInclude) +
        Math.Probability.pmfTV
          (((new player).map quittingFiniteDeadlineTimingActionCensor).map
            quittingFiniteDeadlineTimingActionInclude)
          (new player) :=
      Math.Probability.pmfTV_triangle _ _ _
    _ ≤ Math.Probability.pmfTV (old player)
          ((new player).map quittingFiniteDeadlineTimingActionCensor) +
        ((new player)
          (quittingFiniteDeadlineTimingBoundaryAction deadline)).toReal := by
      apply add_le_add
      · exact Math.Probability.pmfTV_map_le
          quittingFiniteDeadlineTimingActionInclude _ _
      · exact pmfTV_quittingFiniteDeadline_include_censor_le_boundary
          deadline (new player)

/-! ## A finite maximum and its zero classes -/

/-- Maximum absolute value of a real observable on a nonempty finite type. -/
def finiteAbsoluteMaximum {α : Type} [Fintype α] [Nonempty α]
    (observable : α → ℝ) : ℝ :=
  (Finset.univ.image fun index => |observable index|).max'
    (Finset.univ_nonempty.image _)

theorem abs_le_finiteAbsoluteMaximum {α : Type} [Fintype α] [Nonempty α]
    (observable : α → ℝ) (index : α) :
    |observable index| ≤ finiteAbsoluteMaximum observable := by
  exact Finset.le_max'
    (Finset.univ.image fun current : α => |observable current|) _
    (Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩)

theorem finiteAbsoluteMaximum_nonneg {α : Type} [Fintype α] [Nonempty α]
    (observable : α → ℝ) :
    0 ≤ finiteAbsoluteMaximum observable := by
  let index : α := Classical.choice inferInstance
  exact (abs_nonneg (observable index)).trans
    (abs_le_finiteAbsoluteMaximum observable index)

theorem finiteAbsoluteMaximum_eq_zero_iff
    {α : Type} [Fintype α] [Nonempty α]
    (observable : α → ℝ) :
    finiteAbsoluteMaximum observable = 0 ↔ ∀ index, observable index = 0 := by
  constructor
  · intro hzero index
    have hle := abs_le_finiteAbsoluteMaximum observable index
    rw [hzero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  · intro hzero
    apply le_antisymm
    · apply Finset.max'_le
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with ⟨index, -, rfl⟩
      simp [hzero index]
    · exact finiteAbsoluteMaximum_nonneg observable

theorem finiteAbsoluteMaximum_neg
    {α : Type} [Fintype α] [Nonempty α]
    (observable : α → ℝ) :
    finiteAbsoluteMaximum (fun index => -observable index) =
      finiteAbsoluteMaximum observable := by
  unfold finiteAbsoluteMaximum
  congr 1
  ext value
  simp only [Finset.mem_image, Finset.mem_univ, true_and, abs_neg]

theorem finiteAbsoluteMaximum_sub_triangle
    {α : Type} [Fintype α] [Nonempty α]
    (first middle last : α → ℝ) :
    finiteAbsoluteMaximum (fun index => first index - last index) ≤
      finiteAbsoluteMaximum (fun index => first index - middle index) +
        finiteAbsoluteMaximum (fun index => middle index - last index) := by
  unfold finiteAbsoluteMaximum
  apply Finset.max'_le
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨index, -, rfl⟩
  calc
    |first index - last index| ≤
        |first index - middle index| + |middle index - last index| :=
      abs_sub_le _ _ _
    _ ≤ (Finset.univ.image fun current =>
          |first current - middle current|).max'
          (Finset.univ_nonempty.image _) +
        (Finset.univ.image fun current =>
          |middle current - last current|).max'
          (Finset.univ_nonempty.image _) :=
      add_le_add
        (Finset.le_max'
          (Finset.univ.image fun current : α =>
            |first current - middle current|) _
          (Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩))
        (Finset.le_max'
          (Finset.univ.image fun current : α =>
            |middle current - last current|) _
          (Finset.mem_image.mpr ⟨index, Finset.mem_univ index, rfl⟩))

/-! ## Operational effect gauge -/

/-- The three finite observable families used by the operational quotient.
The action type includes every hard finite date and literal `Never`. -/
structure FiniteClockOperationalObservables
    (ι action : Type) where
  never : ι → ℝ
  payoff : ι → ℝ
  gain : ι → action → ℝ

omit [Fintype ι] [DecidableEq ι] in
@[ext]
theorem FiniteClockOperationalObservables.ext
    {action : Type}
    {first second : FiniteClockOperationalObservables ι action}
    (hnever : first.never = second.never)
    (hpayoff : first.payoff = second.payoff)
    (hgain : first.gain = second.gain) : first = second := by
  cases first
  cases second
  simp_all

/-- Operational pseudodistance between two finite clocks.  It is the maximum
of the exact three normalized coordinate discrepancies from the reviewed
packet. -/
def finiteClockOperationalEffectDistance
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    (bound : ℝ)
    (first second : FiniteClockOperationalObservables ι action) : ℝ :=
  max
    (finiteAbsoluteMaximum fun player =>
      first.never player - second.never player)
    (max
      (finiteAbsoluteMaximum (fun player =>
        first.payoff player - second.payoff player) / (2 * bound))
      (finiteAbsoluteMaximum (fun entry : ι × action =>
        first.gain entry.1 entry.2 - second.gain entry.1 entry.2) /
          (4 * bound)))

theorem finiteClockOperationalEffectDistance_nonneg
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound : ℝ} (_hbound : 0 < bound)
    (first second : FiniteClockOperationalObservables ι action) :
    0 ≤ finiteClockOperationalEffectDistance bound first second := by
  unfold finiteClockOperationalEffectDistance
  exact le_max_of_le_left (finiteAbsoluteMaximum_nonneg _)

@[simp]
theorem finiteClockOperationalEffectDistance_self
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound : ℝ} (_hbound : 0 < bound)
    (observables : FiniteClockOperationalObservables ι action) :
    finiteClockOperationalEffectDistance bound observables observables = 0 := by
  unfold finiteClockOperationalEffectDistance
  simp only [sub_self]
  change max (finiteAbsoluteMaximum (fun _ : ι => 0))
      (max (finiteAbsoluteMaximum (fun _ : ι => 0) / (2 * bound))
        (finiteAbsoluteMaximum (fun _ : ι × action => 0) /
          (4 * bound))) = 0
  rw [(finiteAbsoluteMaximum_eq_zero_iff _).2 (fun _ => rfl),
    (finiteAbsoluteMaximum_eq_zero_iff _).2 (fun _ => rfl)]
  norm_num

theorem finiteClockOperationalEffectDistance_symm
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    (bound : ℝ)
    (first second : FiniteClockOperationalObservables ι action) :
    finiteClockOperationalEffectDistance bound first second =
      finiteClockOperationalEffectDistance bound second first := by
  have hnever : finiteAbsoluteMaximum (fun player =>
      first.never player - second.never player) =
      finiteAbsoluteMaximum (fun player =>
        second.never player - first.never player) := by
    rw [← finiteAbsoluteMaximum_neg (fun player =>
      first.never player - second.never player)]
    congr 1
    funext player
    ring
  have hpayoff : finiteAbsoluteMaximum (fun player =>
      first.payoff player - second.payoff player) =
      finiteAbsoluteMaximum (fun player =>
        second.payoff player - first.payoff player) := by
    rw [← finiteAbsoluteMaximum_neg (fun player =>
      first.payoff player - second.payoff player)]
    congr 1
    funext player
    ring
  have hgain : finiteAbsoluteMaximum (fun entry : ι × action =>
      first.gain entry.1 entry.2 - second.gain entry.1 entry.2) =
      finiteAbsoluteMaximum (fun entry : ι × action =>
        second.gain entry.1 entry.2 - first.gain entry.1 entry.2) := by
    rw [← finiteAbsoluteMaximum_neg (fun entry : ι × action =>
      first.gain entry.1 entry.2 - second.gain entry.1 entry.2)]
    congr 1
    funext entry
    ring
  simp only [finiteClockOperationalEffectDistance, hnever, hpayoff, hgain]

/-- The operational gauge obeys the triangle inequality, so together with
the zero and symmetry laws it is a pseudometric on displayed observables. -/
theorem finiteClockOperationalEffectDistance_triangle
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound : ℝ} (hbound : 0 < bound)
    (first middle last : FiniteClockOperationalObservables ι action) :
    finiteClockOperationalEffectDistance bound first last ≤
      finiteClockOperationalEffectDistance bound first middle +
        finiteClockOperationalEffectDistance bound middle last := by
  have htwo : 0 ≤ 2 * bound := (mul_pos (by norm_num) hbound).le
  have hfour : 0 ≤ 4 * bound := (mul_pos (by norm_num) hbound).le
  unfold finiteClockOperationalEffectDistance
  apply max_le
  · exact (finiteAbsoluteMaximum_sub_triangle
      first.never middle.never last.never).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
  · apply max_le
    · calc
        finiteAbsoluteMaximum (fun player =>
            first.payoff player - last.payoff player) / (2 * bound) ≤
            (finiteAbsoluteMaximum (fun player =>
                first.payoff player - middle.payoff player) +
              finiteAbsoluteMaximum (fun player =>
                middle.payoff player - last.payoff player)) /
              (2 * bound) :=
          div_le_div_of_nonneg_right
            (finiteAbsoluteMaximum_sub_triangle
              first.payoff middle.payoff last.payoff) htwo
        _ = finiteAbsoluteMaximum (fun player =>
              first.payoff player - middle.payoff player) / (2 * bound) +
            finiteAbsoluteMaximum (fun player =>
              middle.payoff player - last.payoff player) / (2 * bound) := by
          ring
        _ ≤ max
              (finiteAbsoluteMaximum (fun player =>
                first.never player - middle.never player))
              (max
                (finiteAbsoluteMaximum (fun player =>
                  first.payoff player - middle.payoff player) / (2 * bound))
                (finiteAbsoluteMaximum (fun entry : ι × action =>
                  first.gain entry.1 entry.2 -
                    middle.gain entry.1 entry.2) / (4 * bound))) +
            max
              (finiteAbsoluteMaximum (fun player =>
                middle.never player - last.never player))
              (max
                (finiteAbsoluteMaximum (fun player =>
                  middle.payoff player - last.payoff player) / (2 * bound))
                (finiteAbsoluteMaximum (fun entry : ι × action =>
                  middle.gain entry.1 entry.2 - last.gain entry.1 entry.2) /
                    (4 * bound))) :=
          add_le_add
            (le_max_of_le_right (le_max_left _ _))
            (le_max_of_le_right (le_max_left _ _))
    · calc
        finiteAbsoluteMaximum (fun entry : ι × action =>
            first.gain entry.1 entry.2 - last.gain entry.1 entry.2) /
            (4 * bound) ≤
            (finiteAbsoluteMaximum (fun entry : ι × action =>
                first.gain entry.1 entry.2 - middle.gain entry.1 entry.2) +
              finiteAbsoluteMaximum (fun entry : ι × action =>
                middle.gain entry.1 entry.2 - last.gain entry.1 entry.2)) /
              (4 * bound) :=
          div_le_div_of_nonneg_right
            (finiteAbsoluteMaximum_sub_triangle
              (fun entry : ι × action => first.gain entry.1 entry.2)
              (fun entry : ι × action => middle.gain entry.1 entry.2)
              (fun entry : ι × action => last.gain entry.1 entry.2)) hfour
        _ = finiteAbsoluteMaximum (fun entry : ι × action =>
              first.gain entry.1 entry.2 - middle.gain entry.1 entry.2) /
              (4 * bound) +
            finiteAbsoluteMaximum (fun entry : ι × action =>
              middle.gain entry.1 entry.2 - last.gain entry.1 entry.2) /
              (4 * bound) := by
          ring
        _ ≤ max
              (finiteAbsoluteMaximum (fun player =>
                first.never player - middle.never player))
              (max
                (finiteAbsoluteMaximum (fun player =>
                  first.payoff player - middle.payoff player) / (2 * bound))
                (finiteAbsoluteMaximum (fun entry : ι × action =>
                  first.gain entry.1 entry.2 -
                    middle.gain entry.1 entry.2) / (4 * bound))) +
            max
              (finiteAbsoluteMaximum (fun player =>
                middle.never player - last.never player))
              (max
                (finiteAbsoluteMaximum (fun player =>
                  middle.payoff player - last.payoff player) / (2 * bound))
                (finiteAbsoluteMaximum (fun entry : ι × action =>
                  middle.gain entry.1 entry.2 - last.gain entry.1 entry.2) /
                    (4 * bound))) :=
          add_le_add
            (le_max_of_le_right (le_max_right _ _))
            (le_max_of_le_right (le_max_right _ _))

/-- Zero operational effect is exactly equality of every displayed
observable. -/
theorem finiteClockOperationalEffectDistance_eq_zero_iff
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound : ℝ} (hbound : 0 < bound)
    (first second : FiniteClockOperationalObservables ι action) :
    finiteClockOperationalEffectDistance bound first second = 0 ↔
      (∀ player, first.never player = second.never player) ∧
      (∀ player, first.payoff player = second.payoff player) ∧
      (∀ player action,
        first.gain player action = second.gain player action) := by
  have htwo : 0 < 2 * bound := mul_pos (by norm_num) hbound
  have hfour : 0 < 4 * bound := mul_pos (by norm_num) hbound
  constructor
  · intro hdistance
    have hneverLe : finiteAbsoluteMaximum (fun player =>
        first.never player - second.never player) ≤ 0 := by
      rw [← hdistance]
      exact le_max_left _ _
    have hneverMax : finiteAbsoluteMaximum (fun player =>
        first.never player - second.never player) = 0 :=
      le_antisymm hneverLe (finiteAbsoluteMaximum_nonneg _)
    have hpayoffScaledLe :
        finiteAbsoluteMaximum (fun player =>
            first.payoff player - second.payoff player) / (2 * bound) ≤ 0 := by
      rw [← hdistance]
      exact le_max_of_le_right (le_max_left _ _)
    have hpayoffMax : finiteAbsoluteMaximum (fun player =>
        first.payoff player - second.payoff player) = 0 := by
      apply le_antisymm
      · rcases (div_nonpos_iff.mp hpayoffScaledLe) with
          ⟨-, hdenom⟩ | ⟨hmaximum, -⟩
        · exact False.elim (not_le_of_gt htwo hdenom)
        · exact hmaximum
      · exact finiteAbsoluteMaximum_nonneg _
    have hgainScaledLe :
        finiteAbsoluteMaximum (fun entry : ι × action =>
            first.gain entry.1 entry.2 - second.gain entry.1 entry.2) /
          (4 * bound) ≤ 0 := by
      rw [← hdistance]
      exact le_max_of_le_right (le_max_right _ _)
    have hgainMax : finiteAbsoluteMaximum (fun entry : ι × action =>
        first.gain entry.1 entry.2 - second.gain entry.1 entry.2) = 0 := by
      apply le_antisymm
      · rcases (div_nonpos_iff.mp hgainScaledLe) with
          ⟨-, hdenom⟩ | ⟨hmaximum, -⟩
        · exact False.elim (not_le_of_gt hfour hdenom)
        · exact hmaximum
      · exact finiteAbsoluteMaximum_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · intro player
      exact sub_eq_zero.mp
        ((finiteAbsoluteMaximum_eq_zero_iff _).mp hneverMax player)
    · intro player
      exact sub_eq_zero.mp
        ((finiteAbsoluteMaximum_eq_zero_iff _).mp hpayoffMax player)
    · intro player action
      exact sub_eq_zero.mp
        ((finiteAbsoluteMaximum_eq_zero_iff _).mp hgainMax (player, action))
  · rintro ⟨hnever, hpayoff, hgain⟩
    have hrecord : first = second := by
      cases first
      cases second
      simp only [FiniteClockOperationalObservables.mk.injEq]
      refine ⟨funext hnever, funext hpayoff, ?_⟩
      funext player action
      exact hgain player action
    subst second
    exact finiteClockOperationalEffectDistance_self hbound first

/-- Literal coordinate bounds exposed by a small operational-effect gauge.
This record is the reusable input expected by robust source-specific paid-edge
compilers; it does not itself assert that such a compiler exists. -/
structure FiniteClockOperationalEffectCoordinates
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    (bound threshold : ℝ)
    (first second : FiniteClockOperationalObservables ι action) : Prop where
  never_lt : ∀ player,
    |first.never player - second.never player| < threshold
  payoff_lt : ∀ player,
    |first.payoff player - second.payoff player| < 2 * bound * threshold
  gain_lt : ∀ player action,
    |first.gain player action - second.gain player action| <
      4 * bound * threshold

/-- A strict operational-effect bound gives the corresponding literal bound
on each observable coordinate. -/
theorem finiteClockOperationalEffectCoordinates_of_distance_lt
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound threshold : ℝ} (hbound : 0 < bound)
    (first second : FiniteClockOperationalObservables ι action)
    (hdistance :
      finiteClockOperationalEffectDistance bound first second < threshold) :
    FiniteClockOperationalEffectCoordinates
      bound threshold first second := by
  have htwo : 0 < 2 * bound := mul_pos (by norm_num) hbound
  have hfour : 0 < 4 * bound := mul_pos (by norm_num) hbound
  refine {
    never_lt := ?_
    payoff_lt := ?_
    gain_lt := ?_
  }
  · intro player
    exact (abs_le_finiteAbsoluteMaximum _ player).trans_lt
      ((le_max_left _ _).trans_lt hdistance)
  · intro player
    have hscaled :
        finiteAbsoluteMaximum (fun current =>
            first.payoff current - second.payoff current) / (2 * bound) <
          threshold :=
      (le_max_of_le_right (le_max_left _ _)).trans_lt hdistance
    have hmaximum : finiteAbsoluteMaximum (fun current =>
        first.payoff current - second.payoff current) <
        2 * bound * threshold := by
      calc
        finiteAbsoluteMaximum (fun current =>
            first.payoff current - second.payoff current) <
            threshold * (2 * bound) := (div_lt_iff₀ htwo).mp hscaled
        _ = 2 * bound * threshold := by ring
    exact (abs_le_finiteAbsoluteMaximum _ player).trans_lt hmaximum
  · intro player selectedAction
    have hscaled :
        finiteAbsoluteMaximum (fun entry : ι × action =>
            first.gain entry.1 entry.2 - second.gain entry.1 entry.2) /
            (4 * bound) < threshold :=
      (le_max_of_le_right (le_max_right _ _)).trans_lt hdistance
    have hmaximum : finiteAbsoluteMaximum (fun entry : ι × action =>
        first.gain entry.1 entry.2 - second.gain entry.1 entry.2) <
        4 * bound * threshold := by
      calc
        finiteAbsoluteMaximum (fun entry : ι × action =>
            first.gain entry.1 entry.2 - second.gain entry.1 entry.2) <
            threshold * (4 * bound) := (div_lt_iff₀ hfour).mp hscaled
        _ = 4 * bound * threshold := by ring
    exact (abs_le_finiteAbsoluteMaximum _
      (player, selectedAction)).trans_lt hmaximum

/-- Generic robust operational split.  The second arm is deliberately a
source-specific compiler from the displayed small-coordinate facts, rather
than a paid edge stored as input data. -/
theorem finiteClockOperationalEffectDistance_ge_or_of_smallCoordinates
    {ι action : Type} [Fintype ι] [Nonempty ι]
    [Fintype action] [Nonempty action]
    {bound threshold : ℝ} (hbound : 0 < bound)
    (first second : FiniteClockOperationalObservables ι action)
    (paid : Prop)
    (hpaid : FiniteClockOperationalEffectCoordinates
      bound threshold first second → paid) :
    threshold ≤ finiteClockOperationalEffectDistance bound first second ∨
      paid := by
  by_cases hlarge : threshold ≤
      finiteClockOperationalEffectDistance bound first second
  · exact Or.inl hlarge
  · exact Or.inr (hpaid
      (finiteClockOperationalEffectCoordinates_of_distance_lt
        hbound first second (lt_of_not_ge hlarge)))

/-! ## Finite timing-law specialization -/

/-- The operational observables of one mixed finite timing law. -/
def quittingFiniteDeadlineOperationalObservables
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    FiniteClockOperationalObservables ι
      (QuittingFiniteDeadlineTimingAction deadline) where
  never player := (mixed player none).toReal
  payoff player :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
      mixed player
  gain player action :=
    (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
      mixed player action

/-- Operational effect distance between two mixed laws on one finite timing
clock. -/
def quittingFiniteDeadlineOperationalEffectDistance
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) : ℝ :=
  finiteClockOperationalEffectDistance bound
    (quittingFiniteDeadlineOperationalObservables reward deadline first)
    (quittingFiniteDeadlineOperationalObservables reward deadline second)

/-- Zero timing-law operational effect preserves every literal `Never`
coefficient. -/
theorem quittingFiniteDeadline_never_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hzero : quittingFiniteDeadlineOperationalEffectDistance
      reward bound deadline first second = 0) (player : ι) :
    (first player none).toReal = (second player none).toReal := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).1 player

/-- Zero timing-law operational effect preserves every hard prescribed
payoff. -/
theorem quittingFiniteDeadline_payoff_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hzero : quittingFiniteDeadlineOperationalEffectDistance
      reward bound deadline first second = 0) (player : ι) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        first player =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.eu
        second player := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).2.1 player

/-- Zero timing-law operational effect preserves every hard pure-action
gain. -/
theorem quittingFiniteDeadline_gain_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hzero : quittingFiniteDeadlineOperationalEffectDistance
      reward bound deadline first second = 0)
    (player : ι) (action : QuittingFiniteDeadlineTimingAction deadline) :
    (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        first player action =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        second player action := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).2.2 player action

/-! ## Literal finite root-word observables -/

/-- Finite root word represented as a list in chronological order. -/
def quittingFiniteRootWord {ι : Type} (length : ℕ)
    (roots : Fin length → ι → PMF Bool) : List (ι → PMF Bool) :=
  List.ofFn roots

/-- The hard zero-tail profile associated with one finite root word. -/
def quittingFiniteRootWordHardProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (roots : Fin length → ι → PMF Bool) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward
    (quittingFiniteRootWord length roots)
    (quittingAlwaysContinueProfile reward)

/-- Literal graft of one finite root word onto a common behavioral tail. -/
def quittingFiniteRootWordGraft
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (roots : Fin length → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRetainedTailFiniteTimingGraft reward
    (quittingFiniteRootWord length roots) tail

/-- Read a finite-word action as its absolute quit date, retaining `Never`. -/
def quittingFiniteRootWordActionTime {length : ℕ} :
    QuittingFiniteDeadlineTimingAction length → Option ℕ
  | none => none
  | some time => some time.val

/-- Exact operational observables of one finite product-root word. -/
def quittingFiniteRootWordOperationalObservables
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (roots : Fin length → ι → PMF Bool) :
    FiniteClockOperationalObservables ι
      (QuittingFiniteDeadlineTimingAction length) where
  never player := quittingLiteralRootStackOwnSurvival
    (quittingFiniteRootWord length roots) player
  payoff player := quittingTerminalPayoff reward
    (quittingFiniteRootWordHardProfile reward length roots) player
  gain player action :=
    quittingPureTimeDeviationPayoff reward
        (quittingFiniteRootWordHardProfile reward length roots) player
        (quittingFiniteRootWordActionTime action) -
      quittingTerminalPayoff reward
        (quittingFiniteRootWordHardProfile reward length roots) player

/-- Operational effect distance specialized to two equal-length finite root
words. -/
def quittingFiniteRootWordOperationalEffectDistance
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (length : ℕ)
    (first second : Fin length → ι → PMF Bool) : ℝ :=
  finiteClockOperationalEffectDistance bound
    (quittingFiniteRootWordOperationalObservables reward length first)
    (quittingFiniteRootWordOperationalObservables reward length second)

/-- The chronological root family realized by one mixed finite timing law. -/
def quittingFiniteDeadlineMixedTimingRootWord
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    Fin deadline → ι → PMF Bool :=
  fun date ↦ quittingProfileLiveRoot reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) date.val

/-- The root-word operational observables reconstructed from a mixed timing
law are exactly its normal-form Never, payoff, and pure-gain observables. -/
theorem quittingFiniteRootWordOperationalObservables_mixedTiming_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteRootWordOperationalObservables reward deadline
        (quittingFiniteDeadlineMixedTimingRootWord reward deadline mixed) =
      quittingFiniteDeadlineOperationalObservables reward deadline mixed := by
  apply FiniteClockOperationalObservables.ext
  · funext player
    exact quittingRetainedTailMixedTimingRootStack_ownSurvival_eq_none
      reward deadline mixed player
  · funext player
    have hprofile := congrArg
      (fun profile ↦ quittingTerminalPayoff reward profile player)
      (quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
        reward deadline mixed)
    change quittingTerminalPayoff reward
        (quittingFiniteRootWordHardProfile reward deadline
          (quittingFiniteDeadlineMixedTimingRootWord reward deadline mixed))
        player = _
    change quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingHardGraft reward
          (quittingRetainedTailMixedTimingRootStack reward deadline mixed))
        player = _
    rw [hprofile, quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
    rfl
  · funext player action
    have hprofile :=
      quittingRetainedTailMixedTimingHardGraft_eq_finiteDeadlineTimingProfile
        reward deadline mixed
    change quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingHardGraft reward
            (quittingRetainedTailMixedTimingRootStack reward deadline mixed))
          player (quittingFiniteRootWordActionTime action) -
        quittingTerminalPayoff reward
          (quittingRetainedTailFiniteTimingHardGraft reward
            (quittingRetainedTailMixedTimingRootStack reward deadline mixed))
          player = _
    rw [hprofile]
    change quittingPureTimeDeviationPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)
          player (quittingFiniteRootWordActionTime action) -
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) player =
      (quittingFiniteDeadlineTimingGame reward deadline).mixedGain
        mixed player action
    unfold KernelGame.mixedGain
    rw [← quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU]
    have hdeviation :=
      quittingFiniteDeadlineTimingProfile_update_pureTime_eq_mixedEU
        reward deadline mixed player action
    have hupdated :=
      quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
        reward deadline (Function.update mixed player (PMF.pure action)) player
    have hdeviation' := hdeviation.trans hupdated.symm
    have hbase := quittingTerminalPayoff_finiteDeadlineTimingProfile_eq_mixedEU
      reward deadline mixed player
    rw [← hbase]
    apply sub_left_inj.mpr
    unfold quittingPureTimeDeviationPayoff at ⊢
    cases action with
    | none => exact hdeviation'
    | some date => exact hdeviation'

/-- Operational effect distance is unchanged by the exact mixed-law to
finite-root-word reconstruction. -/
theorem quittingFiniteRootWordOperationalEffectDistance_mixedTiming_eq
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteRootWordOperationalEffectDistance reward bound deadline
        (quittingFiniteDeadlineMixedTimingRootWord reward deadline first)
        (quittingFiniteDeadlineMixedTimingRootWord reward deadline second) =
      quittingFiniteDeadlineOperationalEffectDistance reward bound deadline
        first second := by
  unfold quittingFiniteRootWordOperationalEffectDistance
    quittingFiniteDeadlineOperationalEffectDistance
  rw [quittingFiniteRootWordOperationalObservables_mixedTiming_eq,
    quittingFiniteRootWordOperationalObservables_mixedTiming_eq]

/-- Zero root-word operational effect gives equality of every pass
coefficient. -/
theorem quittingFiniteRootWord_never_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0) (player : ι) :
    quittingLiteralRootStackOwnSurvival
        (quittingFiniteRootWord length first) player =
      quittingLiteralRootStackOwnSurvival
        (quittingFiniteRootWord length second) player := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).1 player

/-- Zero root-word operational effect gives equality of every hard
prescribed payoff. -/
theorem quittingFiniteRootWord_payoff_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0) (player : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteRootWordHardProfile reward length first) player =
      quittingTerminalPayoff reward
        (quittingFiniteRootWordHardProfile reward length second) player := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).2.1 player

/-- Zero root-word operational effect gives equality of every hard pure
timing gain, including `Never`. -/
theorem quittingFiniteRootWord_gain_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0)
    (player : ι) (action : QuittingFiniteDeadlineTimingAction length) :
    (quittingFiniteRootWordOperationalObservables reward length first).gain
        player action =
      (quittingFiniteRootWordOperationalObservables reward length second).gain
        player action := by
  exact ((finiteClockOperationalEffectDistance_eq_zero_iff hbound _ _).mp
    hzero).2.2 player action

/-- The hard `Never` deviation is the literal force-Continue pass profile. -/
theorem quittingFiniteRootWordHardProfile_update_never_eq_pass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (length : ℕ) (roots : Fin length → ι → PMF Bool) (player : ι) :
    Function.update (quittingFiniteRootWordHardProfile reward length roots)
        player (quittingPureTimeBehaviorStrategy reward player none) =
      quittingRetainedTailFiniteTimingPassProfile reward
        (quittingFiniteRootWord length roots)
        (quittingAlwaysContinueProfile reward) player := by
  have hcontinue :=
    quittingPureTimeBehaviorStrategy_absolute_eq_continueDeviation
      reward (quittingFiniteRootWord length roots) player none
  simp only [quittingAbsolutePureTime] at hcontinue
  rw [hcontinue]
  unfold quittingFiniteRootWordHardProfile
    quittingRetainedTailFiniteTimingGraft
    quittingRetainedTailFiniteTimingPassProfile
  rw [update_quittingLiteralRootStackProfile_continueDeviation]
  congr 1
  funext other time history
  by_cases hother : other = player
  · subst other
    simp [quittingAlwaysContinueProfile, quittingPureTimeBehaviorStrategy,
      quittingPureTimeHazard, StochasticGame.stationaryBehaviorProfile]
    rfl
  · simp [Function.update_of_ne hother]

/-- Zero operational effect makes the prescribed payoffs of every common
literal graft equal. -/
theorem quittingFiniteRootWord_graft_payoff_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0) (player : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteRootWordGraft reward length first tail) player =
      quittingTerminalPayoff reward
        (quittingFiniteRootWordGraft reward length second tail) player := by
  let firstRoots := quittingFiniteRootWord length first
  let secondRoots := quittingFiniteRootWord length second
  have hhard := quittingFiniteRootWord_payoff_eq_of_effectDistance_eq_zero
    reward hbound length first second hzero player
  have hown : ∀ who,
      quittingLiteralRootStackOwnSurvival firstRoots who =
        quittingLiteralRootStackOwnSurvival secondRoots who := fun who =>
    quittingFiniteRootWord_never_eq_of_effectDistance_eq_zero
      reward hbound length first second hzero who
  have hjoint : quittingLiteralRootStackJointSurvival firstRoots =
      quittingLiteralRootStackJointSurvival secondRoots := by
    rw [quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival,
      quittingLiteralRootStackJointSurvival_eq_prod_ownSurvival]
    exact Finset.prod_congr rfl fun who _ => hown who
  have hfirst :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward firstRoots tail (quittingAlwaysContinueProfile reward) player
  have hsecond :=
    quittingRetainedTailFiniteTimingGraft_payoff_sub_eq_jointReturn_mul
      reward secondRoots tail (quittingAlwaysContinueProfile reward) player
  simp only [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero] at hfirst hsecond
  change quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward firstRoots tail) player =
    quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward secondRoots tail) player
  change quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward firstRoots
        (quittingAlwaysContinueProfile reward)) player =
    quittingTerminalPayoff reward
      (quittingRetainedTailFiniteTimingGraft reward secondRoots
        (quittingAlwaysContinueProfile reward)) player at hhard
  calc
    quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward firstRoots tail) player =
        quittingLiteralRootStackJointSurvival firstRoots *
            quittingTerminalPayoff reward tail player +
          quittingTerminalPayoff reward
            (quittingRetainedTailFiniteTimingGraft reward firstRoots
              (quittingAlwaysContinueProfile reward)) player := by
      linarith [hfirst]
    _ = quittingLiteralRootStackJointSurvival secondRoots *
            quittingTerminalPayoff reward tail player +
          quittingTerminalPayoff reward
            (quittingRetainedTailFiniteTimingGraft reward secondRoots
              (quittingAlwaysContinueProfile reward)) player := by
      rw [hjoint, hhard]
    _ = quittingTerminalPayoff reward
        (quittingRetainedTailFiniteTimingGraft reward secondRoots tail) player := by
      linarith [hsecond]

/-- Zero operational effect makes every pure-time deviation payoff equal
after grafting one common behavioral tail. -/
theorem quittingFiniteRootWord_graft_pureTime_eq_of_effectDistance_eq_zero
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (tail : (quittingGame reward).BehaviorProfile)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0)
    (player : ι) (choice : Option ℕ) :
    quittingPureTimeDeviationPayoff reward
        (quittingFiniteRootWordGraft reward length first tail) player choice =
      quittingPureTimeDeviationPayoff reward
        (quittingFiniteRootWordGraft reward length second tail) player choice := by
  let firstRoots := quittingFiniteRootWord length first
  let secondRoots := quittingFiniteRootWord length second
  have hhardPay := quittingFiniteRootWord_payoff_eq_of_effectDistance_eq_zero
    reward hbound length first second hzero player
  have hhardAction (action : QuittingFiniteDeadlineTimingAction length) :
      quittingPureTimeDeviationPayoff reward
          (quittingFiniteRootWordHardProfile reward length first) player
          (quittingFiniteRootWordActionTime action) =
        quittingPureTimeDeviationPayoff reward
          (quittingFiniteRootWordHardProfile reward length second) player
          (quittingFiniteRootWordActionTime action) := by
    have hgain := quittingFiniteRootWord_gain_eq_of_effectDistance_eq_zero
      reward hbound length first second hzero player action
    unfold quittingFiniteRootWordOperationalObservables at hgain
    linarith
  have hown : ∀ who,
      quittingLiteralRootStackOwnSurvival firstRoots who =
        quittingLiteralRootStackOwnSurvival secondRoots who := fun who =>
    quittingFiniteRootWord_never_eq_of_effectDistance_eq_zero
      reward hbound length first second hzero who
  have hopponent :
      quittingLiteralRootStackOpponentSurvival firstRoots player =
        quittingLiteralRootStackOpponentSurvival secondRoots player := by
    rw [quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase,
      quittingLiteralRootStackOpponentSurvival_eq_prod_ownSurvival_erase]
    exact Finset.prod_congr rfl fun who _ => hown who
  cases choice with
  | none =>
      have hfirst :=
        quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
          reward firstRoots tail (quittingAlwaysContinueProfile reward)
          player none
      have hsecond :=
        quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
          reward secondRoots tail (quittingAlwaysContinueProfile reward)
          player none
      simp only [quittingAbsolutePureTime,
        quittingTerminalPayoff_quittingAlwaysContinue, sub_zero] at hfirst hsecond
      rw [← quittingFiniteRootWordHardProfile_update_never_eq_pass] at hfirst hsecond
      have hnever : quittingTerminalPayoff reward
          (Function.update (quittingFiniteRootWordHardProfile
            reward length first) player
            (quittingPureTimeBehaviorStrategy reward player none)) player =
        quittingTerminalPayoff reward
          (Function.update (quittingFiniteRootWordHardProfile
            reward length second) player
            (quittingPureTimeBehaviorStrategy reward player none)) player := by
        simpa [quittingPureTimeDeviationPayoff,
          quittingFiniteRootWordActionTime] using hhardAction none
      change quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward firstRoots tail)
          player none =
        quittingPureTimeDeviationPayoff reward
          (quittingRetainedTailFiniteTimingGraft reward secondRoots tail)
          player none
      rw [hopponent, hnever] at hfirst
      linarith [hfirst, hsecond]
  | some time =>
      by_cases htime : time < length
      · let action : QuittingFiniteDeadlineTimingAction length :=
          some ⟨time, htime⟩
        have hfirst := quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
          reward firstRoots tail (quittingAlwaysContinueProfile reward)
          player time (by simpa [firstRoots, quittingFiniteRootWord] using htime)
        have hsecond := quittingPureTimeDeviationPayoff_retainedTail_eq_of_lt
          reward secondRoots tail (quittingAlwaysContinueProfile reward)
          player time (by simpa [secondRoots, quittingFiniteRootWord] using htime)
        have hhard := hhardAction action
        simpa [quittingFiniteRootWordActionTime, action,
          quittingFiniteRootWordGraft, quittingFiniteRootWordHardProfile,
          firstRoots, secondRoots] using hfirst.trans (hhard.trans hsecond.symm)
      · let delay := time - length
        have htimeEq : length + delay = time := by
          dsimp only [delay]
          omega
        have hfirst :=
          quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
            reward firstRoots tail (quittingAlwaysContinueProfile reward)
            player (some delay)
        have hsecond :=
          quittingPureTimeDeviationPayoff_absolute_sub_crossTailPass_eq
            reward secondRoots tail (quittingAlwaysContinueProfile reward)
            player (some delay)
        simp only [quittingTerminalPayoff_quittingAlwaysContinue, sub_zero] at hfirst hsecond
        rw [← quittingFiniteRootWordHardProfile_update_never_eq_pass] at hfirst hsecond
        have hnever : quittingTerminalPayoff reward
            (Function.update (quittingFiniteRootWordHardProfile
              reward length first) player
              (quittingPureTimeBehaviorStrategy reward player none)) player =
          quittingTerminalPayoff reward
            (Function.update (quittingFiniteRootWordHardProfile
              reward length second) player
              (quittingPureTimeBehaviorStrategy reward player none)) player := by
          simpa [quittingPureTimeDeviationPayoff,
            quittingFiniteRootWordActionTime] using hhardAction none
        change quittingPureTimeDeviationPayoff reward
            (quittingRetainedTailFiniteTimingGraft reward firstRoots tail)
            player (some time) =
          quittingPureTimeDeviationPayoff reward
            (quittingRetainedTailFiniteTimingGraft reward secondRoots tail)
            player (some time)
        have hfirstLength : firstRoots.length = length := by
          simp [firstRoots, quittingFiniteRootWord]
        have hsecondLength : secondRoots.length = length := by
          simp [secondRoots, quittingFiniteRootWord]
        simp only [hfirstLength, hsecondLength, quittingAbsolutePureTime] at hfirst hsecond
        rw [htimeEq] at hfirst hsecond
        rw [hopponent, hnever] at hfirst
        linarith [hfirst, hsecond]

/-- Every zero class of the operational effect gauge is a graft-universal
terminal-semantic null direction.  The converse is deliberately not claimed. -/
theorem finiteClockOperationalEffectDistance_zero_graftSemantic_eq
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (length : ℕ)
    (first second : Fin length → ι → PMF Bool)
    (hzero : quittingFiniteRootWordOperationalEffectDistance
      reward bound length first second = 0)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingFiniteRootWordGraft reward length first tail) =
      quittingTerminalSemanticPair reward
        (quittingFiniteRootWordGraft reward length second tail) := by
  apply Prod.ext
  · funext player
    exact quittingFiniteRootWord_graft_payoff_eq_of_effectDistance_eq_zero
      reward hbound length first second tail hzero player
  · funext player
    change quittingContinuationBestResponseValue reward
        (quittingFiniteRootWordGraft reward length first tail) player =
      quittingContinuationBestResponseValue reward
        (quittingFiniteRootWordGraft reward length second tail) player
    rw [quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff,
      quittingContinuationBestResponseValue_eq_sSup_pureTimeDeviationPayoff]
    congr 1
    ext value
    constructor <;> rintro ⟨choice, rfl⟩
    · exact ⟨choice,
        (quittingFiniteRootWord_graft_pureTime_eq_of_effectDistance_eq_zero
          reward hbound length first second tail hzero player choice).symm⟩
    · exact ⟨choice,
        quittingFiniteRootWord_graft_pureTime_eq_of_effectDistance_eq_zero
          reward hbound length first second tail hzero player choice⟩

/-- Zero mixed-law operational distance gives equality of the full terminal
semantic pair of the two actual retained-tail grafts.  This is a semantic
quotient statement; terminal-law equality is not asserted. -/
theorem quittingFiniteDeadlineOperationalEffectDistance_zero_retainedTailSemantic_eq
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 < bound) (deadline : ℕ)
    (first second : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (hzero : quittingFiniteDeadlineOperationalEffectDistance
      reward bound deadline first second = 0)
    (tail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward deadline first tail) =
      quittingTerminalSemanticPair reward
        (quittingRetainedTailMixedTimingProfile reward deadline second tail) := by
  have hrootZero : quittingFiniteRootWordOperationalEffectDistance
      reward bound deadline
        (quittingFiniteDeadlineMixedTimingRootWord reward deadline first)
        (quittingFiniteDeadlineMixedTimingRootWord reward deadline second) = 0 := by
    rw [quittingFiniteRootWordOperationalEffectDistance_mixedTiming_eq]
    exact hzero
  have hsemantic := finiteClockOperationalEffectDistance_zero_graftSemantic_eq
    reward hbound deadline
      (quittingFiniteDeadlineMixedTimingRootWord reward deadline first)
      (quittingFiniteDeadlineMixedTimingRootWord reward deadline second)
      hrootZero tail
  exact hsemantic

end GameTheory
