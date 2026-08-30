/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiniteDeadlineProjectiveCompatibility

/-!
# Inverse limit of projectively compatible finite timing laws

An exactly censor-compatible family of finite-deadline timing laws has one
inverse-limit stopping law on `ℕ ∪ {∞}` for each player: its finite atom at a
date is the mass newly exposed at that date, and its `Never` atom is the
infimum of the displayed `Never` masses.  Every finite-deadline law of the
family is the horizon cap of that limit law.

Capping every clock of an independent profile changes an independent
expectation of a bounded observable by at most twice the observable bound
times the probability that the cap moves some clock.  For the inverse limit
that probability tends to zero, so prescribed payoffs and every fixed
pure-time deviation payoff converge.  Together with mixed Nash optimality at
arbitrarily late deadlines this gives exact behavioral optimality of the limit
profile, and hence a uniform-equilibrium payoff.

The inverse-limit construction uses censor compatibility alone; optimality
enters only in the final consumers.
-/

noncomputable section

namespace GameTheory

open Filter
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open scoped ENNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Complementary event masses -/

/-- An event and its complement carry complementary real mass. -/
theorem pmfMass_toReal_add_not {α : Type*} (law : PMF α) (event : α → Prop) :
    (pmfMass (μ := law) event).toReal +
        (pmfMass (μ := law) (fun sample => ¬ event sample)).toReal = 1 := by
  classical
  have hsum : pmfMass (μ := law) event +
      pmfMass (μ := law) (fun sample => ¬ event sample) = 1 := by
    unfold pmfMass
    rw [← ENNReal.tsum_add]
    rw [show (∑' sample, (pmfMask (μ := law) event sample +
        pmfMask (μ := law) (fun sample => ¬ event sample) sample)) =
          ∑' sample, law sample from tsum_congr fun sample => ?_]
    · exact law.tsum_coe
    · by_cases hsample : event sample <;> simp [pmfMask, hsample]
  have htoReal := congrArg ENNReal.toReal hsum
  rwa [ENNReal.toReal_add (pmfMass_ne_top law event)
    (pmfMass_ne_top law fun sample => ¬ event sample),
    ENNReal.toReal_one] at htoReal

/-! ## Capping every clock of an independent stopping-law profile -/

/-- Mass of the clocks that a horizon cap actually moves. -/
def compactStoppingLawCapDefect
    (law : PMF CompactStoppingTime) (horizon : ℕ) : ℝ :=
  (pmfMass (μ := law)
    (fun choice => ¬ compactStoppingTimeCap horizon choice = choice)).toReal

/-- Probability that a horizon cap moves at least one clock of an independent
profile. -/
def quittingCapEscapeMass
    (laws : ι → PMF CompactStoppingTime) (horizon : ℕ) : ℝ :=
  1 - ∏ player, (1 - compactStoppingLawCapDefect (laws player) horizon)

theorem compactStoppingLawCapDefect_nonneg
    (law : PMF CompactStoppingTime) (horizon : ℕ) :
    0 ≤ compactStoppingLawCapDefect law horizon :=
  ENNReal.toReal_nonneg

/-- A deterministic clock that the horizon cap fixes has no cap defect. -/
theorem compactStoppingLawCapDefect_pure_eq_zero
    {choice : CompactStoppingTime} {horizon : ℕ}
    (hchoice : compactStoppingTimeCap horizon choice = choice) :
    compactStoppingLawCapDefect (PMF.pure choice) horizon = 0 := by
  classical
  have hzero : pmfMass (μ := PMF.pure choice)
      (fun sample => ¬ compactStoppingTimeCap horizon sample = sample) = 0 := by
    simp only [pmfMass, pmfMask]
    rw [ENNReal.tsum_eq_zero]
    intro sample
    by_cases hcap : compactStoppingTimeCap horizon sample = sample
    · simp [hcap]
    · have hne : sample ≠ choice := by
        intro heq
        exact hcap (heq ▸ hchoice)
      simp [hcap, PMF.pure_apply_of_ne _ _ hne]
  simp [compactStoppingLawCapDefect, hzero]

omit [DecidableEq ι] in
/-- The exact escape mass of one independent profile: the horizon cap moves no
clock exactly when it fixes every coordinate. -/
theorem pmfMass_toReal_pmfPi_capMoves_eq
    (laws : ι → PMF CompactStoppingTime) (horizon : ℕ) :
    (pmfMass (μ := Math.PMFProduct.pmfPi laws)
        (fun choices => ¬ ∀ player,
          compactStoppingTimeCap horizon (choices player) = choices player)).toReal =
      quittingCapEscapeMass laws horizon := by
  classical
  have hforall := Math.PMFProduct.pmfMass_pmfPi_forall laws
    (fun player choice => compactStoppingTimeCap horizon choice = choice)
  have hkeep : (pmfMass (μ := Math.PMFProduct.pmfPi laws)
      (fun choices => ∀ player,
        compactStoppingTimeCap horizon (choices player) = choices player)).toReal =
      ∏ player, (1 - compactStoppingLawCapDefect (laws player) horizon) := by
    rw [hforall, ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun player _ => ?_
    have hcomplement := pmfMass_toReal_add_not (laws player)
      (fun choice => compactStoppingTimeCap horizon choice = choice)
    unfold compactStoppingLawCapDefect
    linarith
  have hsplit := pmfMass_toReal_add_not (Math.PMFProduct.pmfPi laws)
    (fun choices => ∀ player,
      compactStoppingTimeCap horizon (choices player) = choices player)
  unfold quittingCapEscapeMass
  rw [hkeep] at hsplit
  linarith

omit [DecidableEq ι] in
/-- Capping every clock of an independent profile perturbs the prescribed
payoff of the pure stopping-time realization by at most twice the reward bound
times the escape mass. -/
theorem abs_expect_quittingTerminalPayoff_sub_capProfile_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF CompactStoppingTime) (observer : ι) (horizon : ℕ)
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |expect (Math.PMFProduct.pmfPi laws)
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer) -
        expect (Math.PMFProduct.pmfPi
            (fun player => (laws player).map (compactStoppingTimeCap horizon)))
          (fun choices => quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer)| ≤
      2 * bound * quittingCapEscapeMass laws horizon := by
  classical
  have hpush : Math.PMFProduct.pmfPi
      (fun player => (laws player).map (compactStoppingTimeCap horizon)) =
      (Math.PMFProduct.pmfPi laws).map
        (fun choices player => compactStoppingTimeCap horizon (choices player)) :=
    (Math.PMFProduct.pmfPi_push_coordwise laws
      (fun _ => compactStoppingTimeCap horizon)).symm
  rw [hpush, expect_map, ← pmfMass_toReal_pmfPi_capMoves_eq laws horizon]
  refine abs_expect_sub_le_mul_pmfMass (Math.PMFProduct.pmfPi laws) _ _ _
    (observableBound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    (fun choices => ?_)
  rw [Set.indicator_apply]
  split_ifs with hmoves
  · rw [mul_one]
    calc
      |quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward choices) observer -
          quittingTerminalPayoff reward
            (quittingPureStoppingTimeProfile reward
              (fun player =>
                compactStoppingTimeCap horizon (choices player))) observer| ≤
          |quittingTerminalPayoff reward
              (quittingPureStoppingTimeProfile reward choices) observer| +
            |quittingTerminalPayoff reward
              (quittingPureStoppingTimeProfile reward
                (fun player =>
                  compactStoppingTimeCap horizon (choices player))) observer| :=
        abs_sub _ _
      _ ≤ bound + bound :=
        add_le_add (abs_quittingTerminalPayoff_le reward _ observer hreward)
          (abs_quittingTerminalPayoff_le reward _ observer hreward)
      _ = 2 * bound := by ring
  · have hall : ∀ player,
        compactStoppingTimeCap horizon (choices player) = choices player := by
      by_contra hcontra
      exact hmoves hcontra
    rw [funext hall, sub_self, abs_zero, mul_zero]

/-! ## Sums over the compactified clock -/

/-- Split a sum over `ℕ ∪ {∞}` into its `Never` term and its finite-date
series. -/
theorem tsum_compactStoppingTime (value : CompactStoppingTime → ℝ≥0∞) :
    ∑' choice, value choice =
      value ⊤ + ∑' date : ℕ, value (WithTop.some date) := by
  rw [ENNReal.tsum_eq_add_tsum_ite (⊤ : CompactStoppingTime)]
  congr 1
  have hsupport : Function.support
      (fun choice => if choice = ⊤ then 0 else value choice) ⊆
      Set.range (WithTop.some : ℕ → CompactStoppingTime) := by
    intro choice hchoice
    induction choice using WithTop.recTopCoe with
    | top => exact absurd (if_pos rfl) hchoice
    | coe date => exact ⟨date, rfl⟩
  have hreindex := (WithTop.coe_injective
    (α := ℕ)).tsum_eq (f := fun choice => if choice = ⊤ then 0 else value choice)
    hsupport
  refine Eq.trans (tsum_congr fun choice => ?_)
    (hreindex.symm.trans (tsum_congr fun date => if_neg WithTop.coe_ne_top))
  by_cases hchoice : choice = ⊤ <;> simp [hchoice]

/-! ## Censor-compatible families of finite timing laws -/

/-- One finite-deadline timing law at every deadline, with literal censor
compatibility between successive laws and no optimality requirement. -/
structure QuittingFiniteDeadlineCompatibleTimingFamily
    (ι : Type) [Fintype ι] [DecidableEq ι] where
  mixed : ∀ deadline, ι → PMF (QuittingFiniteDeadlineTimingAction deadline)
  censor_succ : ∀ deadline,
    quittingFiniteDeadlineTimingProfileCensor (mixed (deadline + 1)) =
      mixed deadline

namespace QuittingFiniteDeadlineCompatibleTimingFamily

variable (family : QuittingFiniteDeadlineCompatibleTimingFamily ι)

/-- Mass newly exposed at one date, read in the first deadline that displays
it. -/
def exposedMass (date : ℕ) (player : ι) : ℝ≥0∞ :=
  family.mixed (date + 1) player
    (quittingFiniteDeadlineTimingBoundaryAction date)

/-- Displayed `Never` mass at one deadline. -/
def neverMass (deadline : ℕ) (player : ι) : ℝ≥0∞ :=
  family.mixed deadline player none

/-- `Never` mass of the inverse limit: the mass no finite deadline exposes. -/
def limitNeverMass (player : ι) : ℝ≥0∞ :=
  ⨅ deadline, family.neverMass deadline player

end QuittingFiniteDeadlineCompatibleTimingFamily

/-- Censoring a successor law adds exactly its new boundary atom to `Never`. -/
theorem censor_none_eq_add_boundary (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1))) :
    (law.map quittingFiniteDeadlineTimingActionCensor) none =
      law none + law (quittingFiniteDeadlineTimingBoundaryAction deadline) := by
  have htoReal :=
    QuittingFiniteDeadlineCompatibleNashFamily.censor_none_toReal_eq_add_boundary
      deadline law
  rw [← ENNReal.toReal_add (PMF.apply_ne_top law none)
    (PMF.apply_ne_top law
      (quittingFiniteDeadlineTimingBoundaryAction deadline))] at htoReal
  refine (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) ?_).1 htoReal
  exact ENNReal.add_ne_top.2 ⟨PMF.apply_ne_top law none,
    PMF.apply_ne_top law (quittingFiniteDeadlineTimingBoundaryAction deadline)⟩

/-- Exactly one successor action censors to a displayed old date. -/
theorem quittingFiniteDeadlineTimingActionCensor_eq_some_iff
    {deadline : ℕ}
    (action : QuittingFiniteDeadlineTimingAction (deadline + 1))
    (date : Fin deadline) :
    quittingFiniteDeadlineTimingActionCensor action = some date ↔
      action = some date.castSucc := by
  cases action with
  | none => simp [quittingFiniteDeadlineTimingActionCensor]
  | some time =>
      by_cases hlt : time.val < deadline
      · simp [quittingFiniteDeadlineTimingActionCensor, hlt, Fin.ext_iff]
      · refine iff_of_false ?_ ?_
        · simp [quittingFiniteDeadlineTimingActionCensor, hlt]
        · intro hcontra
          have hval : time.val = date.val := by
            simpa using congrArg Fin.val (Option.some.inj hcontra)
          exact hlt (hval ▸ date.isLt)

/-- Censoring retains every date the old clock already displayed. -/
theorem censor_some_eq (deadline : ℕ)
    (law : PMF (QuittingFiniteDeadlineTimingAction (deadline + 1)))
    (date : Fin deadline) :
    (law.map quittingFiniteDeadlineTimingActionCensor) (some date) =
      law (some date.castSucc) := by
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (some date.castSucc)]
  · exact if_pos ((quittingFiniteDeadlineTimingActionCensor_eq_some_iff
      (some date.castSucc) date).2 rfl).symm
  · intro other _ hother
    exact if_neg fun hcontra => hother
      ((quittingFiniteDeadlineTimingActionCensor_eq_some_iff other date).1
        hcontra.symm)
  · intro hmem
    exact absurd (Finset.mem_univ
      (some date.castSucc : QuittingFiniteDeadlineTimingAction (deadline + 1)))
      hmem

/-- The operational law of a finite timing law puts its whole `Never` action
mass at infinity. -/
theorem map_actionTime_apply_top {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    (law.map quittingFiniteDeadlineTimingActionTime) ⊤ = law none := by
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single none]
  · exact if_pos rfl
  · intro action _ haction
    refine if_neg ?_
    cases action with
    | none => exact absurd rfl haction
    | some time => simp [quittingFiniteDeadlineTimingActionTime]
  · intro hmem
    exact absurd (Finset.mem_univ
      (none : QuittingFiniteDeadlineTimingAction deadline)) hmem

/-- The operational law of a finite timing law reproduces its atom at every
displayed date and vanishes beyond the deadline. -/
theorem map_actionTime_apply_coe {deadline : ℕ}
    (law : PMF (QuittingFiniteDeadlineTimingAction deadline)) (date : ℕ) :
    (law.map quittingFiniteDeadlineTimingActionTime) (WithTop.some date) =
      if hdate : date < deadline then law (some ⟨date, hdate⟩) else 0 := by
  rw [PMF.map_apply, tsum_fintype]
  by_cases hdate : date < deadline
  · rw [dif_pos hdate, Finset.sum_eq_single (some ⟨date, hdate⟩)]
    · exact if_pos rfl
    · intro action _ haction
      refine if_neg ?_
      cases action with
      | none => simp [quittingFiniteDeadlineTimingActionTime]
      | some time =>
          intro hcontra
          refine haction (congrArg some (Fin.ext ?_))
          simpa [quittingFiniteDeadlineTimingActionTime] using hcontra.symm
    · intro hmem
      exact absurd (Finset.mem_univ
        (some ⟨date, hdate⟩ : QuittingFiniteDeadlineTimingAction deadline)) hmem
  · rw [dif_neg hdate]
    refine Finset.sum_eq_zero fun action _ => if_neg ?_
    cases action with
    | none => simp [quittingFiniteDeadlineTimingActionTime]
    | some time =>
        intro hcontra
        have hval : date = time.val := by
          simpa [quittingFiniteDeadlineTimingActionTime] using hcontra
        exact hdate (hval ▸ time.isLt)

namespace QuittingFiniteDeadlineCompatibleTimingFamily

variable (family : QuittingFiniteDeadlineCompatibleTimingFamily ι)

/-- Exact telescope step: the mass exposed at one date leaves `Never`. -/
theorem neverMass_succ_add_exposedMass (deadline : ℕ) (player : ι) :
    family.neverMass (deadline + 1) player +
        family.exposedMass deadline player =
      family.neverMass deadline player := by
  have hcompat := congrFun (family.censor_succ deadline) player
  simp only [quittingFiniteDeadlineTimingProfileCensor] at hcompat
  unfold neverMass exposedMass
  rw [← hcompat]
  exact (censor_none_eq_add_boundary deadline
    (family.mixed (deadline + 1) player)).symm

/-- Deadline zero displays only `Never`. -/
theorem neverMass_zero (player : ι) : family.neverMass 0 player = 1 := by
  have htsum := (family.mixed 0 player).tsum_coe
  rw [tsum_fintype, Fintype.sum_option] at htsum
  simpa [neverMass] using htsum

/-- Exposed masses and the displayed `Never` mass exhaust one deadline. -/
theorem sum_exposedMass_add_neverMass (deadline : ℕ) (player : ι) :
    (∑ date ∈ Finset.range deadline, family.exposedMass date player) +
        family.neverMass deadline player = 1 := by
  induction deadline with
  | zero => simpa using family.neverMass_zero player
  | succ d ih =>
      rw [Finset.sum_range_succ, add_assoc,
        add_comm (family.exposedMass d player) (family.neverMass (d + 1) player),
        family.neverMass_succ_add_exposedMass d player]
      exact ih

/-- The exposed masses and the limiting `Never` mass exhaust the whole law. -/
theorem tsum_exposedMass_add_limitNeverMass (player : ι) :
    (∑' date, family.exposedMass date player) +
      family.limitNeverMass player = 1 := by
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_add]
    refine iSup_le fun horizon => ?_
    calc (∑ date ∈ Finset.range horizon, family.exposedMass date player) +
          family.limitNeverMass player ≤
          (∑ date ∈ Finset.range horizon, family.exposedMass date player) +
            family.neverMass horizon player :=
        add_le_add_right (iInf_le _ horizon) _
      _ = 1 := family.sum_exposedMass_add_neverMass horizon player
  · have hlower : ∀ horizon : ℕ, (1 : ℝ≥0∞) ≤
        (∑' date, family.exposedMass date player) +
          family.neverMass horizon player := by
      intro horizon
      rw [← family.sum_exposedMass_add_neverMass horizon player]
      exact add_le_add_left (ENNReal.sum_le_tsum _) _
    calc (1 : ℝ≥0∞) ≤ ⨅ horizon : ℕ,
          ((∑' date, family.exposedMass date player) +
            family.neverMass horizon player) := le_iInf hlower
      _ = (∑' date, family.exposedMass date player) +
            family.limitNeverMass player := ENNReal.add_iInf.symm

/-- Split the exposed-mass series at one deadline. -/
theorem sum_range_add_tsum_tail_exposedMass (deadline : ℕ) (player : ι) :
    (∑ date ∈ Finset.range deadline, family.exposedMass date player) +
        (∑' date, if deadline ≤ date then
          family.exposedMass date player else 0) =
      ∑' date, family.exposedMass date player := by
  have hhead : (∑' date : ℕ, if date < deadline then
      family.exposedMass date player else 0) =
      ∑ date ∈ Finset.range deadline, family.exposedMass date player := by
    rw [tsum_eq_sum (s := Finset.range deadline)
      (fun date hdate => if_neg (by simpa using hdate))]
    exact Finset.sum_congr rfl fun date hdate =>
      if_pos (Finset.mem_range.1 hdate)
  rw [← hhead, ← ENNReal.tsum_add]
  refine tsum_congr fun date => ?_
  by_cases hdate : date < deadline
  · simp [hdate, Nat.not_le.2 hdate]
  · simp [hdate, Nat.not_lt.1 hdate]

/-- The displayed `Never` mass at one deadline is exactly the mass of the
later finite dates together with the limiting `Never` mass. -/
theorem tsum_tail_exposedMass_add_limitNeverMass (deadline : ℕ) (player : ι) :
    (∑' date, if deadline ≤ date then family.exposedMass date player else 0) +
        family.limitNeverMass player = family.neverMass deadline player := by
  have hfinite := family.sum_exposedMass_add_neverMass deadline player
  have hne : (∑ date ∈ Finset.range deadline,
      family.exposedMass date player) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (hfinite ▸ le_self_add)
  refine (ENNReal.add_right_inj hne).1 ?_
  rw [← add_assoc, family.sum_range_add_tsum_tail_exposedMass deadline player,
    family.tsum_exposedMass_add_limitNeverMass player, hfinite]

/-- Every deadline displays the exposed mass of each date it reaches. -/
theorem mixed_some_eq_exposedMass (player : ι) (deadline date : ℕ)
    (hdate : date < deadline) :
    family.mixed deadline player (some ⟨date, hdate⟩) =
      family.exposedMass date player := by
  revert hdate
  induction deadline with
  | zero => exact fun hdate => absurd hdate (Nat.not_lt_zero date)
  | succ earlier ih =>
      intro hdate
      by_cases hlt : date < earlier
      · have hcompat := congrFun (family.censor_succ earlier) player
        simp only [quittingFiniteDeadlineTimingProfileCensor] at hcompat
        have hstep := censor_some_eq earlier (family.mixed (earlier + 1) player)
          ⟨date, hlt⟩
        rw [hcompat] at hstep
        exact hstep.symm.trans (ih hlt)
      · have hlast : date = earlier := by omega
        subst hlast
        rfl

/-! ## The inverse-limit stopping law -/

/-- Atom function of the inverse-limit stopping law: exposed masses at the
finite dates and the limiting `Never` mass at infinity. -/
def limitValue (player : ι) (choice : CompactStoppingTime) : ℝ≥0∞ :=
  WithTop.recTopCoe (family.limitNeverMass player)
    (fun date => family.exposedMass date player) choice

theorem tsum_limitValue (player : ι) :
    ∑' choice, family.limitValue player choice = 1 := by
  rw [tsum_compactStoppingTime]
  rw [add_comm]
  exact family.tsum_exposedMass_add_limitNeverMass player

/-- The inverse-limit stopping law of one player. -/
def limitLaw (player : ι) : PMF CompactStoppingTime :=
  ⟨family.limitValue player, by
    rw [← family.tsum_limitValue player]
    exact ENNReal.summable.hasSum⟩

@[simp] theorem limitLaw_apply_top (player : ι) :
    family.limitLaw player ⊤ = family.limitNeverMass player := rfl

@[simp] theorem limitLaw_apply_coe (player : ι) (date : ℕ) :
    family.limitLaw player (WithTop.some date) =
      family.exposedMass date player := rfl

/-- The capped inverse limit assigns the whole late-or-never mass to
infinity. -/
theorem map_cap_limitLaw_apply_top (player : ι) (horizon : ℕ) :
    ((family.limitLaw player).map (compactStoppingTimeCap horizon)) ⊤ =
      family.neverMass (horizon + 1) player := by
  rw [PMF.map_apply, tsum_compactStoppingTime,
    ← family.tsum_tail_exposedMass_add_limitNeverMass (horizon + 1) player,
    add_comm]
  congr 1
  · refine tsum_congr fun date => ?_
    by_cases hdate : date ≤ horizon
    · have hne : ¬ ((⊤ : CompactStoppingTime) = WithTop.some date) := by simp
      have hlate : ¬ (horizon + 1 ≤ date) := by omega
      rw [compactStoppingTimeCap_coe_of_le horizon date hdate, if_neg hne,
        if_neg hlate]
    · have hlate : horizon + 1 ≤ date := by omega
      rw [compactStoppingTimeCap_coe_of_lt horizon date (Nat.not_le.1 hdate),
        if_pos (rfl : (⊤ : CompactStoppingTime) = ⊤), if_pos hlate]
      rfl
  · rw [compactStoppingTimeCap_top, if_pos rfl]
    rfl

/-- The capped inverse limit retains every date it still displays. -/
theorem map_cap_limitLaw_apply_coe (player : ι) (horizon date : ℕ) :
    ((family.limitLaw player).map (compactStoppingTimeCap horizon))
        (WithTop.some date) =
      if date ≤ horizon then family.exposedMass date player else 0 := by
  rw [PMF.map_apply, tsum_compactStoppingTime, compactStoppingTimeCap_top,
    if_neg (by simp), zero_add]
  by_cases hdate : date ≤ horizon
  · rw [if_pos hdate, tsum_eq_single date]
    · rw [compactStoppingTimeCap_coe_of_le horizon date hdate, if_pos rfl,
        limitLaw_apply_coe]
    · intro other hother
      by_cases hle : other ≤ horizon
      · rw [compactStoppingTimeCap_coe_of_le horizon other hle]
        exact if_neg fun hcontra => hother (by simpa using hcontra.symm)
      · rw [compactStoppingTimeCap_coe_of_lt horizon other (Nat.not_le.1 hle)]
        exact if_neg (by simp)
  · rw [if_neg hdate, ENNReal.tsum_eq_zero]
    intro other
    by_cases hle : other ≤ horizon
    · rw [compactStoppingTimeCap_coe_of_le horizon other hle]
      refine if_neg fun hcontra => hdate ?_
      have hval : date = other := by simpa using hcontra
      exact hval ▸ hle
    · rw [compactStoppingTimeCap_coe_of_lt horizon other (Nat.not_le.1 hle)]
      exact if_neg (by simp)

/-- **Truncation identity.**  Every finite-deadline law of a compatible family
is exactly the horizon cap of the inverse-limit law. -/
theorem map_cap_limitLaw_eq (player : ι) (horizon : ℕ) :
    (family.limitLaw player).map (compactStoppingTimeCap horizon) =
      (family.mixed (horizon + 1) player).map
        quittingFiniteDeadlineTimingActionTime := by
  refine PMF.ext fun choice => ?_
  induction choice using WithTop.recTopCoe with
  | top =>
      rw [family.map_cap_limitLaw_apply_top player horizon,
        map_actionTime_apply_top]
      rfl
  | coe date =>
      rw [family.map_cap_limitLaw_apply_coe player horizon date,
        map_actionTime_apply_coe]
      by_cases hdate : date ≤ horizon
      · rw [if_pos hdate, dif_pos (Nat.lt_succ_of_le hdate),
          family.mixed_some_eq_exposedMass player (horizon + 1) date
            (Nat.lt_succ_of_le hdate)]
      · rw [if_neg hdate, dif_neg (by omega)]

/-! ## Vanishing escape mass -/

/-- Mass the inverse limit still places at or beyond one deadline. -/
def limitTailMass (deadline : ℕ) (player : ι) : ℝ≥0∞ :=
  ∑' date, if deadline ≤ date then family.exposedMass date player else 0

theorem limitTailMass_add_limitNeverMass (deadline : ℕ) (player : ι) :
    family.limitTailMass deadline player + family.limitNeverMass player =
      family.neverMass deadline player :=
  family.tsum_tail_exposedMass_add_limitNeverMass deadline player

theorem limitNeverMass_ne_top (player : ι) :
    family.limitNeverMass player ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← family.neverMass_zero player]
  exact iInf_le _ 0

theorem limitTailMass_antitone (player : ι) :
    Antitone fun deadline => family.limitTailMass deadline player := by
  refine antitone_nat_of_succ_le fun deadline => ?_
  refine ENNReal.tsum_le_tsum fun date => ?_
  by_cases hdate : deadline + 1 ≤ date
  · rw [if_pos hdate, if_pos (by omega)]
  · rw [if_neg hdate]
    exact bot_le

theorem iInf_limitTailMass (player : ι) :
    (⨅ deadline, family.limitTailMass deadline player) = 0 := by
  refine (ENNReal.add_left_inj (family.limitNeverMass_ne_top player)).1 ?_
  rw [ENNReal.iInf_add, zero_add]
  simp only [family.limitTailMass_add_limitNeverMass]
  rfl

theorem tendsto_limitTailMass (player : ι) :
    Tendsto (fun deadline => family.limitTailMass deadline player) atTop
      (nhds 0) := by
  have hlimit := tendsto_atTop_iInf (family.limitTailMass_antitone player)
  rwa [family.iInf_limitTailMass player] at hlimit

/-- The cap defect of the inverse limit is exactly its tail mass beyond the
horizon. -/
theorem capDefect_limitLaw_eq (player : ι) (horizon : ℕ) :
    compactStoppingLawCapDefect (family.limitLaw player) horizon =
      (family.limitTailMass (horizon + 1) player).toReal := by
  have hmass : pmfMass (μ := family.limitLaw player)
      (fun choice => ¬ compactStoppingTimeCap horizon choice = choice) =
      family.limitTailMass (horizon + 1) player := by
    rw [pmfMass, tsum_compactStoppingTime, limitTailMass]
    rw [show pmfMask (μ := family.limitLaw player)
        (fun choice => ¬ compactStoppingTimeCap horizon choice = choice) ⊤ = 0
      from by simp [pmfMask], zero_add]
    refine tsum_congr fun date => ?_
    simp only [pmfMask]
    by_cases hdate : date ≤ horizon
    · have hfix : ¬ ¬ (compactStoppingTimeCap horizon (WithTop.some date) =
          WithTop.some date) :=
        not_not_intro (compactStoppingTimeCap_coe_of_le horizon date hdate)
      rw [if_neg hfix, if_neg (by omega)]
    · have hmove : ¬ (compactStoppingTimeCap horizon (WithTop.some date) =
          WithTop.some date) := by
        rw [compactStoppingTimeCap_coe_of_lt horizon date (Nat.not_le.1 hdate)]
        simp
      rw [if_pos hmove, if_pos (by omega)]
      rfl
  rw [compactStoppingLawCapDefect, hmass]

theorem tendsto_capDefect_limitLaw (player : ι) :
    Tendsto (fun horizon =>
        compactStoppingLawCapDefect (family.limitLaw player) horizon)
      atTop (nhds 0) := by
  simp only [family.capDefect_limitLaw_eq player]
  have htail : Tendsto (fun horizon =>
      family.limitTailMass (horizon + 1) player) atTop (nhds 0) :=
    (family.tendsto_limitTailMass player).comp (tendsto_add_atTop_nat 1)
  have hreal := (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp htail
  simpa [Function.comp_def] using hreal

end QuittingFiniteDeadlineCompatibleTimingFamily

/-- A deterministic clock is eventually fixed by the horizon cap. -/
theorem tendsto_compactStoppingLawCapDefect_pure
    (choice : CompactStoppingTime) :
    Tendsto (fun horizon =>
        compactStoppingLawCapDefect (PMF.pure choice) horizon)
      atTop (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  induction choice using WithTop.recTopCoe with
  | top =>
      exact Filter.Eventually.of_forall fun horizon =>
        (compactStoppingLawCapDefect_pure_eq_zero
          (compactStoppingTimeCap_top horizon)).symm
  | coe date =>
      filter_upwards [Filter.eventually_ge_atTop date] with horizon hhorizon
      exact (compactStoppingLawCapDefect_pure_eq_zero
        (compactStoppingTimeCap_coe_of_le horizon date hhorizon)).symm

omit [DecidableEq ι] in
/-- Coordinatewise vanishing cap defects make the escape mass vanish. -/
theorem tendsto_quittingCapEscapeMass
    (laws : ι → PMF CompactStoppingTime)
    (hlaws : ∀ player, Tendsto (fun horizon =>
      compactStoppingLawCapDefect (laws player) horizon) atTop (nhds 0)) :
    Tendsto (fun horizon => quittingCapEscapeMass laws horizon)
      atTop (nhds 0) := by
  have hfactors : ∀ player ∈ (Finset.univ : Finset ι),
      Tendsto (fun horizon =>
          1 - compactStoppingLawCapDefect (laws player) horizon)
        atTop (nhds ((1 : ℝ) - 0)) :=
    fun player _ => (tendsto_const_nhds (x := (1 : ℝ))).sub (hlaws player)
  have hprod := tendsto_finsetProd Finset.univ hfactors
  simp only [sub_zero, Finset.prod_const_one] at hprod
  simpa [quittingCapEscapeMass] using
    (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hprod

/-- Every clock is eventually fixed by the horizon cap. -/
theorem eventually_compactStoppingTimeCap_eq (choice : CompactStoppingTime) :
    ∀ᶠ horizon : ℕ in atTop, compactStoppingTimeCap horizon choice = choice := by
  induction choice using WithTop.recTopCoe with
  | top =>
      exact Filter.Eventually.of_forall fun horizon =>
        compactStoppingTimeCap_top horizon
  | coe date =>
      filter_upwards [Filter.eventually_ge_atTop date] with horizon hhorizon
      exact compactStoppingTimeCap_coe_of_le horizon date hhorizon

/-- A clock the horizon cap fixes is one of the pure times a finite-deadline
Nash certificate already controls. -/
theorem compactStoppingTime_mem_finiteDeadlineMenu
    {choice : CompactStoppingTime} {horizon : ℕ}
    (hchoice : compactStoppingTimeCap horizon choice = choice) :
    choice = none ∨ ∃ time < horizon + 1, choice = some time := by
  revert hchoice
  induction choice using WithTop.recTopCoe with
  | top => exact fun _ => Or.inl rfl
  | coe date =>
      intro hchoice
      refine Or.inr ⟨date, ?_, rfl⟩
      by_contra hcontra
      rw [compactStoppingTimeCap_coe_of_lt horizon date (by omega)] at hchoice
      exact absurd hchoice (by simp)

/-- The literal realization of a finite timing law has the independent
expectation of its operational clocks as prescribed payoff. -/
theorem quittingTerminalPayoff_finiteDeadline_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (observer : ι) :
    quittingTerminalPayoff reward
        (quittingFiniteDeadlineTimingProfile reward deadline mixed) observer =
      expect (Math.PMFProduct.pmfPi (fun player =>
          (mixed player).map quittingFiniteDeadlineTimingActionTime))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer) := by
  rw [quittingFiniteDeadlineTimingProfile,
    quittingTerminalPayoff_compactStoppingLawProfile_eq_expect]
  simp only [quittingFiniteDeadlineTimingLaw,
    _root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]

namespace QuittingFiniteDeadlineCompatibleTimingFamily

variable (family : QuittingFiniteDeadlineCompatibleTimingFamily ι)

/-! ## The limit profile -/

/-- Literal behavioral realization of the inverse-limit stopping laws. -/
def limitProfile (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (quittingGame reward).BehaviorProfile :=
  quittingCompactStoppingLawProfile reward
    (fun player => CompactStoppingLaw.ofPMF (family.limitLaw player))

/-- Clocks of a pure-time deviation against the inverse limit. -/
def deviationLaws (who : ι) (choice : CompactStoppingTime) :
    ι → PMF CompactStoppingTime :=
  fun player => if player = who then PMF.pure choice else family.limitLaw player

theorem quittingTerminalPayoff_limitProfile_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (observer : ι) :
    quittingTerminalPayoff reward (family.limitProfile reward) observer =
      expect (Math.PMFProduct.pmfPi family.limitLaw)
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer) := by
  rw [limitProfile, quittingTerminalPayoff_compactStoppingLawProfile_eq_expect]
  simp only [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]

/-- Prescribed payoffs of the inverse limit and of one finite deadline differ
by at most twice the reward bound times the escape mass. -/
theorem abs_quittingTerminalPayoff_limitProfile_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (observer : ι)
    (horizon : ℕ) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingTerminalPayoff reward (family.limitProfile reward) observer -
        quittingTerminalPayoff reward
          (quittingFiniteDeadlineTimingProfile reward (horizon + 1)
            (family.mixed (horizon + 1))) observer| ≤
      2 * bound * quittingCapEscapeMass family.limitLaw horizon := by
  rw [family.quittingTerminalPayoff_limitProfile_eq_expect reward observer,
    quittingTerminalPayoff_finiteDeadline_eq_expect reward (horizon + 1)
      (family.mixed (horizon + 1)) observer,
    show (fun player => (family.mixed (horizon + 1) player).map
          quittingFiniteDeadlineTimingActionTime) =
        (fun player =>
          (family.limitLaw player).map (compactStoppingTimeCap horizon)) from
      funext fun player => (family.map_cap_limitLaw_eq player horizon).symm]
  exact abs_expect_quittingTerminalPayoff_sub_capProfile_le reward
    family.limitLaw observer horizon hreward

/-- Pure-time deviation payoffs against the inverse limit and against one
finite deadline differ by at most twice the reward bound times the escape mass
of the deviation clocks. -/
theorem abs_quittingTerminalPayoff_update_limitProfile_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι)
    (choice : CompactStoppingTime) (horizon : ℕ)
    (hchoice : compactStoppingTimeCap horizon choice = choice) {bound : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    |quittingTerminalPayoff reward
          (Function.update (family.limitProfile reward) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward
              (horizon + 1) (family.mixed (horizon + 1))) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who| ≤
      2 * bound *
        quittingCapEscapeMass (family.deviationLaws who choice) horizon := by
  have hlimit : quittingTerminalPayoff reward
      (Function.update (family.limitProfile reward) who
        (quittingPureTimeBehaviorStrategy reward who choice)) who =
      expect (Math.PMFProduct.pmfPi (family.deviationLaws who choice))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) who) := by
    have hlaws : (fun player => (quittingPureDeviationCompactLaws
        (fun other => CompactStoppingLaw.ofPMF (family.limitLaw other)) who
        choice player).toPMF) = family.deviationLaws who choice := by
      funext player
      by_cases hplayer : player = who <;>
        simp [quittingPureDeviationCompactLaws, deviationLaws, hplayer]
    rw [limitProfile,
      quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
      hlaws]
  have hdeadline : quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward
        (horizon + 1) (family.mixed (horizon + 1))) who
          (quittingPureTimeBehaviorStrategy reward who choice)) who =
      expect (Math.PMFProduct.pmfPi (fun player =>
          (family.deviationLaws who choice player).map
            (compactStoppingTimeCap horizon)))
        (fun choices => quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) who) := by
    have hlaws : (fun player => (quittingPureDeviationCompactLaws
        (fun other =>
          quittingFiniteDeadlineTimingLaw (family.mixed (horizon + 1) other))
        who choice player).toPMF) =
        fun player => (family.deviationLaws who choice player).map
          (compactStoppingTimeCap horizon) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingPureDeviationCompactLaws, deviationLaws, PMF.pure_map,
          hchoice]
      · simp [quittingPureDeviationCompactLaws, deviationLaws, hplayer,
          quittingFiniteDeadlineTimingLaw,
          family.map_cap_limitLaw_eq player horizon]
    rw [quittingFiniteDeadlineTimingProfile,
      quittingTerminalPayoff_update_compactStoppingLawProfile_pureTime_eq_expect,
      hlaws]
  rw [hlimit, hdeadline]
  exact abs_expect_quittingTerminalPayoff_sub_capProfile_le reward
    (family.deviationLaws who choice) who horizon hreward

/-- Deviation clocks of the inverse limit also have vanishing escape mass. -/
theorem tendsto_quittingCapEscapeMass_deviationLaws
    (who : ι) (choice : CompactStoppingTime) :
    Tendsto (fun horizon =>
        quittingCapEscapeMass (family.deviationLaws who choice) horizon)
      atTop (nhds 0) := by
  refine tendsto_quittingCapEscapeMass _ fun player => ?_
  by_cases hplayer : player = who
  · subst player
    simpa [deviationLaws] using
      tendsto_compactStoppingLawCapDefect_pure choice
  · simpa [deviationLaws, hplayer] using family.tendsto_capDefect_limitLaw player

/-- **Exact behavioral optimality of the inverse limit.**  If the deadline
laws of a censor-compatible family are mixed Nash equilibria of their finite
timing games at arbitrarily late deadlines, the behavioral realization of the
inverse-limit laws admits no profitable unilateral behavioral deviation
whatsoever.  Compatibility already determines the early laws from the late
ones, so optimality at every deadline is not required. -/
theorem isZeroAsymptoticNash_limitProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnash : ∀ᶠ deadline in atTop,
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
        (family.mixed deadline)) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 (family.limitProfile reward) := by
  obtain ⟨bound, -, hreward⟩ := exists_quittingRewardBound reward
  have hnashSucc : ∀ᶠ horizon : ℕ in atTop,
      (quittingFiniteDeadlineTimingGame reward
        (horizon + 1)).mixedExtension.IsNash (family.mixed (horizon + 1)) :=
    (tendsto_add_atTop_nat 1).eventually hnash
  have hpure : ∀ (who : ι) (choice : CompactStoppingTime),
      quittingTerminalPayoff reward
          (Function.update (family.limitProfile reward) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who ≤
        quittingTerminalPayoff reward (family.limitProfile reward) who := by
    intro who choice
    have herror : Tendsto (fun horizon : ℕ =>
        2 * bound * quittingCapEscapeMass family.limitLaw horizon +
          2 * bound * quittingCapEscapeMass
            (family.deviationLaws who choice) horizon) atTop (nhds 0) := by
      have hlimit := tendsto_quittingCapEscapeMass family.limitLaw
        family.tendsto_capDefect_limitLaw
      have hdeviation :=
        family.tendsto_quittingCapEscapeMass_deviationLaws who choice
      simpa using ((tendsto_const_nhds (x := 2 * bound)).mul hlimit).add
        ((tendsto_const_nhds (x := 2 * bound)).mul hdeviation)
    refine sub_nonpos.1 (ge_of_tendsto herror ?_)
    filter_upwards [eventually_compactStoppingTimeCap_eq choice, hnashSucc] with
      horizon hhorizon hhorizonNash
    have hcertificate := quittingFiniteDeadlineTimingProfile_isFiniteDeadline
      reward (horizon + 1) (family.mixed (horizon + 1)) hhorizonNash
    have hnashPure := hcertificate.pureTime_le who choice
      (compactStoppingTime_mem_finiteDeadlineMenu hhorizon)
    have hprescribed := family.abs_quittingTerminalPayoff_limitProfile_sub_le
      reward who horizon hreward
    have hdeviationClose :=
      family.abs_quittingTerminalPayoff_update_limitProfile_sub_le
        reward who choice horizon hhorizon hreward
    have hprescribedBound := abs_le.1 hprescribed
    have hdeviationBound := abs_le.1 hdeviationClose
    linarith [hprescribedBound.1, hprescribedBound.2, hdeviationBound.1,
      hdeviationBound.2, hnashPure]
  intro who deviation
  have hsup := quittingTerminalPayoff_update_le_sSup_pureTimeBehaviorStrategy
    reward (family.limitProfile reward) who deviation
  have hbound : sSup (Set.range fun quitTime : Option ℕ =>
      quittingTerminalPayoff reward
        (Function.update (family.limitProfile reward) who
          (quittingPureTimeBehaviorStrategy reward who quitTime)) who) ≤
      quittingTerminalPayoff reward (family.limitProfile reward) who := by
    refine csSup_le ⟨_, ⟨none, rfl⟩⟩ ?_
    rintro _ ⟨quitTime, rfl⟩
    exact hpure who quitTime
  simpa only [add_zero] using hsup.trans hbound

/-- The prescribed payoff of the inverse-limit profile is a uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff_limitProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnash : ∀ᶠ deadline in atTop,
      (quittingFiniteDeadlineTimingGame reward deadline).mixedExtension.IsNash
        (family.mixed deadline)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward (family.limitProfile reward)) :=
  quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward
    (family.limitProfile reward)
    (family.isZeroAsymptoticNash_limitProfile reward hnash)

end QuittingFiniteDeadlineCompatibleTimingFamily

namespace QuittingFiniteDeadlineCompatibleNashFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Forget the deadlinewise Nash property of a projective family. -/
def toTimingFamily (family : QuittingFiniteDeadlineCompatibleNashFamily reward) :
    QuittingFiniteDeadlineCompatibleTimingFamily ι where
  mixed := family.mixed
  censor_succ := family.censor_succ

/-- **Positive projective compiler.**  An exactly projectively compatible
family of finite-deadline timing Nash laws compiles to one behavioral profile
that is exactly terminal Nash against every unilateral behavioral deviation. -/
theorem isZeroAsymptoticNash_limitProfile
    (family : QuittingFiniteDeadlineCompatibleNashFamily reward) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (family.toTimingFamily.limitProfile reward) :=
  family.toTimingFamily.isZeroAsymptoticNash_limitProfile reward
    (Filter.Eventually.of_forall family.isNash)

/-- **Exact uniform-equilibrium payoff.**  The prescribed payoff of the
inverse-limit profile of an exactly projectively compatible family of finite
timing Nash laws is a uniform-equilibrium payoff. -/
theorem isUniformEquilibriumPayoff_limitProfile
    (family : QuittingFiniteDeadlineCompatibleNashFamily reward) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward
        (family.toTimingFamily.limitProfile reward)) :=
  family.toTimingFamily.isUniformEquilibriumPayoff_limitProfile reward
    (Filter.Eventually.of_forall family.isNash)

end QuittingFiniteDeadlineCompatibleNashFamily

end GameTheory
