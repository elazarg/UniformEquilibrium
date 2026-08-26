/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.QuantileClockCollision
import MathUE.ProbabilityMassFunction.Coupling
import Research.Quitting.FiniteClockTerminalSemantics

/-!
# Active common-quantile semantic transport

This module owns the executable active-cell common-quantile compression and its
two-sided payoff and unrestricted-cap comparison. Raw parity tags are used only
for collision bookkeeping; target stopping laws use consecutive active cells,
retain Never exactly, and have literal finite-clock support.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.ProbabilityMassFunction Math.PMFProduct Math.Topology
open QuittingBoundaryHolonomy
open QuittingSureSetOwnerRepair
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Replacing one source law by a pure clock commutes exactly with the
coordinatewise active-cell quotient. -/
theorem pmfPi_pureDeviationActiveCompressedLaws_eq_map
    (laws : ι → PMF (Option ℕ)) (marks : Finset ℕ)
    (who : ι) (choice : Option ℕ) :
    pmfPi (quittingPureDeviationStoppingLaws
        (fun player => Math.Probability.finiteClockActiveCompressedLaw
          (laws player) marks)
        who (Math.Probability.finiteClockActiveQuotient marks choice)) =
      (pmfPi (quittingPureDeviationStoppingLaws laws who choice)).map
        (fun choices player =>
          Math.Probability.finiteClockActiveQuotient marks
            (choices player)) := by
  rw [show quittingPureDeviationStoppingLaws
      (fun player => Math.Probability.finiteClockActiveCompressedLaw
        (laws player) marks)
      who (Math.Probability.finiteClockActiveQuotient marks choice) =
      fun player =>
        (quittingPureDeviationStoppingLaws laws who choice player).map
          (Math.Probability.finiteClockActiveQuotient marks) by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [quittingPureDeviationStoppingLaws]
      exact (PMF.pure_map
        (Math.Probability.finiteClockActiveQuotient marks) choice).symm
    · simp [quittingPureDeviationStoppingLaws,
        Math.Probability.finiteClockActiveCompressedLaw, hplayer]]
  exact (pmfPi_push_coordwise
    (quittingPureDeviationStoppingLaws laws who choice)
    (fun _ => Math.Probability.finiteClockActiveQuotient marks)).symm

/-- Number of finite clock cells in the finite-player common-quantile packet. -/
def quantileClockSupport (ι : Type) [Fintype ι]
    (level : ℕ) : ℕ :=
  2 * Fintype.card ι * level + 1

/-- Coordinatewise semantic error in the finite-player common-quantile
packet. -/
def quantileClockRadius (ι : Type) [Fintype ι]
    (level : ℕ) : ℝ :=
  ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / (level : ℝ)

/-- Quantile-clock semantic radius for terminal rewards bounded in absolute
value by `bound`. -/
def quantileClockScaledRadius (ι : Type) [Fintype ι]
    (bound : ℝ) (level : ℕ) : ℝ :=
  bound * quantileClockRadius ι level

/-- Union-bound budget for pair collisions in common unmarked cells. -/
def quantileClockCollisionBudget (ι : Type) [Fintype ι]
    (level : ℕ) : ℝ :=
  ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) /
    (2 * (level : ℝ))

theorem two_mul_quantileClockCollisionBudget
    (ι : Type) [Fintype ι] {level : ℕ} (hlevel : 0 < level) :
    2 * quantileClockCollisionBudget ι level =
      quantileClockRadius ι level := by
  have hlevelNe : (level : ℝ) ≠ 0 := by exact_mod_cast hlevel.ne'
  unfold quantileClockCollisionBudget quantileClockRadius
  field_simp

theorem quantileClockRadius_nonneg (ι : Type) [Fintype ι]
    (level : ℕ) : 0 ≤ quantileClockRadius ι level := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem quantileClockRadius_tendsto_zero (ι : Type) [Fintype ι] :
    Tendsto (quantileClockRadius ι) atTop (𝓝 0) := by
  exact tendsto_const_div_atTop_nhds_zero_nat
    ((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ)

theorem quantileClockScaledRadius_nonneg (ι : Type) [Fintype ι]
    {bound : ℝ} (hbound : 0 ≤ bound) (level : ℕ) :
    0 ≤ quantileClockScaledRadius ι bound level := by
  exact mul_nonneg hbound (quantileClockRadius_nonneg ι level)

theorem quantileClockScaledRadius_tendsto_zero (ι : Type) [Fintype ι]
    (bound : ℝ) :
    Tendsto (quantileClockScaledRadius ι bound) atTop (𝓝 0) := by
  change Tendsto (fun level => bound * quantileClockRadius ι level)
    atTop (𝓝 0)
  simpa using
    (quantileClockRadius_tendsto_zero ι).const_mul bound

/-! ## Canonical common-quantile compression -/

/-- Complete stopping laws extracted from the live spine of a source profile. -/
def quittingQuantileClockSourceLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    ι → PMF (Option ℕ) :=
  fun who => quittingBehaviorStoppingLaw reward (profile who)

/-- The common union of every player's positive-grid first-crossing dates. -/
def quittingQuantileClockMarks
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) : Finset ℕ :=
  Math.Probability.commonStoppingLawQuantileMarks
    (quittingQuantileClockSourceLaws reward profile) level

/-- Push each stopping law separately through the same ordered finite-cell
quotient.  This preserves independence and retains Never exactly. -/
def quittingQuantileClockCompressedLaws
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    ι → PMF (Option ℕ) :=
  fun who => Math.Probability.finiteClockActiveCompressedLaw
    (quittingQuantileClockSourceLaws reward profile who)
    (quittingQuantileClockMarks reward profile level)

/-- Literal independent behavioral reconstruction of the compressed laws. -/
def quittingQuantileClockCompressedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    (quittingGame reward).BehaviorProfile :=
  quittingStoppingLawProfile reward
    (quittingQuantileClockCompressedLaws reward profile level)

/-- Coordinatewise quotient applied to one joint vector of independently
sampled source clocks. -/
def quittingQuantileClockJointQuotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ)
    (choices : ι → Option ℕ) : ι → Option ℕ :=
  fun who => Math.Probability.finiteClockActiveQuotient
    (quittingQuantileClockMarks reward profile level) (choices who)

/-- Raw alternating cell tags used only to identify common unmarked-gap
collisions.  Unlike the executable joint quotient, these tags may contain
unattained holes and are not used as target clock dates. -/
def quittingQuantileClockRawJointQuotient
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ)
    (choices : ι → Option ℕ) : ι → Option ℕ :=
  fun who => Math.Probability.finiteClockRawQuotient
    (quittingQuantileClockMarks reward profile level) (choices who)

/-- Removing unattained raw cells preserves every deterministic terminal
payoff off the event that two players occupy one common unmarked gap.  Ties
at marked dates are retained exactly, and the all-Never branch stays zero. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (observer : ι)
    (hnoCollision : ¬hasRawEvenSomeCollision (fun who =>
      Math.Probability.finiteClockRawQuotient marks (choices who))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun who =>
          Math.Probability.finiteClockActiveQuotient marks
            (choices who)) observer := by
  by_cases hfinite : ∃ time, ∃ who, choices who = some time
  · let first := Nat.find hfinite
    have hfirstWitness : ∃ who, choices who = some first :=
      Nat.find_spec hfinite
    have hsourceFirst : (Finset.univ.filter fun who =>
        choices who = some first).Nonempty := by
      obtain ⟨who, hwho⟩ := hfirstWitness
      exact ⟨who, by simp [hwho]⟩
    have hsourceBefore : ∀ time < first, ∀ who,
        choices who ≠ some time := by
      intro time htime who hwho
      exact (Nat.not_le_of_lt htime)
        (Nat.find_min' hfinite ⟨who, hwho⟩)
    let target : ι → Option ℕ := fun who =>
      Math.Probability.finiteClockActiveQuotient marks (choices who)
    let targetFirst :=
      Math.Probability.finiteClockActiveCellIndex marks first
    have hcoalition : (Finset.univ.filter fun who =>
        target who = some targetFirst) =
        Finset.univ.filter fun who => choices who = some first := by
      ext who
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro htarget
        cases hchoice : choices who with
        | none => simp [target, hchoice] at htarget
        | some time =>
            have hactive :
                Math.Probability.finiteClockActiveCellIndex marks time =
                  Math.Probability.finiteClockActiveCellIndex marks first := by
              simpa [target, targetFirst, hchoice] using htarget
            have hraw :=
              (Math.Probability.finiteClockActiveCellIndex_eq_iff
                marks time first).mp hactive
            by_cases heqTime : time = first
            · subst time
              rfl
            · exfalso
              have heven :=
                (Math.Probability.finiteClockRawCellIndex_eq_implies_eq_or_even
                  marks hraw).resolve_left heqTime
              obtain ⟨anchor, hanchorMem⟩ := hsourceFirst
              have hanchor : choices anchor = some first := by
                simpa using hanchorMem
              have hne : who ≠ anchor := by
                intro heqWho
                subst anchor
                rw [hanchor] at hchoice
                cases hchoice
                exact (heqTime rfl).elim
              apply hnoCollision
              refine ⟨who, anchor, hne,
                Math.Probability.finiteClockRawCellIndex marks time,
                heven, ?_, ?_⟩
              · simp [hchoice, Math.Probability.finiteClockRawQuotient]
              · rw [hraw]
                simp [hanchor, Math.Probability.finiteClockRawQuotient]
      · intro hsource
        simp [target, targetFirst, hsource]
    have htargetFirst : (Finset.univ.filter fun who =>
        target who = some targetFirst).Nonempty := by
      rw [hcoalition]
      exact hsourceFirst
    have htargetBefore : ∀ time < targetFirst, ∀ who,
        target who ≠ some time := by
      intro time htime who htarget
      cases hchoice : choices who with
      | none => simp [target, hchoice] at htarget
      | some sourceTime =>
          have hactive :
              Math.Probability.finiteClockActiveCellIndex marks sourceTime =
                time := by
            simpa [target, hchoice] using htarget
          have hsourceLe : first ≤ sourceTime := by
            by_contra hnotLe
            exact hsourceBefore sourceTime (Nat.lt_of_not_ge hnotLe)
              who hchoice
          have hmono :=
            Math.Probability.finiteClockActiveCellIndex_mono marks hsourceLe
          rw [hactive] at hmono
          exact (Nat.not_le_of_lt htime) hmono
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward choices observer first hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer targetFirst htargetFirst htargetBefore]
    rw [hcoalition]
  · have hallNever : ∀ who, choices who = none := by
      intro who
      cases hchoice : choices who with
      | none => rfl
      | some time => exact (hfinite ⟨time, who, hchoice⟩).elim
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
      reward choices hallNever observer]
    apply Eq.symm
    apply quittingTerminalPayoff_pureStoppingTimeProfile_eq_zero_of_allNever
    intro who
    simp [hallNever who]

/-- Moving one deterministic deviator later preserves terminal payoff when
every opponent either stops strictly before the old date or Never stops. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_update_some_eq_of_others_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (choices : ι → Option ℕ) (who observer : ι)
    {first second : ℕ} (hlt : first < second)
    (hothers : ∀ player, player ≠ who →
      choices player = none ∨
        ∃ time < first, choices player = some time) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices who (some first))) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update choices who (some second))) observer := by
  let source := Function.update choices who (some first)
  let target := Function.update choices who (some second)
  change quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward source) observer =
    quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward target) observer
  by_cases hopponent : ∃ time, ∃ player, player ≠ who ∧
      choices player = some time
  · let earliest := Nat.find hopponent
    obtain ⟨anchor, hanchorNe, hanchor⟩ := Nat.find_spec hopponent
    have hearliestLt : earliest < first := by
      rcases hothers anchor hanchorNe with hnever | ⟨time, htime, heq⟩
      · rw [hnever] at hanchor
        cases hanchor
      · rw [heq] at hanchor
        cases hanchor
        exact htime
    have hsourceBefore : ∀ time < earliest, ∀ player,
        source player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [source]
        omega
      · simp [source, hplayer]
        intro heq
        exact (Nat.not_le_of_lt htime)
          (Nat.find_min' hopponent ⟨player, hplayer, heq⟩)
    have htargetBefore : ∀ time < earliest, ∀ player,
        target player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [target]
        omega
      · simp [target, hplayer]
        intro heq
        exact (Nat.not_le_of_lt htime)
          (Nat.find_min' hopponent ⟨player, hplayer, heq⟩)
    have hcoalition : (Finset.univ.filter fun player =>
        source player = some earliest) =
        Finset.univ.filter fun player => target player = some earliest := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [source, target]
        omega
      · simp [source, target, Function.update, hplayer]
    have hsourceFirst : (Finset.univ.filter fun player =>
        source player = some earliest).Nonempty := by
      refine ⟨anchor, ?_⟩
      simp [source, hanchorNe]
      exact hanchor
    have htargetFirst : (Finset.univ.filter fun player =>
        target player = some earliest).Nonempty := by
      rw [← hcoalition]
      exact hsourceFirst
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward source observer earliest hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer earliest htargetFirst htargetBefore]
    rw [hcoalition]
  · push Not at hopponent
    have hallNever : ∀ player, player ≠ who → choices player = none := by
      intro player hplayer
      cases hchoice : choices player with
      | none => rfl
      | some time => exact (hopponent time player hplayer hchoice).elim
    have hsourceFirst : (Finset.univ.filter fun player =>
        source player = some first).Nonempty := by
      refine ⟨who, ?_⟩
      simp [source]
    have htargetFirst : (Finset.univ.filter fun player =>
        target player = some second).Nonempty := by
      refine ⟨who, ?_⟩
      simp [target]
    have hsourceBefore : ∀ time < first, ∀ player,
        source player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [source]
        omega
      · simp [source, hplayer, hallNever player hplayer]
    have htargetBefore : ∀ time < second, ∀ player,
        target player ≠ some time := by
      intro time htime player
      by_cases hplayer : player = who
      · subst player
        simp [target]
        omega
      · simp [target, hplayer, hallNever player hplayer]
    have hcoalition : (Finset.univ.filter fun player =>
        source player = some first) =
        Finset.univ.filter fun player => target player = some second := by
      ext player
      by_cases hplayer : player = who
      · subst player
        simp [source, target]
      · simp [source, target, Function.update, hplayer,
          hallNever player hplayer]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward source observer first hsourceFirst hsourceBefore]
    rw [quittingTerminalPayoff_pureStoppingTimeProfile_eq_firstCoalition
      reward target observer second htargetFirst htargetBefore]
    rw [hcoalition]

/-- A representative of the last active cell can be moved to any padded
target date.  Off raw terminal-gap collisions, all opponents are strictly
earlier or Never, so the deterministic terminal payoff is unchanged. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_paddedActiveTarget_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (who observer : ι)
    (sourceTime targetTime : ℕ)
    (hsourceLast :
      Math.Probability.finiteClockActiveCellIndex marks sourceTime =
        Math.Probability.finiteClockActiveCellCount marks - 1)
    (htarget : Math.Probability.finiteClockActiveCellCount marks ≤ targetTime)
    (hsourceWho : choices who = some sourceTime)
    (hnoCollision : ¬hasRawEvenSomeCollision (fun player =>
      Math.Probability.finiteClockRawQuotient marks (choices player))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update
            (fun player => Math.Probability.finiteClockActiveQuotient
              marks (choices player))
            who (some targetTime))) observer := by
  let active : ι → Option ℕ := fun player =>
    Math.Probability.finiteClockActiveQuotient marks (choices player)
  let last := Math.Probability.finiteClockActiveCellCount marks - 1
  have hcount : 0 < Math.Probability.finiteClockActiveCellCount marks :=
    Math.Probability.finiteClockActiveCellCount_pos marks
  have hlastLt : last < targetTime := by
    dsimp [last]
    omega
  have hsourceActive : active who = some last := by
    simp [active, hsourceWho, hsourceLast, last]
  have hothers : ∀ player, player ≠ who →
      active player = none ∨ ∃ time < last, active player = some time := by
    intro player hplayer
    cases hchoice : choices player with
    | none => exact Or.inl (by simp [active, hchoice])
    | some time =>
        right
        let cell := Math.Probability.finiteClockActiveCellIndex marks time
        refine ⟨cell, ?_, by simp [active, hchoice, cell]⟩
        have hcellCount :=
          Math.Probability.finiteClockActiveCellIndex_lt_count marks time
        have hneLast : cell ≠ last := by
          intro heq
          have hactiveEq :
              Math.Probability.finiteClockActiveCellIndex marks time =
                Math.Probability.finiteClockActiveCellIndex
                  marks sourceTime := by
            rw [hsourceLast]
            exact heq
          have hrawEq :=
            (Math.Probability.finiteClockActiveCellIndex_eq_iff
              marks time sourceTime).mp hactiveEq
          have heven :=
            Math.Probability.finiteClockRawCellIndex_even_of_activeCellIndex_eq_last
              marks hsourceLast
          apply hnoCollision
          refine ⟨player, who, hplayer,
            Math.Probability.finiteClockRawCellIndex marks sourceTime,
            heven, ?_, ?_⟩
          · simp [hchoice, Math.Probability.finiteClockRawQuotient, hrawEq]
          · simp [hsourceWho, Math.Probability.finiteClockRawQuotient]
        dsimp [cell, last] at hcellCount hneLast ⊢
        omega
  calc
    _ = quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward active) observer :=
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices observer hnoCollision
    _ = quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward
          (Function.update active who (some last))) observer := by
      have hclock : active = Function.update active who (some last) := by
        symm
        rw [← hsourceActive]
        exact Function.update_eq_self who active
      exact congrArg (fun clock => quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward clock) observer) hclock
    _ = _ :=
      quittingTerminalPayoff_pureStoppingTimeProfile_update_some_eq_of_others_lt
        reward active who observer hlastLt hothers

/-- Reverse coupling coordinate.  On the deterministic source atom of the
deviator it emits the requested target date; outside that null mismatch it
falls back to the ordinary active quotient. -/
def quittingQuantileClockReverseCoordinate
    (marks : Finset ℕ) (who : ι) (source target : Option ℕ)
    (player : ι) (choice : Option ℕ) : Option ℕ :=
  if player = who then
    if choice = source then target
    else Math.Probability.finiteClockActiveQuotient marks choice
  else Math.Probability.finiteClockActiveQuotient marks choice

/-- The fixed-source reverse coupling pushes the independently modified
source product exactly to the independently modified active target product. -/
theorem pmfPi_pureDeviationActiveCompressedLaws_eq_reverseMap
    (laws : ι → PMF (Option ℕ)) (marks : Finset ℕ) (who : ι)
    (source target : Option ℕ) :
    pmfPi (quittingPureDeviationStoppingLaws
        (fun player => Math.Probability.finiteClockActiveCompressedLaw
          (laws player) marks)
        who target) =
      (pmfPi (quittingPureDeviationStoppingLaws laws who source)).map
        (fun choices player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) := by
  rw [show quittingPureDeviationStoppingLaws
      (fun player => Math.Probability.finiteClockActiveCompressedLaw
        (laws player) marks)
      who target = fun player =>
        (quittingPureDeviationStoppingLaws laws who source player).map
          (quittingQuantileClockReverseCoordinate
            marks who source target player) by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp only [quittingPureDeviationStoppingLaws, if_pos]
      rw [PMF.pure_map]
      congr 1
      simp [quittingQuantileClockReverseCoordinate]
    · simp only [quittingPureDeviationStoppingLaws, if_neg hplayer]
      change (laws player).map
          (Math.Probability.finiteClockActiveQuotient marks) =
        (laws player).map
          (quittingQuantileClockReverseCoordinate
            marks who source target player)
      congr 1
      funext choice
      simp [quittingQuantileClockReverseCoordinate, hplayer]]
  exact (pmfPi_push_coordwise
    (quittingPureDeviationStoppingLaws laws who source)
    (quittingQuantileClockReverseCoordinate marks who source target)).symm

/-- Pointwise reverse coupling equality off raw gap collisions.  Internal
active target dates are represented exactly; padded dates use the final-cell
move-later lemma. -/
theorem quittingTerminalPayoff_pureStoppingTimeProfile_eq_reverseActiveCoupling_of_no_rawCollision
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (marks : Finset ℕ) (choices : ι → Option ℕ) (who observer : ι)
    (source target : Option ℕ)
    (hcase : Math.Probability.finiteClockActiveQuotient marks source = target ∨
      ∃ sourceTime targetTime,
        source = some sourceTime ∧ target = some targetTime ∧
        Math.Probability.finiteClockActiveCellIndex marks sourceTime =
          Math.Probability.finiteClockActiveCellCount marks - 1 ∧
        Math.Probability.finiteClockActiveCellCount marks ≤ targetTime)
    (hnoCollision : ¬hasRawEvenSomeCollision (fun player =>
      Math.Probability.finiteClockRawQuotient marks (choices player))) :
    quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) observer =
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward fun player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) observer := by
  let active : ι → Option ℕ := fun player =>
    Math.Probability.finiteClockActiveQuotient marks (choices player)
  by_cases hmatch : choices who = source
  · rcases hcase with hquotient | ⟨sourceTime, targetTime,
        hsource, htarget, hlast, hpadded⟩
    · have hmap : (fun player =>
          quittingQuantileClockReverseCoordinate
            marks who source target player (choices player)) = active := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [quittingQuantileClockReverseCoordinate,
            active, hmatch, hquotient]
        · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
      rw [hmap]
      exact
        quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
          reward marks choices observer hnoCollision
    · rcases hsource with rfl
      rcases htarget with rfl
      have hmap : (fun player =>
          quittingQuantileClockReverseCoordinate
            marks who (some sourceTime) (some targetTime)
              player (choices player)) =
          Function.update active who (some targetTime) := by
        funext player
        by_cases hplayer : player = who
        · subst player
          simp [quittingQuantileClockReverseCoordinate, active, hmatch]
        · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
      rw [hmap]
      exact
        quittingTerminalPayoff_pureStoppingTimeProfile_eq_paddedActiveTarget_of_no_rawCollision
          reward marks choices who observer sourceTime targetTime hlast
          hpadded hmatch hnoCollision
  · have hmap : (fun player =>
        quittingQuantileClockReverseCoordinate
          marks who source target player (choices player)) = active := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [quittingQuantileClockReverseCoordinate, active, hmatch]
      · simp [quittingQuantileClockReverseCoordinate, active, hplayer]
    rw [hmap]
    exact
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices observer hnoCollision

/-- Every target clock has a source representative suitable for the reverse
coupling.  Active dates are represented exactly, `Never` is literal, and all
padding dates are represented by the last genuine finite cell. -/
theorem exists_finiteClockReverseRepresentative
    (marks : Finset ℕ) (target : Option ℕ) :
    ∃ source,
      Math.Probability.finiteClockActiveQuotient marks source = target ∨
        ∃ sourceTime targetTime,
          source = some sourceTime ∧ target = some targetTime ∧
          Math.Probability.finiteClockActiveCellIndex marks sourceTime =
            Math.Probability.finiteClockActiveCellCount marks - 1 ∧
          Math.Probability.finiteClockActiveCellCount marks ≤ targetTime := by
  cases target with
  | none =>
      exact ⟨none, Or.inl rfl⟩
  | some targetTime =>
      by_cases hactive : targetTime <
          Math.Probability.finiteClockActiveCellCount marks
      · obtain ⟨sourceTime, hsource⟩ :=
          Math.Probability.exists_finiteClockActiveCellIndex_eq marks hactive
        refine ⟨some sourceTime, Or.inl ?_⟩
        simp [hsource]
      · have hpadded :
            Math.Probability.finiteClockActiveCellCount marks ≤ targetTime :=
          Nat.le_of_not_gt hactive
        have hcount :=
          Math.Probability.finiteClockActiveCellCount_pos marks
        obtain ⟨sourceTime, hsource⟩ :=
          Math.Probability.exists_finiteClockActiveCellIndex_eq marks
            (show Math.Probability.finiteClockActiveCellCount marks - 1 <
              Math.Probability.finiteClockActiveCellCount marks by omega)
        exact ⟨some sourceTime, Or.inr
          ⟨sourceTime, targetTime, rfl, rfl, hsource, hpadded⟩⟩

omit [DecidableEq ι] in
/-- The product of the compressed marginals is exactly the pushforward of the
original independent product law through the coordinatewise common quotient. -/
theorem pmfPi_quittingQuantileClockCompressedLaws_eq_map
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    pmfPi (quittingQuantileClockCompressedLaws reward profile level) =
      (pmfPi (quittingQuantileClockSourceLaws reward profile)).map
        (quittingQuantileClockJointQuotient reward profile level) := by
  change pmfPi (fun who =>
      (quittingQuantileClockSourceLaws reward profile who).map
        (Math.Probability.finiteClockActiveQuotient
          (quittingQuantileClockMarks reward profile level))) =
    (pmfPi (quittingQuantileClockSourceLaws reward profile)).map
      (fun choices who => Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) (choices who))
  exact (pmfPi_push_coordwise
    (quittingQuantileClockSourceLaws reward profile)
    (fun _ => Math.Probability.finiteClockActiveQuotient
      (quittingQuantileClockMarks reward profile level))).symm

omit [DecidableEq ι] in
@[simp] theorem quittingQuantileClockCompressedLaws_none
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) (who : ι) :
    quittingQuantileClockCompressedLaws reward profile level who none =
      quittingQuantileClockSourceLaws reward profile who none := by
  simp [quittingQuantileClockCompressedLaws,
    quittingQuantileClockMarks]

omit [DecidableEq ι] in
theorem quittingQuantileClockCompressedLaws_isFiniteClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) (who : ι) :
    IsFiniteClockStoppingLaw (quantileClockSupport ι level)
      (quittingQuantileClockCompressedLaws reward profile level who) := by
  intro choice hchoice
  exact Math.Probability.finiteClockActiveCompressedLaw_support_commonQuantile
    (quittingQuantileClockSourceLaws reward profile) level who hchoice

/-- The canonical compressed semantic pair belongs to the literal
finite-clock reachable set with the sharp support count. -/
theorem quittingQuantileClockCompressed_semanticPair_mem_reachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (level : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingQuantileClockCompressedProfile reward profile level) ∈
      quittingFiniteClockSemanticReachable reward
        (quantileClockSupport ι level) := by
  refine ⟨quittingQuantileClockCompressedLaws reward profile level,
    fun who => quittingQuantileClockCompressedLaws_isFiniteClock
      reward profile level who, rfl⟩

/-- The prescribed-payoff part of quantile compression follows from an
explicit bad-event coupling and the sharp pair-collision budget. -/
theorem abs_quittingTerminalPayoff_sub_compressed_le_of_collisionEvent
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (observer : ι)
    (event : Set (ι → Option ℕ))
    (heq : ∀ choices, choices ∉ event →
      quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward choices) observer =
        quittingTerminalPayoff reward
          (quittingPureStoppingTimeProfile reward
            (quittingQuantileClockJointQuotient
              reward profile level choices)) observer)
    (hmass : (Math.ProbabilityMassFunction.pmfMass
        (pmfPi (quittingQuantileClockSourceLaws reward profile))
        fun choices => choices ∈ event).toReal ≤
      quantileClockCollisionBudget ι level) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ 2 * bound * quantileClockCollisionBudget ι level := by
  have hsourceCanonical := congrFun (congrArg Prod.fst
    (quittingTerminalSemanticPair_eq_stoppingLawProfile reward profile)) observer
  change quittingTerminalPayoff reward profile observer =
    quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (quittingQuantileClockSourceLaws reward profile)) observer at hsourceCanonical
  rw [hsourceCanonical, quittingQuantileClockCompressedProfile,
    quittingTerminalPayoff_stoppingLawProfile_eq_expect,
    quittingTerminalPayoff_stoppingLawProfile_eq_expect,
    pmfPi_quittingQuantileClockCompressedLaws_eq_map]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi (quittingQuantileClockSourceLaws reward profile))
    (quittingQuantileClockJointQuotient reward profile level)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) observer)
    event
    (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ observer hreward)
    heq
  calc
    _ ≤ 2 * bound *
        (Math.ProbabilityMassFunction.pmfMass
          (pmfPi (quittingQuantileClockSourceLaws reward profile))
          fun choices => choices ∈ event).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hbound)

/-- The canonical active-cell compression preserves every prescribed payoff
within the reward bound times the quantile radius.  The only bad event is a
pair sharing one raw unmarked gap; the consecutive target indexing itself
introduces no hole. -/
theorem abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (observer : ι) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ bound * quantileClockRadius ι level := by
  let event : Set (ι → Option ℕ) := {choices |
    hasRawEvenSomeCollision
      (quittingQuantileClockRawJointQuotient
        reward profile level choices)}
  rw [show bound * quantileClockRadius ι level =
      2 * bound * quantileClockCollisionBudget ι level by
    rw [← two_mul_quantileClockCollisionBudget ι hlevel]
    ring]
  apply abs_quittingTerminalPayoff_sub_compressed_le_of_collisionEvent
    reward hbound hreward profile observer event
  · intro choices hchoices
    exact
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward (quittingQuantileClockMarks reward profile level)
        choices observer hchoices
  · have hmass :=
      Math.Probability.pmfMass_commonQuantileRawQuotient_hasRawEvenSomeCollision_toReal_le
        (quittingQuantileClockSourceLaws reward profile) hlevel
    change (Math.ProbabilityMassFunction.pmfMass
      (pmfPi (quittingQuantileClockSourceLaws reward profile))
      (fun choices => hasRawEvenSomeCollision (fun who =>
        Math.Probability.finiteClockRawQuotient
          (Math.Probability.commonStoppingLawQuantileMarks
            (quittingQuantileClockSourceLaws reward profile) level)
          (choices who)))).toReal ≤ quantileClockCollisionBudget ι level
    simpa only [quantileClockCollisionBudget] using hmass

/-- Unit-bounded specialization of the prescribed-payoff compression bound. -/
theorem abs_quittingTerminalPayoff_sub_quantileClockCompressed_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (observer : ι) :
    |quittingTerminalPayoff reward profile observer -
        quittingTerminalPayoff reward
          (quittingQuantileClockCompressedProfile reward profile level)
          observer| ≤ quantileClockRadius ι level := by
  simpa using
    abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel observer

/-- The fixed-original-marks collision budget remains valid after replacing
one source marginal by an arbitrary deterministic finite date or `Never`. -/
theorem pmfMass_quittingQuantileClock_update_pure_collision_toReal_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι) (choice : Option ℕ) :
    (Math.ProbabilityMassFunction.pmfMass
      (pmfPi (quittingPureDeviationStoppingLaws
        (quittingQuantileClockSourceLaws reward profile) who choice))
      (fun choices => hasRawEvenSomeCollision (fun player =>
        Math.Probability.finiteClockRawQuotient
          (quittingQuantileClockMarks reward profile level)
          (choices player)))).toReal ≤
      quantileClockCollisionBudget ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  let sourceModified := quittingPureDeviationStoppingLaws laws who choice
  have hmass :=
    Math.Probability.pmfMass_commonQuantileRawQuotient_update_pure_collision_toReal_le
      laws hlevel who choice
  have hmodifiedClassical : sourceModified =
      @Function.update ι (fun _ => PMF (Option ℕ))
        (fun first second => Classical.propDecidable (first = second))
        laws who (PMF.pure choice) := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [sourceModified, quittingPureDeviationStoppingLaws]
    · simp [sourceModified, quittingPureDeviationStoppingLaws, hplayer,
        Function.update]
  have hmassBase : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => hasRawEvenSomeCollision (fun player =>
        Math.Probability.finiteClockRawQuotient marks
          (choices player)))).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
    rw [hmodifiedClassical]
    simpa [marks, laws, quittingQuantileClockMarks] using hmass
  rw [Math.Probability.natCast_choose_two_eq_mul_sub_div_two] at hmassBase
  change (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => hasRawEvenSomeCollision (fun player =>
        Math.Probability.finiteClockRawQuotient marks
          (choices player)))).toReal ≤ _
  calc
    _ ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / 2) /
        (level : ℝ) := hmassBase
    _ = quantileClockCollisionBudget ι level := by
      unfold quantileClockCollisionBudget
      ring

/-- Every source pure-time deviation has an active-cell target deviation with
payoff error at most the reward bound times the quantile radius. -/
theorem abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (choice : Option ℕ) :
    |quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who
              (Math.Probability.finiteClockActiveQuotient
                (quittingQuantileClockMarks reward profile level)
                choice))) who| ≤ bound * quantileClockRadius ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  let targetChoice :=
    Math.Probability.finiteClockActiveQuotient marks choice
  let sourceModified :=
    quittingPureDeviationStoppingLaws laws who choice
  let targetModified := quittingPureDeviationStoppingLaws
    (quittingQuantileClockCompressedLaws reward profile level)
    who targetChoice
  let event : Set (ι → Option ℕ) := {choices |
    hasRawEvenSomeCollision (fun player =>
      Math.Probability.finiteClockRawQuotient marks (choices player))}
  rw [quittingTerminalPayoff_update_pureTime_eq_stoppingLawProfile]
  change |quittingTerminalPayoff reward
          (Function.update (quittingStoppingLawProfile reward laws) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who - _| ≤ _
  rw [quittingQuantileClockCompressedProfile]
  rw [quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  change |Math.Probability.expect (pmfPi sourceModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who) -
    Math.Probability.expect (pmfPi targetModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who)| ≤ _
  have htargetLaw : pmfPi targetModified =
      (pmfPi sourceModified).map (fun choices player =>
        Math.Probability.finiteClockActiveQuotient marks
          (choices player)) := by
    exact pmfPi_pureDeviationActiveCompressedLaws_eq_map
      laws marks who choice
  rw [htargetLaw]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi sourceModified)
    (fun choices player =>
      Math.Probability.finiteClockActiveQuotient marks (choices player))
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    event (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices hchoices =>
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_activeQuotient_of_no_rawCollision
        reward marks choices who hchoices)
  have hmass :=
    Math.Probability.pmfMass_commonQuantileRawQuotient_update_pure_collision_toReal_le
      laws hlevel who choice
  have hmass' : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => choices ∈ event)).toReal ≤
      quantileClockCollisionBudget ι level := by
    have hmodifiedClassical : sourceModified =
        @Function.update ι (fun _ => PMF (Option ℕ))
          (fun first second => Classical.propDecidable (first = second))
          laws who (PMF.pure choice) := by
      funext player
      by_cases hplayer : player = who
      · subst player
        simp [sourceModified, quittingPureDeviationStoppingLaws]
      · simp [sourceModified, quittingPureDeviationStoppingLaws, hplayer,
          Function.update]
    have hmassBase : (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal ≤
        ((Fintype.card ι).choose 2 : ℝ) / (level : ℝ) := by
      rw [hmodifiedClassical]
      simpa [event, marks, laws, quittingQuantileClockMarks] using hmass
    rw [Math.Probability.natCast_choose_two_eq_mul_sub_div_two] at hmassBase
    calc
      _ ≤ (((Fintype.card ι * (Fintype.card ι - 1) : ℕ) : ℝ) / 2) /
          (level : ℝ) := hmassBase
      _ = quantileClockCollisionBudget ι level := by
        unfold quantileClockCollisionBudget
        ring
  calc
    _ ≤ 2 * bound * (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass'
        (mul_nonneg (by norm_num) hbound)
    _ = bound * quantileClockRadius ι level := by
      rw [← two_mul_quantileClockCollisionBudget ι hlevel]
      ring

/-- Unit-bounded forward pure-time transport. -/
theorem abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (choice : Option ℕ) :
    |quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who
              (Math.Probability.finiteClockActiveQuotient
                (quittingQuantileClockMarks reward profile level)
                choice))) who| ≤ quantileClockRadius ι level := by
  simpa using
    abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel who choice

/-- Every target pure-time deviation, including padding dates and `Never`,
has a source pure-time representative with payoff error at most the reward
bound times the quantile radius. -/
theorem exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (target : Option ℕ) :
    ∃ source,
      |quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who target)) who -
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who source)) who| ≤
        bound * quantileClockRadius ι level := by
  let laws := quittingQuantileClockSourceLaws reward profile
  let marks := quittingQuantileClockMarks reward profile level
  obtain ⟨source, hcase⟩ :=
    exists_finiteClockReverseRepresentative marks target
  refine ⟨source, ?_⟩
  let sourceModified :=
    quittingPureDeviationStoppingLaws laws who source
  let targetModified := quittingPureDeviationStoppingLaws
    (quittingQuantileClockCompressedLaws reward profile level) who target
  let quotient : (ι → Option ℕ) → ι → Option ℕ := fun choices player =>
    quittingQuantileClockReverseCoordinate
      marks who source target player (choices player)
  let event : Set (ι → Option ℕ) := {choices |
    hasRawEvenSomeCollision (fun player =>
      Math.Probability.finiteClockRawQuotient marks (choices player))}
  have hsourceCanonical :=
    quittingTerminalPayoff_update_pureTime_eq_stoppingLawProfile
      reward profile who source
  rw [quittingQuantileClockCompressedProfile]
  rw [hsourceCanonical,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect,
    quittingTerminalPayoff_update_stoppingLawProfile_pureTime_eq_expect]
  change |Math.Probability.expect (pmfPi targetModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who) -
    Math.Probability.expect (pmfPi sourceModified) (fun choices =>
      quittingTerminalPayoff reward
        (quittingPureStoppingTimeProfile reward choices) who)| ≤ _
  have htargetLaw : pmfPi targetModified =
      (pmfPi sourceModified).map quotient := by
    exact pmfPi_pureDeviationActiveCompressedLaws_eq_reverseMap
      laws marks who source target
  rw [htargetLaw, abs_sub_comm]
  have hcoupling := abs_expect_sub_expect_map_le_of_eq_off_event
    (pmfPi sourceModified) quotient
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    (fun choices => quittingTerminalPayoff reward
      (quittingPureStoppingTimeProfile reward choices) who)
    event (bound := bound)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices => abs_quittingTerminalPayoff_le reward _ who hreward)
    (fun choices hchoices =>
      quittingTerminalPayoff_pureStoppingTimeProfile_eq_reverseActiveCoupling_of_no_rawCollision
        reward marks choices who who source target hcase hchoices)
  have hmass : (Math.ProbabilityMassFunction.pmfMass
      (pmfPi sourceModified)
      (fun choices => choices ∈ event)).toReal ≤
      quantileClockCollisionBudget ι level := by
    exact pmfMass_quittingQuantileClock_update_pure_collision_toReal_le
      reward profile hlevel who source
  calc
    _ ≤ 2 * bound * (Math.ProbabilityMassFunction.pmfMass
        (pmfPi sourceModified)
        (fun choices => choices ∈ event)).toReal := hcoupling
    _ ≤ 2 * bound * quantileClockCollisionBudget ι level := by
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (by norm_num) hbound)
    _ = bound * quantileClockRadius ι level := by
      rw [← two_mul_quantileClockCollisionBudget ι hlevel]
      ring

/-- Unit-bounded reverse pure-time transport. -/
theorem exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1)
    (profile : (quittingGame reward).BehaviorProfile)
    {level : ℕ} (hlevel : 0 < level) (who : ι)
    (target : Option ℕ) :
    ∃ source,
      |quittingTerminalPayoff reward
          (Function.update
            (quittingQuantileClockCompressedProfile reward profile level) who
            (quittingPureTimeBehaviorStrategy reward who target)) who -
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who source)) who| ≤
        quantileClockRadius ι level := by
  simpa using
    exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
      reward (bound := 1) (by norm_num) hreward profile hlevel who target

omit [Fintype ι] [DecidableEq ι] in
/-- Mutual pointwise approximation of two families controls the difference
of their suprema.  This is the order-theoretic final step in unrestricted-cap
compression. -/
theorem abs_sSup_range_sub_sSup_range_le_of_mutual_approx
    {Source Target : Type*} [Nonempty Source] [Nonempty Target]
    (source : Source → ℝ) (target : Target → ℝ)
    (hsource : BddAbove (Set.range source))
    (htarget : BddAbove (Set.range target)) {error : ℝ}
    (hforward : ∀ choice, ∃ mapped,
      |source choice - target mapped| ≤ error)
    (hbackward : ∀ choice, ∃ mapped,
      |target choice - source mapped| ≤ error) :
    |sSup (Set.range source) - sSup (Set.range target)| ≤ error := by
  have hsourceTarget : sSup (Set.range source) ≤
      sSup (Set.range target) + error := by
    apply csSup_le (Set.range_nonempty source)
    rintro value ⟨choice, rfl⟩
    obtain ⟨mapped, hmapped⟩ := hforward choice
    have hle : target mapped ≤ sSup (Set.range target) :=
      le_csSup htarget (Set.mem_range_self mapped)
    have hsigned : source choice - target mapped ≤ error :=
      (le_abs_self _).trans hmapped
    linarith
  have htargetSource : sSup (Set.range target) ≤
      sSup (Set.range source) + error := by
    apply csSup_le (Set.range_nonempty target)
    rintro value ⟨choice, rfl⟩
    obtain ⟨mapped, hmapped⟩ := hbackward choice
    have hle : source mapped ≤ sSup (Set.range source) :=
      le_csSup hsource (Set.mem_range_self mapped)
    have hsigned : target choice - source mapped ≤ error :=
      (le_abs_self _).trans hmapped
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Mutual comparison of every deterministic quit time, including Never,
controls the literal unrestricted behavioral best-response caps. -/
theorem abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile) (who : ι)
    {error : ℝ}
    (hforward : ∀ choice : Option ℕ, ∃ mapped : Option ℕ,
      |quittingTerminalPayoff reward
          (Function.update source who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update target who
            (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤ error)
    (hbackward : ∀ choice : Option ℕ, ∃ mapped : Option ℕ,
      |quittingTerminalPayoff reward
          (Function.update target who
            (quittingPureTimeBehaviorStrategy reward who choice)) who -
        quittingTerminalPayoff reward
          (Function.update source who
            (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤ error) :
    |quittingContinuationBestResponseValue reward source who -
        quittingContinuationBestResponseValue reward target who| ≤ error := by
  let sourceValue : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update source who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  let targetValue : Option ℕ → ℝ := fun choice =>
    quittingTerminalPayoff reward
      (Function.update target who
        (quittingPureTimeBehaviorStrategy reward who choice)) who
  have hsourceBdd : BddAbove (Set.range sourceValue) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
  have htargetBdd : BddAbove (Set.range targetValue) := by
    refine ⟨quittingRewardBound reward, ?_⟩
    rintro value ⟨choice, rfl⟩
    exact (le_abs_self _).trans
      (abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who)
  unfold quittingContinuationBestResponseValue
  rw [sSup_range_quittingTerminalPayoff_update_eq_pureTime,
    sSup_range_quittingTerminalPayoff_update_eq_pureTime]
  exact abs_sSup_range_sub_sSup_range_le_of_mutual_approx
    sourceValue targetValue hsourceBdd htargetBdd hforward hbackward

/-- Two-sided payoff transport at the radius appropriate for an explicit
absolute terminal-reward bound.  The last two clauses include every finite
quit time and Never. -/
def HasEscapeAwareQuantileClockPayoffTransportAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      (∀ observer,
        |quittingTerminalPayoff reward profile observer -
          quittingTerminalPayoff reward
            (quittingQuantileClockCompressedProfile reward profile level)
            observer| ≤ quantileClockScaledRadius ι bound level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockScaledRadius ι bound level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockScaledRadius ι bound level)

/-- The active-cell common-quantile construction satisfies full two-sided
payoff transport for every explicit absolute reward bound. -/
theorem hasEscapeAwareQuantileClockPayoffTransportAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    HasEscapeAwareQuantileClockPayoffTransportAtBound reward bound := by
  intro profile level hlevel
  refine ⟨?_, ?_, ?_⟩
  · simpa [quantileClockScaledRadius] using
      abs_quittingTerminalPayoff_sub_quantileClockCompressed_le_of_bound
        reward hbound hreward profile hlevel
  · intro who choice
    refine ⟨Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) choice, ?_⟩
    simpa [quantileClockScaledRadius] using
      abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le_of_bound
        reward hbound hreward profile hlevel who choice
  · intro who choice
    simpa [quantileClockScaledRadius] using
      exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le_of_bound
        reward hbound hreward profile hlevel who choice

/-- Exact probabilistic transport property for the canonical common-quantile
quotient.  The last two clauses include all deterministic finite quit times
and Never in both directions. -/
def HasEscapeAwareQuantileClockPayoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      (∀ observer,
        |quittingTerminalPayoff reward profile observer -
          quittingTerminalPayoff reward
            (quittingQuantileClockCompressedProfile reward profile level)
            observer| ≤ quantileClockRadius ι level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockRadius ι level) ∧
      (∀ who choice, ∃ mapped,
        |quittingTerminalPayoff reward
            (Function.update
              (quittingQuantileClockCompressedProfile reward profile level) who
              (quittingPureTimeBehaviorStrategy reward who choice)) who -
          quittingTerminalPayoff reward
            (Function.update profile who
              (quittingPureTimeBehaviorStrategy reward who mapped)) who| ≤
            quantileClockRadius ι level)

/-- The active-cell common-quantile construction satisfies full two-sided
payoff transport at the sharp normalized radius. -/
theorem hasEscapeAwareQuantileClockPayoffTransport_of_normalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    HasEscapeAwareQuantileClockPayoffTransport reward := by
  intro profile level hlevel
  refine ⟨abs_quittingTerminalPayoff_sub_quantileClockCompressed_le
      reward hreward profile hlevel, ?_, ?_⟩
  · intro who choice
    exact ⟨Math.Probability.finiteClockActiveQuotient
        (quittingQuantileClockMarks reward profile level) choice,
      abs_quittingTerminalPayoff_update_pureTime_sub_compressed_mapped_le
        reward hreward profile hlevel who choice⟩
  · intro who choice
    exact
      exists_abs_quittingTerminalPayoff_compressed_pureTime_sub_update_le
        reward hreward profile hlevel who choice

/-- Every executable semantic pair admits a finite-clock representative at
the radius scaled by an explicit absolute reward bound. -/
def HasEscapeAwareQuantileClockCompressionAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      semanticPairWithin (quantileClockScaledRadius ι bound level)
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (quittingQuantileClockCompressedProfile reward profile level))

theorem hasEscapeAwareQuantileClockCompressionAtBound_of_payoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ)
    (htransport :
      HasEscapeAwareQuantileClockPayoffTransportAtBound reward bound) :
    HasEscapeAwareQuantileClockCompressionAtBound reward bound := by
  intro profile level hlevel
  obtain ⟨hpayoff, hforward, hbackward⟩ :=
    htransport profile level hlevel
  constructor
  · exact hpayoff
  · intro who
    exact abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
      reward profile
      (quittingQuantileClockCompressedProfile reward profile level) who
      (hforward who) (hbackward who)

/-- Arbitrarily bounded terminal rewards have canonical finite-clock
semantic compression, with the literal unrestricted behavioral cap and exact
Never atom. -/
theorem hasEscapeAwareQuantileClockCompressionAtBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    HasEscapeAwareQuantileClockCompressionAtBound reward bound :=
  hasEscapeAwareQuantileClockCompressionAtBound_of_payoffTransport reward bound
    (hasEscapeAwareQuantileClockPayoffTransportAtBound
      reward hbound hreward)

/-- The canonical game-specific reward bound always discharges the scaled
compression hypothesis. -/
theorem hasEscapeAwareQuantileClockCompressionAtRewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasEscapeAwareQuantileClockCompressionAtBound reward
      (quittingRewardBound reward) :=
  hasEscapeAwareQuantileClockCompressionAtBound reward
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-- Every executable semantic pair admits a finite-clock representative at the
stated support and coordinatewise rate.
The envelope coordinate in `semanticPairWithin` is the unrestricted
behavioral cap, not a finite-horizon verifier. -/
def HasEscapeAwareQuantileClockCompression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile,
    ∀ level, 0 < level →
      semanticPairWithin (quantileClockRadius ι level)
        (quittingTerminalSemanticPair reward profile)
        (quittingTerminalSemanticPair reward
          (quittingQuantileClockCompressedProfile reward profile level))

theorem hasEscapeAwareQuantileClockCompression_of_payoffTransport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (htransport : HasEscapeAwareQuantileClockPayoffTransport reward) :
    HasEscapeAwareQuantileClockCompression reward := by
  intro profile level hlevel
  obtain ⟨hpayoff, hforward, hbackward⟩ :=
    htransport profile level hlevel
  constructor
  · exact hpayoff
  · intro who
    exact abs_quittingContinuationBestResponseValue_sub_le_of_mutual_pureTime
      reward profile
      (quittingQuantileClockCompressedProfile reward profile level) who
      (hforward who) (hbackward who)

/-- Normalized terminal rewards have the canonical finite-clock semantic
compression, with the literal unrestricted behavioral cap and exact Never
atom. -/
theorem hasEscapeAwareQuantileClockCompression_of_normalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hreward : ∀ terminal player, |reward terminal player| ≤ 1) :
    HasEscapeAwareQuantileClockCompression reward :=
  hasEscapeAwareQuantileClockCompression_of_payoffTransport reward
    (hasEscapeAwareQuantileClockPayoffTransport_of_normalized reward hreward)

end GameTheory
