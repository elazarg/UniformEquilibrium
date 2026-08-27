/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.SameStageEndpointMonodromy

/-!
# Partial pure-root purification at one date

This Research module records the finite, literal part of a possible
preliminary purification argument.  An `Option Bool` assignment marks the
players already processed at one date; a nodup list processes each player at
most once.  The initial semantic mass floor is supplied, while each recursive
step chooses and verifies the existing canonical best endpoint.  The literal
adapter from an arbitrary behavioral profile and marked coalition is checked
below; semantic bounds remain explicit hypotheses.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A partial fixed-date pure-root assignment. -/
def quittingLiteralPartialRootProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool) :
    (quittingGame reward).BehaviorProfile :=
  fun who => match assignment who with
    | none => profile who
    | some action => quittingLiteralOneDateOverride (profile who) stage action

/-- Mark one player as processed at the selected date. -/
def quittingPartialRootAssignmentUpdate
    (assignment : ι → Option Bool) (who : ι) (action : Bool) : ι → Option Bool :=
  Function.update assignment who (some action)

theorem quittingLiteralPartialRootProfile_update_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool)
    (who : ι) (action : Bool) :
    Function.update
        (quittingLiteralPartialRootProfile reward profile stage assignment) who
        (quittingLiteralOneDateOverride
          ((quittingLiteralPartialRootProfile reward profile stage assignment) who)
          stage action) =
      quittingLiteralPartialRootProfile reward profile stage
        (quittingPartialRootAssignmentUpdate assignment who action) := by
  funext player time history
  by_cases hplayer : player = who
  · subst player
    cases hassigned : assignment who with
    | none =>
        simp [quittingLiteralPartialRootProfile,
          quittingPartialRootAssignmentUpdate, quittingLiteralOneDateOverride,
          hassigned]
    | some oldAction =>
        by_cases htime : time = stage
        · simp [quittingLiteralPartialRootProfile,
            quittingPartialRootAssignmentUpdate, quittingLiteralOneDateOverride,
            hassigned, htime]
        · simp [quittingLiteralPartialRootProfile,
          quittingPartialRootAssignmentUpdate, quittingLiteralOneDateOverride,
          hassigned, htime]
  · simp [Function.update, quittingLiteralPartialRootProfile,
      quittingPartialRootAssignmentUpdate, hplayer]

/-- Process a finite assignment list.  The recursion processes the tail before
the head, so `order` is a bookkeeping list and is not chronological execution
order. -/
def quittingPartialRootAssignment_process
    (assignment : ι → Option Bool) (order : List ι) (action : ι → Bool) :
    ι → Option Bool :=
  match order with
  | [] => assignment
  | who :: tail =>
      quittingPartialRootAssignmentUpdate
        (quittingPartialRootAssignment_process assignment tail action) who (action who)

def quittingLiteralPartialRootProfile_process
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool)
    (order : List ι) (action : ι → Bool) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralPartialRootProfile reward profile stage
    (quittingPartialRootAssignment_process assignment order action)

theorem quittingLiteralPartialRootProfile_process_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool)
    (action : ι → Bool) :
    quittingLiteralPartialRootProfile_process reward profile stage assignment
        [] action = quittingLiteralPartialRootProfile reward profile stage assignment := by
  rfl

theorem quittingLiteralPartialRootProfile_process_cons
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool)
    (who : ι) (order : List ι) (action : ι → Bool) :
    quittingLiteralPartialRootProfile_process reward profile stage assignment
        (who :: order) action =
      Function.update
        (quittingLiteralPartialRootProfile_process reward profile stage assignment
          order action) who
        (quittingLiteralOneDateOverride
          ((quittingLiteralPartialRootProfile_process reward profile stage assignment
            order action) who) stage (action who)) := by
  unfold quittingLiteralPartialRootProfile_process
  simp only [quittingPartialRootAssignment_process]
  rw [quittingLiteralPartialRootProfile_update_eq]

omit [DecidableEq ι] in
theorem quittingPartialRootAssignment_process_length_le_card
    (order : List ι) (hnodup : order.Nodup) :
    order.length ≤ Fintype.card ι := by
  exact hnodup.length_le_card

omit [Fintype ι] in
theorem quittingPartialRootAssignment_process_eq_of_not_mem
    (assignment : ι → Option Bool) (order : List ι) (action : ι → Bool)
    {who : ι} (hnot : who ∉ order) :
    quittingPartialRootAssignment_process assignment order action who = assignment who := by
  induction order with
  | nil => rfl
  | cons head tail ih =>
      simp only [quittingPartialRootAssignment_process, List.mem_cons, not_or] at hnot ⊢
      rw [quittingPartialRootAssignmentUpdate]
      simp [hnot.1]
      exact ih hnot.2

omit [Fintype ι] in
theorem quittingPartialRootAssignment_process_eq_some_of_mem
    (assignment : ι → Option Bool) (order : List ι) (action : ι → Bool)
    (hnodup : order.Nodup) {who : ι} (hmem : who ∈ order) :
    quittingPartialRootAssignment_process assignment order action who = some (action who) := by
  induction order with
  | nil => simp at hmem
  | cons head tail ih =>
      have hmem' : who = head ∨ who ∈ tail := by simpa using hmem
      by_cases hhead : head = who
      · subst head
        have htail : who ∉ tail := by
          exact (List.nodup_cons.mp hnodup).1
        change quittingPartialRootAssignmentUpdate
          (quittingPartialRootAssignment_process assignment tail action) who
            (action who) who = some (action who)
        simp [quittingPartialRootAssignmentUpdate]
      · have htail : who ∈ tail := by
          rcases hmem' with hEq | htail
          · exact False.elim (hhead hEq.symm)
          · exact htail
        have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
        change quittingPartialRootAssignmentUpdate
          (quittingPartialRootAssignment_process assignment tail action) head
            (action head) who = some (action who)
        have hneq : who ≠ head := Ne.symm hhead
        simpa [quittingPartialRootAssignmentUpdate, hhead, hneq] using
          ih htailNodup htail

omit [DecidableEq ι] in
theorem quittingLiteralPartialRootProfile_eq_total_of_complete
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (assignment : ι → Option Bool)
    (hcomplete : ∀ who, ∃ action, assignment who = some action) :
    quittingLiteralPartialRootProfile reward profile stage assignment =
      quittingLiteralPureRootProfile reward profile stage
        (fun who => (assignment who).getD false) := by
  funext who time history
  obtain ⟨action, haction⟩ := hcomplete who
  simp [quittingLiteralPartialRootProfile, quittingLiteralPureRootProfile,
    haction]

structure QuittingPartialPurificationState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ) where
  assignment : ι → Option Bool
  coalition : QuittingNonsingletonCoalition ι
  mass_floor : lambda ≤ quittingStageCoalitionMass reward
    (quittingLiteralPartialRootProfile reward baseProfile stage assignment) stage
    (quittingTerminalOfNonsingletonCoalition coalition)

def quittingPartialPurificationStateProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda) :=
  quittingLiteralPartialRootProfile reward baseProfile stage state.assignment

def quittingPartialPurificationBestAction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda)
    (who : ι) : Bool :=
  quittingRootBestEndpointAction reward
    (quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (quittingPartialPurificationStateProfile reward baseProfile stage lambda state)
        (stage + 1))).1
    (quittingProfileLiveRoot reward
      (quittingPartialPurificationStateProfile reward baseProfile stage lambda state) stage) who

structure QuittingPartialPurificationSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda) where
  who : ι
  action : Bool
  action_eq_best : action =
    quittingPartialPurificationBestAction reward baseProfile stage lambda state who
  singleton : {S : Finset ι // S.Nonempty}
  singleton_card : singleton.val.card = 1
  routed : singleton.val =
    quittingPureEndpointRoutedCoalition state.coalition.1 who action
  mass_le : quittingStageCoalitionMass reward
      (quittingPartialPurificationStateProfile reward baseProfile stage lambda state) stage
      (quittingTerminalOfNonsingletonCoalition state.coalition) ≤
    quittingStageCoalitionMass reward
      (quittingLiteralOneDateProfile reward
        (quittingPartialPurificationStateProfile reward baseProfile stage lambda state)
        who stage action) stage singleton

structure QuittingPartialPurificationCarry
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda)
    (who : ι) where
  action : Bool
  action_eq_best : action =
    quittingPartialPurificationBestAction reward baseProfile stage lambda state who
  next : QuittingPartialPurificationState reward baseProfile stage lambda
  next_assignment : next.assignment =
    quittingPartialRootAssignmentUpdate state.assignment who action
  next_coalition : next.coalition.1 =
    quittingPureEndpointRoutedCoalition state.coalition.1 who action

inductive QuittingPartialPurificationPath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ) :
    QuittingPartialPurificationState reward baseProfile stage lambda →
      QuittingPartialPurificationState reward baseProfile stage lambda → ℕ → Prop
  | refl (state : QuittingPartialPurificationState reward baseProfile stage lambda) :
      QuittingPartialPurificationPath reward baseProfile stage lambda state state 0
  | edge {state : QuittingPartialPurificationState reward baseProfile stage lambda}
      {who : ι}
      (carry : QuittingPartialPurificationCarry reward baseProfile stage lambda state who) :
      QuittingPartialPurificationPath reward baseProfile stage lambda state carry.next 1
  | trans {state middle final : QuittingPartialPurificationState reward baseProfile stage lambda}
      {steps₁ steps₂ : ℕ}
      (first : QuittingPartialPurificationPath reward baseProfile stage lambda state middle steps₁)
      (second : QuittingPartialPurificationPath reward baseProfile stage lambda
        middle final steps₂) :
      QuittingPartialPurificationPath reward baseProfile stage lambda state final (steps₁ + steps₂)

theorem quittingPartialPurification_exists_step
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda)
    (who : ι) :
    Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda state) ∨
      Nonempty (QuittingPartialPurificationCarry reward baseProfile stage lambda state who) := by
  let currentProfile :=
    quittingPartialPurificationStateProfile reward baseProfile stage lambda state
  let terminal := quittingTerminalOfNonsingletonCoalition state.coalition
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward currentProfile (stage + 1))
  let root := quittingProfileLiveRoot reward currentProfile stage
  let action := quittingRootBestEndpointAction reward tail.1 root who
  have hroute := quittingStageCoalitionMass_le_stagePureEndpointRouted
    reward currentProfile who stage terminal action state.coalition.property
  let routed := quittingPureEndpointRoutedCoalition terminal.val who action
  obtain ⟨hrouted, hmassCanonical⟩ := hroute
  have hmassLiteral := quittingStageCoalitionMass_literalOneDateProfile_eq_canonical
    reward currentProfile who stage ⟨routed, hrouted⟩ action
  have hmassUpdate : lambda ≤ quittingStageCoalitionMass reward
      (quittingLiteralOneDateProfile reward currentProfile who stage action) stage
      ⟨routed, hrouted⟩ := by
    rw [hmassLiteral]
    exact state.mass_floor.trans hmassCanonical
  by_cases hsingleton : routed.card = 1
  · left
    refine ⟨{
      who := who
      action := action
      action_eq_best := by
        rfl
      singleton := ⟨routed, hrouted⟩
      singleton_card := hsingleton
      routed := by
        change quittingPureEndpointRoutedCoalition state.coalition.1 who action =
          quittingPureEndpointRoutedCoalition state.coalition.1 who action
        rfl
      mass_le := by
        rw [hmassLiteral]
        exact hmassCanonical
    }⟩

  · have hnonsingleton : 1 < routed.card := by
      have hpos : 0 < routed.card := Finset.card_pos.mpr hrouted
      omega
    right
    let next : QuittingPartialPurificationState reward baseProfile stage lambda := {
      assignment := quittingPartialRootAssignmentUpdate state.assignment who action
      coalition := ⟨routed, hnonsingleton⟩
      mass_floor := by
        rw [show quittingLiteralPartialRootProfile reward baseProfile stage
            (quittingPartialRootAssignmentUpdate state.assignment who action) =
          quittingLiteralOneDateProfile reward currentProfile who stage action by
            exact (quittingLiteralPartialRootProfile_update_eq reward baseProfile stage
              state.assignment who action).symm]
        exact hmassUpdate
    }
    refine ⟨{
      action := action
      action_eq_best := by
        rfl
      next := next
      next_assignment := rfl
      next_coalition := by
        change quittingPureEndpointRoutedCoalition state.coalition.1 who action =
          quittingPureEndpointRoutedCoalition state.coalition.1 who action
        rfl
    }⟩

theorem quittingPartialPurification_exists_result
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (order : List ι) (hnodup : order.Nodup)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda) :
    (∃ state' : QuittingPartialPurificationState reward baseProfile stage lambda,
      Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda state')) ∨
      ∃ finalState : QuittingPartialPurificationState reward baseProfile stage lambda,
        ∀ who ∈ order, finalState.assignment who ≠ none := by
  induction order with
  | nil =>
      exact Or.inr ⟨state, by simp⟩
  | cons head tail ih =>
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      rcases ih htailNodup with hstop | ⟨tailState, hcomplete⟩
      · exact Or.inl hstop
      · rcases quittingPartialPurification_exists_step reward baseProfile stage lambda
          tailState head with hsingleton | hcarry
        · exact Or.inl ⟨tailState, hsingleton⟩
        · right
          obtain ⟨carry⟩ := hcarry
          refine ⟨carry.next, ?_⟩
          intro who hmem
          have hassign := carry.next_assignment
          rw [hassign]
          by_cases hhead : who = head
          · subst who
            simp [quittingPartialRootAssignmentUpdate]
          · have htailMem : who ∈ tail := by
              rcases (by simpa using hmem : who = head ∨ who ∈ tail) with hEq | hEq
              · exact False.elim (hhead hEq)
              · exact hEq
            have hnot : head ≠ who := Ne.symm hhead
            simpa [quittingPartialRootAssignmentUpdate, hnot, hhead] using
              hcomplete who htailMem

theorem quittingPartialPurification_exists_path_result
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (order : List ι) (hnodup : order.Nodup)
    (state : QuittingPartialPurificationState reward baseProfile stage lambda) :
    (∃ preState steps,
      Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda preState) ∧
        QuittingPartialPurificationPath reward baseProfile stage lambda state preState steps ∧
        steps ≤ order.length) ∨
      ∃ finalState steps,
        QuittingPartialPurificationPath reward baseProfile stage lambda state finalState steps ∧
          steps ≤ order.length ∧
          ∀ who ∈ order, finalState.assignment who ≠ none := by
  induction order with
  | nil =>
      right
      exact ⟨state, 0, .refl state, Nat.zero_le _, by simp⟩
  | cons head tail ih =>
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      rcases ih htailNodup with hstop |
          ⟨tailState, steps, hpath, hsteps, hcomplete⟩
      · rcases hstop with ⟨preState, steps, hsingleton, hpath, hsteps⟩
        left
        refine ⟨preState, steps, hsingleton, hpath, ?_⟩
        exact hsteps.trans (Nat.le_succ _)
      · rcases quittingPartialPurification_exists_step reward baseProfile stage lambda
          tailState head with hsingleton | hcarry
        · left
          exact ⟨tailState, steps, hsingleton, hpath,
            hsteps.trans (Nat.le_succ _)⟩
        · right
          obtain ⟨carry⟩ := hcarry
          refine ⟨carry.next, steps + 1,
            QuittingPartialPurificationPath.trans hpath
              (QuittingPartialPurificationPath.edge carry), ?_, ?_⟩
          · simp only [List.length_cons]
            omega
          · intro who hmem
            have hassign := carry.next_assignment
            rw [hassign]
            by_cases hhead : who = head
            · subst who
              simp [quittingPartialRootAssignmentUpdate]
            · have htailMem : who ∈ tail := by
                rcases (by simpa using hmem : who = head ∨ who ∈ tail) with hEq | hEq
                · exact False.elim (hhead hEq)
                · exact hEq
              have hnot : head ≠ who := Ne.symm hhead
              simpa [quittingPartialRootAssignmentUpdate, hnot, hhead] using
                hcomplete who htailMem

def quittingPartialPurificationInitialState
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    QuittingPartialPurificationState reward baseProfile stage lambda :=
  {
    assignment := fun _ => none
    coalition := coalition
    mass_floor := by
      change lambda ≤ quittingStageCoalitionMass reward baseProfile stage
        (quittingTerminalOfNonsingletonCoalition coalition)
      exact hmass
  }

omit [DecidableEq ι] in
theorem quittingLiteralPartialRootProfile_none_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) :
    quittingLiteralPartialRootProfile reward baseProfile stage (fun _ => none) = baseProfile := by
  funext who time history
  simp [quittingLiteralPartialRootProfile]

theorem quittingPartialPurificationInitialState_profile_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    quittingPartialPurificationStateProfile reward baseProfile stage lambda
        (quittingPartialPurificationInitialState reward baseProfile stage lambda coalition hmass) =
      baseProfile := by
  exact quittingLiteralPartialRootProfile_none_eq reward baseProfile stage

theorem quittingPartialPurificationInitialState_coalition_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    (quittingPartialPurificationInitialState reward baseProfile stage lambda
      coalition hmass).coalition =
      coalition := by
  rfl

theorem quittingPartialPurificationInitialState_terminal_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    quittingTerminalOfNonsingletonCoalition
        (quittingPartialPurificationInitialState reward baseProfile stage lambda
          coalition hmass).coalition =
      quittingTerminalOfNonsingletonCoalition coalition := by
  rw [quittingPartialPurificationInitialState_coalition_eq]

theorem quittingPartialPurification_initial_adapter
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    quittingPartialPurificationStateProfile reward baseProfile stage lambda
        (quittingPartialPurificationInitialState reward baseProfile stage lambda coalition hmass) =
        baseProfile ∧
      (quittingPartialPurificationInitialState reward baseProfile stage lambda
        coalition hmass).coalition =
        coalition ∧
      quittingTerminalOfNonsingletonCoalition
          (quittingPartialPurificationInitialState reward baseProfile stage lambda
            coalition hmass).coalition =
        quittingTerminalOfNonsingletonCoalition coalition := by
  exact ⟨quittingPartialPurificationInitialState_profile_eq reward baseProfile stage lambda
      coalition hmass,
    quittingPartialPurificationInitialState_coalition_eq reward baseProfile stage lambda
      coalition hmass,
    quittingPartialPurificationInitialState_terminal_eq reward baseProfile stage lambda
      coalition hmass⟩

theorem quittingPartialPurification_exists_total_or_singleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition)) :
    (∃ state steps,
      Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda state) ∧
        QuittingPartialPurificationPath reward baseProfile stage lambda
          (quittingPartialPurificationInitialState reward baseProfile stage lambda coalition hmass)
          state steps ∧
        steps ≤ Fintype.card ι) ∨
      ∃ finalState steps,
        QuittingPartialPurificationPath reward baseProfile stage lambda
            (quittingPartialPurificationInitialState reward baseProfile stage lambda
              coalition hmass)
            finalState steps ∧
        steps ≤ Fintype.card ι ∧
        (∀ who, finalState.assignment who ≠ none) ∧
        quittingLiteralPartialRootProfile reward baseProfile stage finalState.assignment =
          quittingLiteralPureRootProfile reward baseProfile stage
            (fun who => (finalState.assignment who).getD false) ∧
        quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPartialRootProfile reward baseProfile stage
                finalState.assignment) (stage + 1)) =
          quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward baseProfile (stage + 1)) := by
  let order := (Finset.univ : Finset ι).toList
  have hnodup : order.Nodup := by
    exact Finset.nodup_toList _
  have hcard : order.length ≤ Fintype.card ι := by
    simp [order]
  let initial := quittingPartialPurificationInitialState reward baseProfile stage lambda
    coalition hmass
  rcases quittingPartialPurification_exists_path_result reward baseProfile stage lambda
      order hnodup initial with hstop |
      ⟨finalState, steps, hpath, hsteps, hcomplete⟩
  · rcases hstop with ⟨state', steps, hsingleton, hpath, hsteps⟩
    exact Or.inl ⟨state', steps, hsingleton, hpath, hsteps.trans hcard⟩
  · right
    have hcomplete' : ∀ who, finalState.assignment who ≠ none := by
      intro who
      apply hcomplete who
      change who ∈ (Finset.univ : Finset ι).toList
      exact Finset.mem_toList.mpr (Finset.mem_univ who)
    refine ⟨finalState, steps, hpath, hsteps.trans hcard, hcomplete', ?_, ?_⟩
    · exact quittingLiteralPartialRootProfile_eq_total_of_complete
        reward baseProfile stage finalState.assignment
        (fun who => Option.ne_none_iff_exists'.mp (hcomplete' who))
    · rw [quittingLiteralPartialRootProfile_eq_total_of_complete
        reward baseProfile stage finalState.assignment
        (fun who => Option.ne_none_iff_exists'.mp (hcomplete' who))]
      exact quittingTerminalSemanticPair_spine_literalPureRoot_tail_eq reward baseProfile stage _

theorem quittingPartialPurification_then_sameStage_dispatch
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (minimum : QuittingTerminalSemanticPair ι)
    (baseProfile : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (lambda : ℝ)
    (coalition : QuittingNonsingletonCoalition ι)
    (hminimumCarrier : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumDebt : 0 < quittingTerminalSemanticDebtSum minimum)
    (hlambda : 0 < lambda)
    (hmass : lambda ≤ quittingStageCoalitionMass reward baseProfile stage
      (quittingTerminalOfNonsingletonCoalition coalition))
    (hlowTail : quittingSpineDebtExcess reward baseProfile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2) :
    (∃ state steps,
      Nonempty (QuittingPartialPurificationSingleton reward baseProfile stage lambda state) ∧
        QuittingPartialPurificationPath reward baseProfile stage lambda
          (quittingPartialPurificationInitialState reward baseProfile stage lambda coalition hmass)
          state steps ∧
        steps ≤ Fintype.card ι) ∨
      ∃ finalState steps,
        QuittingPartialPurificationPath reward baseProfile stage lambda
            (quittingPartialPurificationInitialState reward baseProfile stage lambda
              coalition hmass)
            finalState steps ∧
        steps ≤ Fintype.card ι ∧
        (∀ who, finalState.assignment who ≠ none) ∧
        ((Nonempty (MathUE.FiniteBooleanEndpointOrbit.DispatchedOrbit
          (QuittingSameStageSingletonRoute
            reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
              finalState) stage)
          (fun source target => Nonempty
            (QuittingSameStageEndpointEdge
              reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                finalState) stage minimum lambda source target))
          finalState.coalition)) ∨
          ∃ trace : MathUE.FiniteBooleanEndpointOrbit.DispatchedClosedSegment
              (QuittingSameStageSingletonRoute
                reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                  finalState) stage)
              (fun source target => Nonempty
                (QuittingSameStageEndpointEdge
                  reward (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                    finalState) stage minimum lambda source target))
              finalState.coalition,
            trace.segment.segment.period ≤
                2 ^ Fintype.card ι - Fintype.card ι - 1 ∧
            quittingLiteralPureRootCoalitionProfile reward
                (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                  finalState) stage
                (trace.orbit (trace.segment.segment.start + trace.segment.segment.period)) =
              quittingLiteralPureRootCoalitionProfile reward
                (quittingPartialPurificationStateProfile reward baseProfile stage lambda
                  finalState) stage
                (trace.orbit trace.segment.segment.start)) := by
  rcases quittingPartialPurification_exists_total_or_singleton reward baseProfile stage lambda
      coalition hmass with hstop |
      ⟨finalState, steps, hpath, hsteps, hcomplete, htotal, htail⟩
  · exact Or.inl hstop
  · right
    refine ⟨finalState, steps, hpath, hsteps, hcomplete, ?_⟩
    let finalProfile :=
      quittingPartialPurificationStateProfile reward baseProfile stage lambda finalState
    have hlowFinal : quittingSpineDebtExcess reward finalProfile
          (quittingTerminalSemanticDebtSum minimum) (stage + 1) <
        lambda * quittingTerminalSemanticDebtSum minimum / 2 := by
      unfold quittingSpineDebtExcess
      change quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (quittingLiteralPartialRootProfile reward baseProfile stage
                finalState.assignment) (stage + 1))) -
          quittingTerminalSemanticDebtSum minimum <
        lambda * quittingTerminalSemanticDebtSum minimum / 2
      rw [htail]
      exact hlowTail
    have hpost := exists_quittingSameStage_terminalRoute_or_closedSegment_of_sourceRow
      reward minimum finalProfile stage
        (quittingTerminalOfNonsingletonCoalition finalState.coalition) lambda
        hminimumCarrier hminimum hminimumDebt hlambda
        finalState.coalition.property finalState.mass_floor hlowFinal
    have hstart :
        (⟨(quittingTerminalOfNonsingletonCoalition finalState.coalition).val,
          finalState.coalition.property⟩ : QuittingNonsingletonCoalition ι) =
          finalState.coalition := by
      apply Subtype.ext
      rfl
    rw [hstart] at hpost
    simpa [finalProfile] using hpost

end GameTheory
