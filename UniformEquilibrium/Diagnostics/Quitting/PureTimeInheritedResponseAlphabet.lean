import UniformEquilibrium.Diagnostics.Quitting.PureTimeCapAttainment

/-!
# Inherited finite clock alphabets for exact pure-time responses

Against a pure-clock opponent profile, an unrestricted exact response can be
chosen from `Never`, date zero, or an opponent deadline.  Consequently a
finite alphabet containing every current clock and those two distinguished
responses is closed under exact one-player responses.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The finite response alphabet inherited from an initial pure-clock profile. -/
def quittingPureTimeInheritedResponseAlphabet
    (initial : QuittingPureTimeProfile ι) : Finset (Option ℕ) :=
  Finset.univ.image initial ∪ {none, some 0}

omit [DecidableEq ι] in
@[simp] theorem quittingPureTime_mem_inheritedResponseAlphabet
    (initial : QuittingPureTimeProfile ι) (who : ι) :
    initial who ∈ quittingPureTimeInheritedResponseAlphabet initial := by
  simp [quittingPureTimeInheritedResponseAlphabet]

omit [DecidableEq ι] in
@[simp] theorem quittingPureTime_never_mem_inheritedResponseAlphabet
    (initial : QuittingPureTimeProfile ι) :
    none ∈ quittingPureTimeInheritedResponseAlphabet initial := by
  simp [quittingPureTimeInheritedResponseAlphabet]

omit [DecidableEq ι] in
@[simp] theorem quittingPureTime_zero_mem_inheritedResponseAlphabet
    (initial : QuittingPureTimeProfile ι) :
    some 0 ∈ quittingPureTimeInheritedResponseAlphabet initial := by
  simp [quittingPureTimeInheritedResponseAlphabet]

omit [DecidableEq ι] in
theorem card_quittingPureTimeInheritedResponseAlphabet_le
    (initial : QuittingPureTimeProfile ι) :
    (quittingPureTimeInheritedResponseAlphabet initial).card ≤
      Fintype.card ι + 2 := by
  unfold quittingPureTimeInheritedResponseAlphabet
  calc
    (Finset.univ.image initial ∪ {none, some 0}).card ≤
        (Finset.univ.image initial).card + ({none, some 0} : Finset (Option ℕ)).card :=
      Finset.card_union_le _ _
    _ ≤ Fintype.card ι + 2 := by
      gcongr
      · exact Finset.card_image_le
      · simp

/-- An exact pure-time cap response can be selected from `Never`, date zero,
or the current opponents' earliest positive finite deadline. -/
theorem exists_quittingPureTime_capAttainer_eq_never_or_zero_or_earliestOpponentDeadline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) :
    ∃ response : Option ℕ,
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times who response)) who =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who ∧
      (response = none ∨ response = some 0 ∨
        ∃ deadline, 0 < deadline ∧ response = some deadline ∧
          (quittingPureTimeOpponentCoalitionAt times who deadline).Nonempty ∧
          ∀ time < deadline,
            quittingPureTimeOpponentCoalitionAt times who time = ∅) := by
  by_cases hsupport :
      (quittingPureTimeOpponentDeadlineSupport times who).Nonempty
  · obtain ⟨deadline, hat, hbefore⟩ :=
      exists_quittingPureTime_firstOpponentDeadline times who hsupport
    rcases Nat.eq_zero_or_pos deadline with rfl | hpositive
    · have hcap :=
        quittingContinuationBestResponseValue_pureTimeProfile_eq_max_two_at_zero
          reward times who hat
      by_cases hjoin :
          reward ⟨quittingPureTimeOpponentCoalitionAt times who 0, hat⟩ who ≤
            reward ⟨insert who
              (quittingPureTimeOpponentCoalitionAt times who 0),
              Finset.insert_nonempty who _⟩ who
      · refine ⟨some 0, ?_, Or.inr (Or.inl rfl)⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
            reward times who 0 hbefore,
          hcap, max_eq_left hjoin]
      · refine ⟨none, ?_, Or.inl rfl⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
            reward times who 0 hbefore hat,
          hcap, max_eq_right (le_of_not_ge hjoin)]
    · have hcap := quittingContinuationBestResponseValue_pureTimeProfile_eq_max_three
        reward times who deadline hpositive hbefore hat
      let singleton := reward (quittingSingletonTerminal who) who
      let join := reward ⟨insert who
        (quittingPureTimeOpponentCoalitionAt times who deadline),
        Finset.insert_nonempty who _⟩ who
      let pass := reward
        ⟨quittingPureTimeOpponentCoalitionAt times who deadline, hat⟩ who
      by_cases hsingle : max join pass ≤ singleton
      · refine ⟨some 0, ?_, Or.inr (Or.inl rfl)⟩
        rw [quittingPureTimeProfileBehavior_update,
          quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
            reward times who deadline 0 hbefore hpositive,
          hcap]
        change singleton = max singleton (max join pass)
        exact (max_eq_left hsingle).symm
      · by_cases hjoin : pass ≤ join
        · refine ⟨some deadline, ?_, Or.inr (Or.inr
            ⟨deadline, hpositive, rfl, hat, hbefore⟩)⟩
          rw [quittingPureTimeProfileBehavior_update,
            quittingTerminalPayoff_pureTimeProfile_update_at_eq_insert
              reward times who deadline hbefore,
            hcap]
          change join = max singleton (max join pass)
          rw [max_eq_left hjoin]
          have hnot : ¬join ≤ singleton := by
            intro hle
            exact hsingle (by simpa [max_eq_left hjoin] using hle)
          exact (max_eq_right (le_of_not_ge hnot)).symm
        · refine ⟨none, ?_, Or.inl rfl⟩
          rw [quittingPureTimeProfileBehavior_update,
            quittingTerminalPayoff_pureTimeProfile_update_never_eq_firstOpponent
              reward times who deadline hbefore hat,
            hcap]
          change pass = max singleton (max join pass)
          rw [max_eq_right (le_of_not_ge hjoin)]
          have hnot : ¬pass ≤ singleton := by
            intro hle
            exact hsingle (by
              simpa [max_eq_right (le_of_not_ge hjoin)] using hle)
          exact (max_eq_right (le_of_not_ge hnot)).symm
  · have hallNever : ∀ other, other ≠ who → times other = none := by
      intro other hne
      cases htime : times other with
      | none => rfl
      | some time =>
          exfalso
          apply hsupport
          exact ⟨time, (mem_quittingPureTimeOpponentDeadlineSupport_iff
            times who time).2 ⟨other, hne, htime⟩⟩
    have hprofileNever :
        quittingPureTimeProfileBehavior reward (Function.update times who none) =
          quittingAlwaysContinueProfile reward := by
      funext other
      by_cases heq : other = who
      · subst other
        rw [quittingPureTimeProfileBehavior_apply, Function.update_self,
          quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
        rfl
      · rw [quittingPureTimeProfileBehavior_apply, Function.update_of_ne heq,
          hallNever other heq,
          quittingPureTimeBehaviorStrategy_none_eq_alwaysContinue]
        rfl
    have hcap : quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who =
        max 0 (reward (quittingSingletonTerminal who) who) := by
      rw [← quittingContinuationBestResponseValue_update_self reward
        (quittingPureTimeProfileBehavior reward times) who
        (quittingPureTimeBehaviorStrategy reward who none),
        ← quittingPureTimeProfileBehavior_update, hprofileNever,
        quittingContinuationBestResponseValue_quittingAlwaysContinueProfile]
    by_cases hsolo : 0 ≤ reward (quittingSingletonTerminal who) who
    · refine ⟨some 0, ?_, Or.inr (Or.inl rfl)⟩
      have hpayoff : quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times who (some 0))) who =
          reward (quittingSingletonTerminal who) who := by
        rw [quittingPureTimeProfileBehavior_update]
        apply quittingTerminalPayoff_pureTimeProfile_update_early_eq_singleton
          reward times who 1 0
        · intro offset hoffset
          rw [show offset = 0 by omega]
          ext other
          constructor
          · intro hmem
            have hne : other ≠ who := (Finset.mem_erase.mp hmem).1
            have htime : times other = some 0 := by
              simpa [quittingPureTimeCoalitionAt] using
                (Finset.mem_erase.mp hmem).2
            rw [hallNever other hne] at htime
            simp at htime
          · intro hmem
            simp at hmem
        · omega
      rw [hpayoff, hcap, max_eq_right hsolo]
    · refine ⟨none, ?_, Or.inl rfl⟩
      rw [hprofileNever, quittingTerminalPayoff_quittingAlwaysContinue,
        hcap, max_eq_left (le_of_not_ge hsolo)]

/-- If every current clock lies in an inherited alphabet, an exact cap response
can be selected from that same alphabet. -/
theorem exists_quittingPureTime_capAttainer_mem_inheritedResponseAlphabet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (initial times : QuittingPureTimeProfile ι) (who : ι)
    (hclosed : ∀ other, times other ∈
      quittingPureTimeInheritedResponseAlphabet initial) :
    ∃ response ∈ quittingPureTimeInheritedResponseAlphabet initial,
      quittingTerminalPayoff reward
          (quittingPureTimeProfileBehavior reward
            (Function.update times who response)) who =
        quittingContinuationBestResponseValue reward
          (quittingPureTimeProfileBehavior reward times) who := by
  obtain ⟨response, hcap, hmenu⟩ :=
    exists_quittingPureTime_capAttainer_eq_never_or_zero_or_earliestOpponentDeadline
      reward times who
  refine ⟨response, ?_, hcap⟩
  rcases hmenu with rfl | rfl | ⟨deadline, _, rfl, hat, _⟩
  · exact quittingPureTime_never_mem_inheritedResponseAlphabet initial
  · exact quittingPureTime_zero_mem_inheritedResponseAlphabet initial
  · obtain ⟨other, hother⟩ := hat
    have htime : times other = some deadline := by
      simpa [quittingPureTimeCoalitionAt] using
        (Finset.mem_erase.mp hother).2
    rw [← htime]
    exact hclosed other

end GameTheory
