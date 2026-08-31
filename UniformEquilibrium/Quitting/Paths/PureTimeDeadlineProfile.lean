import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

/-!
# Canonical pure-time deadline profiles

This file contains the literal pure-time profile and its finite deadline
bookkeeping.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A canonical quitting profile is one pure finite quit date or `Never` per
player. -/
abbrev QuittingPureTimeProfile (ι : Type) := ι → Option ℕ

/-- Behavioral realization of a canonical pure-time profile. -/
def quittingPureTimeProfileBehavior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) :
    (quittingGame reward).BehaviorProfile :=
  fun who => quittingPureTimeBehaviorStrategy reward who (times who)

/-- The players whose canonical clock fires at one displayed date. -/
def quittingPureTimeCoalitionAt
    (times : QuittingPureTimeProfile ι) (time : ℕ) : Finset ι :=
  Finset.univ.filter fun who => times who = some time

/-- Opponents of one player whose canonical clock fires at a displayed date. -/
def quittingPureTimeOpponentCoalitionAt
    (times : QuittingPureTimeProfile ι) (who : ι) (time : ℕ) : Finset ι :=
  (quittingPureTimeCoalitionAt times time).erase who

/-- The finite set of dates used by a canonical profile; `Never` is omitted. -/
def quittingPureTimeDeadlineSupport (times : QuittingPureTimeProfile ι) :
    Finset ℕ :=
  Finset.univ.biUnion fun who => (times who).toFinset

omit [DecidableEq ι] in
@[simp] theorem mem_quittingPureTimeDeadlineSupport_iff
    (times : QuittingPureTimeProfile ι) (time : ℕ) :
    time ∈ quittingPureTimeDeadlineSupport times ↔
      ∃ who, times who = some time := by
  simp [quittingPureTimeDeadlineSupport]

/-- Finite dates used by the opponents of one displayed player. -/
def quittingPureTimeOpponentDeadlineSupport
    (times : QuittingPureTimeProfile ι) (who : ι) : Finset ℕ :=
  quittingPureTimeDeadlineSupport (Function.update times who none)

@[simp] theorem mem_quittingPureTimeOpponentDeadlineSupport_iff
    (times : QuittingPureTimeProfile ι) (who : ι) (time : ℕ) :
    time ∈ quittingPureTimeOpponentDeadlineSupport times who ↔
      ∃ other, other ≠ who ∧ times other = some time := by
  simp only [quittingPureTimeOpponentDeadlineSupport,
    mem_quittingPureTimeDeadlineSupport_iff]
  constructor
  · rintro ⟨other, hother⟩
    by_cases heq : other = who
    · subst other
      simp at hother
    · exact ⟨other, heq, by simpa [Function.update_of_ne heq] using hother⟩
  · rintro ⟨other, hne, hother⟩
    exact ⟨other, by simpa [Function.update_of_ne hne] using hother⟩

omit [DecidableEq ι] in
@[simp] theorem quittingPureTimeDeadlineSupport_all_never :
    quittingPureTimeDeadlineSupport (fun _ : ι => none) = ∅ := by
  ext time
  simp

/-- Natural-valued deadline rank. -/
def quittingPureTimeDeadlineRank (times : QuittingPureTimeProfile ι) : ℕ :=
  (quittingPureTimeDeadlineSupport times).card

omit [DecidableEq ι] in
theorem quittingPureTimeDeadlineRank_le_card
    (times : QuittingPureTimeProfile ι) :
    quittingPureTimeDeadlineRank times ≤ Fintype.card ι := by
  classical
  unfold quittingPureTimeDeadlineRank quittingPureTimeDeadlineSupport
  calc
    (Finset.univ.biUnion fun who : ι => (times who).toFinset).card ≤
        ∑ who : ι, (times who).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _who : ι, 1 := by
      apply Finset.sum_le_sum
      intro who _
      cases times who <;> simp
    _ = Fintype.card ι := by simp

omit [DecidableEq ι] in
@[simp] theorem quittingPureTimeProfileBehavior_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) :
    quittingPureTimeProfileBehavior reward times who =
      quittingPureTimeBehaviorStrategy reward who (times who) := rfl

theorem quittingPureTimeProfileBehavior_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (times : QuittingPureTimeProfile ι) (who : ι) (time : Option ℕ) :
    quittingPureTimeProfileBehavior reward (Function.update times who time) =
      Function.update (quittingPureTimeProfileBehavior reward times) who
        (quittingPureTimeBehaviorStrategy reward who time) := by
  funext other
  by_cases hother : other = who
  · subst other
    simp [quittingPureTimeProfileBehavior]
  · simp [quittingPureTimeProfileBehavior, hother]

/-- The coalition at one displayed date after replacing one player's pure
time.  This is literal unilateral ancestry bookkeeping. -/
theorem quittingPureTimeCoalitionAt_update
    (times : QuittingPureTimeProfile ι) (who : ι)
    (replacement : Option ℕ) (time : ℕ) :
    quittingPureTimeCoalitionAt (Function.update times who replacement) time =
      if replacement = some time then
        insert who ((quittingPureTimeCoalitionAt times time).erase who)
      else
        (quittingPureTimeCoalitionAt times time).erase who := by
  ext other
  by_cases hreplacement : replacement = some time
  · by_cases hother : other = who
    · subst other
      simp [quittingPureTimeCoalitionAt, hreplacement]
    · simp [quittingPureTimeCoalitionAt, hreplacement, hother]
  · by_cases hother : other = who
    · subst other
      simp [quittingPureTimeCoalitionAt, hreplacement]
    · simp [quittingPureTimeCoalitionAt, hreplacement, hother]

/-- Replacing the unique owner of a deadline by `Never`, or by a distinct
already-used deadline, erases exactly that deadline from the support. -/
theorem quittingPureTimeDeadlineSupport_update_eq_erase
    (times : QuittingPureTimeProfile ι) (owner : ι) (deadline : ℕ)
    (replacement : Option ℕ)
    (howner : times owner = some deadline)
    (hunique : ∀ other, times other = some deadline → other = owner)
    (hreplacement : replacement = none ∨
      ∃ other, other ≠ owner ∧ replacement = times other ∧
        replacement ≠ some deadline) :
    quittingPureTimeDeadlineSupport (Function.update times owner replacement) =
      (quittingPureTimeDeadlineSupport times).erase deadline := by
  ext time
  simp only [mem_quittingPureTimeDeadlineSupport_iff, Finset.mem_erase]
  constructor
  · rintro ⟨other, hother⟩
    by_cases heq : other = owner
    · subst other
      simp only [Function.update_self] at hother
      rcases hreplacement with rfl | ⟨source, hsourceNe, hreplacement, hne⟩
      · simp at hother
      · rw [hreplacement] at hother hne
        refine ⟨?_, ⟨source, hother⟩⟩
        intro htime
        subst time
        exact hne (by rw [hother])
    · rw [Function.update_of_ne heq] at hother
      refine ⟨?_, ⟨other, hother⟩⟩
      intro htime
      subst time
      exact heq (hunique other hother)
  · rintro ⟨htimeNe, other, hother⟩
    by_cases heq : other = owner
    · subst other
      rw [howner] at hother
      exact (htimeNe (Option.some.inj hother.symm)).elim
    · exact ⟨other, by simpa [Function.update_of_ne heq] using hother⟩

/-- The corresponding deadline rank drops strictly. -/
theorem quittingPureTimeDeadlineRank_update_lt
    (times : QuittingPureTimeProfile ι) (owner : ι) (deadline : ℕ)
    (replacement : Option ℕ)
    (howner : times owner = some deadline)
    (hunique : ∀ other, times other = some deadline → other = owner)
    (hreplacement : replacement = none ∨
      ∃ other, other ≠ owner ∧ replacement = times other ∧
        replacement ≠ some deadline) :
    quittingPureTimeDeadlineRank (Function.update times owner replacement) <
      quittingPureTimeDeadlineRank times := by
  have hmem : deadline ∈ quittingPureTimeDeadlineSupport times :=
    (mem_quittingPureTimeDeadlineSupport_iff times deadline).2 ⟨owner, howner⟩
  unfold quittingPureTimeDeadlineRank
  rw [quittingPureTimeDeadlineSupport_update_eq_erase times owner deadline
      replacement howner hunique hreplacement,
    Finset.card_erase_of_mem hmem]
  exact Nat.sub_lt (Finset.card_pos.mpr ⟨deadline, hmem⟩) Nat.zero_lt_one

end GameTheory
