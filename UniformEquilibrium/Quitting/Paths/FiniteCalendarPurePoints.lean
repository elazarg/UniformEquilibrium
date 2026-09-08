import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPayoff

/-!
# Literal pure points of the finite quitting calendar

The constructors below are points of the actual product of standard
simplices used by the finite-calendar raw payoff map.  All-Never has Never
mass one and zero prescribed payoff.  A nonempty coalition assigned one
common finite date has exactly that first-coalition mass one and receives its
literal reward row.  These statements concern prescribed masses and payoffs;
they make no claim about unilateral-deviation caps.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The deterministic product-simplex point attached to one timing action per
player. -/
def quittingFiniteCalendarPurePoint {deadline : ℕ}
    (action : ι → QuittingFiniteDeadlineTimingAction deadline) :
    MixedSimplex ι (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) :=
  fun who ↦ stdSimplex.pure (action who)

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteCalendarPurePoint_apply {deadline : ℕ}
    (action : ι → QuittingFiniteDeadlineTimingAction deadline)
    (who : ι) (choice : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteCalendarPurePoint action who choice =
      if choice = action who then 1 else 0 := by
  rfl

/-- The literal all-Never point on any finite calendar. -/
def quittingFiniteCalendarAllNeverPoint (deadline : ℕ) :
    MixedSimplex ι (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) :=
  quittingFiniteCalendarPurePoint fun _ ↦ none

/-- The literal point where precisely `coalition` stops at `date`, while all
other players choose Never.  For the empty coalition this is All-Never. -/
def quittingFiniteCalendarPureCoalitionPoint {deadline : ℕ}
    (coalition : Finset ι) (date : Fin deadline) :
    MixedSimplex ι (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) :=
  quittingFiniteCalendarPurePoint fun who ↦
    if who ∈ coalition then some date else none

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteCalendarAllNeverPoint_apply
    (deadline : ℕ) (who : ι)
    (choice : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteCalendarAllNeverPoint deadline who choice =
      if choice = none then 1 else 0 := by
  rfl

@[simp] theorem quittingFiniteCalendarPureCoalitionPoint_apply
    {deadline : ℕ} (coalition : Finset ι) (date : Fin deadline)
    (who : ι) (choice : QuittingFiniteDeadlineTimingAction deadline) :
    quittingFiniteCalendarPureCoalitionPoint coalition date who choice =
      if choice = (if who ∈ coalition then some date else none) then 1 else 0 := by
  rfl

theorem quittingFiniteCalendarPureCoalitionPoint_empty {deadline : ℕ}
    (date : Fin deadline) :
    quittingFiniteCalendarPureCoalitionPoint (∅ : Finset ι) date =
      quittingFiniteCalendarAllNeverPoint deadline := by
  rfl

omit [DecidableEq ι] in
@[simp] theorem quittingFiniteCalendarNeverMass_allNever (deadline : ℕ) :
    quittingFiniteCalendarNeverMass
      (quittingFiniteCalendarAllNeverPoint (ι := ι) deadline) = 1 := by
  unfold quittingFiniteCalendarNeverMass
  apply Finset.prod_eq_one
  intro who _
  rw [quittingFiniteCalendarAllNeverPoint_apply]
  simp

@[simp] theorem quittingFiniteCalendarCoalitionMass_allNever
    (deadline : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    quittingFiniteCalendarCoalitionMass
      (quittingFiniteCalendarAllNeverPoint (ι := ι) deadline) terminal = 0 := by
  unfold quittingFiniteCalendarCoalitionMass
  apply Finset.sum_eq_zero
  intro time _
  obtain ⟨who, hwho⟩ := terminal.property
  have hproduct :
      ∏ member ∈ terminal.val,
          quittingFiniteCalendarAllNeverPoint deadline member (some time) = 0 := by
    apply Finset.prod_eq_zero hwho
    simp
  rw [hproduct, zero_mul]

@[simp] theorem quittingFiniteCalendarRawPayoff_allNever
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ) :
    quittingFiniteCalendarRawPayoff reward deadline
      (quittingFiniteCalendarAllNeverPoint deadline) = 0 := by
  funext observer
  unfold quittingFiniteCalendarRawPayoff
  simp

private theorem strictTail_pureCoalition_of_notMem {deadline : ℕ}
    (coalition : Finset ι) (date time : Fin deadline)
    (who : ι) (hwho : who ∉ coalition) :
    quittingFiniteCalendarStrictTail
      (quittingFiniteCalendarPureCoalitionPoint coalition date) who time = 1 := by
  unfold quittingFiniteCalendarStrictTail
  simp only [quittingFiniteCalendarPureCoalitionPoint_apply]
  simp [hwho]

private theorem strictTail_pureCoalition_at_date_of_mem {deadline : ℕ}
    (coalition : Finset ι) (date : Fin deadline)
    (who : ι) (hwho : who ∈ coalition) :
    quittingFiniteCalendarStrictTail
      (quittingFiniteCalendarPureCoalitionPoint coalition date) who date = 0 := by
  unfold quittingFiniteCalendarStrictTail
  simp only [quittingFiniteCalendarPureCoalitionPoint_apply]
  simp [hwho]
  apply Finset.sum_eq_zero
  intro later _
  by_cases hlater : date < later
  · simp [hlater, ne_of_gt hlater]
  · simp [hlater]

/-- A nonempty pure coalition assigned a common date has its own coalition
mass exactly one. -/
@[simp] theorem quittingFiniteCalendarCoalitionMass_pureCoalition
    {deadline : ℕ} (coalition : Finset ι) (hcoalition : coalition.Nonempty)
    (date : Fin deadline) :
    quittingFiniteCalendarCoalitionMass
      (quittingFiniteCalendarPureCoalitionPoint coalition date)
        ⟨coalition, hcoalition⟩ = 1 := by
  unfold quittingFiniteCalendarCoalitionMass
  classical
  change (∑ time : Fin deadline,
    (∏ who ∈ coalition,
      quittingFiniteCalendarPureCoalitionPoint coalition date who (some time)) *
      ∏ who ∈ coalitionᶜ,
        quittingFiniteCalendarStrictTail
          (quittingFiniteCalendarPureCoalitionPoint coalition date) who time) = 1
  calc
    _ = ∑ time : Fin deadline, if time = date then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro time _
      by_cases htime : time = date
      · subst time
        simp only [if_pos]
        have hmembers :
            ∏ who ∈ coalition,
              quittingFiniteCalendarPureCoalitionPoint coalition date who
                (some date) = 1 := by
          apply Finset.prod_eq_one
          intro who hwho
          simp [hwho]
        have houtsiders :
            ∏ who ∈ coalitionᶜ,
              quittingFiniteCalendarStrictTail
                (quittingFiniteCalendarPureCoalitionPoint coalition date)
                  who date = 1 := by
          apply Finset.prod_eq_one
          intro who hwho
          exact strictTail_pureCoalition_of_notMem coalition date date who
            (by simpa using hwho)
        rw [hmembers, houtsiders, one_mul]
      · rw [if_neg htime]
        obtain ⟨who, hwho⟩ := hcoalition
        have hzero :
            quittingFiniteCalendarPureCoalitionPoint coalition date who
              (some time) = 0 := by
          simp [hwho, htime]
        have hproduct :
            ∏ member ∈ coalition,
              quittingFiniteCalendarPureCoalitionPoint coalition date member
                (some time) = 0 := by
          exact Finset.prod_eq_zero hwho hzero
        rw [hproduct, zero_mul]
    _ = 1 := by simp

/-- Every different first coalition has mass zero at a pure-coalition point. -/
theorem quittingFiniteCalendarCoalitionMass_pureCoalition_of_ne
    {deadline : ℕ} (coalition : Finset ι) (date : Fin deadline)
    (terminal : {S : Finset ι // S.Nonempty})
    (hne : terminal.val ≠ coalition) :
    quittingFiniteCalendarCoalitionMass
      (quittingFiniteCalendarPureCoalitionPoint coalition date) terminal = 0 := by
  unfold quittingFiniteCalendarCoalitionMass
  apply Finset.sum_eq_zero
  intro time _
  by_cases htime : time = date
  · subst time
    by_cases hsubset : terminal.val ⊆ coalition
    · have hnotSubset : ¬ coalition ⊆ terminal.val := by
        intro hreverse
        exact hne (Finset.Subset.antisymm hsubset hreverse)
      obtain ⟨who, hwhoCoalition, hwhoTerminal⟩ := Set.not_subset.mp hnotSubset
      have hcomplement : who ∈ terminal.valᶜ := by simpa using hwhoTerminal
      have htail : quittingFiniteCalendarStrictTail
          (quittingFiniteCalendarPureCoalitionPoint coalition date) who date = 0 :=
        strictTail_pureCoalition_at_date_of_mem coalition date who hwhoCoalition
      have hproduct :
          ∏ outsider ∈ terminal.valᶜ,
            quittingFiniteCalendarStrictTail
              (quittingFiniteCalendarPureCoalitionPoint coalition date)
                outsider date = 0 :=
        Finset.prod_eq_zero hcomplement htail
      rw [hproduct, mul_zero]
    · obtain ⟨who, hwhoTerminal, hwhoCoalition⟩ := Set.not_subset.mp hsubset
      have hpoint :
          quittingFiniteCalendarPureCoalitionPoint coalition date who
            (some date) = 0 := by
        have hnotMem : who ∉ coalition := hwhoCoalition
        simp [hnotMem]
      have hproduct :
          ∏ member ∈ terminal.val,
            quittingFiniteCalendarPureCoalitionPoint coalition date member
              (some date) = 0 :=
        Finset.prod_eq_zero hwhoTerminal hpoint
      rw [hproduct, zero_mul]
  · obtain ⟨who, hwho⟩ := terminal.property
    have hpoint :
        quittingFiniteCalendarPureCoalitionPoint coalition date who
          (some time) = 0 := by
      by_cases hwhoCoalition : who ∈ coalition
      · simp [hwhoCoalition, htime]
      · simp [hwhoCoalition]
    have hproduct :
        ∏ member ∈ terminal.val,
          quittingFiniteCalendarPureCoalitionPoint coalition date member
            (some time) = 0 :=
      Finset.prod_eq_zero hwho hpoint
    rw [hproduct, zero_mul]

/-- A nonempty pure coalition has Never mass zero. -/
@[simp] theorem quittingFiniteCalendarNeverMass_pureCoalition
    {deadline : ℕ} (coalition : Finset ι) (hcoalition : coalition.Nonempty)
    (date : Fin deadline) :
    quittingFiniteCalendarNeverMass
      (quittingFiniteCalendarPureCoalitionPoint coalition date) = 0 := by
  unfold quittingFiniteCalendarNeverMass
  obtain ⟨who, hwho⟩ := hcoalition
  apply Finset.prod_eq_zero (Finset.mem_univ who)
  simp [hwho]

/-- The raw payoff of a nonempty pure coalition point is its literal reward
row. -/
@[simp] theorem quittingFiniteCalendarRawPayoff_pureCoalition
    {deadline : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (coalition : Finset ι) (hcoalition : coalition.Nonempty)
    (date : Fin deadline) :
    quittingFiniteCalendarRawPayoff reward deadline
      (quittingFiniteCalendarPureCoalitionPoint coalition date) =
        reward ⟨coalition, hcoalition⟩ := by
  funext observer
  unfold quittingFiniteCalendarRawPayoff
  classical
  rw [Finset.sum_eq_single ⟨coalition, hcoalition⟩]
  · simp
  · intro terminal _ hterminal
    rw [quittingFiniteCalendarCoalitionMass_pureCoalition_of_ne]
    · simp
    · intro heq
      apply hterminal
      exact Subtype.ext heq
  · intro hnotMem
    exact (hnotMem (Finset.mem_univ _)).elim

namespace FinFourDateZero

/-- The packet's finite-calendar size for four players. -/
abbrev deadline : ℕ := 4 * (4 + 1)

def dateZero : Fin deadline := ⟨0, by norm_num⟩

def allNeverPoint :
    MixedSimplex (Fin 4)
      (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) :=
  quittingFiniteCalendarAllNeverPoint deadline

def pureCoalitionPoint (coalition : Finset (Fin 4)) :
    MixedSimplex (Fin 4)
      (fun _ ↦ QuittingFiniteDeadlineTimingAction deadline) :=
  quittingFiniteCalendarPureCoalitionPoint coalition dateZero

theorem allNeverPoint_neverMass :
    quittingFiniteCalendarNeverMass allNeverPoint = 1 := by
  exact quittingFiniteCalendarNeverMass_allNever deadline

theorem allNeverPoint_rawPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingFiniteCalendarRawPayoff reward deadline allNeverPoint = 0 := by
  exact quittingFiniteCalendarRawPayoff_allNever reward deadline

theorem pureCoalitionPoint_mass
    (coalition : Finset (Fin 4)) (hcoalition : coalition.Nonempty) :
    quittingFiniteCalendarCoalitionMass (pureCoalitionPoint coalition)
      ⟨coalition, hcoalition⟩ = 1 := by
  exact quittingFiniteCalendarCoalitionMass_pureCoalition
    coalition hcoalition dateZero

theorem pureCoalitionPoint_rawPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) (hcoalition : coalition.Nonempty) :
    quittingFiniteCalendarRawPayoff reward deadline
      (pureCoalitionPoint coalition) = reward ⟨coalition, hcoalition⟩ := by
  exact quittingFiniteCalendarRawPayoff_pureCoalition
    reward coalition hcoalition dateZero

end FinFourDateZero

end GameTheory
