import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalMixedLaw

/-!
# Shared deterministic response witnesses

The first coalition can be placed at any finite date. A singleton witness
additionally hides a passive coalition one date later, including the empty
passive family. These clocks and payoff identities serve both terminal
withdrawal converses without duplicating their outcome calculations.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem quietExtension_childCoalition_singleton (i : ι) :
    cappedClockChildCoalition {i} = {some i} := by
  simp [cappedClockChildCoalition]
  rfl

/-- Put exactly the specified coalition at one finite date. -/
def quietExtensionCoalitionTimes (A : Finset ι) (first : ℕ) (j : ι) : Option ℕ :=
  if j ∈ A then some first else none

omit [Nonempty ι] in
theorem quietExtensionCoalitionTimes_first (A : Finset ι) (hA : A.Nonempty)
    (first : ℕ) :
    quittingEarliestStoppingValue (quietExtensionCoalitionTimes A first) =
      (first : WithTop ℕ) := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hA
    have hle := Finset.inf_le (f := fun j =>
      quittingStoppingTimeValue (quietExtensionCoalitionTimes A first j))
      (Finset.mem_univ i)
    simpa [quittingEarliestStoppingValue, quietExtensionCoalitionTimes, hi,
      quittingStoppingTimeValue] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro j _
    by_cases hj : j ∈ A <;>
      simp [quietExtensionCoalitionTimes, hj, quittingStoppingTimeValue]

omit [Nonempty ι] in
theorem quietExtensionCoalitionTimes_coalition (A : Finset ι) (hA : A.Nonempty)
    (first : ℕ) :
    quittingEarliestStoppingCoalition (quietExtensionCoalitionTimes A first) = A := by
  ext j
  by_cases hj : j ∈ A <;>
    simp [quittingEarliestStoppingCoalition, quietExtensionCoalitionTimes_first A hA first,
      quietExtensionCoalitionTimes, hj, quittingStoppingTimeValue]

/-- A singleton first quitter and a possible passive coalition one date later. -/
def quietExtensionSingletonTimes (i : ι) (B : Finset ι) (first : ℕ)
    (j : ι) : Option ℕ :=
  if j = i then some first else if j ∈ B then some (first + 1) else none

omit [Nonempty ι] in
theorem quietExtensionSingletonTimes_first (i : ι) (B : Finset ι) (first : ℕ) :
    quittingEarliestStoppingValue (quietExtensionSingletonTimes i B first) =
      (first : WithTop ℕ) := by
  apply le_antisymm
  · have hle := Finset.inf_le (f := fun j =>
      quittingStoppingTimeValue (quietExtensionSingletonTimes i B first j))
      (Finset.mem_univ i)
    simpa [quittingEarliestStoppingValue, quietExtensionSingletonTimes,
      quittingStoppingTimeValue] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro j _
    by_cases hj : j = i
    · simp [quietExtensionSingletonTimes, hj, quittingStoppingTimeValue]
    · by_cases hjB : j ∈ B
      · simp only [quietExtensionSingletonTimes, hj, hjB, ↓reduceIte,
          quittingStoppingTimeValue]
        exact_mod_cast Nat.le_succ first
      · simp [quietExtensionSingletonTimes, hj, hjB, quittingStoppingTimeValue]

omit [Nonempty ι] in
theorem quietExtensionSingletonTimes_coalition (i : ι) (B : Finset ι) (first : ℕ) :
    quittingEarliestStoppingCoalition (quietExtensionSingletonTimes i B first) = {i} := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [quittingEarliestStoppingCoalition, quietExtensionSingletonTimes_first,
      quietExtensionSingletonTimes, quittingStoppingTimeValue]
  · by_cases hjB : j ∈ B <;>
      simp [quittingEarliestStoppingCoalition, quietExtensionSingletonTimes_first,
        quietExtensionSingletonTimes, quittingStoppingTimeValue, hj, hjB]

omit [Fintype ι] [Nonempty ι] in
theorem quietExtensionSingletonTimes_update (i : ι) (B : Finset ι) (first : ℕ)
    (hiB : i ∉ B) :
    Function.update (quietExtensionSingletonTimes i B first) i none =
      quietExtensionCoalitionTimes B (first + 1) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [quietExtensionCoalitionTimes, hiB]
  · simp [quietExtensionSingletonTimes, quietExtensionCoalitionTimes, hj]

omit [Fintype ι] [Nonempty ι] in
/-- Cancelling an owner's private clock is its literal Never update. -/
theorem quietExtensionPrivateClocks_cancel (times : ι → Option ℕ) (i : ι) :
    deadlinePrivateChildClocks times i none =
      quietParentClocks (Function.update times i none) := by
  funext player
  cases player with
  | none => rfl
  | some j => by_cases hj : j = i <;>
      simp [deadlinePrivateChildClocks, quietParentClocks, hj]

/-- A supplied first date and coalition determine the quiet terminal outcome. -/
theorem quietExtension_outcome_of_first
    (times : ι → Option ℕ) (first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) :
    quittingFirstStoppingOutcome (quietParentClocks times) =
      some ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ := by
  simpa only [hcoalition] using
    quittingFirstStoppingOutcome_quietParentClocks_of_first_eq times first hfirst

/-- A supplied first date and coalition determine every quiet terminal payoff. -/
theorem quietExtension_terminalPayoff_of_first
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) (who : Option ι) :
    quittingPureClockTerminalPayoff reward (quietParentClocks times) who =
      reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ who := by
  rw [quittingPureClockTerminalPayoff,
    quietExtension_outcome_of_first times first A hA hfirst hcoalition]

/-- Before child absorption, the outsider gains its singleton minus the old reward. -/
theorem quietExtension_outsideGain_of_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) (hbefore : time < first) :
    cappedClockActualOutsideGain reward times (some time) =
      reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none := by
  have hbefore' : (time : WithTop ℕ) < quittingEarliestStoppingValue times := by
    rw [hfirst]
    exact_mod_cast hbefore
  have houtcome := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    times time hbefore'
  rw [cappedClockActualOutsideGain,
    quietExtension_terminalPayoff_of_first reward times first A hA hfirst hcoalition none]
  simp only [quittingPureClockTerminalPayoff, houtcome]

/-- At a first-date tie, the outsider gains its joined reward minus the old reward. -/
theorem quietExtension_outsideGain_of_tie
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) :
    cappedClockActualOutsideGain reward times (some first) =
      reward ⟨cappedClockJoinedCoalition A, cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ none := by
  have houtcome := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
    times first hfirst
  rw [cappedClockActualOutsideGain,
    quietExtension_terminalPayoff_of_first reward times first A hA hfirst hcoalition none]
  simp only [quittingPureClockTerminalPayoff, houtcome, hcoalition]

/-- An advancing child before absorption quits alone. -/
theorem quietExtension_childGain_of_before
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (time first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) (hbefore : time < first)
    (i : ι) :
    cappedClockActualChildGain reward times (some time) i =
      reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some i)
        := by
  have hbefore' : (time : WithTop ℕ) < quittingEarliestStoppingValue times := by
    rw [hfirst]
    exact_mod_cast hbefore
  have houtcome := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    times time i hbefore'
  rw [cappedClockActualChildGain,
    quietExtension_terminalPayoff_of_first reward times first A hA hfirst hcoalition (some i)]
  simp only [quittingPureClockTerminalPayoff, houtcome]

/-- An advancing child at a tie joins the first child coalition. -/
theorem quietExtension_childGain_of_tie
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (first : ℕ) (A : Finset ι) (hA : A.Nonempty)
    (hfirst : quittingEarliestStoppingValue times = (first : WithTop ℕ))
    (hcoalition : quittingEarliestStoppingCoalition times = A) (i : ι) :
    cappedClockActualChildGain reward times (some first) i =
      reward ⟨cappedClockChildCoalition (insert i A),
          cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
        reward ⟨cappedClockChildCoalition A, cappedClockChildCoalition_nonempty hA⟩ (some i)
        := by
  have houtcome := quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
    times first i hfirst
  rw [cappedClockActualChildGain,
    quietExtension_terminalPayoff_of_first reward times first A hA hfirst hcoalition (some i)]
  simp only [quittingPureClockTerminalPayoff, houtcome, hcoalition]

/-- The joint-Never tuple tests the literal outside and advancing singleton rewards. -/
theorem quietExtension_allNeverGains
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) (time : ℕ) :
    cappedClockActualOutsideGain reward (fun _ => none) (some time) =
        reward ⟨{none}, Finset.singleton_nonempty none⟩ none ∧
      ∀ i, cappedClockActualChildGain reward (fun _ => none) (some time) i =
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) := by
  have hfirst : quittingEarliestStoppingValue (fun _ : ι => none) = ⊤ := by
    simp [quittingEarliestStoppingValue, quittingStoppingTimeValue]
  have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top
    (fun _ : ι => none) hfirst
  have houtside := quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    (fun _ : ι => none) time (by simp [hfirst])
  have hchild (i : ι) := quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    (fun _ : ι => none) time i (by simp [hfirst])
  constructor
  · simp [cappedClockActualOutsideGain, quittingPureClockTerminalPayoff, hquiet, houtside]
  · intro i
    simp [cappedClockActualChildGain, quittingPureClockTerminalPayoff, hquiet, hchild]

end GameTheory
