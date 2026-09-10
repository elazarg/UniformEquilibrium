import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition

/-!
# Raw capped-clock rows and deterministic pointwise domination

Reward-table inequalities imply domination of the outsider's gain by weighted
child gains under separate unilateral clock caps. Clocks are literal `Option Nat`
stopping times, with `none` meaning Never. The result covers nonnegative antitone
evaluations; passage to behavioral stopping laws is separate.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private def childPlayerEmbedding : ι ↪ Option ι where
  toFun := some
  inj' := Option.some_injective ι

/-- A child coalition as the literal parent coalition containing precisely its
`some`-labelled players. -/
def cappedClockChildCoalition (A : Finset ι) : Finset (Option ι) :=
  A.map childPlayerEmbedding

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem cappedClockChildCoalition_nonempty {A : Finset ι} (hA : A.Nonempty) :
    (cappedClockChildCoalition A).Nonempty := by
  exact Finset.map_nonempty.mpr hA

/-- The corresponding parent coalition after the outsider `none` joins. -/
def cappedClockJoinedCoalition (A : Finset ι) : Finset (Option ι) :=
  insert none (cappedClockChildCoalition A)

omit [Fintype ι] [Nonempty ι] in
theorem cappedClockJoinedCoalition_nonempty (A : Finset ι) :
    (cappedClockJoinedCoalition A).Nonempty := by
  exact ⟨none, Finset.mem_insert_self none _⟩

/-- Literal terminal payoff of a deterministic clock tuple, evaluated through
the repository's labelled first-stopping outcome. -/
def quittingPureClockTerminalPayoff
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (reward : {A : Finset κ // A.Nonempty} → κ → ℝ)
    (times : κ → Option ℕ) (who : κ) : ℝ :=
  match quittingFirstStoppingOutcome times with
  | none => 0
  | some A => reward A who

/-- Quietly embed child clocks into the literal parent: the outsider is
deterministically Never. -/
def quietParentClocks (times : ι → Option ℕ) : Option ι → Option ℕ
  | none => none
  | some i => times i

/-- Replace the quiet outsider's clock by one proposed finite-or-Never clock. -/
def outsideDeadlineClocks (times : ι → Option ℕ) (deadline : Option ℕ) :
    Option ι → Option ℕ
  | none => deadline
  | some i => times i

/-- Literal minimum of two finite-or-Never clocks. -/
def cappedStoppingClock (first second : Option ℕ) : Option ℕ :=
  if quittingStoppingTimeValue first ≤ quittingStoppingTimeValue second then first
  else second

/-- The separate child experiment that caps only child `i` by `deadline`, with
the outsider still prescribed Never. -/
def cappedChildParentClocks (times : ι → Option ℕ) (deadline : Option ℕ)
    (i : ι) : Option ι → Option ℕ
  | none => none
  | some j => if j = i then cappedStoppingClock (times j) deadline else times j

omit [DecidableEq ι] in
/-- Quiet embedding preserves the literal earliest clock. -/
theorem quittingEarliestStoppingValue_quietParentClocks
    (times : ι → Option ℕ) :
    quittingEarliestStoppingValue (quietParentClocks times) =
      quittingEarliestStoppingValue times := by
  apply le_antisymm
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf
      (Finset.univ : Finset ι) Finset.univ_nonempty
      (fun i => quittingStoppingTimeValue (times i))
    have hle := Finset.inf_le
      (f := fun player => quittingStoppingTimeValue (quietParentClocks times player))
      (Finset.mem_univ (some i))
    simpa [quittingEarliestStoppingValue, quietParentClocks, ← hi] using hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro player _
    cases player with
    | none => simp [quietParentClocks, quittingStoppingTimeValue]
    | some i =>
        simpa [quietParentClocks] using
          (Finset.inf_le
            (f := fun j => quittingStoppingTimeValue (times j))
            (Finset.mem_univ i))

omit [DecidableEq ι] in
theorem quittingEarliestStoppingValue_outsideDeadlineClocks
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    quittingEarliestStoppingValue (outsideDeadlineClocks times deadline) =
      min (quittingEarliestStoppingValue times)
        (quittingStoppingTimeValue deadline) := by
  apply le_antisymm
  · apply le_min
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf
        (Finset.univ : Finset ι) Finset.univ_nonempty
        (fun i => quittingStoppingTimeValue (times i))
      have hle := Finset.inf_le
        (f := fun player =>
          quittingStoppingTimeValue (outsideDeadlineClocks times deadline player))
        (Finset.mem_univ (some i))
      simpa [quittingEarliestStoppingValue, outsideDeadlineClocks, ← hi] using hle
    · simpa [quittingEarliestStoppingValue, outsideDeadlineClocks] using
        (Finset.inf_le
          (f := fun player =>
            quittingStoppingTimeValue (outsideDeadlineClocks times deadline player))
          (Finset.mem_univ none))
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro player _
    cases player with
    | none => simp [outsideDeadlineClocks]
    | some i =>
        exact (min_le_left _ _).trans
          (Finset.inf_le
            (f := fun j => quittingStoppingTimeValue (times j))
            (Finset.mem_univ i))

theorem quittingEarliestStoppingValue_cappedChildParentClocks
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) :
    quittingEarliestStoppingValue (cappedChildParentClocks times deadline i) =
      min (quittingEarliestStoppingValue times)
        (quittingStoppingTimeValue deadline) := by
  apply le_antisymm
  · apply le_min
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf
        (Finset.univ : Finset ι) Finset.univ_nonempty
        (fun j => quittingStoppingTimeValue (times j))
      have hle := Finset.inf_le
        (f := fun player => quittingStoppingTimeValue
          (cappedChildParentClocks times deadline i player))
        (Finset.mem_univ (some j))
      change quittingEarliestStoppingValue times =
        quittingStoppingTimeValue (times j) at hj
      by_cases hji : j = i
      · subst j
        rw [cappedChildParentClocks] at hle
        simp only [ite_true] at hle
        unfold cappedStoppingClock at hle
        by_cases hc : quittingStoppingTimeValue (times i) ≤
            quittingStoppingTimeValue deadline
        · rw [if_pos hc] at hle
          change quittingEarliestStoppingValue
              (cappedChildParentClocks times deadline i) ≤
            quittingStoppingTimeValue (times i) at hle
          rw [hj]
          exact hle
        · rw [if_neg hc] at hle
          change quittingEarliestStoppingValue
              (cappedChildParentClocks times deadline i) ≤
            quittingStoppingTimeValue deadline at hle
          rw [hj]
          exact hle.trans (le_of_not_ge hc)
      · simpa [quittingEarliestStoppingValue, cappedChildParentClocks,
          hji, ← hj] using hle
    · have hle := Finset.inf_le
        (f := fun player => quittingStoppingTimeValue
          (cappedChildParentClocks times deadline i player))
        (Finset.mem_univ (some i))
      rw [cappedChildParentClocks] at hle
      simp only [ite_true] at hle
      unfold cappedStoppingClock at hle
      by_cases hc : quittingStoppingTimeValue (times i) ≤
          quittingStoppingTimeValue deadline
      · rw [if_pos hc] at hle
        change quittingEarliestStoppingValue
            (cappedChildParentClocks times deadline i) ≤
          quittingStoppingTimeValue (times i) at hle
        exact hle.trans hc
      · rw [if_neg hc] at hle
        change quittingEarliestStoppingValue
            (cappedChildParentClocks times deadline i) ≤
          quittingStoppingTimeValue deadline at hle
        exact hle
  · unfold quittingEarliestStoppingValue
    apply Finset.le_inf
    intro player _
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some j =>
        by_cases hji : j = i
        · subst j
          simp only [cappedChildParentClocks, if_true]
          unfold cappedStoppingClock
          split_ifs
          · exact (min_le_left _ _).trans
              (Finset.inf_le (Finset.mem_univ i))
          · exact min_le_right _ _
        · simp only [cappedChildParentClocks, hji, if_false]
          exact (min_le_left _ _).trans
            (Finset.inf_le (Finset.mem_univ j))

private theorem stoppingTime_eq_some_of_value_eq
    {clock : Option ℕ} {time : ℕ}
    (h : quittingStoppingTimeValue clock = (time : WithTop ℕ)) :
    clock = some time := by
  cases clock with
  | none => simp [quittingStoppingTimeValue] at h
  | some clockTime =>
      simp only [quittingStoppingTimeValue] at h
      exact congrArg some (WithTop.coe_eq_coe.mp h)

omit [DecidableEq ι] [Nonempty ι] in
private theorem first_le_stoppingTimeValue
    (times : ι → Option ℕ) (i : ι) :
    quittingEarliestStoppingValue times ≤ quittingStoppingTimeValue (times i) := by
  exact Finset.inf_le (Finset.mem_univ i)

/-- Finite quiet child absorption becomes the corresponding literal parent
coalition; the outsider remains strictly later at Never. -/
theorem quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
    (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    quittingFirstStoppingOutcome (quietParentClocks times) =
      some ⟨cappedClockChildCoalition
          (quittingEarliestStoppingCoalition times),
        cappedClockChildCoalition_nonempty
          (quittingEarliestStoppingCoalition_nonempty times)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
  · intro player hplayer
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hplayer
    apply stoppingTime_eq_some_of_value_eq
    change quittingStoppingTimeValue (times i) = (time : WithTop ℕ)
    simpa [quittingEarliestStoppingCoalition, hfirst] using hi
  · intro player hplayer
    cases player with
    | none => simp [quietParentClocks, quittingStoppingTimeValue]
    | some i =>
        have hi : i ∉ quittingEarliestStoppingCoalition times := by
          intro hi
          apply hplayer
          exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
        have hne : quittingStoppingTimeValue (times i) ≠ (time : WithTop ℕ) := by
          simpa [quittingEarliestStoppingCoalition, hfirst] using hi
        have hle : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times i) := by
          rw [← hfirst]
          exact first_le_stoppingTimeValue times i
        simpa [quietParentClocks, quittingStoppingTimeValue] using
          lt_of_le_of_ne hle hne.symm

/-- An outsider deadline strictly before the child first clock produces the
literal outsider singleton outcome. -/
theorem quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
    (times : ι → Option ℕ) (time : ℕ)
    (hbefore : (time : WithTop ℕ) < quittingEarliestStoppingValue times) :
    quittingFirstStoppingOutcome (outsideDeadlineClocks times (some time)) =
      some ⟨{none}, Finset.singleton_nonempty none⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
  · intro player hplayer
    simp only [Finset.mem_singleton] at hplayer
    subst player
    rfl
  · intro player hplayer
    cases player with
    | none => simp at hplayer
    | some i =>
        have hle := first_le_stoppingTimeValue times i
        exact hbefore.trans_le hle

/-- A deadline tied with the child first clock joins the literal first child
coalition. -/
theorem quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
    (times : ι → Option ℕ) (time : ℕ)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    quittingFirstStoppingOutcome (outsideDeadlineClocks times (some time)) =
      some ⟨cappedClockJoinedCoalition
          (quittingEarliestStoppingCoalition times),
        cappedClockJoinedCoalition_nonempty _⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
  · intro player hplayer
    cases player with
    | none => rfl
    | some i =>
        have hm : some i ∈ cappedClockChildCoalition
            (quittingEarliestStoppingCoalition times) := by
          simpa [cappedClockJoinedCoalition] using hplayer
        obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hm
        have hi : i ∈ quittingEarliestStoppingCoalition times := by
          have : j = i := Option.some.inj (by
            simpa [childPlayerEmbedding] using hji)
          simpa [this] using hj
        apply stoppingTime_eq_some_of_value_eq
        change quittingStoppingTimeValue (times i) = (time : WithTop ℕ)
        simpa [quittingEarliestStoppingCoalition, hfirst] using hi
  · intro player hplayer
    cases player with
    | none => exact (hplayer (Finset.mem_insert_self none _)).elim
    | some i =>
        have hi : i ∉ quittingEarliestStoppingCoalition times := by
          intro hi
          apply hplayer
          apply Finset.mem_insert_of_mem
          exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
        have hne : quittingStoppingTimeValue (times i) ≠ (time : WithTop ℕ) := by
          simpa [quittingEarliestStoppingCoalition, hfirst] using hi
        have hle : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times i) := by
          rw [← hfirst]
          exact first_le_stoppingTimeValue times i
        exact lt_of_le_of_ne hle hne.symm

/-- An outsider clock strictly after the child first clock leaves the literal
parent outcome unchanged. -/
theorem quittingFirstStoppingOutcome_outsideDeadlineClocks_of_first_lt
    (times : ι → Option ℕ) (deadline : ℕ)
    (hafter : quittingEarliestStoppingValue times <
      (deadline : WithTop ℕ)) :
    quittingFirstStoppingOutcome (outsideDeadlineClocks times (some deadline)) =
      quittingFirstStoppingOutcome (quietParentClocks times) := by
  let A := quittingEarliestStoppingCoalition times
  have hA : A.Nonempty := quittingEarliestStoppingCoalition_nonempty times
  let blocker := hA.choose
  have hblocker : blocker ∈ A := hA.choose_spec
  apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
    (first := outsideDeadlineClocks times (some deadline))
    (second := quietParentClocks times) (hidden := none)
    (blocker := some blocker)
  · intro other hother
    cases other with
    | none => exact (hother rfl).elim
    | some j => rfl
  · have hvalue : quittingStoppingTimeValue (times blocker) =
        quittingEarliestStoppingValue times := by
      simpa [A, quittingEarliestStoppingCoalition] using hblocker
    change quittingStoppingTimeValue (times blocker) <
      quittingStoppingTimeValue (some deadline)
    rw [hvalue]
    simpa [quittingStoppingTimeValue] using hafter
  · have hvalue : quittingStoppingTimeValue (times blocker) =
        quittingEarliestStoppingValue times := by
      simpa [A, quittingEarliestStoppingCoalition] using hblocker
    change quittingStoppingTimeValue (times blocker) <
      quittingStoppingTimeValue none
    rw [hvalue]
    exact hafter.trans (by simp [quittingStoppingTimeValue])

/-- Capping one child strictly before the original child first clock produces
that child's singleton parent outcome. -/
theorem quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hbefore : (time : WithTop ℕ) < quittingEarliestStoppingValue times) :
    quittingFirstStoppingOutcome
        (cappedChildParentClocks times (some time) i) =
      some ⟨{some i}, Finset.singleton_nonempty (some i)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
  · intro player hplayer
    simp only [Finset.mem_singleton] at hplayer
    subst player
    have hlt : (time : WithTop ℕ) < quittingStoppingTimeValue (times i) :=
      hbefore.trans_le (first_le_stoppingTimeValue times i)
    have hnle : ¬quittingStoppingTimeValue (times i) ≤ (time : WithTop ℕ) :=
      not_le.mpr hlt
    have hnle' : ¬quittingStoppingTimeValue (times i) ≤
        quittingStoppingTimeValue (some time) := by
      simpa [quittingStoppingTimeValue] using hnle
    rw [cappedChildParentClocks]
    simp only [ite_true]
    unfold cappedStoppingClock
    rw [if_neg hnle']
  · intro player hplayer
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some j =>
        have hji : j ≠ i := by
          intro h
          subst j
          exact hplayer (Finset.mem_singleton_self (some i))
        simp only [cappedChildParentClocks, hji, ↓reduceIte]
        exact hbefore.trans_le (first_le_stoppingTimeValue times j)

/-- Capping at the original first date adds the capped child to the first
child coalition (and is idempotent when it was already a member). -/
theorem quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
    (times : ι → Option ℕ) (time : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times = (time : WithTop ℕ)) :
    quittingFirstStoppingOutcome
        (cappedChildParentClocks times (some time) i) =
      some ⟨cappedClockChildCoalition
          (insert i (quittingEarliestStoppingCoalition times)),
        cappedClockChildCoalition_nonempty (Finset.insert_nonempty _ _)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := time)
  · intro player hplayer
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hplayer
    simp only [Finset.mem_insert] at hj
    rcases hj with hji | hj
    · subst j
      have hge : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times i) := by
        rw [← hfirst]
        exact first_le_stoppingTimeValue times i
      change cappedChildParentClocks times (some time) i (some i) = some time
      rw [cappedChildParentClocks]
      simp only [ite_true]
      unfold cappedStoppingClock
      by_cases hle : quittingStoppingTimeValue (times i) ≤
          quittingStoppingTimeValue (some time)
      · rw [if_pos hle]
        apply stoppingTime_eq_some_of_value_eq
        exact le_antisymm (by simpa [quittingStoppingTimeValue] using hle) hge
      · rw [if_neg hle]
    · have hclock : times j = some time := by
        apply stoppingTime_eq_some_of_value_eq
        simpa [quittingEarliestStoppingCoalition, hfirst] using hj
      by_cases hji : j = i
      · subst j
        change cappedChildParentClocks times (some time) i (some i) = some time
        rw [cappedChildParentClocks]
        simp only [ite_true]
        simp [cappedStoppingClock, hclock,
          quittingStoppingTimeValue]
      · change (if j = i then cappedStoppingClock (times j) (some time)
          else times j) = some time
        simp [hji, hclock]
  · intro player hplayer
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some j =>
        have hji : j ≠ i := by
          intro h
          subst j
          apply hplayer
          exact Finset.mem_map.mpr ⟨i, Finset.mem_insert_self i _, rfl⟩
        have hj : j ∉ quittingEarliestStoppingCoalition times := by
          intro hj
          apply hplayer
          exact Finset.mem_map.mpr ⟨j, Finset.mem_insert_of_mem hj, rfl⟩
        have hne : quittingStoppingTimeValue (times j) ≠ (time : WithTop ℕ) := by
          simpa [quittingEarliestStoppingCoalition, hfirst] using hj
        have hle : (time : WithTop ℕ) ≤ quittingStoppingTimeValue (times j) := by
          rw [← hfirst]
          exact first_le_stoppingTimeValue times j
        simp only [cappedChildParentClocks, hji, ↓reduceIte]
        exact lt_of_le_of_ne hle hne.symm

/-- A child cap strictly after finite child absorption preserves the literal
first parent coalition. -/
theorem quittingFirstStoppingOutcome_cappedChildParentClocks_of_first_lt
    (times : ι → Option ℕ) (firstTime deadline : ℕ) (i : ι)
    (hfirst : quittingEarliestStoppingValue times =
      (firstTime : WithTop ℕ))
    (hafter : (firstTime : WithTop ℕ) < (deadline : WithTop ℕ)) :
    quittingFirstStoppingOutcome
        (cappedChildParentClocks times (some deadline) i) =
      some ⟨cappedClockChildCoalition
          (quittingEarliestStoppingCoalition times),
        cappedClockChildCoalition_nonempty
          (quittingEarliestStoppingCoalition_nonempty times)⟩ := by
  apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
      (time := firstTime)
  · intro player hplayer
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hplayer
    have hclock : times j = some firstTime := by
      apply stoppingTime_eq_some_of_value_eq
      simpa [quittingEarliestStoppingCoalition, hfirst] using hj
    change (if j = i then cappedStoppingClock (times j) (some deadline)
      else times j) = some firstTime
    by_cases hji : j = i
    · subst j
      simp only [if_true, hclock]
      unfold cappedStoppingClock
      have hle : quittingStoppingTimeValue (some firstTime) ≤
          quittingStoppingTimeValue (some deadline) := by
        simpa [quittingStoppingTimeValue] using hafter.le
      rw [if_pos hle]
    · simp [hji, hclock]
  · intro player hplayer
    cases player with
    | none => simp [cappedChildParentClocks, quittingStoppingTimeValue]
    | some j =>
        have hj : j ∉ quittingEarliestStoppingCoalition times := by
          intro hj
          apply hplayer
          exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
        have hne : quittingStoppingTimeValue (times j) ≠
            (firstTime : WithTop ℕ) := by
          simpa [quittingEarliestStoppingCoalition, hfirst] using hj
        have hclockAfter : (firstTime : WithTop ℕ) <
            quittingStoppingTimeValue (times j) := by
          apply lt_of_le_of_ne
          · rw [← hfirst]
            exact first_le_stoppingTimeValue times j
          · exact hne.symm
        change quittingStoppingTimeValue
            (if j = i then cappedStoppingClock (times j) (some deadline)
              else times j) > (firstTime : WithTop ℕ)
        by_cases hji : j = i
        · subst j
          simp only [if_true]
          unfold cappedStoppingClock
          split_ifs <;> simp only [quittingStoppingTimeValue]
          · exact hclockAfter
          · exact hafter
        · simp [hji]
          exact hclockAfter

omit [DecidableEq ι] [Nonempty ι] in
private theorem all_never_of_earliest_eq_top
    (times : ι → Option ℕ)
    (hfirst : quittingEarliestStoppingValue times = ⊤) :
    times = fun _ => none := by
  funext i
  have htop : quittingStoppingTimeValue (times i) = ⊤ := by
    apply top_unique
    rw [← hfirst]
    exact first_le_stoppingTimeValue times i
  cases h : times i with
  | none => rfl
  | some time => simp [h, quittingStoppingTimeValue] at htop

omit [DecidableEq ι] in
/-- Joint child Never is literal joint parent Never under the quiet lift. -/
theorem quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top
    (times : ι → Option ℕ)
    (hfirst : quittingEarliestStoppingValue times = ⊤) :
    quittingFirstStoppingOutcome (quietParentClocks times) = none := by
  have hall := all_never_of_earliest_eq_top times hfirst
  rw [hall]
  have hparent : quietParentClocks (fun _ : ι => none) =
      fun _ : Option ι => none := by
    funext player
    cases player <;> rfl
  rw [hparent]
  exact quittingFirstStoppingOutcome_all_never

/-- Reward inequalities for joint Never, a deadline before future absorption,
and a deadline joining the first coalition, all read from one parent table. -/
structure CappedClockParentRewardCertificate
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ) where
  weight : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  never_row :
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none ≤
      ∑ i, weight i *
        reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i)
  future_row : ∀ A (hA : A.Nonempty),
    reward ⟨{none}, Finset.singleton_nonempty none⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, weight i *
        (reward ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))
  join_row : ∀ A (hA : A.Nonempty),
    reward ⟨cappedClockJoinedCoalition A,
          cappedClockJoinedCoalition_nonempty A⟩ none -
        reward ⟨cappedClockChildCoalition A,
          cappedClockChildCoalition_nonempty hA⟩ none ≤
      ∑ i, weight i *
        (reward ⟨cappedClockChildCoalition (insert i A),
            cappedClockChildCoalition_nonempty (Finset.insert_nonempty i A)⟩ (some i) -
          reward ⟨cappedClockChildCoalition A,
            cappedClockChildCoalition_nonempty hA⟩ (some i))

/-- Literal outsider payoff gain from replacing quiet Never by `deadline`. -/
def cappedClockActualOutsideGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) : ℝ :=
  quittingPureClockTerminalPayoff reward
      (outsideDeadlineClocks times deadline) none -
    quittingPureClockTerminalPayoff reward (quietParentClocks times) none

/-- Literal payoff gain in the separate experiment capping child `i`. -/
def cappedClockActualChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  quittingPureClockTerminalPayoff reward
      (cappedChildParentClocks times deadline i) (some i) -
    quittingPureClockTerminalPayoff reward (quietParentClocks times) (some i)

/-- Literal evaluated payoff of a deterministic clock tuple.  The evaluation
is applied to the actual earliest clock retained alongside the labelled
terminal outcome. -/
def quittingPureClockEvaluatedPayoff
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (reward : {A : Finset κ // A.Nonempty} → κ → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : κ → Option ℕ) (who : κ) : ℝ :=
  match quittingFirstStoppingOutcome times with
  | none => 0
  | some A => evaluation (quittingEarliestStoppingValue times) * reward A who

/-- Literal evaluated outsider gain from replacing quiet Never. -/
def cappedClockActualEvaluatedOutsideGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) : ℝ :=
  quittingPureClockEvaluatedPayoff reward evaluation
      (outsideDeadlineClocks times deadline) none -
    quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks times) none

/-- Literal evaluated gain in the separate experiment capping child `i`. -/
def cappedClockActualEvaluatedChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (evaluation : WithTop ℕ → ℝ)
    (times : ι → Option ℕ) (deadline : Option ℕ) (i : ι) : ℝ :=
  quittingPureClockEvaluatedPayoff reward evaluation
      (cappedChildParentClocks times deadline i) (some i) -
    quittingPureClockEvaluatedPayoff reward evaluation
      (quietParentClocks times) (some i)

omit [DecidableEq ι] [Nonempty ι] in
private theorem actual_evaluated_future_row
    (weight singleton childReward : ι → ℝ)
    (outsideSingleton outsideReward earlyWeight lateWeight : ℝ)
    (hLateNonneg : 0 ≤ lateWeight) (hWeight : lateWeight ≤ earlyWeight)
    (hNever : outsideSingleton ≤ ∑ i, weight i * singleton i)
    (hFuture : outsideSingleton - outsideReward ≤
      ∑ i, weight i * (singleton i - childReward i)) :
    earlyWeight * outsideSingleton - lateWeight * outsideReward ≤
      ∑ i, weight i *
        (earlyWeight * singleton i - lateWeight * childReward i) := by
  have hNeverResidual : outsideSingleton - ∑ i, weight i * singleton i ≤ 0 :=
    sub_nonpos.mpr hNever
  have hFutureResidual : outsideSingleton - outsideReward -
      ∑ i, weight i * (singleton i - childReward i) ≤ 0 := sub_nonpos.mpr hFuture
  have hFirst := mul_nonpos_of_nonneg_of_nonpos
    (sub_nonneg.mpr hWeight) hNeverResidual
  have hSecond := mul_nonpos_of_nonneg_of_nonpos hLateNonneg hFutureResidual
  have sum_weight_mul (factor : ℝ) (value : ι → ℝ) :
      (∑ i, weight i * (factor * value i)) =
        factor * ∑ i, weight i * value i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have sum_weight_sub (first second : ι → ℝ) :
      (∑ i, weight i * (first i - second i)) =
        (∑ i, weight i * first i) - ∑ i, weight i * second i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  apply sub_nonpos.mp
  calc
    earlyWeight * outsideSingleton - lateWeight * outsideReward -
          ∑ i, weight i *
            (earlyWeight * singleton i - lateWeight * childReward i) =
        (earlyWeight - lateWeight) *
            (outsideSingleton - ∑ i, weight i * singleton i) +
          lateWeight * (outsideSingleton - outsideReward -
            ∑ i, weight i * (singleton i - childReward i)) := by
              rw [sum_weight_sub, sum_weight_sub, sum_weight_mul, sum_weight_mul]
              ring
    _ ≤ 0 := add_nonpos hFirst hSecond

/-- Literal evaluated pointwise domination for the parent table. -/
theorem cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (evaluation : WithTop ℕ → ℝ)
    (evaluation_nonneg : ∀ clock, 0 ≤ evaluation clock)
    (evaluation_antitone : Antitone evaluation)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualEvaluatedOutsideGain reward evaluation times deadline ≤
      ∑ i, certificate.weight i *
        cappedClockActualEvaluatedChildGain reward evaluation times deadline i := by
  cases deadline with
  | none =>
      have houtside : outsideDeadlineClocks times none = quietParentClocks times := by
        funext player
        cases player <;> rfl
      have hchild (i : ι) :
          cappedChildParentClocks times none i = quietParentClocks times := by
        funext player
        cases player with
        | none => rfl
        | some j =>
            by_cases hji : j = i
            · subst j
              simp [cappedChildParentClocks, cappedStoppingClock,
                quietParentClocks, quittingStoppingTimeValue]
            · simp [cappedChildParentClocks, quietParentClocks, hji]
      simp [cappedClockActualEvaluatedOutsideGain,
        cappedClockActualEvaluatedChildGain, houtside, hchild]
  | some deadline =>
      let first := quittingEarliestStoppingValue times
      have hquietFirst := quittingEarliestStoppingValue_quietParentClocks times
      have houtsideFirst :=
        quittingEarliestStoppingValue_outsideDeadlineClocks times (some deadline)
      have hcapFirst (i : ι) :=
        quittingEarliestStoppingValue_cappedChildParentClocks times (some deadline) i
      by_cases hafter : first < (deadline : WithTop ℕ)
      · have houtcome :=
          quittingFirstStoppingOutcome_outsideDeadlineClocks_of_first_lt
            times deadline hafter
        induction hfirst : first using WithTop.recTopCoe with
        | top =>
            rw [hfirst] at hafter
            exact (not_lt_of_ge le_top hafter).elim
        | coe firstTime =>
            have hfirst' : quittingEarliestStoppingValue times =
                (firstTime : WithTop ℕ) := by simpa [first] using hfirst
            have hafter' : (firstTime : WithTop ℕ) <
                (deadline : WithTop ℕ) := by simpa [hfirst] using hafter
            have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
              times firstTime hfirst'
            have hcap (i : ι) :=
              quittingFirstStoppingOutcome_cappedChildParentClocks_of_first_lt
                times firstTime deadline i hfirst' hafter'
            simp [cappedClockActualEvaluatedOutsideGain,
              cappedClockActualEvaluatedChildGain,
              quittingPureClockEvaluatedPayoff, houtcome, hquiet, hcap,
              hquietFirst, houtsideFirst, hcapFirst, first, hfirst,
              quittingStoppingTimeValue, min_eq_left hafter'.le]
      · by_cases htie : first = (deadline : WithTop ℕ)
        · have hfirst' : quittingEarliestStoppingValue times =
              (deadline : WithTop ℕ) := by simpa [first] using htie
          have hquiet := quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
            times deadline hfirst'
          have houtcome :=
            quittingFirstStoppingOutcome_outsideDeadlineClocks_of_eq_first
              times deadline hfirst'
          have hcap (i : ι) :=
            quittingFirstStoppingOutcome_cappedChildParentClocks_of_eq_first
              times deadline i hfirst'
          have hrow := mul_le_mul_of_nonneg_left
            (certificate.join_row (quittingEarliestStoppingCoalition times)
              (quittingEarliestStoppingCoalition_nonempty times))
            (evaluation_nonneg first)
          rw [Finset.mul_sum] at hrow
          simpa [cappedClockActualEvaluatedOutsideGain,
            cappedClockActualEvaluatedChildGain,
            quittingPureClockEvaluatedPayoff, hquiet, houtcome, hcap,
            hquietFirst, houtsideFirst, hcapFirst, first, htie,
            quittingStoppingTimeValue, mul_sub, mul_assoc, mul_left_comm] using hrow
        · have hdeadline_lt : (deadline : WithTop ℕ) < first :=
            lt_of_le_of_ne (le_of_not_gt hafter) (fun h => htie h.symm)
          induction hfirst : first using WithTop.recTopCoe with
          | top =>
              have htop : quittingEarliestStoppingValue times = ⊤ := by
                simpa [first] using hfirst
              have hquiet :=
                quittingFirstStoppingOutcome_quietParentClocks_of_first_eq_top
                  times htop
              have houtcome :=
                quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
                  times deadline (by simp [htop])
              have hcap (i : ι) :=
                quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
                  times deadline i (by simp [htop])
              have hrow := mul_le_mul_of_nonneg_left certificate.never_row
                (evaluation_nonneg (deadline : WithTop ℕ))
              rw [Finset.mul_sum] at hrow
              simpa [cappedClockActualEvaluatedOutsideGain,
                cappedClockActualEvaluatedChildGain,
                quittingPureClockEvaluatedPayoff, hquiet, houtcome, hcap,
                hquietFirst, houtsideFirst, hcapFirst, first, hfirst,
                quittingStoppingTimeValue,
                mul_assoc, mul_left_comm] using hrow
          | coe firstTime =>
              have hfirst' : quittingEarliestStoppingValue times =
                  (firstTime : WithTop ℕ) := by simpa [first] using hfirst
              have hdeadline_lt' : (deadline : WithTop ℕ) <
                  (firstTime : WithTop ℕ) := by
                simpa [hfirst] using hdeadline_lt
              have hquiet :=
                quittingFirstStoppingOutcome_quietParentClocks_of_first_eq
                  times firstTime hfirst'
              have houtcome :=
                quittingFirstStoppingOutcome_outsideDeadlineClocks_of_lt_first
                  times deadline (by simpa [first, hfirst] using hdeadline_lt)
              have hcap (i : ι) :=
                quittingFirstStoppingOutcome_cappedChildParentClocks_of_lt_first
                  times deadline i (by simpa [first, hfirst] using hdeadline_lt)
              simpa [cappedClockActualEvaluatedOutsideGain,
                cappedClockActualEvaluatedChildGain,
                quittingPureClockEvaluatedPayoff, hquiet, houtcome, hcap,
                hquietFirst, houtsideFirst, hcapFirst, first, hfirst,
                quittingStoppingTimeValue, min_eq_right hdeadline_lt'.le] using
                  (actual_evaluated_future_row certificate.weight
                    (fun i => reward
                      ⟨{some i}, Finset.singleton_nonempty (some i)⟩ (some i))
                    (fun i => reward
                      ⟨cappedClockChildCoalition
                          (quittingEarliestStoppingCoalition times),
                        cappedClockChildCoalition_nonempty
                          (quittingEarliestStoppingCoalition_nonempty times)⟩
                        (some i))
                    (reward ⟨{none}, Finset.singleton_nonempty none⟩ none)
                    (reward
                      ⟨cappedClockChildCoalition
                          (quittingEarliestStoppingCoalition times),
                        cappedClockChildCoalition_nonempty
                          (quittingEarliestStoppingCoalition_nonempty times)⟩ none)
                    (evaluation deadline) (evaluation first)
                    (evaluation_nonneg first)
                    (evaluation_antitone hdeadline_lt.le)
                    certificate.never_row
                    (certificate.future_row
                      (quittingEarliestStoppingCoalition times)
                      (quittingEarliestStoppingCoalition_nonempty times)))

/-- Terminal evaluation is one on finite clocks and zero at Never. -/
def cappedClockTerminalEvaluation (clock : WithTop ℕ) : ℝ :=
  if clock = ⊤ then 0 else 1

theorem cappedClockTerminalEvaluation_nonneg (clock : WithTop ℕ) :
    0 ≤ cappedClockTerminalEvaluation clock := by
  unfold cappedClockTerminalEvaluation
  split_ifs <;> norm_num

theorem cappedClockTerminalEvaluation_antitone :
    Antitone cappedClockTerminalEvaluation := by
  intro first second hle
  by_cases hfirst : first = ⊤
  · have hsecond : second = ⊤ := top_unique (hfirst ▸ hle)
    simp [cappedClockTerminalEvaluation, hfirst, hsecond]
  · unfold cappedClockTerminalEvaluation
    split_ifs <;> norm_num

theorem quittingPureClockEvaluatedPayoff_terminalEvaluation
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (reward : {A : Finset κ // A.Nonempty} → κ → ℝ)
    (times : κ → Option ℕ) (who : κ) :
    quittingPureClockEvaluatedPayoff reward cappedClockTerminalEvaluation
        times who =
      quittingPureClockTerminalPayoff reward times who := by
  unfold quittingPureClockEvaluatedPayoff quittingPureClockTerminalPayoff
  cases hOutcome : quittingFirstStoppingOutcome times with
  | none => rfl
  | some A =>
      have hfinite : quittingEarliestStoppingValue times ≠ ⊤ := by
        intro htop
        rw [quittingFirstStoppingOutcome, if_pos htop] at hOutcome
        contradiction
      simp [cappedClockTerminalEvaluation, hfinite]

/-- Terminal pointwise domination is the finite-one/Never-zero specialization
of the literal evaluated theorem. -/
theorem cappedClockActualOutsideGain_le_weighted_actualChildGain
    (reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ)
    (certificate : CappedClockParentRewardCertificate reward)
    (times : ι → Option ℕ) (deadline : Option ℕ) :
    cappedClockActualOutsideGain reward times deadline ≤
      ∑ i, certificate.weight i *
        cappedClockActualChildGain reward times deadline i := by
  simpa [cappedClockActualOutsideGain, cappedClockActualChildGain,
    cappedClockActualEvaluatedOutsideGain,
    cappedClockActualEvaluatedChildGain,
    quittingPureClockEvaluatedPayoff_terminalEvaluation] using
      (cappedClockActualEvaluatedOutsideGain_le_weighted_actualChildGain
        reward certificate cappedClockTerminalEvaluation
        cappedClockTerminalEvaluation_nonneg
        cappedClockTerminalEvaluation_antitone times deadline)
end GameTheory
