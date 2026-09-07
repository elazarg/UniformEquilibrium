import Mathlib.Data.Finset.Sort
import GameTheory.Math.Probability.FinDist
import UniformEquilibrium.Quitting.Paths.CounterfactualStoppingLaw

/-! # Common retiming preserves the first-quitter outcome law

Only supported clock comparisons and finite/Never status must be preserved.
The common map need not preserve ordering outside the supported calendar.
-/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Retiming onto zero-based order ranks in one common finite calendar.
Dates outside the calendar are fixed; only supported dates are compressed. -/
def quittingFiniteCalendarRetiming
    (calendar : Finset ℕ) : Option ℕ → Option ℕ
  | none => none
  | some time => if htime : time ∈ calendar then
      some (((calendar.orderIsoOfFin rfl).symm ⟨time, htime⟩).val)
    else some time

/-- Union of the finite dates in a finite family of stopping laws. -/
def quittingFiniteStoppingCalendar
    (laws : ι → FinDist (Option ℕ)) : Finset ℕ :=
  Finset.univ.biUnion fun who => (laws who).supportFinset.biUnion fun choice =>
    choice.elim (∅ : Finset ℕ) singleton

omit [DecidableEq ι] [Nonempty ι] in
theorem mem_quittingFiniteStoppingCalendar_of_mem_support
    (laws : ι → FinDist (Option ℕ)) (who : ι) (time : ℕ)
    (htime : some time ∈ (laws who).support) :
    time ∈ quittingFiniteStoppingCalendar laws := by
  simp only [quittingFiniteStoppingCalendar, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  refine ⟨who, ?_⟩
  exact ⟨some time, FinDist.mem_supportFinset.mpr htime, by simp⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem card_quittingFiniteStoppingCalendar_le
    (laws : ι → FinDist (Option ℕ))
    (hsupport : ∀ who, (laws who).supportFinset.card ≤
      Fintype.card ι + 1) :
    (quittingFiniteStoppingCalendar laws).card ≤
      Fintype.card ι * (Fintype.card ι + 1) := by
  calc
    (quittingFiniteStoppingCalendar laws).card ≤
        ∑ who, ((laws who).supportFinset.biUnion fun choice =>
          choice.elim ∅ singleton).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _who : ι, (Fintype.card ι + 1) := by
      apply Finset.sum_le_sum
      intro who _
      refine (Finset.card_biUnion_le.trans ?_).trans (hsupport who)
      calc
        ∑ choice ∈ (laws who).supportFinset,
            (choice.elim (∅ : Finset ℕ) singleton).card ≤
            (laws who).supportFinset.card • 1 := by
          apply Finset.sum_le_card_nsmul
          intro choice _
          cases choice <;> simp
        _ = (laws who).supportFinset.card := by simp
    _ = Fintype.card ι * (Fintype.card ι + 1) := by simp

/-- Two pure clock profiles have the same finite/Never status and the same
weak ordering of all labelled clocks. -/
def QuittingPureClockOrderEquivalent
    (first second : ι → Option ℕ) : Prop :=
  (∀ who, first who = none ↔ second who = none) ∧
  ∀ i j,
    quittingStoppingTimeValue (first i) ≤ quittingStoppingTimeValue (first j) ↔
      quittingStoppingTimeValue (second i) ≤ quittingStoppingTimeValue (second j)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Ranking every supported finite date in one common calendar preserves the
finite/Never status and all pairwise clock comparisons. -/
theorem quittingPureClockOrderEquivalent_finiteCalendarRetiming
    (calendar : Finset ℕ) (times : ι → Option ℕ)
    (hcalendar : ∀ who time, times who = some time → time ∈ calendar) :
    QuittingPureClockOrderEquivalent times
      (fun who => quittingFiniteCalendarRetiming calendar (times who)) := by
  constructor
  · intro who
    cases hchoice : times who with
    | none => simp [hchoice, quittingFiniteCalendarRetiming]
    | some time =>
        have hmem := hcalendar who time hchoice
        simp [hchoice, quittingFiniteCalendarRetiming, hmem]
  · intro first second
    cases hfirst : times first with
    | none =>
        cases hsecond : times second with
        | none => simp [hfirst, hsecond, quittingStoppingTimeValue,
            quittingFiniteCalendarRetiming]
        | some time =>
            have hmem := hcalendar second time hsecond
            simp [hfirst, hsecond, quittingStoppingTimeValue,
              quittingFiniteCalendarRetiming, hmem]
    | some firstTime =>
        cases hsecond : times second with
        | none =>
            simp [hfirst, hsecond, quittingStoppingTimeValue,
              quittingFiniteCalendarRetiming]
        | some secondTime =>
            have hfirstMem := hcalendar first firstTime hfirst
            have hsecondMem := hcalendar second secondTime hsecond
            have hretimeFirst : quittingFiniteCalendarRetiming calendar
                (times first) = some
                  ((calendar.orderIsoOfFin rfl).symm
                    ⟨firstTime, hfirstMem⟩).val := by
              simp [hfirst, quittingFiniteCalendarRetiming, hfirstMem]
            have hretimeSecond : quittingFiniteCalendarRetiming calendar
                (times second) = some
                  ((calendar.orderIsoOfFin rfl).symm
                    ⟨secondTime, hsecondMem⟩).val := by
              simp [hsecond, quittingFiniteCalendarRetiming, hsecondMem]
            change _ ↔ quittingStoppingTimeValue
                (quittingFiniteCalendarRetiming calendar (times first)) ≤
              quittingStoppingTimeValue
                (quittingFiniteCalendarRetiming calendar (times second))
            rw [hretimeFirst, hretimeSecond]
            simp only [quittingStoppingTimeValue]
            have hnat : firstTime ≤ secondTime ↔
                ((calendar.orderIsoOfFin rfl).symm
                    ⟨firstTime, hfirstMem⟩).val ≤
                  ((calendar.orderIsoOfFin rfl).symm
                    ⟨secondTime, hsecondMem⟩).val := by
              exact ((calendar.orderIsoOfFin rfl).symm.le_iff_le
                (x := ⟨firstTime, hfirstMem⟩)
                (y := ⟨secondTime, hsecondMem⟩)).symm
            exact WithTop.coe_le_coe.trans (hnat.trans WithTop.coe_le_coe.symm)

omit [DecidableEq ι] [Nonempty ι] in
theorem quittingEarliestStoppingValue_eq_top_iff
    (times : ι → Option ℕ) :
    quittingEarliestStoppingValue times = ⊤ ↔ ∀ who, times who = none := by
  constructor
  · intro htop who
    have hinfLe : quittingEarliestStoppingValue times ≤
        quittingStoppingTimeValue (times who) :=
      Finset.inf_le (Finset.mem_univ who)
    rw [htop] at hinfLe
    cases hchoice : times who with
    | none => rfl
    | some time =>
        simp [quittingStoppingTimeValue, hchoice] at hinfLe
  · intro hall
    simp [quittingEarliestStoppingValue, hall, quittingStoppingTimeValue]

omit [DecidableEq ι] [Nonempty ι] in
theorem mem_quittingEarliestStoppingCoalition_iff
    (times : ι → Option ℕ) (who : ι) :
    who ∈ quittingEarliestStoppingCoalition times ↔
      ∀ other, quittingStoppingTimeValue (times who) ≤
        quittingStoppingTimeValue (times other) := by
  rw [quittingEarliestStoppingCoalition, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro heq other
    rw [heq]
    exact Finset.inf_le (Finset.mem_univ other)
  · intro hleast
    letI : Nonempty ι := ⟨who⟩
    apply le_antisymm
    · obtain ⟨other, _, hother⟩ := Finset.exists_mem_eq_inf
          (Finset.univ : Finset ι) Finset.univ_nonempty
          (fun player => quittingStoppingTimeValue (times player))
      unfold quittingEarliestStoppingValue
      rw [hother]
      exact hleast other
    · exact Finset.inf_le (Finset.mem_univ who)

omit [DecidableEq ι] in
/-- A common retiming that preserves finite/Never status and every labelled
clock comparison preserves the first-quitter outcome, including ties. -/
theorem quittingFirstStoppingOutcome_eq_of_clockOrderEquivalent
    {first second : ι → Option ℕ}
    (hequivalent : QuittingPureClockOrderEquivalent first second) :
    quittingFirstStoppingOutcome first = quittingFirstStoppingOutcome second := by
  have htop : quittingEarliestStoppingValue first = ⊤ ↔
      quittingEarliestStoppingValue second = ⊤ := by
    rw [quittingEarliestStoppingValue_eq_top_iff,
      quittingEarliestStoppingValue_eq_top_iff]
    exact forall_congr' hequivalent.1
  have hcoalition : quittingEarliestStoppingCoalition first =
      quittingEarliestStoppingCoalition second := by
    ext who
    rw [mem_quittingEarliestStoppingCoalition_iff,
      mem_quittingEarliestStoppingCoalition_iff]
    exact forall_congr' fun other => hequivalent.2 who other
  unfold quittingFirstStoppingOutcome
  by_cases hnever : quittingEarliestStoppingValue first = ⊤
  · rw [if_pos hnever, if_pos (htop.mp hnever)]
  · rw [if_neg hnever, if_neg (mt htop.mpr hnever)]
    congr

omit [DecidableEq ι] in
/-- Retiming every marginal by one common calendar map preserves the terminal
outcome law when it preserves clock order on every supported joint sample. -/
theorem quittingIndependentTerminalOutcomeLaw_map_eq_of_orderEquivalent
    (laws : ι → PMF (Option ℕ)) (retime : Option ℕ → Option ℕ)
    (hretime : ∀ times ∈ (Math.PMFProduct.pmfPi laws).support,
      QuittingPureClockOrderEquivalent times (fun who => retime (times who))) :
    quittingIndependentTerminalOutcomeLaw
        (fun who => (laws who).map retime) =
      quittingIndependentTerminalOutcomeLaw laws := by
  unfold quittingIndependentTerminalOutcomeLaw
  rw [← PMF.bind_pure_comp, Math.PMFProduct.pmfPi_map_bind]
  rw [← PMF.bind_pure_comp]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro times htimes
  simp only [Function.comp_apply]
  rw [quittingFirstStoppingOutcome_eq_of_clockOrderEquivalent
    (hretime times htimes)]

omit [DecidableEq ι] in
/-- Ranking the finite supports of finite stopping laws into their common
calendar preserves their independent terminal-outcome law. -/
theorem quittingIndependentTerminalOutcomeLaw_finiteCalendarRetiming_eq
    (laws : ι → FinDist (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw (fun who =>
        (laws who).toPMF.map
          (quittingFiniteCalendarRetiming
            (quittingFiniteStoppingCalendar laws))) =
      quittingIndependentTerminalOutcomeLaw fun who => (laws who).toPMF := by
  apply quittingIndependentTerminalOutcomeLaw_map_eq_of_orderEquivalent
  intro times htimes
  apply quittingPureClockOrderEquivalent_finiteCalendarRetiming
  intro who time htime
  have hproduct : (∏ player, (laws player).toPMF (times player)) ≠ 0 := by
    simpa only [PMF.mem_support_iff, Math.PMFProduct.pmfPi_apply] using htimes
  have hcoordinate : (laws who).toPMF (times who) ≠ 0 := by
    intro hzero
    exact hproduct (Finset.prod_eq_zero (Finset.mem_univ who) hzero)
  have hsupport : times who ∈ (laws who).support := by
    exact (PMF.mem_support_iff (laws who).toPMF (times who)).2 hcoordinate
  rw [htime] at hsupport
  exact mem_quittingFiniteStoppingCalendar_of_mem_support laws who time hsupport

omit [DecidableEq ι] [Nonempty ι] in
/-- Every finite date after common-calendar retiming lies below the calendar
cardinality. -/
theorem finiteCalendarRetiming_support_lt_card
    (laws : ι → FinDist (Option ℕ)) (who : ι) {time : ℕ}
    (htime : some time ∈ ((laws who).toPMF.map
      (quittingFiniteCalendarRetiming
        (quittingFiniteStoppingCalendar laws))).support) :
    time < (quittingFiniteStoppingCalendar laws).card := by
  obtain ⟨choice, hchoice, hretime⟩ := (PMF.mem_support_map_iff _ _ _).1 htime
  cases choice with
  | none => simp [quittingFiniteCalendarRetiming] at hretime
  | some original =>
      have horiginal := mem_quittingFiniteStoppingCalendar_of_mem_support
        laws who original hchoice
      simp [quittingFiniteCalendarRetiming, horiginal] at hretime
      subst time
      exact ((quittingFiniteStoppingCalendar laws).orderIsoOfFin rfl).symm
        ⟨original, horiginal⟩ |>.isLt

end GameTheory
