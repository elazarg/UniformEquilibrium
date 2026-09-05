import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import MathUE.ProbabilityMassFunction.FiniteTailCollapse

/-! # Actual pivot-law invariance against finite opponent clocks -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem stoppingValue_eq_top_iff (time : Option ℕ) :
    quittingStoppingTimeValue time = ⊤ ↔ time = none := by
  cases time <;> simp [quittingStoppingTimeValue]

omit [DecidableEq ι] in
/-- Pairwise stopping order and the literal Never events determine the first
terminal coalition, including the all-Never outcome. -/
theorem quittingFirstStoppingOutcome_eq_of_order_and_never
    (first second : ι → Option ℕ)
    (horder : ∀ i j, quittingStoppingTimeValue (first i) ≤
        quittingStoppingTimeValue (first j) ↔
      quittingStoppingTimeValue (second i) ≤ quittingStoppingTimeValue (second j))
    (hnever : ∀ i, first i = none ↔ second i = none) :
    quittingFirstStoppingOutcome first = quittingFirstStoppingOutcome second := by
  have hminimal (times : ι → Option ℕ) (i : ι) :
      quittingStoppingTimeValue (times i) = quittingEarliestStoppingValue times ↔
        ∀ j, quittingStoppingTimeValue (times i) ≤ quittingStoppingTimeValue (times j) := by
    constructor
    · intro heq j
      rw [heq]
      exact Finset.inf_le (Finset.mem_univ j)
    · intro hle
      apply le_antisymm
      · exact Finset.le_inf fun j _ ↦ hle j
      · exact Finset.inf_le (Finset.mem_univ i)
  have hcoalition : quittingEarliestStoppingCoalition first =
      quittingEarliestStoppingCoalition second := by
    ext i
    simp only [quittingEarliestStoppingCoalition, Finset.mem_filter,
      Finset.mem_univ, true_and, hminimal]
    exact forall_congr' fun j ↦ horder i j
  have htop (times : ι → Option ℕ) :
      quittingEarliestStoppingValue times = ⊤ ↔ ∀ i, times i = none := by
    simp [quittingEarliestStoppingValue, stoppingValue_eq_top_iff]
  have htopIff : quittingEarliestStoppingValue first = ⊤ ↔
      quittingEarliestStoppingValue second = ⊤ := by
    rw [htop, htop]
    exact forall_congr' hnever
  unfold quittingFirstStoppingOutcome
  by_cases hfirst : quittingEarliestStoppingValue first = ⊤
  · rw [if_pos hfirst, if_pos (htopIff.mp hfirst)]
  · rw [if_neg hfirst, if_neg (fun h ↦ hfirst (htopIff.mpr h))]
    exact congrArg some (Subtype.ext hcoalition)

private theorem stoppingValue_collapse_le_early_iff
    (choice : Option ℕ) {deadline time : ℕ} (htime : time < deadline) :
    quittingStoppingTimeValue (collapseLateFiniteStoppingTime deadline choice) ≤
        quittingStoppingTimeValue (some time) ↔
      quittingStoppingTimeValue choice ≤ quittingStoppingTimeValue (some time) := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some chosen =>
      change ((min chosen deadline : ℕ) : WithTop ℕ) ≤ (time : WithTop ℕ) ↔
        (chosen : WithTop ℕ) ≤ (time : WithTop ℕ)
      exact_mod_cast (show min chosen deadline ≤ time ↔ chosen ≤ time by omega)

private theorem stoppingValue_early_le_collapse_iff
    (choice : Option ℕ) {deadline time : ℕ} (htime : time < deadline) :
    quittingStoppingTimeValue (some time) ≤
        quittingStoppingTimeValue (collapseLateFiniteStoppingTime deadline choice) ↔
      quittingStoppingTimeValue (some time) ≤ quittingStoppingTimeValue choice := by
  cases choice with
  | none => simp [quittingStoppingTimeValue]
  | some chosen =>
      change (time : WithTop ℕ) ≤ ((min chosen deadline : ℕ) : WithTop ℕ) ↔
        (time : WithTop ℕ) ≤ (chosen : WithTop ℕ)
      exact_mod_cast (show time ≤ min chosen deadline ↔ time ≤ chosen by omega)

omit [Nonempty ι] in
/-- With every other finite time before the deadline, collapsing one player's
late finite time preserves the complete labelled terminal outcome. -/
theorem quittingFirstStoppingOutcome_collapse_pivot
    (times : ι → Option ℕ) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot →
      times j = none ∨ ∃ time < deadline, times j = some time) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingFirstStoppingOutcome
        (Function.update times pivot (collapseLateFiniteStoppingTime deadline (times pivot))) =
      quittingFirstStoppingOutcome times := by
  letI : Nonempty ι := ⟨pivot⟩
  apply quittingFirstStoppingOutcome_eq_of_order_and_never
  · intro i j
    by_cases hi : i = pivot
    · subst i
      by_cases hj : j = pivot
      · subst j
        simp
      · simp only [Function.update_self, Function.update_of_ne hj]
        rcases hfinite j hj with hnever | ⟨time, htime, heq⟩
        · simp [hnever, quittingStoppingTimeValue]
        · rw [heq]
          exact stoppingValue_collapse_le_early_iff _ htime
    · by_cases hj : j = pivot
      · subst j
        simp only [Function.update_self, Function.update_of_ne hi]
        rcases hfinite i hi with hnever | ⟨time, htime, heq⟩
        · simp only [hnever, quittingStoppingTimeValue, top_le_iff]
          exact (stoppingValue_eq_top_iff _).trans
            ((collapseLateFiniteStoppingTime_eq_none_iff _ _).trans
              (stoppingValue_eq_top_iff _).symm)
        · rw [heq]
          exact stoppingValue_early_le_collapse_iff _ htime
      · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
  · intro i
    by_cases hi : i = pivot
    · subst i
      simp
    · simp [Function.update_of_ne hi]

omit [Nonempty ι] in
/-- All finite nonpivot laws remain unchanged; the full labelled terminal law
is unchanged when the actual pivot law's finite tail is collapsed. -/
theorem quittingIndependentTerminalOutcomeLaw_collapse_pivot
    (laws : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (laws j)) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingIndependentTerminalOutcomeLaw
        (Function.update laws pivot (collapseLateFiniteStoppingLaw (laws pivot) deadline)) =
      quittingIndependentTerminalOutcomeLaw laws := by
  letI : Nonempty ι := ⟨pivot⟩
  unfold quittingIndependentTerminalOutcomeLaw collapseLateFiniteStoppingLaw
  rw [← Math.PMFProduct.pmfPi_bind_update_map, PMF.map_bind]
  simp only [PMF.pure_map]
  change (Math.PMFProduct.pmfPi laws).map
      (fun times ↦ quittingFirstStoppingOutcome
        (Function.update times pivot (collapseLateFiniteStoppingTime deadline (times pivot)))) = _
  apply pmf_map_eq_of_eq_on_support
  intro times htimes
  apply quittingFirstStoppingOutcome_collapse_pivot
  intro j hj
  apply hfinite j hj (times j)
  intro hzero
  apply htimes
  rw [Math.PMFProduct.pmfPi_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hzero

omit [Nonempty ι] in
/-- Arbitrary actual pivot laws with the same head and Never atom have the
same terminal outcome law against these fixed finite opponents. -/
theorem quittingIndependentTerminalOutcomeLaw_pivot_eq_of_head_and_never
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (first second : PMF (Option ℕ))
    (hhead : ∀ time < deadline, first (some time) = second (some time))
    (hnever : first none = second none) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingIndependentTerminalOutcomeLaw (Function.update opponents pivot first) =
      quittingIndependentTerminalOutcomeLaw (Function.update opponents pivot second) := by
  letI : Nonempty ι := ⟨pivot⟩
  have hfinite' (law : PMF (Option ℕ)) :
      ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline
        (Function.update opponents pivot law j) := by
    intro j hj
    simpa [Function.update_of_ne hj] using hfinite j hj
  rw [← quittingIndependentTerminalOutcomeLaw_collapse_pivot
      (Function.update opponents pivot first) pivot deadline (hfinite' first),
    ← quittingIndependentTerminalOutcomeLaw_collapse_pivot
      (Function.update opponents pivot second) pivot deadline (hfinite' second)]
  simp only [Function.update_self, Function.update_idem]
  rw [collapseLateFiniteStoppingLaw_eq_of_head_and_never first second deadline hhead hnever]

omit [Nonempty ι] in
/-- Matching pivot head and Never atoms preserves every player's payoff in
the actual behavioral realizations, with no sign assumption on rewards. -/
theorem quittingTerminalPayoff_pivot_eq_of_head_and_never
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (first second : PMF (Option ℕ))
    (hhead : ∀ time < deadline, first (some time) = second (some time))
    (hnever : first none = second none) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot first)) =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot second)) := by
  letI : Nonempty ι := ⟨pivot⟩
  funext observer
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  rw [quittingIndependentTerminalOutcomeLaw_pivot_eq_of_head_and_never
    opponents pivot deadline hfinite first second hhead hnever]

omit [Nonempty ι] in
/-- The same exact outcome invariance survives any nonpivot replacement law
supported on the displayed head and Never. It covers every displayed pure
date and the Never response without restricting the actual pivot law. -/
theorem quittingIndependentTerminalOutcomeLaw_pivot_finiteReplacement_eq
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (first second : PMF (Option ℕ))
    (hhead : ∀ time < deadline, first (some time) = second (some time))
    (hnever : first none = second none)
    (observer : ι) (hne : observer ≠ pivot) (replacement : PMF (Option ℕ))
    (hreplacement : IsFiniteClockStoppingLaw deadline replacement) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingIndependentTerminalOutcomeLaw
        (Function.update (Function.update opponents pivot first) observer replacement) =
      quittingIndependentTerminalOutcomeLaw
        (Function.update (Function.update opponents pivot second) observer replacement) := by
  letI : Nonempty ι := ⟨pivot⟩
  rw [Function.update_comm hne.symm, Function.update_comm hne.symm]
  apply quittingIndependentTerminalOutcomeLaw_pivot_eq_of_head_and_never
    (Function.update opponents observer replacement) pivot deadline _ first second hhead hnever
  intro j hj
  by_cases hobserver : j = observer
  · subst j
    simpa using hreplacement
  · simpa [Function.update_of_ne hobserver] using hfinite j hj

omit [Nonempty ι] in
/-- Finite nonpivot replacement payoffs are unchanged by a pivot replacement
that retains the head and Never atom. These are literal terminal payoffs of
independent behavioral realizations, not formal payoff coefficients. -/
theorem quittingTerminalPayoff_pivot_finiteReplacement_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ pivot → IsFiniteClockStoppingLaw deadline (opponents j))
    (first second : PMF (Option ℕ))
    (hhead : ∀ time < deadline, first (some time) = second (some time))
    (hnever : first none = second none)
    (observer : ι) (hne : observer ≠ pivot) (replacement : PMF (Option ℕ))
    (hreplacement : IsFiniteClockStoppingLaw deadline replacement) (who : ι) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents pivot first) observer replacement)) who =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents pivot second) observer replacement)) who := by
  letI : Nonempty ι := ⟨pivot⟩
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  rw [quittingIndependentTerminalOutcomeLaw_pivot_finiteReplacement_eq
    opponents pivot deadline hfinite first second hhead hnever observer hne
      replacement hreplacement]

omit [Nonempty ι] in
/-- The pivot's own unrestricted behavioral cap depends only on its fixed
opponents, for arbitrary complete pivot laws. -/
theorem quittingContinuationBestResponseValue_stoppingLawProfile_update_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot : ι)
    (first second : PMF (Option ℕ)) :
    quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot first)) pivot =
      quittingContinuationBestResponseValue reward
        (quittingStoppingLawProfile reward (Function.update opponents pivot second)) pivot := by
  letI : Nonempty ι := ⟨pivot⟩
  rw [← quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile,
    ← quittingStoppingLawCap_eq_continuationBestResponseValue_stoppingLawProfile]
  simp only [quittingStoppingLawReplacementPayoffCap, Function.update_idem]

end GameTheory
