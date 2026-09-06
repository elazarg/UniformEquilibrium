import UniformEquilibrium.Quitting.Paths.FiniteOpponentPivotLaw
import UniformEquilibrium.Quitting.Terminal.CompactStoppingLawCapUpperBound

/-! # Signed late responses against actual finite opponent laws -/

noncomputable section

namespace GameTheory

open Filter
open _root_.Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Actual independent stopping-law payoffs are affine in an arbitrary
complete marginal law, for every payoff observer. -/
theorem quittingTerminalPayoff_stoppingLawProfile_update_eq_expect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer observer : ι) (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update laws mixer law)) observer =
      expect law (fun choice ↦ quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure choice))) observer) := by
  letI : Nonempty ι := ⟨mixer⟩
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff, quittingIndependentTerminalOutcomeLaw]
  rw [Math.PMFProduct.pmfPi_update_bind, PMF.map_bind, expect_bind]

/-- Reconstructing a pure marginal law and playing the corresponding pure
time produce the same terminal payoff to every observer. -/
theorem quittingTerminalPayoff_stoppingLawProfile_update_pure_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer observer : ι) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure choice))) observer =
      quittingTerminalPayoff reward
        (Function.update (quittingStoppingLawProfile reward laws) mixer
          (quittingPureTimeBehaviorStrategy reward mixer choice)) observer := by
  have hprofile : quittingStoppingLawProfile reward
      (Function.update laws mixer (PMF.pure choice)) =
      Function.update (quittingStoppingLawProfile reward laws) mixer
        (quittingStoppingLawBehaviorStrategy reward mixer (PMF.pure choice)) := by
    funext player
    by_cases hplayer : player = mixer
    · subst player
      simp [quittingStoppingLawProfile]
    · simp [quittingStoppingLawProfile, Function.update_of_ne hplayer]
  rw [hprofile, quittingTerminalPayoff_update_stoppingLawBehaviorStrategy_eq_expect,
    expect_pure]

/-- Against finite opponent clocks, all late finite deterministic marginal
responses have exactly the same signed payoff, for every observer. -/
theorem quittingTerminalPayoff_stoppingLawProfile_late_pure_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer observer : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ mixer → IsFiniteClockStoppingLaw deadline (laws j))
    {first second : ℕ} (hfirst : deadline ≤ first) (hsecond : deadline ≤ second) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure (some first)))) observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure (some second)))) observer := by
  apply congrFun (quittingTerminalPayoff_pivot_eq_of_head_and_never
    reward laws mixer deadline hfinite (PMF.pure (some first)) (PMF.pure (some second))
    (fun time htime ↦ by
      simp [PMF.pure_apply, show time ≠ first by omega, show time ≠ second by omega])
    (by simp)) observer

/-- The signed late finite payoff differs from Never by precisely the
all-opponents-Never probability times the deviator's singleton reward. -/
theorem quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ mixer → IsFiniteClockStoppingLaw deadline (laws j))
    {time : ℕ} (htime : deadline ≤ time) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure (some time)))) mixer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure none))) mixer +
        (∏ j ∈ Finset.univ.erase mixer, (laws j none).toReal) *
          reward (quittingSingletonTerminal mixer) mixer := by
  let compact := fun j ↦ CompactStoppingLaw.ofPMF (laws j)
  have hprofile : quittingCompactStoppingLawProfile reward compact =
      quittingStoppingLawProfile reward laws := by
    funext player
    change quittingStoppingLawBehaviorStrategy reward player
        (CompactStoppingLaw.ofPMF (laws player)).toPMF = _
    rw [CompactStoppingLaw.toPMF_ofPMF]
    rfl
  have hlimit :=
    quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
      reward compact mixer
  rw [hprofile] at hlimit
  simp only [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq] at hlimit
  have hevent : ∀ᶠ later in atTop,
      quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update laws mixer (PMF.pure (some later)))) mixer =
        quittingTerminalPayoff reward
          (quittingStoppingLawProfile reward
            (Function.update laws mixer (PMF.pure (some time)))) mixer := by
    filter_upwards [eventually_ge_atTop deadline] with later hlater
    exact quittingTerminalPayoff_stoppingLawProfile_late_pure_eq
      reward laws mixer mixer deadline hfinite hlater htime
  have heq := tendsto_nhds_unique tendsto_const_nhds (hlimit.congr' hevent)
  have hproduct : quittingOpponentNeverProduct compact mixer =
      ∏ j ∈ Finset.univ.erase mixer, (laws j none).toReal := by
    unfold quittingOpponentNeverProduct
    apply Finset.prod_congr rfl
    intro j _
    rw [← CompactStoppingLaw.toPMF_apply_toReal]
    simp only [compact, CompactStoppingLaw.toPMF_ofPMF]
    rfl
  simpa only [hproduct] using heq

/-- The same exact signed late-row identity holds for an arbitrary payoff
observer, not only for the player choosing the late time. -/
theorem quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer observer : ι) (deadline : ℕ)
    (hfinite : ∀ j, j ≠ mixer → IsFiniteClockStoppingLaw deadline (laws j))
    {time : ℕ} (htime : deadline ≤ time) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure (some time)))) observer =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws mixer (PMF.pure none))) observer +
        (∏ j ∈ Finset.univ.erase mixer, (laws j none).toReal) *
          reward (quittingSingletonTerminal mixer) observer := by
  have h := quittingTerminalPayoff_stoppingLawProfile_late_pure_eq_never_add
    (quittingObserverReward reward observer) laws mixer deadline hfinite htime
  letI : Nonempty ι := ⟨mixer⟩
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at h ⊢
  have hobs (actual : ι → PMF (Option ℕ)) :
      quittingStoppingLawExpectedPayoff (quittingObserverReward reward observer) actual mixer =
        quittingStoppingLawExpectedPayoff reward actual observer := by
    unfold quittingStoppingLawExpectedPayoff
    apply congrArg (expect _)
    funext outcome
    cases outcome <;> rfl
  rw [hobs, hobs] at h
  exact h

private theorem firstStoppingOutcome_one_date
    (coalition : Finset ι) (hne : coalition.Nonempty) (time : ℕ) :
    letI : Nonempty ι := ⟨hne.choose⟩
    quittingFirstStoppingOutcome
        (fun player ↦ if player ∈ coalition then some time else none) =
      some ⟨coalition, hne⟩ := by
  letI : Nonempty ι := ⟨hne.choose⟩
  have hmin : quittingEarliestStoppingValue
      (fun player ↦ if player ∈ coalition then some time else none) = (time : WithTop ℕ) := by
    unfold quittingEarliestStoppingValue
    apply le_antisymm
    · have hle := Finset.inf_le
        (f := fun player ↦ quittingStoppingTimeValue
          (if player ∈ coalition then some time else none))
        (Finset.mem_univ hne.choose)
      simpa only [if_pos hne.choose_spec, quittingStoppingTimeValue] using hle
    · apply Finset.le_inf
      intro player _
      by_cases hplayer : player ∈ coalition <;> simp [hplayer, quittingStoppingTimeValue]
  have hcoalition : quittingEarliestStoppingCoalition
      (fun player ↦ if player ∈ coalition then some time else none) = coalition := by
    ext player
    simp only [quittingEarliestStoppingCoalition, Finset.mem_filter,
      Finset.mem_univ, true_and, hmin]
    by_cases hplayer : player ∈ coalition <;> simp [hplayer, quittingStoppingTimeValue]
  unfold quittingFirstStoppingOutcome
  rw [hmin, if_neg (by simp)]
  exact congrArg some (Subtype.ext hcoalition)

/-- If all other finite times precede the deadline, a late simultaneous
pair quit only changes the all-Never realization of the pinned baseline. -/
theorem quittingFirstStoppingOutcome_late_pair
    (times : ι → Option ℕ) (pivot observer : ι) (hne : observer ≠ pivot)
    (deadline time : ℕ) (htime : deadline ≤ time)
    (hpivot : times pivot = none) (hobserver : times observer = none)
    (hfinite : ∀ j, j ≠ pivot → j ≠ observer →
      times j = none ∨ ∃ chosen < deadline, times j = some chosen) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingFirstStoppingOutcome
        (Function.update (Function.update times pivot (some time)) observer (some time)) =
      if ∀ j, times j = none then
        some ⟨{pivot, observer}, by simp⟩ else quittingFirstStoppingOutcome times := by
  letI : Nonempty ι := ⟨pivot⟩
  by_cases hall : ∀ j, times j = none
  · rw [if_pos hall]
    have htimes : Function.update (Function.update times pivot (some time)) observer
        (some time) = fun j ↦ if j ∈ ({pivot, observer} : Finset ι) then some time
          else none := by
      funext j
      by_cases hjp : j = pivot
      · subst j
        simp [hne.symm]
      · by_cases hjo : j = observer
        · subst j
          simp
        · simp [hjp, hjo, hall j]
    rw [htimes]
    exact firstStoppingOutcome_one_date {pivot, observer} (by simp) time
  · rw [if_neg hall]
    obtain ⟨blocker, hblocker⟩ := not_forall.mp hall
    have hbp : blocker ≠ pivot := fun heq ↦ hblocker (heq ▸ hpivot)
    have hbo : blocker ≠ observer := fun heq ↦ hblocker (heq ▸ hobserver)
    obtain ⟨chosen, hchosen, heq⟩ := (hfinite blocker hbp hbo).resolve_left hblocker
    have hchosenTime : quittingStoppingTimeValue (some chosen) <
        quittingStoppingTimeValue (some time) := by
      change (chosen : WithTop ℕ) < (time : WithTop ℕ)
      exact_mod_cast (show chosen < time by omega)
    have hchosenNever : quittingStoppingTimeValue (some chosen) <
        quittingStoppingTimeValue none := by simp [quittingStoppingTimeValue]
    calc
      quittingFirstStoppingOutcome
          (Function.update (Function.update times pivot (some time)) observer (some time)) =
          quittingFirstStoppingOutcome (Function.update times pivot (some time)) := by
        apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
          (hidden := observer) (blocker := blocker)
        · intro j hj
          simp [Function.update_of_ne hj]
        · simpa [Function.update_of_ne hbp, Function.update_of_ne hbo, heq]
            using hchosenTime
        · simpa [Function.update_of_ne hbp, Function.update_of_ne hne,
            heq, hobserver] using hchosenNever
      _ = quittingFirstStoppingOutcome times := by
        apply quittingFirstStoppingOutcome_eq_of_earlier_stopper
          (hidden := pivot) (blocker := blocker)
        · intro j hj
          simp [Function.update_of_ne hj]
        · simpa [Function.update_of_ne hbp, heq] using hchosenTime
        · simpa [heq, hpivot] using hchosenNever

omit [DecidableEq ι] in
/-- Never is exactly the event that every complete stopping time is Never. -/
theorem quittingFirstStoppingOutcome_eq_none_iff [Nonempty ι]
    (times : ι → Option ℕ) :
    quittingFirstStoppingOutcome times = none ↔ ∀ j, times j = none := by
  have htime (choice : Option ℕ) : quittingStoppingTimeValue choice = ⊤ ↔ choice = none := by
    cases choice <;> simp [quittingStoppingTimeValue]
  simp [quittingFirstStoppingOutcome, quittingEarliestStoppingValue, htime]

omit [DecidableEq ι] in
/-- The actual all-Never outcome mass is the product of the actual marginal
Never atoms. No finite-support or properness assumption is needed. -/
theorem quittingIndependentTerminalOutcomeLaw_none [Nonempty ι]
    (laws : ι → PMF (Option ℕ)) :
    quittingIndependentTerminalOutcomeLaw laws none = ∏ j, laws j none := by
  classical
  rw [quittingIndependentTerminalOutcomeLaw, PMF.map_apply,
    tsum_eq_single (fun _ ↦ none)]
  · simp [Math.PMFProduct.pmfPi_apply]
  · intro times htimes
    rw [if_neg]
    intro houtcome
    apply htimes
    exact funext (quittingFirstStoppingOutcome_eq_none_iff times |>.mp houtcome.symm)

/-- Turning a pair pinned at Never into a simultaneous late quit replaces
only the Never atom of the actual terminal law by the pair coalition. -/
theorem quittingIndependentTerminalOutcomeLaw_late_pair
    (laws : ι → PMF (Option ℕ)) (pivot observer : ι) (hne : observer ≠ pivot)
    (deadline time : ℕ) (htime : deadline ≤ time)
    (hpivot : laws pivot = PMF.pure none) (hobserver : laws observer = PMF.pure none)
    (hfinite : ∀ j, j ≠ pivot → j ≠ observer →
      IsFiniteClockStoppingLaw deadline (laws j)) :
    letI : Nonempty ι := ⟨pivot⟩
    quittingIndependentTerminalOutcomeLaw
        (Function.update (Function.update laws pivot (PMF.pure (some time)))
          observer (PMF.pure (some time))) =
      (quittingIndependentTerminalOutcomeLaw laws).map
        (fun outcome ↦ some (outcome.getD ⟨{pivot, observer}, by simp⟩)) := by
  letI : Nonempty ι := ⟨pivot⟩
  unfold quittingIndependentTerminalOutcomeLaw
  rw [← Math.PMFProduct.pmfPi_bind_update_pure,
    ← Math.PMFProduct.pmfPi_bind_update_pure]
  simp only [PMF.map_bind, PMF.bind_bind, PMF.pure_bind, PMF.pure_map,
    PMF.map_comp]
  apply pmf_map_eq_of_eq_on_support
  intro times htimes
  have hcoordinate (j : ι) : laws j (times j) ≠ 0 := by
    intro hzero
    apply htimes
    rw [Math.PMFProduct.pmfPi_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
  have htp : times pivot = none := by
    have h := hcoordinate pivot
    rw [hpivot, PMF.pure_apply] at h
    split_ifs at h with heq
    · exact heq
    · exact (h rfl).elim
  have hto : times observer = none := by
    have h := hcoordinate observer
    rw [hobserver, PMF.pure_apply] at h
    split_ifs at h with heq
    · exact heq
    · exact (h rfl).elim
  rw [quittingFirstStoppingOutcome_late_pair times pivot observer hne deadline time
    htime htp hto (fun j hjp hjo ↦ hfinite j hjp hjo _ (hcoordinate j))]
  simp only [Function.comp_apply]
  by_cases hall : ∀ j, times j = none
  · rw [if_pos hall, quittingFirstStoppingOutcome_eq_none_iff times |>.mpr hall]
    rfl
  · rw [if_neg hall]
    have hnot : quittingFirstStoppingOutcome times ≠ none :=
      fun heq ↦ hall (quittingFirstStoppingOutcome_eq_none_iff times |>.mp heq)
    cases houtcome : quittingFirstStoppingOutcome times with
    | none => exact (hnot houtcome).elim
    | some terminal => rfl

/-- The exact signed payoff contribution of a simultaneous late pair quit.
The baseline is the actual independent profile with that pair pinned at
Never, and its surviving probability multiplies the actual pair reward. -/
theorem quittingTerminalPayoff_stoppingLawProfile_late_pair_eq_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (pivot observer who : ι) (hne : observer ≠ pivot)
    (deadline time : ℕ) (htime : deadline ≤ time)
    (hpivot : laws pivot = PMF.pure none) (hobserver : laws observer = PMF.pure none)
    (hfinite : ∀ j, j ≠ pivot → j ≠ observer →
      IsFiniteClockStoppingLaw deadline (laws j)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update laws pivot (PMF.pure (some time)))
            observer (PMF.pure (some time)))) who =
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward laws) who +
        (∏ j, (laws j none).toReal) * reward ⟨{pivot, observer}, by simp⟩ who := by
  letI : Nonempty ι := ⟨pivot⟩
  classical
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff,
    quittingStoppingLawExpectedPayoff]
  rw [quittingIndependentTerminalOutcomeLaw_late_pair laws pivot observer hne
    deadline time htime hpivot hobserver hfinite, expect_map]
  have hpointwise :
      (fun outcome : QuittingTerminalOutcome ι ↦ quittingTerminalOutcomeReward reward
        (some (outcome.getD ⟨{pivot, observer}, by simp⟩)) who) =
      fun outcome ↦ quittingTerminalOutcomeReward reward outcome who +
        if outcome = none then reward ⟨{pivot, observer}, by simp⟩ who else 0 := by
    funext outcome
    cases outcome <;> simp [quittingTerminalOutcomeReward]
  rw [hpointwise, expect_add]
  congr 1
  have hsingle : expect (quittingIndependentTerminalOutcomeLaw laws)
      (fun outcome ↦ if outcome = none then reward ⟨{pivot, observer}, by simp⟩ who else 0) =
        (quittingIndependentTerminalOutcomeLaw laws none).toReal *
          reward ⟨{pivot, observer}, by simp⟩ who := by
    rw [expect_eq_sum, Finset.sum_eq_single none]
    · simp
    · intro outcome _ hne
      simp [hne]
    · simp
  rw [hsingle, quittingIndependentTerminalOutcomeLaw_none, ENNReal.toReal_prod]

/-- If two displayed players quit at distinct late dates, only the earlier
player's singleton reward contributes on the baseline Never event. -/
theorem quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (earlier later who : ι) (hne : later ≠ earlier)
    (deadline first second : ℕ) (hfirst : deadline ≤ first) (horder : first < second)
    (hearlier : laws earlier = PMF.pure none) (hlater : laws later = PMF.pure none)
    (hfinite : ∀ j, j ≠ earlier → j ≠ later →
      IsFiniteClockStoppingLaw deadline (laws j)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update laws earlier (PMF.pure (some first)))
            later (PMF.pure (some second)))) who =
      quittingTerminalPayoff reward (quittingStoppingLawProfile reward laws) who +
        (∏ j, (laws j none).toReal) * reward (quittingSingletonTerminal earlier) who := by
  let mid := Function.update laws earlier (PMF.pure (some first))
  have hmidFinite : ∀ j, j ≠ later → IsFiniteClockStoppingLaw (first + 1) (mid j) := by
    intro j hj choice hchoice
    by_cases hje : j = earlier
    · subst j
      have hchoice' : choice = some first := by
        simpa [mid, PMF.pure_apply] using hchoice
      exact Or.inr ⟨first, by omega, hchoice'⟩
    · have hsupport : laws j choice ≠ 0 := by simpa [mid, hje] using hchoice
      rcases hfinite j hje hj choice hsupport with hnever | ⟨chosen, hchosen, heq⟩
      · exact Or.inl hnever
      · exact Or.inr ⟨chosen, by omega, heq⟩
  have hlate := quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward mid later who (first + 1) hmidFinite (show first + 1 ≤ second by omega)
  have hzero : (∏ j ∈ Finset.univ.erase later, (mid j none).toReal) = 0 := by
    apply Finset.prod_eq_zero (show earlier ∈ Finset.univ.erase later by simp [hne.symm])
    simp [mid]
  have hmidLater : mid later = PMF.pure none := by simp [mid, hne, hlater]
  rw [hzero, zero_mul, add_zero, ← hmidLater, Function.update_eq_self] at hlate
  rw [hlate]
  have hbaseFinite : ∀ j, j ≠ earlier → IsFiniteClockStoppingLaw deadline (laws j) := by
    intro j hj choice hchoice
    by_cases hjl : j = later
    · subst j
      left
      simpa [hlater, PMF.pure_apply] using hchoice
    · exact hfinite j hj hjl choice hchoice
  have hearly := quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
    reward laws earlier who deadline hbaseFinite hfirst
  rw [← hearlier, Function.update_eq_self] at hearly
  have hproduct : (∏ j ∈ Finset.univ.erase earlier, (laws j none).toReal) =
      ∏ j, (laws j none).toReal := by
    simpa [hearlier] using Finset.prod_erase_mul Finset.univ
      (fun j ↦ (laws j none).toReal) (Finset.mem_univ earlier)
  simpa only [mid, hproduct] using hearly

end GameTheory
