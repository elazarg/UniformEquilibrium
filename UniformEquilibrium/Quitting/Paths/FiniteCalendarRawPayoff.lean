import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffClosure
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass
import UniformEquilibrium.Quitting.Paths.StageCoalitionStoppingLaw

/-! # Literal finite-calendar terminal masses and payoffs -/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Probability that one finite-calendar clock lies strictly after a date,
including its Never atom. -/
def quittingFiniteCalendarStrictTail {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (time : Fin deadline) : ℝ :=
  x who none + ∑ later : Fin deadline, if time < later then x who (some later) else 0

/-- Literal polynomial mass of a nonempty first-quitter coalition on a
finite calendar. -/
def quittingFiniteCalendarCoalitionMass {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  ∑ time : Fin deadline,
    (∏ who ∈ terminal.val, x who (some time)) *
      ∏ who ∈ terminal.valᶜ, quittingFiniteCalendarStrictTail x who time

/-- Literal all-Never mass on a finite calendar. -/
def quittingFiniteCalendarNeverMass {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) : ℝ :=
  ∏ who, x who none

/-- Whole prescribed payoff polynomial induced by the finite-calendar first
coalition masses. -/
def quittingFiniteCalendarRawPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (x : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline)) : Payoff ι :=
  fun observer => ∑ terminal, quittingFiniteCalendarCoalitionMass x terminal *
    reward terminal observer

omit [DecidableEq ι] in
@[simp]
theorem finiteCalendarSimplexPMF_toReal {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (choice : Option (Fin deadline)) :
    ((Math.ProbabilityMassFunction.stdSimplexEquiv.symm (x who)) choice).toReal =
      x who choice := by
  exact Math.ProbabilityMassFunction.ofVector_toReal (x who).property choice

def quittingFiniteCalendarDecodedLaws {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    ι → PMF (Option ℕ) := fun who =>
  (Math.ProbabilityMassFunction.stdSimplexEquiv.symm (x who)).map
    (_root_.Math.Probability.finiteStoppingTimeDecode deadline)

omit [DecidableEq ι] in
@[simp]
theorem quittingFiniteCalendarDecodedLaws_some_toReal {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (time : Fin deadline) :
    (quittingFiniteCalendarDecodedLaws x who (some time.val)).toReal =
      x who (some time) := by
  classical
  unfold quittingFiniteCalendarDecodedLaws
  rw [PMF.map_apply, tsum_eq_single (some time)]
  · simp [_root_.Math.Probability.finiteStoppingTimeDecode,
      ENNReal.toReal_ofReal (stdSimplex.zero_le (x who) (some time))]
  · intro choice hchoice
    cases choice with
    | none => simp [_root_.Math.Probability.finiteStoppingTimeDecode]
    | some other =>
        simp only [_root_.Math.Probability.finiteStoppingTimeDecode,
          Option.map_some, Option.some.injEq]
        rw [if_neg]
        intro heq
        apply hchoice
        exact congrArg some (Fin.ext heq.symm)

omit [DecidableEq ι] in
@[simp]
theorem quittingFiniteCalendarDecodedLaws_none_toReal {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    (quittingFiniteCalendarDecodedLaws x who none).toReal = x who none := by
  classical
  unfold quittingFiniteCalendarDecodedLaws
  rw [PMF.map_apply, tsum_eq_single none]
  · simp [_root_.Math.Probability.finiteStoppingTimeDecode,
      ENNReal.toReal_ofReal (stdSimplex.zero_le (x who) none)]
  · intro choice hchoice
    cases choice with
    | none => exact (hchoice rfl).elim
    | some other =>
        simp [_root_.Math.Probability.finiteStoppingTimeDecode]

omit [DecidableEq ι] in
theorem quittingFiniteCalendarDecodedLaws_some_eq_zero_of_le {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (time : ℕ) (htime : deadline ≤ time) :
    quittingFiniteCalendarDecodedLaws x who (some time) = 0 := by
  classical
  unfold quittingFiniteCalendarDecodedLaws
  rw [PMF.map_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro choice
  rw [if_neg]
  cases choice with
  | none => simp [_root_.Math.Probability.finiteStoppingTimeDecode]
  | some bounded =>
      simp only [_root_.Math.Probability.finiteStoppingTimeDecode,
        Option.map_some, Option.some.injEq]
      exact fun heq => (not_lt_of_ge htime) (heq ▸ bounded.isLt)

omit [DecidableEq ι] in
theorem quittingFiniteCalendarStrictTail_eq_one_sub_head {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (time : Fin deadline) :
    quittingFiniteCalendarStrictTail x who time =
      1 - ∑ earlier : Fin deadline,
        if earlier ≤ time then x who (some earlier) else 0 := by
  classical
  have htotal := (x who).property.2
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun later : Fin deadline => later ≤ time) (fun later => x who (some later))
  simp only [Finset.sum_filter, not_le] at hsplit
  unfold quittingFiniteCalendarStrictTail
  -- The standard-simplex total is the Never coordinate plus all finite dates.
  rw [Fintype.sum_option] at htotal
  change x who none + ∑ later : Fin deadline, x who (some later) = 1 at htotal
  linarith

omit [DecidableEq ι] in
theorem quittingFiniteCalendarStrictTail_eq_stoppingLawSurvival {deadline : ℕ}
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) (time : Fin deadline) :
    quittingFiniteCalendarStrictTail x who time =
      _root_.Math.Probability.DiscreteHazard.StoppingLaw.survival
        (quittingFiniteCalendarDecodedLaws x who) (time.val + 1) := by
  rw [quittingFiniteCalendarStrictTail_eq_one_sub_head]
  unfold _root_.Math.Probability.DiscreteHazard.StoppingLaw.survival
    _root_.Math.Probability.DiscreteHazard.StoppingLaw.finiteMass
  congr 1
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun earlier _ => earlier.val)
    ?_ ?_ ?_ ?_
  · intro earlier hearlier
    simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (Finset.mem_filter.mp hearlier).2
  · intro first hfirst second hsecond heq
    exact Fin.ext heq
  · intro index hindex
    have hle : index ≤ time.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hindex)
    let earlier : Fin deadline :=
      ⟨index, lt_of_le_of_lt hle time.isLt⟩
    refine ⟨earlier, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact hle
    · rfl
  · intro earlier hearlier
    rw [quittingFiniteCalendarDecodedLaws_some_toReal]

theorem quittingStageCoalitionMass_finiteCalendar_eq {deadline : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (time : Fin deadline) (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x)) time.val terminal =
      (∏ who ∈ terminal.val, x who (some time)) *
        ∏ who ∈ terminal.valᶜ,
          quittingFiniteCalendarStrictTail x who time := by
  letI : Nonempty ι := ⟨terminal.property.choose⟩
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro who _
    rw [quittingBehaviorStoppingLaw_stoppingLawProfile,
      quittingFiniteCalendarDecodedLaws_some_toReal]
  · apply Finset.prod_congr rfl
    intro who _
    rw [quittingFiniteCalendarStrictTail_eq_stoppingLawSurvival,
      ← stoppingLawSurvival_quittingBehaviorStoppingLaw]
    rw [quittingBehaviorStoppingLaw_stoppingLawProfile]

theorem quittingStageCoalitionMass_finiteCalendar_eq_zero_of_le {deadline : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (time : ℕ) (htime : deadline ≤ time)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x)) time terminal = 0 := by
  letI : Nonempty ι := ⟨terminal.property.choose⟩
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  have hproduct : (∏ who ∈ terminal.val,
      (quittingBehaviorStoppingLaw reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x) who) (some time)).toReal) = 0 := by
    obtain ⟨who, hwho⟩ := terminal.property
    apply Finset.prod_eq_zero hwho
    rw [quittingBehaviorStoppingLaw_stoppingLawProfile,
      quittingFiniteCalendarDecodedLaws_some_eq_zero_of_le x who time htime]
    rfl
  rw [hproduct, zero_mul]

theorem quittingTerminalOutcomeMass_finiteCalendar_eq {deadline : ℕ}
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline))
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x)) (some terminal) =
      quittingFiniteCalendarCoalitionMass x terminal := by
  letI : Nonempty ι := ⟨terminal.property.choose⟩
  rw [quittingTerminalOutcomeMass_eq_timeDisintegration]
  change (∑' time : ℕ, quittingStageCoalitionMass reward
      (quittingStoppingLawProfile reward
        (quittingFiniteCalendarDecodedLaws x)) time terminal) = _
  rw [tsum_eq_sum (s := Finset.range deadline)]
  · rw [← Fin.sum_univ_eq_sum_range]
    unfold quittingFiniteCalendarCoalitionMass
    apply Finset.sum_congr rfl
    intro time _
    exact quittingStageCoalitionMass_finiteCalendar_eq reward x time terminal
  · intro time htime
    apply quittingStageCoalitionMass_finiteCalendar_eq_zero_of_le reward x time
    simpa using htime

omit [DecidableEq ι] in
theorem quittingTerminalOutcomeMass_finiteCalendar_none_eq {deadline : ℕ}
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingTerminalOutcomeMass reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x)) none =
      quittingFiniteCalendarNeverMass x := by
  unfold quittingTerminalOutcomeMass quittingFiniteCalendarNeverMass
  rw [quittingLiveMassLimit_eq_prod_hazardNeverMass]
  apply Finset.prod_congr rfl
  intro who _
  rw [← quittingBehaviorStoppingLaw_none_toReal,
    quittingBehaviorStoppingLaw_stoppingLawProfile,
    quittingFiniteCalendarDecodedLaws_none_toReal]

/-- The displayed nonempty-coalition masses and the Never mass sum to one. -/
theorem quittingFiniteCalendarNeverMass_add_sum_coalitionMass {deadline : ℕ}
    [Nonempty ι]
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteCalendarNeverMass x +
        ∑ terminal, quittingFiniteCalendarCoalitionMass x terminal = 1 := by
  let reward : {S : Finset ι // S.Nonempty} → Payoff ι := fun _ _ => 0
  let profile := quittingStoppingLawProfile reward
    (quittingFiniteCalendarDecodedLaws x)
  have htotal := (quittingTerminalOutcomeMass_mem_stdSimplex reward profile).2
  rw [Fintype.sum_option] at htotal
  change quittingTerminalOutcomeMass reward profile none +
      ∑ terminal, quittingTerminalOutcomeMass reward profile (some terminal) = 1 at htotal
  dsimp only [profile] at htotal
  rw [quittingTerminalOutcomeMass_finiteCalendar_none_eq reward x] at htotal
  simp_rw [quittingTerminalOutcomeMass_finiteCalendar_eq reward x] at htotal
  exact htotal

/-- The literal polynomial is exactly the whole prescribed terminal payoff
of the independent finite-calendar profile. -/
theorem quittingFiniteCalendarRawPayoff_eq_terminalPayoff {deadline : ℕ}
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteCalendarRawPayoff reward deadline x =
      fun observer => quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (quittingFiniteCalendarDecodedLaws x)) observer := by
  funext observer
  unfold quittingFiniteCalendarRawPayoff quittingTerminalPayoff
  apply Finset.sum_congr rfl
  intro terminal _
  rw [← quittingTerminalOutcomeMass_finiteCalendar_eq reward x terminal]
  rfl

/-- The raw payoff polynomial is the payoff map of the finite timing game. -/
theorem quittingFiniteCalendarRawPayoff_eq_timingPayoffMap {deadline : ℕ}
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction deadline)) :
    quittingFiniteCalendarRawPayoff reward deadline x =
      quittingFiniteDeadlineTimingPayoffMap reward deadline x := by
  rw [quittingFiniteCalendarRawPayoff_eq_terminalPayoff]
  let mixed : ι → PMF (Option (Fin deadline)) := fun who =>
    Math.ProbabilityMassFunction.stdSimplexEquiv.symm (x who)
  have hlaws : ∀ who,
      (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingFiniteCalendarDecodedLaws x who := by
    intro who
    unfold quittingFiniteDeadlineTimingLaw quittingFiniteCalendarDecodedLaws
    rw [_root_.Math.Probability.CompactStoppingLaw.toPMF_ofPMF]
    congr 1
    funext action
    cases action <;> rfl
  rw [← finiteDeadlineTimingProfile_eq_stoppingLawProfile_of_laws
    reward deadline mixed (quittingFiniteCalendarDecodedLaws x) hlaws]
  have hmap := quittingFiniteDeadlineTimingPayoffMap_stdSimplexEquiv
    reward deadline mixed
  have hrecover :
      (fun who => Math.ProbabilityMassFunction.stdSimplexEquiv (mixed who)) = x := by
    funext who
    exact Math.ProbabilityMassFunction.stdSimplexEquiv.apply_symm_apply (x who)
  rw [hrecover] at hmap
  exact hmap.symm

end GameTheory
