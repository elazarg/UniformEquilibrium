import UniformEquilibrium.Quitting.Terminal.FiniteOpponentLateResponse
import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators

/-! # Exact signed late response to an arbitrary pivot stopping law -/

noncomputable section

namespace GameTheory

open _root_.Math.Probability
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem never_product_erase_eq
    (laws : ι → PMF (Option ℕ)) (who : ι) (hwho : laws who = PMF.pure none) :
    (∏ j ∈ Finset.univ.erase who, (laws j none).toReal) =
      ∏ j, (laws j none).toReal := by
  simpa [hwho] using Finset.prod_erase_mul Finset.univ
    (fun j ↦ (laws j none).toReal) (Finset.mem_univ who)

private theorem finite_clock_pure_none (deadline : ℕ) :
    IsFiniteClockStoppingLaw deadline (PMF.pure none) := by
  intro choice hchoice
  left
  simpa [PMF.pure_apply] using hchoice

/-- The exact pure-pivot integrand for a late response, expressed through
the actual censored-head payoff and three literal stopping-time indicators. -/
theorem quittingTerminalPayoff_pure_pivot_late_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline time : ℕ) (hdeadline : 0 < deadline) (htime : deadline ≤ time)
    (hpivot : laws pivot = PMF.pure none) (hresponder : laws responder = PMF.pure none)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (laws j)) (choice : Option ℕ) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update laws pivot (PMF.pure choice))
            responder (PMF.pure (some time)))) who =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws pivot
            (PMF.pure (censorLateFiniteStoppingOutcome (deadline - 1) choice)))) who +
        (∏ j, (laws j none).toReal) *
          (reward (quittingSingletonTerminal responder) who *
              stoppingLawTailIndicator deadline choice +
            (reward (quittingSingletonTerminal pivot) who -
              reward (quittingSingletonTerminal responder) who) *
              stoppingLawIntervalIndicator deadline time choice +
            (reward ⟨{pivot, responder}, by simp⟩ who -
              reward (quittingSingletonTerminal responder) who) *
              (if choice = some time then 1 else 0)) := by
  have hunpin : Function.update laws pivot (PMF.pure none) = laws := by
    rw [← hpivot, Function.update_eq_self]
  have hbaseFinite : ∀ j, j ≠ responder → IsFiniteClockStoppingLaw deadline (laws j) := by
    intro j hj
    by_cases hjp : j = pivot
    · subst j
      rw [hpivot]
      exact finite_clock_pure_none deadline
    · exact hfinite j hjp hj
  cases choice with
  | none =>
      rw [hunpin]
      rw [quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
        reward laws responder who deadline hbaseFinite htime]
      rw [← hresponder, Function.update_eq_self,
        never_product_erase_eq laws responder hresponder]
      simp [censorLateFiniteStoppingOutcome, hunpin,
        stoppingLawTailIndicator, stoppingLawIntervalIndicator]
  | some chosen =>
      by_cases hchosen : chosen < deadline
      · have hfinite' : ∀ j, j ≠ responder → IsFiniteClockStoppingLaw deadline
            (Function.update laws pivot (PMF.pure (some chosen)) j) := by
          intro j hj value hvalue
          by_cases hjp : j = pivot
          · subst j
            right
            refine ⟨chosen, hchosen, ?_⟩
            simpa [PMF.pure_apply] using hvalue
          · apply hbaseFinite j hj value
            simpa [Function.update_of_ne hjp] using hvalue
        have hlate := quittingTerminalPayoff_stoppingLawProfile_late_pure_observer_eq_never_add
          reward (Function.update laws pivot (PMF.pure (some chosen))) responder who
          deadline hfinite' htime
        have hzero :
            (∏ j ∈ Finset.univ.erase responder,
              (Function.update laws pivot (PMF.pure (some chosen)) j none).toReal) = 0 := by
          apply Finset.prod_eq_zero
            (show pivot ∈ Finset.univ.erase responder by simp [hne.symm])
          simp
        rw [hzero, zero_mul, add_zero] at hlate
        have hnone : Function.update laws pivot (PMF.pure (some chosen)) responder =
            PMF.pure none := by simp [hne, hresponder]
        rw [← hnone, Function.update_eq_self] at hlate
        rw [hlate]
        simp [censorLateFiniteStoppingOutcome, show chosen ≤ deadline - 1 by omega,
          stoppingLawTailIndicator, stoppingLawIntervalIndicator, hchosen,
          show ¬ deadline ≤ chosen by omega, show chosen ≠ time by omega]
      · have hchosenGe : deadline ≤ chosen := by omega
        have hcensor : censorLateFiniteStoppingOutcome (deadline - 1) (some chosen) =
            none := by
          simp [censorLateFiniteStoppingOutcome, show ¬ chosen ≤ deadline - 1 by omega]
        rw [hcensor, hunpin]
        rcases lt_trichotomy chosen time with hbefore | htie | hafter
        · rw [quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
            reward laws pivot responder who hne deadline chosen time hchosenGe hbefore
            hpivot hresponder hfinite]
          simp [stoppingLawTailIndicator, stoppingLawIntervalIndicator, hchosen,
            hchosenGe, hbefore, ne_of_lt hbefore]
        · subst chosen
          rw [quittingTerminalPayoff_stoppingLawProfile_late_pair_eq_never_add
            reward laws pivot responder who hne deadline time htime hpivot hresponder hfinite]
          simp [stoppingLawTailIndicator, stoppingLawIntervalIndicator, hchosen]
        · rw [Function.update_comm hne.symm]
          rw [quittingTerminalPayoff_stoppingLawProfile_ordered_late_pair_eq_never_add
            reward laws responder pivot who hne.symm deadline time chosen htime hafter
            hresponder hpivot (fun j hjr hjp ↦ hfinite j hjp hjr)]
          simp [stoppingLawTailIndicator, stoppingLawIntervalIndicator, hchosen,
            hchosenGe, show ¬ chosen < time by omega, ne_of_gt hafter]

/-- The exact signed late-response formula for an arbitrary actual
pivot PMF. The early contribution is the actual censored-law payoff, not a
supplied coefficient or a conditional payoff divided by survival. -/
theorem quittingTerminalPayoff_arbitrary_pivot_late_response
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline time : ℕ) (hdeadline : 0 < deadline) (htime : deadline ≤ time)
    (hpivot : laws pivot = PMF.pure none) (hresponder : laws responder = PMF.pure none)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (laws j)) (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update laws pivot law)
            responder (PMF.pure (some time)))) who =
      quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update laws pivot (censorLateFiniteStoppingLaw law (deadline - 1)))) who +
        (∏ j, (laws j none).toReal) *
          (reward (quittingSingletonTerminal responder) who *
              (stoppingLawLateFiniteMass law (deadline - 1) + (law none).toReal) +
            (reward (quittingSingletonTerminal pivot) who -
              reward (quittingSingletonTerminal responder) who) *
              (∑ chosen ∈ Finset.Ico deadline time, (law (some chosen)).toReal) +
            (reward ⟨{pivot, responder}, by simp⟩ who -
              reward (quittingSingletonTerminal responder) who) *
              (law (some time)).toReal) := by
  let early := fun choice ↦ quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward (Function.update laws pivot
      (PMF.pure (censorLateFiniteStoppingOutcome (deadline - 1) choice)))) who
  have hactual : quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update (Function.update laws pivot law) responder (PMF.pure (some time)))) who =
      expect law (fun choice ↦ quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update laws pivot (PMF.pure choice))
            responder (PMF.pure (some time)))) who) := by
    rw [Function.update_comm hne.symm, quittingTerminalPayoff_stoppingLawProfile_update_eq_expect]
    apply congrArg (expect law)
    funext choice
    rw [Function.update_comm hne]
  have hearly : expect law early = quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update laws pivot (censorLateFiniteStoppingLaw law (deadline - 1)))) who := by
    symm
    rw [quittingTerminalPayoff_stoppingLawProfile_update_eq_expect,
      censorLateFiniteStoppingLaw, expect_map]
  have hearlyBound : ∀ choice, |early choice| ≤ quittingRewardBound reward := by
    intro choice
    exact abs_quittingTerminalPayoff_le_quittingRewardBound reward _ who
  rw [hactual]
  calc
    _ = expect law (fun choice ↦ early choice + (∏ j, (laws j none).toReal) *
          (reward (quittingSingletonTerminal responder) who *
              stoppingLawTailIndicator deadline choice +
            (reward (quittingSingletonTerminal pivot) who -
              reward (quittingSingletonTerminal responder) who) *
              stoppingLawIntervalIndicator deadline time choice +
            (reward ⟨{pivot, responder}, by simp⟩ who -
              reward (quittingSingletonTerminal responder) who) *
              (if choice = some time then 1 else 0))) := by
      apply congrArg (expect law)
      funext choice
      exact quittingTerminalPayoff_pure_pivot_late_response reward laws pivot responder who hne
        deadline time hdeadline htime hpivot hresponder hfinite choice
    _ = _ := by
      rw [expect_stoppingLaw_late_affine law deadline time early hearlyBound,
        hearly, stoppingLaw_survival_eq_lateFiniteMass_add_none law hdeadline]

/-- Unconditional early contribution read from the actual pivot law censored
at the inclusive cutoff immediately before the deadline, while the responder
chooses Never. -/
def quittingPivotEarlyContribution
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι)
    (deadline : ℕ) (law : PMF (Option ℕ)) : ℝ :=
  quittingTerminalPayoff reward
    (quittingStoppingLawProfile reward
      (Function.update
        (Function.update opponents pivot (censorLateFiniteStoppingLaw law (deadline - 1)))
        responder (PMF.pure none))) who

/-- The signed late-response identity for an arbitrary actual pivot law and fixed finite
remaining opponents. Both the early term and every probability coefficient
are computed from the source laws; rewards have arbitrary signs. -/
theorem quittingTerminalPayoff_pivot_late_response_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline time : ℕ) (hdeadline : 0 < deadline) (htime : deadline ≤ time)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (opponents j)) (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents pivot law)
            responder (PMF.pure (some time)))) who =
      quittingPivotEarlyContribution reward opponents pivot responder who deadline law +
        (∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal) *
          (reward (quittingSingletonTerminal responder) who *
              (stoppingLawLateFiniteMass law (deadline - 1) + (law none).toReal) +
            (reward (quittingSingletonTerminal pivot) who -
              reward (quittingSingletonTerminal responder) who) *
              (∑ chosen ∈ Finset.Ico deadline time, (law (some chosen)).toReal) +
            (reward ⟨{pivot, responder}, by simp⟩ who -
              reward (quittingSingletonTerminal responder) who) *
              (law (some time)).toReal) := by
  let baseline := Function.update (Function.update opponents pivot (PMF.pure none))
    responder (PMF.pure none)
  have hpivot : baseline pivot = PMF.pure none := by simp [baseline, hne.symm]
  have hresponder : baseline responder = PMF.pure none := by simp [baseline]
  have hbaseFinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (baseline j) := by
    intro j hjp hjr
    simpa [baseline, hjp, hjr] using hfinite j hjp hjr
  have h := quittingTerminalPayoff_arbitrary_pivot_late_response reward baseline
    pivot responder who hne deadline time hdeadline htime hpivot hresponder hbaseFinite law
  have hinput : Function.update (Function.update baseline pivot law)
      responder (PMF.pure (some time)) =
      Function.update (Function.update opponents pivot law) responder (PMF.pure (some time)) := by
    funext j
    by_cases hjr : j = responder
    · subst j
      simp
    · by_cases hjp : j = pivot
      · subst j
        simp [hne.symm]
      · simp [baseline, hjr, hjp]
  have hhead : Function.update baseline pivot (censorLateFiniteStoppingLaw law (deadline - 1)) =
      Function.update
        (Function.update opponents pivot (censorLateFiniteStoppingLaw law (deadline - 1)))
        responder (PMF.pure none) := by
    funext j
    by_cases hjr : j = responder
    · subst j
      simp [baseline, hne]
    · by_cases hjp : j = pivot
      · subst j
        simp [hne.symm]
      · simp [baseline, hjr, hjp]
  have hproduct : (∏ j, (baseline j none).toReal) =
      ∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal := by
    rw [← never_product_erase_eq baseline pivot hpivot]
    rw [← Finset.prod_erase_mul (Finset.univ.erase pivot)
      (fun j ↦ (baseline j none).toReal) (show responder ∈ Finset.univ.erase pivot by simp [hne])]
    simp only [hresponder, PMF.pure_apply_self, ENNReal.toReal_one, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    have hjr := Finset.ne_of_mem_erase hj
    have hjp := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    simp [baseline, hjr, hjp]
  rw [hinput, hhead, hproduct] at h
  exact h

end GameTheory
