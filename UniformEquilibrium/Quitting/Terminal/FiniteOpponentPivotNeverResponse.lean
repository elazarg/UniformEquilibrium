import UniformEquilibrium.Quitting.Terminal.GeometricPivotCapDomination

/-! # The exact signed Never endpoint of an actual pivot law -/

noncomputable section

namespace GameTheory

open Filter
open _root_.Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Against arbitrary independent complete stopping laws, late finite
responses converge to the actual Never payoff plus the surviving signed
singleton contribution, for every payoff observer. -/
theorem quittingTerminalPayoff_stoppingLawProfile_pure_tendsto_never_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → PMF (Option ℕ)) (mixer observer : ι) :
    Tendsto (fun time ↦ quittingTerminalPayoff reward
      (quittingStoppingLawProfile reward
        (Function.update laws mixer (PMF.pure (some time)))) observer) atTop
      (nhds (quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward (Function.update laws mixer (PMF.pure none))) observer +
        (∏ j ∈ Finset.univ.erase mixer, (laws j none).toReal) *
          reward (quittingSingletonTerminal mixer) observer)) := by
  letI : Nonempty ι := ⟨mixer⟩
  let observed := quittingObserverReward reward observer
  let compact := fun j ↦ CompactStoppingLaw.ofPMF (laws j)
  have hprofile : quittingCompactStoppingLawProfile observed compact =
      quittingStoppingLawProfile observed laws := by
    funext player
    change quittingStoppingLawBehaviorStrategy observed player
        (CompactStoppingLaw.ofPMF (laws player)).toPMF = _
    rw [CompactStoppingLaw.toPMF_ofPMF]
    rfl
  have hlimit :=
    quittingTerminalPayoff_update_finiteTime_tendsto_never_add_opponentNever_mul_singleton
      observed compact mixer
  rw [hprofile] at hlimit
  simp only [← quittingTerminalPayoff_stoppingLawProfile_update_pure_eq,
    quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff] at hlimit
  have hobs (actual : ι → PMF (Option ℕ)) :
      quittingStoppingLawExpectedPayoff observed actual mixer =
        quittingStoppingLawExpectedPayoff reward actual observer := by
    unfold quittingStoppingLawExpectedPayoff
    apply congrArg (expect _)
    funext outcome
    cases outcome <;> rfl
  simp only [hobs] at hlimit
  have hproduct : quittingOpponentNeverProduct compact mixer =
      ∏ j ∈ Finset.univ.erase mixer, (laws j none).toReal := by
    unfold quittingOpponentNeverProduct
    apply Finset.prod_congr rfl
    intro j _
    rw [← CompactStoppingLaw.toPMF_apply_toReal]
    simp only [compact, CompactStoppingLaw.toPMF_ofPMF]
    rfl
  simp only [quittingTerminalPayoff_stoppingLawProfile_eq_expectedPayoff]
  simpa only [hproduct, observed, quittingObserverReward] using hlimit

/-- The exact actual Never response equals its unconditional early
contribution plus the surviving finite pivot tail times the pivot singleton
reward. No payoff-sign or properness assumption is needed. -/
theorem quittingTerminalPayoff_pivot_never_response_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (opponents : ι → PMF (Option ℕ)) (pivot responder who : ι) (hne : responder ≠ pivot)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (hfinite : ∀ j, j ≠ pivot → j ≠ responder →
      IsFiniteClockStoppingLaw deadline (opponents j)) (law : PMF (Option ℕ)) :
    quittingTerminalPayoff reward
        (quittingStoppingLawProfile reward
          (Function.update (Function.update opponents pivot law) responder (PMF.pure none))) who =
      quittingPivotEarlyContribution reward opponents pivot responder who deadline law +
        (∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal) *
          reward (quittingSingletonTerminal pivot) who *
          stoppingLawLateFiniteMass law (deadline - 1) := by
  have hgeneral := quittingTerminalPayoff_stoppingLawProfile_pure_tendsto_never_add
    reward (Function.update opponents pivot law) responder who
  have hfiniteLimit := quittingTerminalPayoff_pivot_late_response_tendsto
    reward opponents pivot responder who hne deadline hdeadline hfinite law
  have hproduct :
      (∏ j ∈ Finset.univ.erase responder,
        (Function.update opponents pivot law j none).toReal) =
      (∏ j ∈ (Finset.univ.erase pivot).erase responder, (opponents j none).toReal) *
        (law none).toReal := by
    rw [← Finset.prod_erase_mul (Finset.univ.erase responder)
      (fun j ↦ (Function.update opponents pivot law j none).toReal)
      (show pivot ∈ Finset.univ.erase responder by simp [hne.symm])]
    simp only [Function.update_self]
    congr 1
    rw [Finset.erase_right_comm]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj))]
  rw [hproduct] at hgeneral
  have heq := tendsto_nhds_unique hgeneral hfiniteLimit
  unfold quittingPivotLateLimitValue at heq
  nlinarith

end GameTheory
