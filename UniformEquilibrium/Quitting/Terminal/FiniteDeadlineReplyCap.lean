import UniformEquilibrium.Quitting.Root.CommonPrefixCapStability
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingGame

/-! # Finite-deadline reply caps -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Best displayed pure reply in the finite date-or-Never timing menu. -/
def quittingFiniteDeadlineReplyCap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset (QuittingFiniteDeadlineTimingAction deadline)).Nonempty)
    (fun action => quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
        (quittingPureTimeBehaviorStrategy reward who
          (quittingFiniteDeadlineTimingActionTime action))) who)

/-- Approximate Nash against exactly the displayed finite timing menu. -/
def IsQuittingFiniteDeadlineNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (error : ℝ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) : Prop :=
  ∀ who, quittingFiniteDeadlineReplyCap reward deadline mixed who ≤
    quittingTerminalPayoff reward
      (quittingFiniteDeadlineTimingProfile reward deadline mixed) who + error

theorem isQuittingFiniteDeadlineNash_iff_pure
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (error : ℝ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    IsQuittingFiniteDeadlineNash reward deadline error mixed ↔
      ∀ who (action : QuittingFiniteDeadlineTimingAction deadline),
        quittingTerminalPayoff reward
            (Function.update
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
              (quittingPureTimeBehaviorStrategy reward who
                (quittingFiniteDeadlineTimingActionTime action))) who ≤
          quittingTerminalPayoff reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed) who + error := by
  constructor
  · intro hnash who action
    exact (Finset.le_sup' (fun choice => quittingTerminalPayoff reward
      (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
        (quittingPureTimeBehaviorStrategy reward who
          (quittingFiniteDeadlineTimingActionTime choice))) who)
      (Finset.mem_univ action)).trans (hnash who)
  · intro hpure who
    apply Finset.sup'_le
    intro action _
    exact hpure who action

/-- The displayed cap is literally the finite supremum of pure stopping-time
values against the behavioral realization's live-root sequence. -/
theorem quittingFiniteDeadlineReplyCap_eq_sup_pureTimeTerminalValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (deadline : ℕ)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline))
    (who : ι) :
    quittingFiniteDeadlineReplyCap reward deadline mixed who =
      Finset.univ.sup' (Finset.univ_nonempty :
        (Finset.univ : Finset (QuittingFiniteDeadlineTimingAction deadline)).Nonempty)
        (fun action => quittingRootSequencePureTimeTerminalValue reward
          (quittingProfileLiveRoot reward
            (quittingFiniteDeadlineTimingProfile reward deadline mixed)) who
          (quittingFiniteDeadlineTimingActionTime action) 0) := by
  unfold quittingFiniteDeadlineReplyCap
  congr 1
  funext action
  exact quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward
    (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
    (quittingFiniteDeadlineTimingActionTime action)

end GameTheory
