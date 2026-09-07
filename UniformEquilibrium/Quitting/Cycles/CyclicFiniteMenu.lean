import UniformEquilibrium.Quitting.Cycles.CyclicFiniteWord
import UniformEquilibrium.Quitting.Root.FiniteDeadlineWordRealization
import UniformEquilibrium.Quitting.Terminal.StoppingLawCanonicalization

/-! # Exact finite-menu realization of literal cyclic truncations -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] {period : ℕ}

omit [DecidableEq ι] in
theorem quittingCyclicFiniteProfile_eq_truncatedRootProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (initial : Fin period) (deadline : ℕ) :
    quittingCyclicFiniteProfile reward roots initial deadline =
      quittingRootSequenceProfile reward
        (quittingTruncatedRoots (quittingCyclicRootSequence roots initial) deadline) 0 := by
  funext who time history
  rw [quittingCyclicFiniteProfile_apply]
  simp only [quittingRootSequenceProfile, Nat.zero_add]
  split_ifs with htime
  · rw [quittingTruncatedRoots_of_lt _ htime]
    rfl
  · rw [quittingTruncatedRoots_of_le _ (Nat.le_of_not_gt htime)]
    rfl

/-- One actual finite product menu realizes the exact laws, the full semantic pair,
and every pure-date response payoff of the same literal finite cyclic profile. -/
theorem exists_finiteDeadlineTimingProfile_cyclicFinite_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : Fin period → ι → PMF Bool) (initial : Fin period) (deadline : ℕ) :
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline),
      (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
        quittingBehaviorStoppingLaw reward
          (quittingCyclicFiniteProfile reward roots initial deadline who)) ∧
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
        quittingTerminalSemanticPair reward
          (quittingCyclicFiniteProfile reward roots initial deadline) ∧
      ∀ who choice, quittingTerminalPayoff reward
          (Function.update (quittingFiniteDeadlineTimingProfile reward deadline mixed) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who =
        quittingTerminalPayoff reward
          (Function.update (quittingCyclicFiniteProfile reward roots initial deadline) who
            (quittingPureTimeBehaviorStrategy reward who choice)) who := by
  obtain ⟨mixed, hmixed⟩ := exists_finiteDeadlineTimingLaws_of_truncatedRoots reward
    (quittingCyclicRootSequence roots initial) deadline
  rw [← quittingCyclicFiniteProfile_eq_truncatedRootProfile] at hmixed
  have hcompact : (fun who => quittingFiniteDeadlineTimingLaw (mixed who)) =
      quittingCompactStoppingLawsOfProfile reward
        (quittingCyclicFiniteProfile reward roots initial deadline) := by
    funext who
    unfold quittingCompactStoppingLawsOfProfile
    apply congrArg Math.Probability.CompactStoppingLaw.ofPMF
    simpa [quittingFiniteDeadlineTimingLaw] using hmixed who
  refine ⟨mixed, hmixed, ?_, ?_⟩
  · rw [quittingTerminalSemanticPair_eq_compactStoppingLawsOfProfile reward
      (quittingCyclicFiniteProfile reward roots initial deadline)]
    simp only [quittingFiniteDeadlineTimingProfile, hcompact]
  · intro who choice
    rw [quittingTerminalPayoff_update_pureTime_eq_compactStoppingLawsOfProfile reward
      (quittingCyclicFiniteProfile reward roots initial deadline)]
    simp only [quittingFiniteDeadlineTimingProfile, hcompact]

end GameTheory
