import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFinFourStrictMinimumPlateauIsolation
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.TerminalSemanticPayoffProjection

/-! # Sign-free four-player weak-subset payoff exclusion

The four-player strict-minimum plateau is prescribed-payoff separated above
every own singleton.  Its exact actual-payoff projection therefore contradicts
weak payoff exclusion on any supplied subset, without singleton sign premises.
-/

noncomputable section

namespace GameTheory

/-- For four players, payoff exclusion on a fixed designated subset implies a
uniform-equilibrium payoff without any singleton sign assumption.  Nonemptiness
of the subset is forced by the exclusion hypothesis itself. -/
theorem exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owners : Finset (Fin 4))
    (hexclusion : ∀ profile : (quittingGame reward).BehaviorProfile,
      ∃ owner ∈ owners,
        quittingTerminalPayoff reward profile owner ≤
          reward (quittingSingletonTerminal owner) owner) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  obtain ⟨pair, hpair, -, -, -, -, habove⟩ :=
    exists_finFour_strictMinimum_allContinuePlateau_of_no_uniformPayoff
      reward hno
  obtain ⟨profile, hprofile⟩ :=
    quittingTerminalSemanticCarrier_prescribed_mem_actualPayoffSet
      reward pair hpair
  obtain ⟨owner, howner, hle⟩ := hexclusion profile
  have hstrict := habove owner |>.2
  have hvalue : quittingTerminalPayoff reward profile owner = pair.1 owner := by
    change (fun observer => quittingTerminalPayoff reward profile observer) owner = _
    exact congrFun hprofile owner
  rw [hvalue] at hle
  exact (not_lt_of_ge hle) hstrict

/-- The sign-free raw finite-calendar exclusion predicate has the same
four-player qualitative consequence. -/
theorem exists_uniformEquilibriumPayoff_of_finFour_rawSignFreeWeakSubsetExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owners : Finset (Fin 4))
    (hexclusion : ∀ point : MixedSimplex (Fin 4)
        (fun _ => QuittingFiniteDeadlineTimingAction (4 * (4 + 1))),
      ∃ owner ∈ owners,
        quittingFiniteCalendarRawPayoff reward _ point owner ≤
          reward (quittingSingletonTerminal owner) owner) :
    ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply exists_uniformEquilibriumPayoff_of_finFour_signFreeWeakSubsetExclusion
    reward owners
  let predicate : Payoff (Fin 4) → Prop := fun value =>
    ∃ owner ∈ owners,
      value owner ≤ reward (quittingSingletonTerminal owner) owner
  exact (forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff
    reward predicate).mp hexclusion

end GameTheory
