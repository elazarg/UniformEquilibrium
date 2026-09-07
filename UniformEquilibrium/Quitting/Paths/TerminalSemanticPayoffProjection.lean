import UniformEquilibrium.Quitting.Paths.FiniteCalendarPayoffClosure
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-! # Exact payoff projection of the terminal semantic carrier

The first projection of the terminal semantic carrier is exactly the set of
actual terminal payoff vectors. Consequently, predicates on prescribed payoffs
can be tested on the fixed finite calendar without any regularity assumption.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem quittingTerminalSemanticCarrier_prescribed_mem_actualPayoffSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    pair.1 ∈ quittingActualTerminalPayoffSet reward := by
  change pair ∈ {candidate : QuittingTerminalSemanticPair ι |
    candidate.1 ∈ quittingActualTerminalPayoffSet reward}
  apply (closure_minimal ?_ ?_) hpair
  · rintro candidate ⟨profile, rfl⟩
    exact ⟨profile, rfl⟩
  · exact (isCompact_quittingActualTerminalPayoffSet reward).isClosed.preimage
      continuous_fst

theorem image_fst_quittingTerminalSemanticCarrier_eq_actualPayoffSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Prod.fst '' quittingTerminalSemanticCarrier reward =
      quittingActualTerminalPayoffSet reward := by
  apply Set.Subset.antisymm
  · rintro payoff ⟨pair, hpair, rfl⟩
    exact quittingTerminalSemanticCarrier_prescribed_mem_actualPayoffSet reward pair hpair
  · rintro payoff ⟨profile, rfl⟩
    exact ⟨quittingTerminalSemanticPair reward profile,
      subset_closure (Set.mem_range_self profile), rfl⟩

theorem forall_semanticCarrier_payoff_iff_forall_finiteCalendar
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (predicate : Payoff ι → Prop) :
    (∀ pair ∈ quittingTerminalSemanticCarrier reward, predicate pair.1) ↔
      ∀ point, predicate (quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1)) point) := by
  have heq := image_fst_quittingTerminalSemanticCarrier_eq_actualPayoffSet reward
  rw [quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff] at heq
  constructor
  · intro h point
    have hmem : quittingFiniteDeadlineTimingPayoffMap reward
        (Fintype.card ι * (Fintype.card ι + 1)) point ∈
        Prod.fst '' quittingTerminalSemanticCarrier reward := by
      rw [heq]
      exact Set.mem_range_self point
    obtain ⟨pair, hpair, hvalue⟩ := hmem
    rw [← hvalue]
    exact h pair hpair
  · intro h pair hpair
    have hmem : pair.1 ∈ Prod.fst '' quittingTerminalSemanticCarrier reward :=
      ⟨pair, hpair, rfl⟩
    rw [heq] at hmem
    obtain ⟨point, hvalue⟩ := hmem
    rw [← hvalue]
    exact h point

end GameTheory
