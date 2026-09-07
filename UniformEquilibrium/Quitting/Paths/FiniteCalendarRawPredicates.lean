import Mathlib.Topology.Order.Lattice
import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPayoff

/-! # Exact payoff-exclusion predicates on the finite calendar -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (predicate : Payoff ι → Prop) :
    (∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
        (Fintype.card ι * (Fintype.card ι + 1))),
      predicate (quittingFiniteCalendarRawPayoff reward _ x)) ↔
      ∀ profile : (quittingGame reward).BehaviorProfile,
        predicate (fun observer => quittingTerminalPayoff reward profile observer) := by
  constructor
  · intro hraw profile
    have hmem : (fun observer => quittingTerminalPayoff reward profile observer) ∈
        quittingActualTerminalPayoffSet reward := ⟨profile, rfl⟩
    rw [quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff reward] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [← hx, ← quittingFiniteCalendarRawPayoff_eq_timingPayoffMap]
    exact hraw x
  · intro hactual x
    let profile := quittingStoppingLawProfile reward
      (quittingFiniteCalendarDecodedLaws x)
    rw [quittingFiniteCalendarRawPayoff_eq_terminalPayoff]
    exact hactual profile

def HasQuittingActualWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owners : Finset ι) : Prop :=
  (∀ who ∈ owners, 0 ≤ reward (quittingSingletonTerminal who) who) ∧
  ∀ profile : (quittingGame reward).BehaviorProfile, ∃ who ∈ owners,
    quittingTerminalPayoff reward profile who ≤
      reward (quittingSingletonTerminal who) who

def HasQuittingFiniteCalendarRawWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owners : Finset ι) : Prop :=
  (∀ who ∈ owners, 0 ≤ reward (quittingSingletonTerminal who) who) ∧
  ∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))), ∃ who ∈ owners,
    quittingFiniteCalendarRawPayoff reward _ x who ≤
      reward (quittingSingletonTerminal who) who

theorem hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owners : Finset ι) :
    HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners ↔
      HasQuittingActualWeakSubsetExclusion reward owners := by
  unfold HasQuittingFiniteCalendarRawWeakSubsetExclusion
    HasQuittingActualWeakSubsetExclusion
  let predicate : Payoff ι → Prop := fun value =>
    ∃ who ∈ owners, value who ≤ reward (quittingSingletonTerminal who) who
  exact and_congr Iff.rfl
    (forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff reward predicate)

def HasQuittingActualStrictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile, ∃ who,
    quittingTerminalPayoff reward profile who ≤
      reward (quittingSingletonTerminal who) who - gap

def HasQuittingFiniteCalendarRawStrictSingletonDeficit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) : Prop :=
  ∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))), ∃ who,
    quittingFiniteCalendarRawPayoff reward _ x who ≤
      reward (quittingSingletonTerminal who) who - gap

theorem hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (gap : ℝ) :
    HasQuittingFiniteCalendarRawStrictSingletonDeficit reward gap ↔
      HasQuittingActualStrictSingletonDeficit reward gap := by
  unfold HasQuittingFiniteCalendarRawStrictSingletonDeficit
    HasQuittingActualStrictSingletonDeficit
  let predicate : Payoff ι → Prop := fun value =>
    ∃ who, value who ≤ reward (quittingSingletonTerminal who) who - gap
  exact forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff reward predicate

def HasQuittingActualNonconcentratedGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ) : Prop :=
  ∀ profile : (quittingGame reward).BehaviorProfile, ∃ weight : ι → ℝ,
    (∀ who, 0 ≤ weight who) ∧ (∑ who, weight who = 1) ∧
    (∀ who, weight who ≤ beta) ∧
    ∑ who, weight who *
      (quittingTerminalPayoff reward profile who -
        reward (quittingSingletonTerminal who) who) ≤ 0

def HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ) : Prop :=
  ∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))), ∃ weight : ι → ℝ,
    (∀ who, 0 ≤ weight who) ∧ (∑ who, weight who = 1) ∧
    (∀ who, weight who ≤ beta) ∧
    ∑ who, weight who *
      (quittingFiniteCalendarRawPayoff reward _ x who -
        reward (quittingSingletonTerminal who) who) ≤ 0

theorem hasQuittingFiniteCalendarRawNonconcentratedGroupExclusion_iff_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (beta : ℝ) :
    HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta ↔
      HasQuittingActualNonconcentratedGroupExclusion reward beta := by
  unfold HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion
    HasQuittingActualNonconcentratedGroupExclusion
  let predicate : Payoff ι → Prop := fun value =>
    ∃ weight : ι → ℝ, (∀ who, 0 ≤ weight who) ∧
      (∑ who, weight who = 1) ∧ (∀ who, weight who ≤ beta) ∧
      ∑ who, weight who *
        (value who - reward (quittingSingletonTerminal who) who) ≤ 0
  exact forall_finiteCalendarRawPayoff_iff_forall_actualTerminalPayoff reward predicate

def HasQuittingFiniteCalendarRawStrictExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ x : MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1))), ∃ who,
    quittingFiniteCalendarRawPayoff reward _ x who <
      reward (quittingSingletonTerminal who) who

def quittingPayoffSingletonDeficitMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : Payoff ι) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun who =>
    reward (quittingSingletonTerminal who) who - value who

omit [DecidableEq ι] in
theorem continuous_quittingPayoffSingletonDeficitMaximum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingPayoffSingletonDeficitMaximum reward) := by
  unfold quittingPayoffSingletonDeficitMaximum
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro who _
  exact continuous_const.sub (continuous_apply who)

theorem exists_positive_actual_strictSingletonDeficit_of_rawStrictExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hraw : HasQuittingFiniteCalendarRawStrictExclusion reward) :
    ∃ gap > 0, HasQuittingActualStrictSingletonDeficit reward gap := by
  let carrier := quittingActualTerminalPayoffSet reward
  have hcompact : IsCompact carrier := isCompact_quittingActualTerminalPayoffSet reward
  have hnonempty : carrier.Nonempty := by
    exact ⟨_, quittingAlwaysContinueProfile reward, rfl⟩
  obtain ⟨minimum, hminimumMem, hminimum⟩ := hcompact.exists_isMinOn hnonempty
    (continuous_quittingPayoffSingletonDeficitMaximum reward).continuousOn
  have hminimumPos : 0 < quittingPayoffSingletonDeficitMaximum reward minimum := by
    dsimp only [carrier] at hminimumMem
    rw [quittingActualTerminalPayoffSet_eq_finiteCalendarPayoff reward] at hminimumMem
    obtain ⟨x, hx⟩ := hminimumMem
    obtain ⟨who, hwho⟩ := hraw x
    have hcoord : 0 < reward (quittingSingletonTerminal who) who - minimum who := by
      rw [← congrFun hx who,
        ← quittingFiniteCalendarRawPayoff_eq_timingPayoffMap]
      linarith
    exact hcoord.trans_le
      (Finset.le_sup' (s := Finset.univ) (f := fun player =>
        reward (quittingSingletonTerminal player) player - minimum player)
        (Finset.mem_univ who))
  refine ⟨quittingPayoffSingletonDeficitMaximum reward minimum,
    hminimumPos, ?_⟩
  intro profile
  let value : Payoff ι := fun observer => quittingTerminalPayoff reward profile observer
  have hvalueMem : value ∈ carrier := ⟨profile, rfl⟩
  have hminLe := hminimum hvalueMem
  change quittingPayoffSingletonDeficitMaximum reward minimum ≤
    quittingPayoffSingletonDeficitMaximum reward value at hminLe
  obtain ⟨who, _, hwho⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who => reward (quittingSingletonTerminal who) who - value who)
  refine ⟨who, ?_⟩
  unfold quittingPayoffSingletonDeficitMaximum
    at hminLe
  rw [hwho] at hminLe
  dsimp only [value] at hminLe
  change quittingTerminalPayoff reward profile who ≤
    reward (quittingSingletonTerminal who) who -
      Finset.univ.sup' Finset.univ_nonempty
        (fun player => reward (quittingSingletonTerminal player) player -
          minimum player)
  linarith

theorem hasQuittingFiniteCalendarRawStrictExclusion_iff_exists_positive_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    HasQuittingFiniteCalendarRawStrictExclusion reward ↔
      ∃ gap > 0, HasQuittingActualStrictSingletonDeficit reward gap := by
  constructor
  · exact exists_positive_actual_strictSingletonDeficit_of_rawStrictExclusion reward
  · rintro ⟨gap, hgap, hactual⟩ x
    have hraw :=
      (hasQuittingFiniteCalendarRawStrictSingletonDeficit_iff_actual reward gap).mpr
        hactual
    obtain ⟨who, hwho⟩ := hraw x
    exact ⟨who, hwho.trans_lt (by linarith)⟩

end GameTheory
