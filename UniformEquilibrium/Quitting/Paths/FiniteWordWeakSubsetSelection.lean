import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.FiniteUnpreemptedSoloExit
import UniformEquilibrium.Quitting.Paths.FiniteWordSelectedOwnerRates
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformPayoffSelection

/-! # Finite selected words under designated weak exclusion

The all-preempted branch uses the shared eligible-owner recurrence.  Its date
bound is uniform across phases for the fixed table and depends on the minimum
strict-preemption gap over designated owners.  It is not the separate
reward-table-uniform threshold algorithm.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weak exclusion on literal finite words, with witnesses retained in a
designated owner set. -/
def QuittingFiniteWordWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι) : Prop :=
  ∀ roots : List (ι → PMF Bool), ∃ owner ∈ owners,
    quittingTerminalPayoff reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) owner ≤
      reward (quittingSingletonTerminal owner) owner

omit [DecidableEq ι] in
/-- Designated weak exclusion is the shared owner-exclusion predicate with
eligibility given by membership in the owner set. -/
theorem finiteWordOwnerExclusion_of_weakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners) :
    QuittingFiniteWordOwnerExclusion reward (fun owner => owner ∈ owners) := by
  intro roots
  obtain ⟨owner, howner, hpayoff⟩ := hWE roots
  exact ⟨owner, howner, hpayoff⟩

omit [DecidableEq ι] in
/-- Actual-profile weak subset exclusion restricts to literal finite words. -/
theorem finiteWordWeakSubsetExclusion_of_actual
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingActualWeakSubsetExclusion reward owners) :
    QuittingFiniteWordWeakSubsetExclusion reward owners := by
  intro roots
  exact hexclusion.2 (quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward))

/-- In the all-designated-preempted branch, a finite literal word has the
shared fixed-table phase and date bounds for some positive minimum designated
preemption gap. -/
theorem exists_finiteWord_debtSum_and_length_le_of_weakSubset_allDesignatedPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners)
    (hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    let initial := quittingFiniteWordDebt reward []
    let scale := (32 * M + 6 * initial) / 3
    ∃ gap : ℝ, 0 < gap ∧
      ∃ roots : List (ι → PMF Bool),
        quittingFiniteWordDebt reward roots ≤ ε ∧
          roots.length ≤ Nat.ceil (scale / ε) *
            quittingSelectedOwnerUniformPhaseRowBound M initial ε gap := by
  dsimp only
  obtain ⟨owner, howner, -⟩ := hWE []
  obtain ⟨preemption⟩ := nonempty_eligibleBlockerCertificate_of_strictPreempted
    reward (fun player => player ∈ owners) ⟨owner, howner⟩ hpreempted
  obtain ⟨roots, hdebt, hlength⟩ :=
    exists_finiteWord_debtSum_and_length_le_of_ownerExclusion
      reward (fun player => player ∈ owners)
        (finiteWordOwnerExclusion_of_weakSubsetExclusion reward owners hWE)
        preemption M hM hreward hε
  exact ⟨preemption.gap, preemption.gap_pos, roots, hdebt, hlength⟩

/-- For one fixed table, the designated preemption certificate and its
positive gap are chosen before the target accuracy.  The same gap therefore
controls the literal-word date bound at every positive accuracy. -/
theorem exists_designatedBlockerCertificate_forall_epsilon_finiteWord_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners)
    (hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ preemption : QuittingEligibleBlockerCertificate reward
        (fun owner => owner ∈ owners),
      ∀ ε : ℝ, 0 < ε →
        let initial := quittingFiniteWordDebt reward []
        let scale := (32 * M + 6 * initial) / 3
        ∃ roots : List (ι → PMF Bool),
          quittingFiniteWordDebt reward roots ≤ ε ∧
            roots.length ≤ Nat.ceil (scale / ε) *
              quittingSelectedOwnerUniformPhaseRowBound
                M initial ε preemption.gap := by
  obtain ⟨owner, howner, -⟩ := hWE []
  obtain ⟨preemption⟩ := nonempty_eligibleBlockerCertificate_of_strictPreempted
    reward (fun player => player ∈ owners) ⟨owner, howner⟩ hpreempted
  refine ⟨preemption, ?_⟩
  intro ε hε
  exact exists_finiteWord_debtSum_and_length_le_of_ownerExclusion
    reward (fun player => player ∈ owners)
      (finiteWordOwnerExclusion_of_weakSubsetExclusion reward owners hWE)
      preemption M hM hreward hε

/-- If every designated owner is strictly preempted, a literal finite word
reaches any positive total-debt accuracy. -/
theorem exists_finiteWord_debtSum_le_of_weakSubset_allDesignatedPreempted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners)
    (hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker)
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  obtain ⟨-, -, roots, hdebt, -⟩ :=
    exists_finiteWord_debtSum_and_length_le_of_weakSubset_allDesignatedPreempted
      reward owners hWE hpreempted hM hε hreward
  exact ⟨roots, hdebt⟩

/-- Literal designated weak exclusion with nonnegative singleton rewards only
on designated owners selects a finite word of arbitrary positive debt
accuracy. -/
theorem exists_finiteWord_debtSum_le_of_weakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners)
    (hsingleton : ∀ owner ∈ owners,
      0 ≤ reward (quittingSingletonTerminal owner) owner)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ roots : List (ι → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε := by
  let M := quittingRewardBound reward + 1
  have hM : 0 < M := by
    dsimp only [M]
    linarith [quittingRewardBound_nonneg reward]
  have hreward : ∀ terminal player, |reward terminal player| ≤ M := by
    intro terminal player
    exact (abs_reward_le_quittingRewardBound reward terminal player).trans (by
      dsimp only [M]
      linarith)
  by_cases hpreempted : ∀ owner ∈ owners, ∃ blocker, 0 <
      reward (quittingSingletonTerminal blocker) blocker -
        reward (quittingSingletonTerminal owner) blocker
  · exact exists_finiteWord_debtSum_le_of_weakSubset_allDesignatedPreempted
      reward owners hWE hpreempted hM hε hreward
  · push Not at hpreempted
    obtain ⟨owner, hownerMem, hunpreempted⟩ := hpreempted
    apply exists_finiteWord_debtSum_le_of_nonnegative_unpreemptedDesignatedOwner
      reward owner hM hε hreward (hsingleton owner hownerMem)
    intro player hplayer
    linarith [hunpreempted player]

/-- Actual weak subset exclusion has a literal finite-word approximate Nash
witness at every positive accuracy. -/
theorem exists_literalRootStack_isEpsilonAsymptoticNash_of_actualWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingActualWeakSubsetExclusion reward owners)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ roots : List (ι → PMF Bool),
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) := by
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakSubsetExclusion reward owners
      (finiteWordWeakSubsetExclusion_of_actual reward owners hexclusion)
      hexclusion.1 hε
  exact ⟨roots,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebt⟩

/-- The finite-calendar raw predicate has the same literal finite-word
selector. -/
theorem exists_literalRootStack_isEpsilonAsymptoticNash_of_rawWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ roots : List (ι → PMF Bool),
      (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)) := by
  let rawPoint := Classical.choice (inferInstance : Nonempty
    (MixedSimplex ι (fun _ => QuittingFiniteDeadlineTimingAction
      (Fintype.card ι * (Fintype.card ι + 1)))))
  obtain ⟨owner, -, -⟩ := hexclusion.2 rawPoint
  letI : Nonempty ι := ⟨owner⟩
  exact
    exists_literalRootStack_isEpsilonAsymptoticNash_of_actualWeakSubsetExclusion
      reward owners
        ((hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
          reward owners).mp hexclusion) hε

/-- Literal designated weak exclusion feeds the terminal all-errors compiler
and yields one fixed uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_finiteWordWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hWE : QuittingFiniteWordWeakSubsetExclusion reward owners)
    (hsingleton : ∀ owner ∈ owners,
      0 ≤ reward (quittingSingletonTerminal owner) owner) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
  intro ε hε
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakSubsetExclusion
      reward owners hWE hsingleton hε
  refine ⟨quittingLiteralRootStackProfile reward roots
    (quittingAlwaysContinueProfile reward), ?_⟩
  exact isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebt

/-- Actual designated weak-subset exclusion has a fixed uniform-equilibrium
payoff, via the literal finite-word selector. -/
theorem exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingActualWeakSubsetExclusion reward owners) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_finiteWordWeakSubsetExclusion
    reward owners
      (finiteWordWeakSubsetExclusion_of_actual reward owners hexclusion)
      hexclusion.1

/-- The exact raw finite-calendar designated weak-subset predicate has the
same constructive uniform-payoff consequence. -/
theorem exists_uniformEquilibriumPayoff_of_finiteCalendarRawWeakSubsetExclusion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owners : Finset ι)
    (hexclusion : HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let deadline := Fintype.card ι * (Fintype.card ι + 1)
  let allNever : MixedSimplex ι
      (fun _ => QuittingFiniteDeadlineTimingAction deadline) := fun _ =>
    Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)
  obtain ⟨inhabitant, -, -⟩ := hexclusion.2 allNever
  letI : Nonempty ι := ⟨inhabitant⟩
  apply exists_uniformEquilibriumPayoff_of_actualWeakSubsetExclusion
    reward owners
  exact (hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
    reward owners).mp hexclusion

end GameTheory
