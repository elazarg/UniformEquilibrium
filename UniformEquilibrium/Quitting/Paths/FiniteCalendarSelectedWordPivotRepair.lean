import UniformEquilibrium.Quitting.Paths.FinFourRawPayoffExclusionFiniteLaws
import UniformEquilibrium.Quitting.Terminal.PivotRepairSmallValueSource
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability

/-! # Actual selected-word debt bounds the optimum for its own nonpivot laws

The word comes from an accepted raw source. Its original marginal laws and
whole payoff/cap pair are retained. A positive calendar padded only with an
unused date handles an empty selected word. The optimizer is produced by the
canonical pivot LP; neither a favorable word nor optimality is an input.
-/

noncomputable section
namespace GameTheory

open _root_.Math.LinearProgramming

/-- The canonical pivot minimizer is bounded by the actual full debt, including
all behavioral replies. This only composes the existing exploitability bound. -/
theorem exists_pivotRepairMinimizer_objective_le_finiteMenu_debt
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (deadline : ℕ) (hdeadline : 0 < deadline)
    (mixed : ι → PMF (QuittingFiniteDeadlineTimingAction deadline)) :
    let : Nonempty ι := ⟨pivot⟩
    let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
      pivot deadline hdeadline
      (fun who : {who : ι // who ≠ pivot} =>
        (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF)
      (fun who => isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who))
    ∃ mass : PivotRepairMass deadline, IsPivotRepairMassFeasible mass ∧
      IsMinOn input.objective (pivotRepairMassFeasibleSet deadline) mass ∧
      input.objective mass ≤ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward deadline mixed)) := by
  let : Nonempty ι := ⟨pivot⟩
  dsimp only
  obtain ⟨mass, hmass, hmin, hvalue⟩ :=
    exists_pivotRepairMinimizer_objective_le_finiteMenu_exploitability
      reward pivot deadline hdeadline mixed
  refine ⟨mass, hmass, hmin, hvalue.trans ?_⟩
  let profile := quittingFiniteDeadlineTimingProfile reward deadline mixed
  have hnonneg : 0 ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalDeviationDebt_nonneg reward profile who
  exact quittingTerminalExploitability_le_of_isεAsymptoticNash reward profile hnonneg
    (isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward profile le_rfl)

/-- Accepted P/G/W source data internally produces one word and the optimal
pivot repair for its SAME nonpivot laws, with optimum at most that word's D.
The player chosen as pivot is arbitrary; no sign restriction is added. -/
theorem exists_finFour_selectedWord_pivotRepairMinimizer_of_rawPayoffExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (pivot : Fin 4)
    (hsource : HasQuittingFiniteCalendarRawStrictExclusion reward ∨
      (∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ∨
      ∃ owners, HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners)
    {error : ℝ} (herror : 0 < error) :
    ∃ roots : List (Fin 4 → PMF Bool),
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward))) < error ∧
      ∃ (deadline : ℕ) (hdeadline : 0 < deadline),
        deadline = max 1 roots.length ∧
        ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction deadline),
          (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
            quittingBehaviorStoppingLaw reward
              (quittingLiteralRootStackProfile reward roots
                (quittingAlwaysContinueProfile reward) who)) ∧
          quittingTerminalSemanticPair reward
              (quittingFiniteDeadlineTimingProfile reward deadline mixed) =
            quittingTerminalSemanticPair reward
              (quittingLiteralRootStackProfile reward roots
                (quittingAlwaysContinueProfile reward)) ∧
          (let input := QuittingPivotRepairLPInput.ofNonpivotLaws (reward := reward)
            pivot deadline hdeadline
            (fun who : {who : Fin 4 // who ≠ pivot} =>
              (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF)
            (fun who => isFiniteClockStoppingLaw_finiteDeadlineTimingLaw (mixed who))
          ∃ mass : PivotRepairMass deadline, IsPivotRepairMassFeasible mass ∧
            IsMinOn input.objective (pivotRepairMassFeasibleSet deadline) mass ∧
            input.objective mass ≤ quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (quittingLiteralRootStackProfile reward roots
                  (quittingAlwaysContinueProfile reward)))) := by
  obtain ⟨roots, hdebt, _⟩ :=
    exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion reward hsource herror
  let deadline := max 1 roots.length
  have hdeadline : 0 < deadline := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨mixed, hlaws, hpair⟩ :=
    exists_finiteDeadlineTimingProfile_literalRootStack_exact reward roots deadline
      (le_max_right _ _)
  obtain ⟨mass, hmass, hmin, hvalue⟩ :=
    exists_pivotRepairMinimizer_objective_le_finiteMenu_debt
      reward pivot deadline hdeadline mixed
  refine ⟨roots, hdebt, deadline, hdeadline, rfl, mixed, hlaws, hpair,
    mass, hmass, hmin, ?_⟩
  simpa only [hpair] using hvalue

end GameTheory
