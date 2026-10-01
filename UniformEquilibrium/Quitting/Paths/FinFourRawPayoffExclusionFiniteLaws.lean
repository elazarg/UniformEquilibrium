import UniformEquilibrium.Quitting.Paths.FiniteCalendarStrictDeficitSource
import UniformEquilibrium.Quitting.Paths.StrictDeficitFiniteWordRates
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordSource
import UniformEquilibrium.Quitting.Paths.GroupExclusionFiniteWordRates
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakSubsetSelection
import UniformEquilibrium.Quitting.Root.LiteralFiniteWordMenuRealization

/-! # Actual finite-law outputs for accepted four-player raw payoff tests

The three raw predicates feed their existing actual word producers. Realizing
that selected word retains every independent first-Quit/Never marginal and the
whole prescribed-payoff/unrestricted-cap pair. No compressed payoff witness is
reused as a favorable cap witness. Uniform targets are existential, not computed.
-/

noncomputable section
namespace GameTheory

private theorem exists_strictFiniteWordDebt_of_rawPayoffExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsource : HasQuittingFiniteCalendarRawStrictExclusion reward ∨
      (∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ∨
      ∃ owners, HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners)
    {error : ℝ} (herror : 0 < error) :
    ∃ roots : List (Fin 4 → PMF Bool),
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward))) < error := by
  rcases hsource with hstrict | ⟨beta, hbeta, hgroup⟩ | ⟨owners, hweak⟩
  · obtain ⟨gap, hgap, hdeficit⟩ :=
      exists_positive_finiteWordStrictSingletonDeficit_of_finiteCalendarRawStrict reward hstrict
    obtain ⟨roots, hdebt, _⟩ := exists_literalFiniteWord_isEpsilonAsymptoticNash_of_strictDeficit
      reward hgap herror (abs_reward_le_quittingRewardBound reward) hdeficit
    exact ⟨roots, hdebt⟩
  · obtain ⟨roots, hdebt, _⟩ := exists_literalFiniteWord_isEpsilonAsymptoticNash_of_groupExclusion
      reward hbeta herror (abs_reward_le_quittingRewardBound reward)
      (hasQuittingFiniteWordNonconcentratedGroupExclusion_of_raw reward beta hgroup)
    exact ⟨roots, hdebt⟩
  · have hactual := (hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
      reward owners).mp hweak
    obtain ⟨roots, hdebt⟩ := exists_finiteWord_debtSum_le_of_weakSubsetExclusion reward owners
      (finiteWordWeakSubsetExclusion_of_actual reward owners hactual) hactual.1
      (half_pos herror)
    exact ⟨roots, hdebt.trans_lt (half_lt_self herror)⟩

/-- Every accepted raw P, G or W predicate internally selects one actual word
and its SAME exact independent date/Never laws, with strict complete debt.
This real-table result has neither rational-table nor preemption hypotheses. -/
theorem exists_finFour_finiteWord_exactLaws_of_rawPayoffExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsource : HasQuittingFiniteCalendarRawStrictExclusion reward ∨
      (∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ∨
      ∃ owners, HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners)
    {error : ℝ} (herror : 0 < error) :
    ∃ roots : List (Fin 4 → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) < error ∧
      ∃ mixed : Fin 4 → PMF (QuittingFiniteDeadlineTimingAction roots.length),
        (∀ who, (quittingFiniteDeadlineTimingLaw (mixed who)).toPMF =
          quittingBehaviorStoppingLaw reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward) who)) ∧
        quittingTerminalSemanticPair reward
            (quittingFiniteDeadlineTimingProfile reward roots.length mixed) =
          quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward)) ∧
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingFiniteDeadlineTimingProfile reward roots.length mixed)) < error ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) error
          (quittingFiniteDeadlineTimingProfile reward roots.length mixed) := by
  obtain ⟨roots, hdebt⟩ :=
    exists_strictFiniteWordDebt_of_rawPayoffExclusion reward hsource herror
  obtain ⟨mixed, hlaws, hpair⟩ :=
    exists_finiteDeadlineTimingProfile_literalRootStack_exact reward roots roots.length le_rfl
  have hdebtMixed : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward roots.length mixed)) < error := by
    rw [hpair]
    exact hdebt
  exact ⟨roots, hdebt, mixed, hlaws, hpair, hdebtMixed,
    isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le reward _ hdebtMixed.le⟩

/-- Acceptance gives one fixed uniform payoff under the original quantifier
order, without asserting that the finite selector computes that target. -/
theorem exists_uniformEquilibriumPayoff_of_finFour_rawPayoffExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hsource : HasQuittingFiniteCalendarRawStrictExclusion reward ∨
      (∃ beta < 1, HasQuittingFiniteCalendarRawNonconcentratedGroupExclusion reward beta) ∨
      ∃ owners, HasQuittingFiniteCalendarRawWeakSubsetExclusion reward owners) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases hsource with hstrict | ⟨beta, hbeta, hgroup⟩ | ⟨owners, hweak⟩
  · obtain ⟨gap, hgap, hdeficit⟩ :=
      exists_positive_finiteWordStrictSingletonDeficit_of_finiteCalendarRawStrict reward hstrict
    exact exists_uniformEquilibriumPayoff_of_finiteWordStrictSingletonDeficit
      reward hgap hdeficit
  · exact exists_uniformEquilibriumPayoff_of_finiteWordGroupExclusion reward hbeta
      (hasQuittingFiniteWordNonconcentratedGroupExclusion_of_raw reward beta hgroup)
  · exact exists_uniformEquilibriumPayoff_of_finiteCalendarRawWeakSubsetExclusion
      reward owners hweak

end GameTheory
