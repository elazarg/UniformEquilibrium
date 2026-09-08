import UniformEquilibrium.Quitting.Root.LiteralFiniteWordMenuRealization
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError
import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionRates
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource
import UniformEquilibrium.Quitting.Terminal.PositiveMinimumSemanticDebt

/-! # Source-preserving finite-menu and horizon bounds for weak exclusion -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The exact timing-menu realization of a literal word inherits its total terminal debt
and has the explicit finite-horizon error `D + 2MN/H`, where `N` is the word length. -/
theorem exists_finiteDeadlineTimingProfile_literalWord_debt_and_horizon
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : List (ι → PMF Bool)) {M : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hsolo : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who) :
    let D := quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingLiteralRootStackProfile reward roots
          (quittingAlwaysContinueProfile reward)))
    ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction roots.length),
      quittingTerminalSemanticPair reward
          (quittingFiniteDeadlineTimingProfile reward roots.length mixed) =
        quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward)) ∧
      ∀ horizon, 0 < horizon →
        (quittingGame reward).IsεHorizonNash none horizon
          (D + 2 * M * roots.length / horizon)
          (quittingFiniteDeadlineTimingProfile reward roots.length mixed) := by
  dsimp only
  obtain ⟨mixed, _, hpair⟩ :=
    exists_finiteDeadlineTimingProfile_literalRootStack_exact
      reward roots roots.length le_rfl
  refine ⟨mixed, hpair, ?_⟩
  intro horizon hhorizon
  have hdebt : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward roots.length mixed)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingLiteralRootStackProfile reward roots
            (quittingAlwaysContinueProfile reward))) := congrArg _ hpair
  have hnash := isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
    reward (quittingFiniteDeadlineTimingProfile reward roots.length mixed)
      (le_of_eq hdebt)
  exact isHorizonNash_finiteDeadline_of_terminalNash
    reward roots.length horizon mixed hnash hreward hsolo hhorizon

/-- The quantitative word selected under weak exclusion is realized by the same actual timing menu.
Its displayed-menu exploitability and pivot post-cutoff scalar are both bounded by
`ε`, its length retains the explicit phase-by-row bound, and the very same menu
inherits the complete terminal and finite-horizon Nash bounds. -/
theorem exists_singlePivot_selectedFiniteWordMenu_errors_and_length_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hcanonical : IsSinglePivotSingletonTable reward pivot)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward)
    (preemption : SingletonColumnBlockerCertificate reward)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    letI : Nonempty ι := ⟨pivot⟩
    let D₀ := ∑ player, reward (quittingSingletonTerminal player) player
    let scale := (32 * M + 6 * D₀) / 3
    ∃ roots : List (ι → PMF Bool),
      roots.length ≤ Nat.ceil (scale / ε) *
          quittingWeakExclusionUniformPhaseRowBound M D₀ ε preemption.gap ∧
      quittingWeakExclusionFiniteWordDebt reward roots ≤ ε ∧
      ∃ mixed : ι → PMF (QuittingFiniteDeadlineTimingAction roots.length),
        quittingTerminalSemanticPair reward
            (quittingFiniteDeadlineTimingProfile reward roots.length mixed) =
          quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward)) ∧
        quittingFiniteDeadlineMenuExploitability reward roots.length mixed ≤ ε ∧
        quittingFiniteDeadlineNeverPayoff reward roots.length mixed pivot +
            quittingFiniteDeadlineOpponentNeverProduct roots.length mixed pivot -
            quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward roots.length mixed) pivot ≤ ε ∧
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε
          (quittingFiniteDeadlineTimingProfile reward roots.length mixed) ∧
        ∀ horizon, 0 < horizon →
          (quittingGame reward).IsεHorizonNash none horizon
            (ε + 2 * M * roots.length / horizon)
            (quittingFiniteDeadlineTimingProfile reward roots.length mixed) := by
  dsimp only
  letI : Nonempty ι := ⟨pivot⟩
  have hsingleton : ∀ player,
      0 ≤ reward (quittingSingletonTerminal player) player := by
    intro player
    rw [hcanonical player]
    split <;> norm_num
  have hpivot : reward (quittingSingletonTerminal pivot) pivot = 1 := by
    simpa using hcanonical pivot
  have hM : 0 < M := by
    have hpivotBound := hreward (quittingSingletonTerminal pivot) pivot
    rw [hpivot, abs_one] at hpivotBound
    linarith
  obtain ⟨roots, hdebt, hlength⟩ :=
    exists_finiteWord_debtSum_and_length_le_of_weakExclusion_nonnegativeSingleton
      reward hWE preemption M hM hreward hsingleton hε
  obtain ⟨mixed, _, hpair⟩ :=
    exists_finiteDeadlineTimingProfile_literalRootStack_exact
      reward roots roots.length le_rfl
  have hdebtMixed : quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (quittingFiniteDeadlineTimingProfile reward roots.length mixed)) ≤ ε := by
    rw [hpair]
    exact hdebt
  have hnash := isEpsilonAsymptoticNash_of_terminalSemanticDebtSum_le
    reward (quittingFiniteDeadlineTimingProfile reward roots.length mixed) hdebtMixed
  have hexploit := quittingTerminalExploitability_le_of_isεAsymptoticNash
    reward (quittingFiniteDeadlineTimingProfile reward roots.length mixed) hε.le hnash
  have hmax := singlePivot_fullExploitability_eq_max_menuExploitability_scalar
    reward pivot hcanonical roots.length mixed
  refine ⟨roots, hlength, hdebt, mixed, hpair, ?_, ?_, hnash, ?_⟩
  · exact (le_max_left _ _).trans (hmax ▸ hexploit)
  · exact (le_max_right _ _).trans (hmax ▸ hexploit)
  · intro horizon hhorizon
    exact isHorizonNash_finiteDeadline_of_terminalNash
      reward roots.length horizon mixed hnash hreward hsingleton hhorizon

end GameTheory
