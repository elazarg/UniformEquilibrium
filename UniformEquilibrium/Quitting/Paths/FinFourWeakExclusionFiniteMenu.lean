import UniformEquilibrium.Quitting.Paths.FiniteWordWeakExclusionSelection
import UniformEquilibrium.Quitting.Root.LiteralFiniteWordMenuRealization
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineHorizonError
import UniformEquilibrium.Quitting.Terminal.SinglePivotFiniteMenuSource

/-! # Same-word four-player timing menus under weak exclusion

For the literal singleton vector (1,0,0,0), weak exclusion produces one actual
finite word whose exact independent first-Quit laws simultaneously control the
displayed menu and the pivot's post-cutoff reply. No preemption certificate,
replacement pivot law, favorable cap or prescribed target is supplied.
-/

noncomputable section

namespace GameTheory

/-- Weak exclusion alone gives the two menu errors on the SAME exact laws of
one selected finite word, including an empty word and every complete reply. -/
theorem exists_finFour_finiteWordMenu_errors_le_of_weakExclusion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hcanonical : IsSinglePivotSingletonTable reward 0)
    (hWE : QuittingFiniteWordWeakSingletonExclusion reward) {M ε : ℝ}
    (hreward : ∀ terminal who, |reward terminal who| ≤ M) (hε : 0 < ε) :
    ∃ roots : List (Fin 4 → PMF Bool),
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingLiteralRootStackProfile reward roots
              (quittingAlwaysContinueProfile reward))) ≤ ε ∧
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
        quittingFiniteDeadlineMenuExploitability reward roots.length mixed ≤ ε ∧
        quittingFiniteDeadlineNeverPayoff reward roots.length mixed 0 +
            quittingFiniteDeadlineOpponentNeverProduct roots.length mixed 0 -
            quittingTerminalPayoff reward
              (quittingFiniteDeadlineTimingProfile reward roots.length mixed) 0 ≤ ε ∧
        (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) ε
          (quittingFiniteDeadlineTimingProfile reward roots.length mixed) ∧
        (∀ horizon, 0 < horizon → ∀ who,
          |(quittingGame reward).finiteAveragePayoff none horizon
                (quittingFiniteDeadlineTimingProfile reward roots.length mixed) who -
              quittingTerminalPayoff reward
                (quittingFiniteDeadlineTimingProfile reward roots.length mixed) who| ≤
            M * roots.length / horizon) ∧
        ∀ horizon, 0 < horizon →
          (quittingGame reward).IsεHorizonNash none horizon
            (ε + 2 * M * (roots.length + 1) / horizon)
            (quittingFiniteDeadlineTimingProfile reward roots.length mixed) := by
  have hsingleton : ∀ who, 0 ≤ reward (quittingSingletonTerminal who) who := by
    intro who
    rw [hcanonical who]
    split <;> norm_num
  obtain ⟨roots, hdebt⟩ :=
    exists_finiteWord_debtSum_le_of_weakExclusion_nonnegativeSingleton
      reward hWE hsingleton hε
  obtain ⟨mixed, hlaws, hpair⟩ :=
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
    reward 0 hcanonical roots.length mixed
  refine ⟨roots, hdebt, mixed, hlaws, hpair, ?_, ?_, hnash, ?_, ?_⟩
  · exact (le_max_left _ _).trans (hmax ▸ hexploit)
  · exact (le_max_right _ _).trans (hmax ▸ hexploit)
  · intro horizon hhorizon who
    exact abs_finiteAveragePayoff_sub_terminal_finiteDeadline_le
      reward roots.length horizon mixed who (fun terminal => hreward terminal who) hhorizon
  · intro horizon hhorizon
    exact isHorizonNash_finiteDeadline_of_terminalNash_add_one
      reward roots.length horizon mixed hnash hreward hsingleton hhorizon

end GameTheory
