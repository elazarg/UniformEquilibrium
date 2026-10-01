import UniformEquilibrium.Quitting.Root.RationalFiniteWordSearch
import UniformEquilibrium.Quitting.Classification.SmallPlayerExistence

/-! # Low-player sources for target-free rational finite-word search

Actual unrestricted low-player equilibrium existence proves termination.
No payoff target or favorable profile is an executable input. The empty
player type and empty calendar remain in scope. The output is accuracy-only:
its actual value need not approximate a prescribed fixed target.
-/

namespace GameTheory

variable {players : ℕ}

theorem rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_card_le_three
    (reward : RationalQuittingReward players) (hplayers : players ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    ∃ threshold : ℕ, ∀ budget, threshold ≤ budget →
      (rationalQuittingFiniteWordBoundedSearch? reward tolerance budget).isSome = true := by
  by_cases hzero : players = 0
  · subst players
    refine ⟨0, fun budget _ => ?_⟩
    apply List.find?_isSome.mpr
    refine ⟨[], ?_, ?_⟩
    · have hmem := mem_rationalQuittingFiniteWordCandidates (players := 0)
        0 0 budget (Nat.zero_le _) (Nat.zero_le _) (fun coordinate => Fin.elim0 coordinate)
      simpa only [rationalQuittingFiniteGridWord, List.ofFn_zero] using hmem
    · simp only [rationalQuittingFiniteWordAccepts, IsEmpty.forall_iff, decide_true]
  · let : Nonempty (Fin players) := Fintype.card_pos_iff.mp
      (by simpa only [Fintype.card_fin] using Nat.pos_of_ne_zero hzero)
    exact rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_uniformPayoff reward
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_le_three
        (by simpa only [Fintype.card_fin] using hplayers) (rationalQuittingRewardToReal reward))
      tolerance htolerance

/-- Executable first-success selection, with low-player existence only in the erased proof. -/
def rationalQuittingFiniteWordSearchOfCardLeThree
    (reward : RationalQuittingReward players) (hplayers : players ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) : List (RationalQuittingRoot players) :=
  rationalQuittingFiniteWordSearchSelector reward tolerance (by
    obtain ⟨threshold, hthreshold⟩ :=
      rationalQuittingFiniteWordBoundedSearch_eventually_succeeds_of_card_le_three
        reward hplayers tolerance htolerance
    exact ⟨threshold, hthreshold threshold le_rfl⟩)

theorem rationalQuittingFiniteWordSearchOfCardLeThree_accepts
    (reward : RationalQuittingReward players) (hplayers : players ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    rationalQuittingFiniteWordAccepts reward tolerance
      (rationalQuittingFiniteWordSearchOfCardLeThree reward hplayers tolerance htolerance) = true
    := by
  unfold rationalQuittingFiniteWordSearchOfCardLeThree
  exact rationalQuittingFiniteWordSearchSelector_accepts reward tolerance _

noncomputable section

/-- The selected word's actual independent laws, including zero players and zero dates. -/
theorem rationalQuittingFiniteWordSearchOfCardLeThree_finiteLaws
    (reward : RationalQuittingReward players) (hplayers : players ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    let word := rationalQuittingFiniteWordSearchOfCardLeThree
      reward hplayers tolerance htolerance
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length who choice : ℝ)) ∧
      ∀ who, quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) who < (tolerance : ℝ) := by
  dsimp only
  let word := rationalQuittingFiniteWordSearchOfCardLeThree
    reward hplayers tolerance htolerance
  obtain ⟨mixed, hmass, hsemantic⟩ := exists_rationalQuittingFiniteWordLaws_exact reward word
  have hword := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward word
  have hsame := hsemantic.trans hword.symm
  have hdebt := (rationalQuittingFiniteWordAccepts_iff reward tolerance word).mp
    (rationalQuittingFiniteWordSearchOfCardLeThree_accepts reward hplayers tolerance htolerance)
  refine ⟨mixed, hmass, ?_⟩
  intro who
  have hequal := congrArg (fun pair : QuittingTerminalSemanticPair (Fin players) =>
    pair.2 who - pair.1 who) hsame
  change quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
      (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
        word.length mixed) who =
    quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (word.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) who at hequal
  exact hequal.trans_lt (hdebt who)

end

end GameTheory
