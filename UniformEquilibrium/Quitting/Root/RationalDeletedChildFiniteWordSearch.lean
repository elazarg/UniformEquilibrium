import UniformEquilibrium.Quitting.Root.RationalLowPlayerFiniteWordSearch
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineTimingQuietTransport

/-! # Actual rational deleted-child word search

The finite labeling is source data, not a selected equilibrium target. The
table is the literal original reward restriction and reindexing. Low-player
existence supplies termination internally. The original child laws retain
the exact selected rational word's calendar and marginal atoms.
-/

namespace GameTheory

variable {players childPlayers : ℕ}

/-- The exact rational table queried by the child word search. -/
def rationalQuittingDeletedChildReward (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) :
    RationalQuittingReward childPlayers := fun terminal who =>
  reward (quittingExtendDeletedCoalition deleted
    ((quittingCoalitionEquiv label).symm terminal)) (label.symm who).1

theorem rationalQuittingDeletedChildReward_cast (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) :
    rationalQuittingRewardToReal (rationalQuittingDeletedChildReward reward deleted label) =
      quittingRewardReindex label
        (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted) := rfl

/-- Accuracy-only actual child word, with no computed or prescribed real target. -/
def rationalQuittingDeletedChildWord (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) : List (RationalQuittingRoot childPlayers) :=
  rationalQuittingFiniteWordSearchOfCardLeThree
    (rationalQuittingDeletedChildReward reward deleted label) hchild tolerance htolerance

noncomputable section

/-- Exact selected masses after reindexing, with the full original child terminal Nash bound. -/
theorem rationalQuittingDeletedChildWord_finiteLaws
    (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (tolerance : ℚ) (htolerance : 0 < tolerance) :
    let word := rationalQuittingDeletedChildWord reward deleted label hchild tolerance htolerance
    ∃ (mixed : QuittingChildPlayer deleted → PMF (Option (Fin word.length))) (error : ℝ),
      0 ≤ error ∧ error < (tolerance : ℝ) ∧
      (∀ who choice, (mixed who choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length (label who) choice : ℝ)) ∧
      (quittingGame
        (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).IsεAsymptoticNash
          (quittingTerminalPayoff
            (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)) error
          (quittingFiniteDeadlineTimingProfile
            (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)
            word.length mixed) := by
  let : Nonempty (Fin childPlayers) := Nonempty.map label inferInstance
  let childReward := rationalQuittingDeletedChildReward reward deleted label
  let word := rationalQuittingDeletedChildWord reward deleted label hchild tolerance htolerance
  obtain ⟨mixed, hmass, hdebt⟩ :=
    rationalQuittingFiniteWordSearchOfCardLeThree_finiteLaws childReward hchild tolerance htolerance
  change Fin childPlayers → PMF (Option (Fin word.length)) at mixed
  let profile := quittingFiniteDeadlineTimingProfile
    (rationalQuittingRewardToReal childReward) word.length mixed
  let error := quittingTerminalExploitability (rationalQuittingRewardToReal childReward) profile
  have hsmall : error < (tolerance : ℝ) := by
    dsimp only [error]
    rw [quittingTerminalExploitability, QuittingBoundaryHolonomy.finitePlayerMax]
    apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
    intro who _
    exact max_lt (Rat.cast_pos.mpr htolerance) (hdebt who)
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le profile
    (show quittingTerminalExploitability (rationalQuittingRewardToReal childReward) profile ≤
      error from le_rfl)
  have hpull := isεAsymptoticNash_quittingProfilePullback label
    (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted) profile hnash
  dsimp only [profile, childReward] at hpull
  rw [rationalQuittingDeletedChildReward_cast,
    quittingFiniteDeadlineTimingProfile_pullback] at hpull
  refine ⟨fun who => mixed (label who), error,
    quittingTerminalExploitability_nonneg _ _, hsmall, ?_, hpull⟩
  intro who choice
  exact hmass (label who) choice

end

end GameTheory
