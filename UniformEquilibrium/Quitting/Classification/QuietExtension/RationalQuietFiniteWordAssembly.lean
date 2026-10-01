import UniformEquilibrium.Quitting.Root.RationalDeletedChildFiniteWordSearch

/-! # Same-calendar quiet finite laws from the actual child word

This internal assembly theorem takes a proved Nash-lift inequality. Public
raw reward-row consumers discharge that inequality from their canonical
source certificates; it is not equilibrium-existence data. The selected
child accuracy is exactly epsilon divided by the rational amplification.
Every parent outsider law is literally Never, every child atom is retained,
and the bound covers all behavioral deviations including late replies.
-/

noncomputable section

namespace GameTheory

variable {players childPlayers : ℕ}

theorem rationalQuittingQuietFiniteWordLaws_of_terminalNashLift
    (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (amplification : ℚ) (hamplification : 1 ≤ amplification)
    (hlift : ∀ (error : ℝ), 0 ≤ error →
      ∀ profile : (quittingGame
        (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).BehaviorProfile,
        (quittingGame
          (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)).IsεAsymptoticNash
            (quittingTerminalPayoff
              (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted)) error profile →
        (quittingGame (rationalQuittingRewardToReal reward)).IsεAsymptoticNash
          (quittingTerminalPayoff (rationalQuittingRewardToReal reward))
          ((amplification : ℝ) * error)
          (quittingLiftDeletedProfile (rationalQuittingRewardToReal reward) deleted profile))
    (accuracy : ℚ) (haccuracy : 0 < accuracy) :
    let positive : 0 < accuracy / amplification := div_pos haccuracy (by linarith)
    let word := rationalQuittingDeletedChildWord reward deleted label hchild
      (accuracy / amplification) positive
    ∃ mixed : Fin players → PMF (Option (Fin word.length)),
      (∀ outside, deleted outside → mixed outside = PMF.pure none) ∧
      (∀ child : QuittingChildPlayer deleted, ∀ choice, (mixed child.1 choice).toReal =
        (rationalFiniteClockMass (rationalQuittingFiniteWordSequence word)
          word.length (label child) choice : ℝ)) ∧
      ∀ who, quittingTerminalDeviationDebt (rationalQuittingRewardToReal reward)
        (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
          word.length mixed) who < (accuracy : ℝ) := by
  let : Nonempty (Fin players) := Nonempty.map Subtype.val
    (inferInstance : Nonempty (QuittingChildPlayer deleted))
  have hpositive : 0 < accuracy / amplification := div_pos haccuracy (by linarith)
  let word := rationalQuittingDeletedChildWord reward deleted label hchild
    (accuracy / amplification) hpositive
  obtain ⟨childMixed, error, herror, hsmall, hmass, hnash⟩ :=
    rationalQuittingDeletedChildWord_finiteLaws reward deleted label hchild
      (accuracy / amplification) hpositive
  let profile := quittingFiniteDeadlineTimingProfile
    (quittingDeleteReward (rationalQuittingRewardToReal reward) deleted) word.length childMixed
  have hparent := hlift error herror profile hnash
  dsimp only [profile] at hparent
  rw [quittingFiniteDeadlineTimingProfile_extendDeleted] at hparent
  let mixed := quittingExtendDeletedFiniteTimingLaws deleted word.length childMixed
  have hbound := quittingTerminalExploitability_le_of_isεAsymptoticNash
    (rationalQuittingRewardToReal reward)
    (quittingFiniteDeadlineTimingProfile (rationalQuittingRewardToReal reward)
      word.length mixed) (mul_nonneg (Rat.cast_nonneg.mpr (by linarith)) herror)
    hparent
  have hfactor : (0 : ℝ) < amplification := Rat.cast_pos.mpr (by linarith)
  have hstrict : (amplification : ℝ) * error < (accuracy : ℝ) := by
    rw [Rat.cast_div] at hsmall
    have h := (lt_div_iff₀ hfactor).mp hsmall
    simpa only [mul_comm] using h
  refine ⟨mixed, ?_, ?_, ?_⟩
  · intro outside houtside
    exact quittingExtendDeletedFiniteTimingLaws_of_deleted deleted word.length childMixed
      outside houtside
  · intro child choice
    dsimp only [mixed]
    rw [quittingExtendDeletedFiniteTimingLaws_apply]
    exact hmass child choice
  · intro who
    exact (quittingTerminalDeviationDebt_le_exploitability _ _ who).trans_lt
      (hbound.trans_lt hstrict)

end GameTheory
