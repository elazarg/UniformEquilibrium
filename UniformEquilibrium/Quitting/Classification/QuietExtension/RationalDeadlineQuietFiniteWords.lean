import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalQuietFiniteWordSourceArithmetic
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFixedTarget

/-! # Raw deadline rows produce actual rational quiet finite laws

The full rational table supplies rational feasible weights internally, once
before accuracy. Their actual maximum amplification determines the exact
child-search acceptance threshold epsilon/K. Low-player existence proves
termination, and canonical full behavioral debt lifting proves acceptance
of the SAME child calendar with literal Never laws for every outsider.
This is an accuracy-only finite-law output, not computation of a fixed
uniform target, an LP runtime bound, or a favorable-profile input.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {players childPlayers : ℕ}

theorem exists_rationalDeadline_quietFiniteWordLaws
    (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)] [Nonempty {who : Fin players // deleted who}]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (source : ∀ outside : {who : Fin players // deleted who},
      DeadlineWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)) :
    letI : Nonempty (Fin players) := Nonempty.map Subtype.val
      (inferInstance : Nonempty (QuittingChildPlayer deleted))
    ∃ certificate : ∀ outside : {who : Fin players // deleted who},
        DeadlineWithdrawalRewardCertificate
          (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside),
      (∀ outside child, Math.IsRationalReal ((certificate outside).advanceWeight child)) ∧
      (∀ outside child, Math.IsRationalReal ((certificate outside).withdrawalWeight child)) ∧
      ∃ amplification : ℚ,
        deadlineWithdrawalOutsiderMaxWeight deleted (rationalQuittingRewardToReal reward)
            certificate = (amplification : ℝ) ∧
          ∃ bounded : 1 ≤ amplification, ∀ accuracy : ℚ, ∀ positive : 0 < accuracy,
            let childPositive : 0 < accuracy / amplification :=
              div_pos positive (by linarith)
            let word := rationalQuittingDeletedChildWord reward deleted label hchild
              (accuracy / amplification) childPositive
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
  choose certificate hadvance hwithdrawal using fun outside =>
    exists_rational_deadlineWithdrawalRewardCertificate
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)
      (isRationalReal_quittingChildWithOutsiderReward_of_rationalReward reward deleted outside)
      ⟨source outside⟩
  have hfactor : Math.IsRationalReal (deadlineWithdrawalOutsiderMaxWeight deleted
      (rationalQuittingRewardToReal reward) certificate) := by
    change Math.IsRationalReal
      (max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ child, (certificate outside).debtWeight child)))
    exact isRationalReal_max_one_sup_sum _ (fun outside child =>
      (hadvance outside child).max (hwithdrawal outside child))
  obtain ⟨amplification, hrepr⟩ := hfactor
  have hreal : (1 : ℝ) ≤ amplification := by
    rw [← hrepr]
    exact le_max_left _ _
  have hbounded : (1 : ℚ) ≤ amplification := by
    exact Rat.cast_le.mp (by simpa only [Rat.cast_one] using hreal)
  refine ⟨certificate, hadvance, hwithdrawal, amplification, hrepr, hbounded, ?_⟩
  intro accuracy haccuracy
  apply rationalQuittingQuietFiniteWordLaws_of_terminalNashLift
    reward deleted label hchild amplification hbounded _ accuracy haccuracy
  intro error herror profile hnash
  have h := isεAsymptoticNash_liftDeletedProfile_of_deadlineWithdrawalFamily
    deleted (rationalQuittingRewardToReal reward) certificate herror profile hnash
  simpa only [hrepr] using h

end GameTheory
