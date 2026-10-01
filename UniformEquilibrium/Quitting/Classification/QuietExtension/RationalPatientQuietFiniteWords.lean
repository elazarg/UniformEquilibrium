import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalQuietFiniteWordSourceArithmetic
import UniformEquilibrium.Quitting.Classification.QuietExtension.PatientWithdrawalFixedTarget

/-! # Actual patient quiet laws from selected rational child words

The actual raw reward certificate supplies rational weights internally.
The source amplification is chosen before accuracy and uses the canonical
sum debt coefficient. Search accepts the CHILD word at epsilon/K;
the parent retains its calendar and rational child atoms and appends literal
Never laws for outsiders. Full behavioral terminal regret is bounded.
No fixed uniform target is computed, and no runtime bound is asserted.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {players childPlayers : ℕ}

theorem exists_rationalPatient_quietFiniteWordLaws
    (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)] [Nonempty {who : Fin players // deleted who}]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (source : ∀ outside : {who : Fin players // deleted who},
      PatientWithdrawalRewardCertificate
        (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)) :
    letI : Nonempty (Fin players) := Nonempty.map Subtype.val
      (inferInstance : Nonempty (QuittingChildPlayer deleted))
    ∃ certificate : ∀ outside : {who : Fin players // deleted who},
        PatientWithdrawalRewardCertificate
          (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside),
      (∀ outside child, Math.IsRationalReal ((certificate outside).advanceWeight child)) ∧
      (∀ outside child, Math.IsRationalReal ((certificate outside).withdrawalWeight child)) ∧
      ∃ amplification : ℚ,
        patientWithdrawalOutsiderMaxWeight deleted (rationalQuittingRewardToReal reward)
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
    exists_rational_patientWithdrawalRewardCertificate
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)
      (isRationalReal_quittingChildWithOutsiderReward_of_rationalReward reward deleted outside)
      ⟨source outside⟩
  have hfactor : Math.IsRationalReal (patientWithdrawalOutsiderMaxWeight deleted
      (rationalQuittingRewardToReal reward) certificate) := by
    change Math.IsRationalReal
      (max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ child, (certificate outside).debtWeight child)))
    exact isRationalReal_max_one_sup_sum _ (fun outside child =>
      (hadvance outside child).add (hwithdrawal outside child))
  obtain ⟨amplification, hrepr⟩ := hfactor
  have hreal : (1 : ℝ) ≤ amplification := by
    rw [← hrepr]
    exact le_max_left _ _
  have hbounded : (1 : ℚ) ≤ amplification :=
    Rat.cast_le.mp (by simpa only [Rat.cast_one] using hreal)
  refine ⟨certificate, hadvance, hwithdrawal, amplification, hrepr, hbounded, ?_⟩
  intro accuracy haccuracy
  apply rationalQuittingQuietFiniteWordLaws_of_terminalNashLift
    reward deleted label hchild amplification hbounded _ accuracy haccuracy
  intro error herror profile hnash
  have h := isεAsymptoticNash_liftDeletedProfile_of_patientWithdrawalFamily
    deleted (rationalQuittingRewardToReal reward) certificate herror profile hnash
  simpa only [hrepr] using h

end GameTheory
