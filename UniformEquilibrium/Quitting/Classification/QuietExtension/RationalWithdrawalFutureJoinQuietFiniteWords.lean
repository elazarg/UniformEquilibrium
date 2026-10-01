import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalQuietFiniteWordSourceArithmetic
import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalWithdrawalFutureJoinWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinFixedTarget

/-! # Actual quiet rational laws with the Never row omitted

All five source response kinds, including outsider-dependent kinds, retain
their actual sum/max coefficients. The positive child singleton pays for
the actual omitted-Never residual. Rational weights and the corrected
source amplification K are chosen internally before accuracy. The literal
child search accepts at epsilon/K and outsiders are appended as Never on
the SAME calendar. The conclusion concerns full behavioral TERMINAL regret,
not all evaluations or computation of a prescribed uniform target.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The actual positive-singleton debt coefficient, including the residual charge. -/
theorem WithdrawalFutureJoinRewardCertificate.isRationalReal_positiveSingletonWeight
    {kind : WithdrawalFutureJoinKind}
    {reward : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind reward)
    (hrational : ∀ coalition who, Math.IsRationalReal (reward coalition who))
    (hadvance : ∀ i, Math.IsRationalReal (certificate.advanceWeight i))
    (hwithdrawal : ∀ i, Math.IsRationalReal (certificate.withdrawalWeight i))
    (pivot i : ι) :
    Math.IsRationalReal (certificate.positiveSingletonWeight pivot i) := by
  unfold WithdrawalFutureJoinRewardCertificate.positiveSingletonWeight
  apply (certificate.isRationalReal_debtWeight hadvance hwithdrawal i).add
  split_ifs
  · obtain ⟨excess, hexcess⟩ :=
      certificate.isRationalReal_neverExcess hrational hadvance hwithdrawal
    obtain ⟨singleton, hsingleton⟩ :=
      hrational ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot)
    exact ⟨excess / singleton, by rw [Rat.cast_div, ← hexcess, ← hsingleton]⟩
  · exact Math.IsRationalReal.zero

/-- Original F/J rows and an actual positive child singleton produce the
literal rational quiet laws. Neither a Never row nor a favorable root is supplied. -/
theorem exists_rationalWithdrawalFutureJoin_quietFiniteWordLaws
    {players childPlayers : ℕ} (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    [Nonempty {who : Fin players // deleted who}]
    (label : QuittingChildPlayer deleted ≃ Fin childPlayers) (hchild : childPlayers ≤ 3)
    (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind)
    (source : ∀ outside : {who : Fin players // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < rationalQuittingRewardToReal reward
      (quittingSingletonTerminal pivot.1) pivot.1) :
    ∃ certificate : ∀ outside : {who : Fin players // deleted who},
        WithdrawalFutureJoinRewardCertificate (kind outside)
          (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside),
      (∀ outside child, Math.IsRationalReal ((certificate outside).advanceWeight child)) ∧
      (∀ outside child, Math.IsRationalReal ((certificate outside).withdrawalWeight child)) ∧
      ∃ amplification : ℚ,
        withdrawalFutureJoinOutsiderMaxWeight deleted (rationalQuittingRewardToReal reward)
            kind certificate pivot = (amplification : ℝ) ∧
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
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  choose certificate hadvance hwithdrawal using fun outside =>
    exists_rational_withdrawalFutureJoinRewardCertificate (kind outside)
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside)
      (isRationalReal_quittingChildWithOutsiderReward_of_rationalReward reward deleted outside)
      ⟨source outside⟩
  have hfactor : Math.IsRationalReal (withdrawalFutureJoinOutsiderMaxWeight deleted
      (rationalQuittingRewardToReal reward) kind certificate pivot) := by
    change Math.IsRationalReal
      (max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ child, (certificate outside).positiveSingletonWeight pivot child)))
    apply isRationalReal_max_one_sup_sum
    intro outside child
    exact (certificate outside).isRationalReal_positiveSingletonWeight
      (isRationalReal_quittingChildWithOutsiderReward_of_rationalReward reward deleted outside)
      (hadvance outside) (hwithdrawal outside) pivot child
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
  have h := isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily
    deleted (rationalQuittingRewardToReal reward) kind certificate pivot hpivot
    herror profile hnash
  simpa only [hrepr] using h

end GameTheory
