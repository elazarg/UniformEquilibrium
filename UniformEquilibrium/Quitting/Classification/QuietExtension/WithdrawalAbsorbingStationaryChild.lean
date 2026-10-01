import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalOneOutsiderTransport
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalWeightedDebtLift
import UniformEquilibrium.Quitting.Stationary.JointNeverMass
import UniformEquilibrium.Quitting.Stationary.EndpointCompiler

/-! # Omitted-Never withdrawal extensions of absorbing stationary children

Joint absorption of the actual child kills the omitted-Never residual. The
same quiet profile is exact terminal Nash when the actual child is, with its
actual parent payoff as one fixed uniform-equilibrium target. No positive
singleton pivot, favorable cap, or supplied joint-Never equality is required.
Each outsider may use any of the five existing raw F/J certificate kinds.
These conclusions are terminal-only, not all-evaluation debt comparisons.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Zero joint Never is derived from this stationary child's absorption and
the exact original-child law transport. Individual Never atoms may be positive. -/
theorem quietOutsiderChildJointNever_absorbingStationary_eq_zero
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who})
    (root : QuittingChildPlayer deleted → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1) :
    (∏ who, (quietOutsiderChildLaws
      (quittingChildWithOutsiderReward reward deleted outside)
      (quittingChildWithOutsiderChildProfile reward deleted outside
        (quittingStationaryProfile (quittingDeleteReward reward deleted) root)) who none).toReal)
      = 0 := by
  simp_rw [quietOutsiderChildLaws_childWithOutsiderChildProfile]
  exact prod_stoppingLaw_none_stationary_eq_zero
    (quittingDeleteReward reward deleted) root habsorbs

/-- All five actual F/J sources bound this outsider's full terminal debt by
the original SUM/MAX child weights. Absorption replaces positive-pivot charging. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin_absorbingStationary
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (outside : {who : α // deleted who}) (kind : WithdrawalFutureJoinKind)
    (certificate : WithdrawalFutureJoinRewardCertificate kind
      (quittingChildWithOutsiderReward reward deleted outside))
    (root : QuittingChildPlayer deleted → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1) :
    let profile := quittingStationaryProfile (quittingDeleteReward reward deleted) root
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.debtWeight who *
        (quittingBehaviorDeviationPayoffCap
            (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  have hpositive : 0 < quittingRootAbsorptionMass root := sub_pos.mpr habsorbs
  obtain ⟨who, _⟩ :=
    (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mp hpositive
  let : Nonempty (QuittingChildPlayer deleted) := ⟨who⟩
  dsimp only
  apply quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound_at
    deleted reward outside certificate.debtWeight
    (quittingStationaryProfile (quittingDeleteReward reward deleted) root)
  exact withdrawalFutureJoin_quietLift_outsideDebt_le_of_jointNever_zero
    (quittingChildWithOutsiderReward reward deleted outside) certificate
    (quittingChildWithOutsiderChildProfile reward deleted outside
      (quittingStationaryProfile (quittingDeleteReward reward deleted) root))
    (quietOutsiderChildJointNever_absorbingStationary_eq_zero
      deleted reward outside root habsorbs)

/-- Arbitrarily many quiet outsiders, with outsider-dependent F/J kinds,
preserve the SAME absorbing stationary child's exact terminal equilibrium.
No singleton sign is assumed. The child hypothesis is full behavioral Nash. -/
theorem isZeroAsymptoticNash_quietLift_of_withdrawalFutureJoin_absorbingStationary
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (root : QuittingChildPlayer deleted → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) 0
      (quittingStationaryProfile (quittingDeleteReward reward deleted) root)) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingLiftDeletedProfile reward deleted
        (quittingStationaryProfile (quittingDeleteReward reward deleted) root)) := by
  let childReward := quittingDeleteReward reward deleted
  let profile := quittingStationaryProfile childReward root
  have hchild (who : QuittingChildPlayer deleted) :
      quittingBehaviorDeviationPayoffCap childReward profile who -
        quittingTerminalPayoff childReward profile who ≤ 0 := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply sub_nonpos.mpr
    apply quittingBestReplyValue_le
    intro deviation
    simpa only [add_zero] using hnash who deviation
  have houtside (outside : {who : α // deleted who}) :
      quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who : QuittingChildPlayer deleted, (0 : ℝ) *
        (quittingBehaviorDeviationPayoffCap childReward profile who -
          quittingTerminalPayoff childReward profile who) := by
    simp only [zero_mul, Finset.sum_const_zero]
    apply (quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin_absorbingStationary
      deleted reward outside (kind outside) (certificate outside) root habsorbs).trans
    apply Finset.sum_nonpos
    intro who _
    exact mul_nonpos_of_nonneg_of_nonpos
      ((certificate outside).debtWeight_nonneg who) (hchild who)
  have hparent := isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds deleted reward
    (fun _ _ => 0) (fun _ _ => le_rfl) 1 le_rfl
    (by intro outside; simp) (error := 0) le_rfl profile houtside hnash
  simpa only [mul_zero] using hparent

/-- The fixed parent UE target is the payoff of this SAME quiet exact Nash
profile. Every retained coordinate equals its actual stationary child payoff. -/
theorem quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (root : QuittingChildPlayer deleted → PMF Bool)
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) 0
      (quittingStationaryProfile (quittingDeleteReward reward deleted) root)) :
    let child := quittingStationaryProfile (quittingDeleteReward reward deleted) root
    let lifted := quittingLiftDeletedProfile reward deleted child
    let target := quittingTerminalPayoff reward lifted
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 lifted ∧
      (∀ who : QuittingChildPlayer deleted,
        target who.1 = quittingTerminalPayoff (quittingDeleteReward reward deleted) child who) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  dsimp only
  have hparent := isZeroAsymptoticNash_quietLift_of_withdrawalFutureJoin_absorbingStationary
    deleted reward kind certificate root habsorbs hnash
  exact ⟨hparent,
    fun who => quittingTerminalPayoff_liftDeletedProfile reward deleted _ who,
    quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact reward _ hparent⟩

/-- Canonical Bellman/endpoint source data compile the child first, including
its actual Never boundary. Joint absorption alone is not substituted for Nash. -/
theorem quietLift_fixedTarget_of_withdrawalFutureJoin_stationaryEndpoint
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {S : Finset α // S.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (root : QuittingChildPlayer deleted → PMF Bool)
    (value : Payoff (QuittingChildPlayer deleted))
    (habsorbs : quittingStationaryContinueMass root < 1)
    (hfixed : value = quittingRootSuccessorPayoff
      (quittingDeleteReward reward deleted) value root)
    (hendpoint : IsεQuittingRootEndpointNash
      (quittingDeleteReward reward deleted) value 0 root)
    (hboundary : IsQuittingStationaryBoundaryAdmissible
      (quittingDeleteReward reward deleted) root value) :
    let lifted := quittingLiftDeletedProfile reward deleted
      (quittingStationaryProfile (quittingDeleteReward reward deleted) root)
    let target := quittingTerminalPayoff reward lifted
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0 lifted ∧
      (∀ who : QuittingChildPlayer deleted, target who.1 = value who) ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none target := by
  have hnash := (isZeroAsymptoticNash_stationary_iff_boundary_of_fixedPoint_endpointNash
    (quittingDeleteReward reward deleted) root value habsorbs hfixed hendpoint).mpr hboundary
  have htarget := quietLift_fixedTarget_of_withdrawalFutureJoin_absorbingStationary
    deleted reward kind certificate root habsorbs hnash
  have hvalue := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    (quittingDeleteReward reward deleted) root value habsorbs hfixed
  simpa only [hvalue] using htarget

end GameTheory
