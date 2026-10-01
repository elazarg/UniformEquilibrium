import UniformEquilibrium.Quitting.Classification.QuietExtension.ExecutableWithdrawalDebtWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockOriginalCoalitionRows
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinFixedTarget
import UniformEquilibrium.Quitting.Root.RationalReward

/-! # Computed original-table withdrawal amplifications

All rational coefficients and K are computed from the original table, deletion
and response kinds before accuracy. Real source feasibility occurs only in proofs.
-/

namespace GameTheory.ExecutableWithdrawal

open scoped BigOperators

variable {players : ℕ}

def originalEmbedding (deleted : Fin players → Prop) [DecidablePred deleted]
    (outside : {who : Fin players // deleted who}) :
    Option (QuittingChildPlayer deleted) ↪ Fin players where
  toFun who := match who with | none => outside.1 | some child => child.1
  inj' := by
    have hagrees (who : Option (QuittingChildPlayer deleted)) :
        quittingChildWithOutsiderOriginalEmbedding deleted outside who =
          (match who with | none => outside.1 | some child => child.1) := by
      cases who with
      | none => exact quittingChildWithOutsiderOriginalEmbedding_none deleted outside
      | some child =>
          exact quittingChildWithOutsiderOriginalEmbedding_some deleted outside child
    intro first second hequal
    apply (quittingChildWithOutsiderOriginalEmbedding deleted outside).injective
    exact (hagrees first).trans (hequal.trans (hagrees second).symm)

theorem originalEmbedding_eq (deleted : Fin players → Prop) [DecidablePred deleted]
    (outside : {who : Fin players // deleted who}) :
    originalEmbedding deleted outside =
      quittingChildWithOutsiderOriginalEmbedding deleted outside := by
  ext who
  cases who <;> rfl

def restriction (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (outside : {who : Fin players // deleted who}) : Reward (QuittingChildPlayer deleted) :=
  fun terminal who =>
    reward ⟨terminal.1.map (originalEmbedding deleted outside),
      Finset.map_nonempty.mpr terminal.2⟩ (originalEmbedding deleted outside who)

theorem restriction_cast (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (outside : {who : Fin players // deleted who}) :
    toReal (restriction reward deleted outside) =
      quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside := by
  funext terminal who
  rw [quittingChildWithOutsiderReward_apply_original]
  simp only [toReal, restriction, originalEmbedding_eq, rationalQuittingRewardToReal]

noncomputable def transportCertificate
    {ι : Type} [Fintype ι] [DecidableEq ι] {kind : WithdrawalFutureJoinKind}
    {first second : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind first) (heq : first = second) :
    WithdrawalFutureJoinRewardCertificate kind second := heq ▸ certificate

theorem transportCertificate_debtWeight
    {ι : Type} [Fintype ι] [DecidableEq ι] {kind : WithdrawalFutureJoinKind}
    {first second : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind first) (heq : first = second)
    (i : ι) :
    (transportCertificate certificate heq).debtWeight i = certificate.debtWeight i := by
  cases heq
  rfl

theorem transportCertificate_neverExcess
    {ι : Type} [Fintype ι] [DecidableEq ι] {kind : WithdrawalFutureJoinKind}
    {first second : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind first) (heq : first = second) :
    (transportCertificate certificate heq).neverExcess = certificate.neverExcess := by
  cases heq
  rfl

theorem transportCertificate_positiveSingletonWeight
    {ι : Type} [Fintype ι] [DecidableEq ι] {kind : WithdrawalFutureJoinKind}
    {first second : {A : Finset (Option ι) // A.Nonempty} → Option ι → ℝ}
    (certificate : WithdrawalFutureJoinRewardCertificate kind first) (heq : first = second)
    (pivot i : ι) :
    (transportCertificate certificate heq).positiveSingletonWeight pivot i =
      certificate.positiveSingletonWeight pivot i := by
  cases heq
  rfl

abbrev FullSource (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind) : Prop :=
  ∀ outside, Nonempty ((kind outside).FullCertificate
    (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside))

abbrev FutureJoinSource (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind) : Prop :=
  ∀ outside, Nonempty (WithdrawalFutureJoinRewardCertificate (kind outside)
    (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside))

section Full

variable (reward : RationalQuittingReward players)
  (deleted : Fin players → Prop) [DecidablePred deleted]
  (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind)
  (hsource : FullSource reward deleted kind)

include hsource in
private theorem full_restriction_source (outside : {who : Fin players // deleted who}) :
    Nonempty ((kind outside).FullCertificate (toReal (restriction reward deleted outside))) := by
  rw [restriction_cast]
  exact hsource outside

def fullSourceWeights (outside : {who : Fin players // deleted who}) :
    QuittingChildPlayer deleted ⊕ QuittingChildPlayer deleted → ℚ :=
  fullWeights (kind outside) (restriction reward deleted outside)
    (full_restriction_source reward deleted kind hsource outside)

noncomputable def fullSourceCertificate (outside : {who : Fin players // deleted who}) :
    WithdrawalFutureJoinRewardCertificate (kind outside)
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside) :=
  transportCertificate
    (fullFutureJoinCertificate (kind outside) (restriction reward deleted outside)
      (full_restriction_source reward deleted kind hsource outside))
    (restriction_cast reward deleted outside)

theorem fullSourceCertificate_debtWeight
    (outside : {who : Fin players // deleted who}) (i : QuittingChildPlayer deleted) :
    (debtWeight (kind outside) (fullSourceWeights reward deleted kind hsource outside) i : ℝ) =
      (fullSourceCertificate reward deleted kind hsource outside).debtWeight i := by
  rw [fullSourceCertificate, transportCertificate_debtWeight]
  exact full_debtWeight_cast _ _ _ i

theorem fullSourceCertificate_excess_eq_zero
    (outside : {who : Fin players // deleted who}) :
    (fullSourceCertificate reward deleted kind hsource outside).neverExcess = 0 := by
  rw [fullSourceCertificate, transportCertificate_neverExcess]
  exact fullFutureJoinCertificate_excess_eq_zero _ _ _

variable [Nonempty {who : Fin players // deleted who}]

def fullAmplification : ℚ :=
  Math.LinearProgramming.rationalWeightAmplification
    (fun outside i => debtWeight (kind outside)
      (fullSourceWeights reward deleted kind hsource outside) i)

theorem fullAmplification_ge_one : 1 ≤ fullAmplification reward deleted kind hsource :=
  Math.LinearProgramming.one_le_rationalWeightAmplification _

theorem fullAmplification_cast :
    (fullAmplification reward deleted kind hsource : ℝ) =
      max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ i,
          (fullSourceCertificate reward deleted kind hsource outside).debtWeight i))
        := by
  unfold fullAmplification
  rw [Math.LinearProgramming.rationalWeightAmplification_cast]
  simp_rw [fullSourceCertificate_debtWeight]

end Full

section FutureJoin

variable (reward : RationalQuittingReward players)
  (deleted : Fin players → Prop) [DecidablePred deleted]
  (kind : {who : Fin players // deleted who} → WithdrawalFutureJoinKind)
  (hsource : FutureJoinSource reward deleted kind)

include hsource in
private theorem futureJoin_restriction_source (outside : {who : Fin players // deleted who}) :
    Nonempty (WithdrawalFutureJoinRewardCertificate (kind outside)
      (toReal (restriction reward deleted outside))) := by
  rw [restriction_cast]
  exact hsource outside

def futureJoinSourceWeights (outside : {who : Fin players // deleted who}) :
    QuittingChildPlayer deleted ⊕ QuittingChildPlayer deleted → ℚ :=
  futureJoinWeights (kind outside) (restriction reward deleted outside)
    (futureJoin_restriction_source reward deleted kind hsource outside)

noncomputable def futureJoinSourceCertificate (outside : {who : Fin players // deleted who}) :
    WithdrawalFutureJoinRewardCertificate (kind outside)
      (quittingChildWithOutsiderReward (rationalQuittingRewardToReal reward) deleted outside) :=
  transportCertificate
    (futureJoinCertificate (kind outside) (restriction reward deleted outside)
      (futureJoin_restriction_source reward deleted kind hsource outside))
    (restriction_cast reward deleted outside)

theorem futureJoinSourceCertificate_correctedWeight
    (outside : {who : Fin players // deleted who}) (pivot i : QuittingChildPlayer deleted) :
    (correctedWeight (kind outside) (restriction reward deleted outside)
      (futureJoinSourceWeights reward deleted kind hsource outside) pivot i : ℝ) =
      (futureJoinSourceCertificate reward deleted kind hsource outside).positiveSingletonWeight
        pivot i := by
  rw [futureJoinSourceCertificate, transportCertificate_positiveSingletonWeight]
  exact futureJoin_correctedWeight_cast _ _ _ pivot i

variable [Nonempty {who : Fin players // deleted who}]

def futureJoinAmplification (pivot : QuittingChildPlayer deleted) : ℚ :=
  Math.LinearProgramming.rationalWeightAmplification (fun outside i =>
    correctedWeight (kind outside) (restriction reward deleted outside)
      (futureJoinSourceWeights reward deleted kind hsource outside) pivot i)

theorem futureJoinAmplification_ge_one (pivot : QuittingChildPlayer deleted) :
    1 ≤ futureJoinAmplification reward deleted kind hsource pivot :=
  Math.LinearProgramming.one_le_rationalWeightAmplification _

theorem futureJoinAmplification_cast (pivot : QuittingChildPlayer deleted) :
    (futureJoinAmplification reward deleted kind hsource pivot : ℝ) =
      withdrawalFutureJoinOutsiderMaxWeight deleted (rationalQuittingRewardToReal reward) kind
        (futureJoinSourceCertificate reward deleted kind hsource) pivot := by
  unfold futureJoinAmplification withdrawalFutureJoinOutsiderMaxWeight
    withdrawalFutureJoinOutsiderWeight
  rw [Math.LinearProgramming.rationalWeightAmplification_cast]
  simp_rw [futureJoinSourceCertificate_correctedWeight]

end FutureJoin

end GameTheory.ExecutableWithdrawal
