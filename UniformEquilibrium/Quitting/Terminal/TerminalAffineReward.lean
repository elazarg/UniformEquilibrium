import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward
import UniformEquilibrium.Quitting.Punishment.FinitePureReplyValue
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryNeverCoupling

/-! # Terminal-only affine reward transport with zero Never payoff -/

noncomputable section

namespace GameTheory

open Set Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Affine terminal rewards leave Never at zero, so their prescribed payoff
contains the actual absorption probability rather than an unconditional shift. -/
theorem quittingTerminalPayoff_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift) profile who =
      scale who * quittingTerminalPayoff reward profile who +
        shift who * (1 - quittingLiveMassLimit reward profile) := by
  have hmass := quittingLiveMassLimit_add_sum_absorbedMassLimit reward profile
  unfold quittingTerminalPayoff
  simp_rw [QuittingLCPClassification.quittingAbsorbedMassLimit_congr_reward
    (quittingPlayerwiseAffineReward reward scale shift) reward profile]
  change (∑ terminal, quittingAbsorbedMassLimit reward profile terminal *
      (scale who * reward terminal who + shift who)) = _
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hscale : (∑ terminal, quittingAbsorbedMassLimit reward profile terminal *
      (scale who * reward terminal who)) = scale who *
        ∑ terminal, quittingAbsorbedMassLimit reward profile terminal * reward terminal who := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro terminal _
    ring
  rw [hscale, ← Finset.sum_mul]
  rw [show (∑ terminal, quittingAbsorbedMassLimit reward profile terminal) =
    1 - quittingLiveMassLimit reward profile by linarith]
  ring

/-- Every finite deterministic reply absorbs, so terminal-only affine
transport has no Never correction on its payoff. -/
theorem quittingTerminalPayoff_finiteTime_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (time : ℕ) :
    quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
        (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some time)))
        who = scale who * quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who (some time))) who + shift who := by
  change quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
      (Function.update profile who (quittingPureTimeBehaviorStrategy
        (quittingPlayerwiseAffineReward reward scale shift) who (some time))) who = _
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy
    (quittingPlayerwiseAffineReward reward scale shift),
    quittingTerminalPayoff_update_pureTimeBehaviorStrategy reward]
  change quittingTerminalPayoff (quittingPlayerwiseAffineReward reward scale shift)
      (quittingRootSequenceProfile reward
        (quittingRootSequenceUpdate (quittingProfileLiveRoot reward profile) who
          (quittingPureTimeHazard (some time))) 0) who = _
  rw [quittingTerminalPayoff_playerwiseAffine,
    quittingLiveMassLimit_rootSequenceUpdate_pureTime_eq_zero reward _ who time 0
      (Nat.zero_le time)]
  simp only [sub_zero, mul_one]
  rfl

/-- Positive affine transport commutes with the supremum over all finite
dates against the same complete independent opponents. -/
theorem quittingFinitePureReplyValue_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (profile : (quittingGame reward).BehaviorProfile)
    (who : ι) (hscale : 0 < scale who) :
    quittingFinitePureReplyValue (quittingPlayerwiseAffineReward reward scale shift)
        profile who = scale who * quittingFinitePureReplyValue reward profile who +
      shift who := by
  let transformed := quittingPlayerwiseAffineReward reward scale shift
  have hpay (time : ℕ) : quittingTerminalPayoff transformed
      (Function.update profile who (quittingPureTimeBehaviorStrategy transformed who (some time)))
      who = scale who * quittingTerminalPayoff reward
        (Function.update profile who (quittingPureTimeBehaviorStrategy reward who (some time)))
        who + shift who :=
    quittingTerminalPayoff_finiteTime_playerwiseAffine reward scale shift profile who time
  apply le_antisymm
  · apply ciSup_le
    intro time
    rw [hpay time]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (quittingTerminalPayoff_finiteTime_le_finitePureReplyValue reward profile who time)
      hscale.le) le_rfl
  · have hsup : quittingFinitePureReplyValue reward profile who ≤
        (quittingFinitePureReplyValue transformed profile who - shift who) / scale who := by
      apply ciSup_le
      intro time
      apply (le_div_iff₀ hscale).mpr
      have h := quittingTerminalPayoff_finiteTime_le_finitePureReplyValue
        transformed profile who time
      rw [hpay time] at h
      nlinarith
    have h := (le_div_iff₀ hscale).mp hsup
    linarith

/-- The finite-response-only infimum transports over the identical domain of
complete behavioral opponent plans. No minimum is assumed attained. -/
theorem quittingFinitePureReplyPunishmentValue_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (scale shift : Payoff ι) (who : ι) (hscale : 0 < scale who) :
    quittingFinitePureReplyPunishmentValue (quittingPlayerwiseAffineReward reward scale shift)
        who = scale who * quittingFinitePureReplyPunishmentValue reward who + shift who := by
  let transformed := quittingPlayerwiseAffineReward reward scale shift
  letI : Nonempty ((quittingGame reward).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile reward⟩
  letI : Nonempty ((quittingGame transformed).BehaviorProfile) :=
    ⟨quittingAlwaysContinueProfile transformed⟩
  apply le_antisymm
  · have hbound : (quittingFinitePureReplyPunishmentValue transformed who - shift who) /
        scale who ≤ quittingFinitePureReplyPunishmentValue reward who := by
      apply le_ciInf
      intro profile
      apply (div_le_iff₀ hscale).mpr
      have h := quittingFinitePureReplyPunishmentValue_le transformed who profile
      rw [quittingFinitePureReplyValue_playerwiseAffine reward scale shift profile who hscale]
        at h
      nlinarith
    have h := (div_le_iff₀ hscale).mp hbound
    linarith
  · apply le_ciInf
    intro profile
    rw [quittingFinitePureReplyValue_playerwiseAffine reward scale shift profile who hscale]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (quittingFinitePureReplyPunishmentValue_le reward who profile) hscale.le) le_rfl

end GameTheory
