/-
Role-swapped localization of a unilateral payoff externality.

A unilateral change of one mover's stopping strategy which raises another
player's terminal payoff is localized at an actually reached first
disagreement row of the lower-payoff successor profile.

The device is an auxiliary quitting reward table which pays the mover the
recipient's original coordinate and pays every other coordinate zero.  The
quitting dynamics — states, actions, transitions, and hence every history
distribution and every absorption mass — do not read the reward table at
all, so behavior profiles transport between the two tables definitionally
and the auxiliary mover payoff is literally the original recipient payoff.
The recipient's externality therefore becomes the mover's own auxiliary
continuation debt, and the actual-reach paid-row theorem applies to it.

Zeroing the untouched auxiliary coordinates, rather than copying the
recipient's coordinate into all of them, keeps the auxiliary reward bound
below the original one: the canonical `quittingRewardBound` is a sum over
all terminal coalitions and all coordinates, not a coordinate maximum.
-/
import FableDebtActualReach
import FableActualReachSupport
import UniformEquilibrium.Quitting.RewardBound
import UniformEquilibrium.Quitting.Cycles.BehaviorPureTimeExtremality
import UniformEquilibrium.Quitting.Boundary.Analytic.UnboundedInverseIterate
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPaidFirstDisagreement

noncomputable section

namespace GameTheory

open StochasticGame _root_.Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The auxiliary role-swapped reward table -/

/-- The auxiliary quitting reward table which pays the mover exactly the
recipient's original terminal coordinate and pays every other coordinate
zero. -/
def quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who => if who = mover then reward terminal recipient else 0

omit [Fintype ι] in
@[simp] theorem quittingRoleSwapReward_apply_mover
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingRoleSwapReward reward mover recipient terminal mover =
      reward terminal recipient := by
  simp [quittingRoleSwapReward]

/-- The auxiliary table never raises the canonical quitting reward bound:
one coordinate is copied and all the others are zeroed. -/
theorem quittingRewardBound_quittingRoleSwapReward_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι) :
    quittingRewardBound (quittingRoleSwapReward reward mover recipient) ≤
      quittingRewardBound reward := by
  unfold quittingRewardBound
  refine Finset.sum_le_sum fun terminal _ => ?_
  have hrow : ∑ who, |quittingRoleSwapReward reward mover recipient terminal who| =
      |reward terminal recipient| := by
    simp [quittingRoleSwapReward, apply_ite abs, Finset.sum_ite_eq']
  rw [hrow]
  exact Finset.single_le_sum (f := fun who => |reward terminal who|)
    (fun who _ => abs_nonneg _) (Finset.mem_univ recipient)

/-! ## Reward independence of the quitting dynamics -/

omit [DecidableEq ι] in
/-- The history distribution of a quitting game does not read the reward
table: states, actions and transitions are reward-free, so one behavior
profile induces the same history law under any two tables. -/
theorem histDist_quittingGame_reward_congr
    (source target : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame source).BehaviorProfile) :
    ∀ time : ℕ, (quittingGame source).histDist profile none time =
      (quittingGame target).histDist profile none time
  | 0 => rfl
  | time + 1 => by
      rw [StochasticGame.histDist_succ, StochasticGame.histDist_succ,
        histDist_quittingGame_reward_congr source target profile time]
      rfl

omit [DecidableEq ι] in
/-- Limiting absorption masses are the same under any two reward tables. -/
theorem quittingAbsorbedMassLimit_reward_congr
    (source target : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame source).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMassLimit source profile terminal =
      quittingAbsorbedMassLimit target profile terminal := by
  unfold quittingAbsorbedMassLimit
  refine iSup_congr fun time => ?_
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  rw [histDist_quittingGame_reward_congr source target profile time]
  rfl

/-! ## Payoff transfer through the auxiliary table -/

/-- **Payoff transfer.**  Under the auxiliary table the mover's terminal
payoff is literally the recipient's original terminal payoff, at every
behavior profile. -/
theorem quittingTerminalPayoff_quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff (quittingRoleSwapReward reward mover recipient)
        profile mover =
      quittingTerminalPayoff reward profile recipient := by
  unfold quittingTerminalPayoff
  refine Finset.sum_congr rfl fun terminal _ => ?_
  rw [quittingAbsorbedMassLimit_reward_congr
    (quittingRoleSwapReward reward mover recipient) reward profile terminal,
    quittingRoleSwapReward_apply_mover]

/-- The canonical live history, and therefore the live root of a behavior
profile, is reward-free. -/
theorem quittingProfileLiveRoot_quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingProfileLiveRoot (quittingRoleSwapReward reward mover recipient)
        profile = quittingProfileLiveRoot reward profile :=
  rfl

/-- The live-spine hazard of a behavior strategy is reward-free. -/
theorem quittingBehaviorLiveHazard_quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (who : ι) (deviation : (quittingGame reward).BehaviorStrategy who) :
    quittingBehaviorLiveHazard (quittingRoleSwapReward reward mover recipient)
        (who := who) deviation =
      quittingBehaviorLiveHazard reward deviation :=
  rfl

/-- The pure-time behavior strategy is reward-free. -/
theorem quittingPureTimeBehaviorStrategy_quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (who : ι) (quitTime : Option ℕ) :
    quittingPureTimeBehaviorStrategy
        (quittingRoleSwapReward reward mover recipient) who quitTime =
      quittingPureTimeBehaviorStrategy reward who quitTime :=
  rfl

/-- **Pure-time payoff transfer.**  The mover's auxiliary pure-time
deviation payoff is the recipient's original payoff at the same literal
pure-time replacement. -/
theorem quittingPureTimeDeviationPayoff_quittingRoleSwapReward
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (mover recipient : ι)
    (profile : (quittingGame reward).BehaviorProfile) (quitTime : Option ℕ) :
    quittingPureTimeDeviationPayoff
        (quittingRoleSwapReward reward mover recipient) profile mover quitTime =
      quittingTerminalPayoff reward
        (Function.update profile mover
          (quittingPureTimeBehaviorStrategy reward mover quitTime)) recipient := by
  unfold quittingPureTimeDeviationPayoff
  exact quittingTerminalPayoff_quittingRoleSwapReward reward mover recipient
    (Function.update profile mover
      (quittingPureTimeBehaviorStrategy reward mover quitTime))

/-! ## The externality is an auxiliary continuation debt -/

/-- **Debt transfer.**  The mover's own strategy in the higher-payoff
profile is a legal unilateral response at the lower-payoff profile, so the
recipient's payoff there is below the mover's auxiliary continuation
best-response value. -/
theorem quittingTerminalPayoff_update_le_roleSwapContinuationBestResponseValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover recipient : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover) :
    quittingTerminalPayoff reward
        (Function.update profile mover deviation) recipient ≤
      quittingContinuationBestResponseValue
        (quittingRoleSwapReward reward mover recipient) profile mover := by
  have hle := quittingTerminalPayoff_update_le_continuationBestResponseValue
    (quittingRoleSwapReward reward mover recipient) profile mover deviation
  rw [quittingTerminalPayoff_quittingRoleSwapReward] at hle
  exact hle

/-- A positive unilateral payoff externality for the recipient is a
positive auxiliary continuation debt for the mover at the lower-payoff
profile. -/
theorem positiveExternality_le_roleSwapContinuationDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover recipient : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover) (Δ : ℝ)
    (hgap : Δ ≤ quittingTerminalPayoff reward
        (Function.update profile mover deviation) recipient -
      quittingTerminalPayoff reward profile recipient) :
    Δ ≤ quittingContinuationBestResponseValue
        (quittingRoleSwapReward reward mover recipient) profile mover -
      quittingTerminalPayoff
        (quittingRoleSwapReward reward mover recipient) profile mover := by
  rw [quittingTerminalPayoff_quittingRoleSwapReward]
  have hle := quittingTerminalPayoff_update_le_roleSwapContinuationBestResponseValue
    reward profile mover recipient deviation
  linarith

/-! ## The localized externality row -/

/-- **Role-swapped externality localization.**  A unilateral payoff
externality of size at least `Δ > 0` for the recipient produces, on the
literal lower-payoff profile, two pure quitting-time plans of the mover
whose recipient-payoff difference is at least `Δ / 4`, together with a
start date whose joint survival prefix carries the division-free floor
`Δ ^ 2 / (32 * quittingRewardBound reward ^ 2)`.

The mover and the recipient need not be distinct; the coincident case is
the ordinary own-payoff statement. -/
theorem positiveExternality_exists_actualJointReach_pureTimeRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover recipient : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : Δ ≤ quittingTerminalPayoff reward
        (Function.update profile mover deviation) recipient -
      quittingTerminalPayoff reward profile recipient) :
    ∃ sourceWitness receivingWitness : Option ℕ, ∃ start : ℕ,
      Δ / 4 ≤ quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover receivingWitness))
            recipient -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover sourceWitness))
            recipient ∧
        Δ * Δ ≤ 32 * quittingRewardBound reward * quittingRewardBound reward *
          quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) start := by
  obtain ⟨row, hreach⟩ :=
    positiveDebt_exists_actualJointReach_paidFirstDisagreementRow
      (quittingRoleSwapReward reward mover recipient) profile mover Δ hΔ
      (positiveExternality_le_roleSwapContinuationDebt reward profile mover
        recipient deviation Δ hgap)
  refine ⟨row.sourceWitness, row.receivingWitness, row.start, ?_, ?_⟩
  · have hedge := row.edge_identity
    have hpaid := row.gain_le_paid
    rw [quittingPureTimeDeviationPayoff_quittingRoleSwapReward,
      quittingPureTimeDeviationPayoff_quittingRoleSwapReward] at hedge
    linarith
  · rw [quittingProfileLiveRoot_quittingRoleSwapReward] at hreach
    have hswap := quittingRewardBound_quittingRoleSwapReward_le reward mover recipient
    have hswap0 :=
      quittingRewardBound_nonneg (quittingRoleSwapReward reward mover recipient)
    have hprefix :=
      quittingSurvivalPrefix_nonneg (quittingProfileLiveRoot reward profile) row.start
    have hsquare : quittingRewardBound (quittingRoleSwapReward reward mover recipient) *
        quittingRewardBound (quittingRoleSwapReward reward mover recipient) ≤
        quittingRewardBound reward * quittingRewardBound reward :=
      mul_le_mul hswap hswap hswap0 (hswap0.trans hswap)
    nlinarith [hreach, hsquare, hprefix]

/-- The note's form of the localization: a fixed externality size `a`, and
any accuracy `Δ` with `0 < Δ ≤ a`. -/
theorem positiveExternality_exists_actualJointReach_pureTimeRow_of_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover recipient : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover)
    (a Δ : ℝ) (hΔ : 0 < Δ) (hΔa : Δ ≤ a)
    (hgap : a ≤ quittingTerminalPayoff reward
        (Function.update profile mover deviation) recipient -
      quittingTerminalPayoff reward profile recipient) :
    ∃ sourceWitness receivingWitness : Option ℕ, ∃ start : ℕ,
      Δ / 4 ≤ quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover receivingWitness))
            recipient -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover sourceWitness))
            recipient ∧
        Δ * Δ ≤ 32 * quittingRewardBound reward * quittingRewardBound reward *
          quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) start :=
  positiveExternality_exists_actualJointReach_pureTimeRow reward profile mover
    recipient deviation Δ hΔ (by linarith)

/-- **Supported role-swapped externality localization.**  The same
localization with the source pure-time plan supported by the mover's own
actual stopping law on the live spine: either it is a finite date carrying
strictly positive stopping mass, or it is the never-quitting plan and that
branch carries strictly positive mass. -/
theorem positiveExternality_exists_actualJointReach_pureTimeRow_withSupport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (mover recipient : ι)
    (deviation : (quittingGame reward).BehaviorStrategy mover)
    (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : Δ ≤ quittingTerminalPayoff reward
        (Function.update profile mover deviation) recipient -
      quittingTerminalPayoff reward profile recipient) :
    ∃ sourceWitness receivingWitness : Option ℕ, ∃ start : ℕ,
      (Δ / 4 ≤ quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover receivingWitness))
            recipient -
          quittingTerminalPayoff reward
            (Function.update profile mover
              (quittingPureTimeBehaviorStrategy reward mover sourceWitness))
            recipient) ∧
        (Δ * Δ ≤ 32 * quittingRewardBound reward * quittingRewardBound reward *
          quittingSurvivalPrefix (quittingProfileLiveRoot reward profile) start) ∧
        ((∃ date, sourceWitness = some date ∧
            0 < quittingHazardStopMass
              (quittingBehaviorLiveHazard reward (profile mover)) date) ∨
          (sourceWitness = none ∧
            0 < quittingHazardNeverMass
              (quittingBehaviorLiveHazard reward (profile mover)))) := by
  obtain ⟨row, hreach, hsupport⟩ :=
    positiveDebt_exists_actualJointReach_paidRow_withSupport
      (quittingRoleSwapReward reward mover recipient) profile mover Δ hΔ
      (positiveExternality_le_roleSwapContinuationDebt reward profile mover
        recipient deviation Δ hgap)
  rw [quittingBehaviorLiveHazard_quittingRoleSwapReward] at hsupport
  refine ⟨row.sourceWitness, row.receivingWitness, row.start, ?_, ?_, hsupport⟩
  · have hedge := row.edge_identity
    have hpaid := row.gain_le_paid
    rw [quittingPureTimeDeviationPayoff_quittingRoleSwapReward,
      quittingPureTimeDeviationPayoff_quittingRoleSwapReward] at hedge
    linarith
  · rw [quittingProfileLiveRoot_quittingRoleSwapReward] at hreach
    have hswap := quittingRewardBound_quittingRoleSwapReward_le reward mover recipient
    have hswap0 :=
      quittingRewardBound_nonneg (quittingRoleSwapReward reward mover recipient)
    have hprefix :=
      quittingSurvivalPrefix_nonneg (quittingProfileLiveRoot reward profile) row.start
    have hsquare : quittingRewardBound (quittingRoleSwapReward reward mover recipient) *
        quittingRewardBound (quittingRoleSwapReward reward mover recipient) ≤
        quittingRewardBound reward * quittingRewardBound reward :=
      mul_le_mul hswap hswap hswap0 (hswap0.trans hswap)
    nlinarith [hreach, hsquare, hprefix]

end GameTheory
