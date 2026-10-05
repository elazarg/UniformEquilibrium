import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinDebt
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalOneOutsiderTransport
import UniformEquilibrium.Quitting.Classification.QuietExtension.TerminalWeightedDebtLift
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockSampledLPDual
import UniformEquilibrium.Quitting.Classification.QuietExtension.DeadlineWithdrawalFinFourExistence
import UniformEquilibrium.Quitting.Classification.ThreePlayer.NonnegativeSingletonEarlyAbsorption

/-! # Fixed-target quiet extensions with the Never row omitted

A strictly positive actual child singleton pays for the explicit terminal
joint-Never residual. The original source F/J rows may use different response
kinds for different outsiders. Actual quiet profiles and fixed child targets
are preserved. This does not assert protection at every evaluation.
-/

noncomputable section

namespace GameTheory

open StochasticGame
open scoped BigOperators

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Original finite future/join rows bound the actual outsider debt while
retaining the joint-Never residual. No singleton sign hypothesis is needed. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty (QuittingChildPlayer deleted)]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (outside : {who : α // deleted who}) (kind : WithdrawalFutureJoinKind)
    (certificate : WithdrawalFutureJoinRewardCertificate kind
      (quittingChildWithOutsiderReward reward deleted outside))
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      (∑ who, certificate.debtWeight who *
        (quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who)) +
      certificate.neverExcess *
        ∏ who, (quittingBehaviorStoppingLaw
          (quittingDeleteReward reward deleted) (profile who) none).toReal := by
  let : Nonempty {who : Option (QuittingChildPlayer deleted) // ¬ who = none} :=
    Nonempty.map (fun who => ⟨some who, Option.some_ne_none who⟩)
      (inferInstance : Nonempty (QuittingChildPlayer deleted))
  apply quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound_add_at
    deleted reward outside certificate.debtWeight
  simpa only [quietOutsiderChildLaws_childWithOutsiderChildProfile] using
    withdrawalFutureJoin_quietLift_outsideDebt_le_add_neverExcess
      (quittingChildWithOutsiderReward reward deleted outside) certificate
      (quittingChildWithOutsiderChildProfile reward deleted outside profile)

omit [Fintype α] in
private theorem childWithOutsider_singleton_positive
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (outside : {who : α // deleted who}) (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1) :
    0 < quittingChildWithOutsiderReward reward deleted outside
      ⟨{some pivot}, Finset.singleton_nonempty (some pivot)⟩ (some pivot) := by
  rw [quittingChildWithOutsiderReward_apply_original]
  simpa only [Finset.map_singleton, quittingChildWithOutsiderOriginalEmbedding_some,
    quittingSingletonTerminal] using hpivot

/-- The actual full-game debt bound produced by original F/J rows and one
positive child singleton. No favorable strategy or response cap is supplied. -/
theorem quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (outside : {who : α // deleted who}) (kind : WithdrawalFutureJoinKind)
    (certificate : WithdrawalFutureJoinRewardCertificate kind
      (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1)
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 -
        quittingTerminalPayoff reward
          (quittingLiftDeletedProfile reward deleted profile) outside.1 ≤
      ∑ who, certificate.positiveSingletonWeight pivot who *
        (quittingBehaviorDeviationPayoffCap (quittingDeleteReward reward deleted) profile who -
          quittingTerminalPayoff (quittingDeleteReward reward deleted) profile who) := by
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  exact quittingLiftDeletedProfile_outsideTerminalDebt_le_of_oneOutsiderBound
    deleted reward outside (certificate.positiveSingletonWeight pivot)
    (fun childProfile =>
      withdrawalFutureJoin_quietLift_outsideDebt_le_positiveSingletonWeights
        (quittingChildWithOutsiderReward reward deleted outside) certificate childProfile
        pivot (childWithOutsider_singleton_positive deleted reward outside pivot hpivot)) profile

/-- One finite outsider amplification, including the residual/singleton charge. -/
def withdrawalFutureJoinOutsiderWeight
    (deleted : α → Prop) [DecidablePred deleted]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted) (outside : {who : α // deleted who}) : ℝ :=
  ∑ who, (certificate outside).positiveSingletonWeight pivot who

/-- One fixed source-dependent amplification for every requested accuracy. -/
def withdrawalFutureJoinOutsiderMaxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (withdrawalFutureJoinOutsiderWeight deleted reward kind certificate pivot))

theorem withdrawalFutureJoinOutsiderWeight_le_maxWeight
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted) (outside : {who : α // deleted who}) :
    withdrawalFutureJoinOutsiderWeight deleted reward kind certificate pivot outside ≤
      withdrawalFutureJoinOutsiderMaxWeight deleted reward kind certificate pivot := by
  exact (Finset.le_sup'
    (f := withdrawalFutureJoinOutsiderWeight deleted reward kind certificate pivot)
    (Finset.mem_univ outside)).trans (le_max_right _ _)

/-- Full behavioral terminal approximate Nash protection for the literal quiet
lift, with the source-derived fixed amplification. -/
theorem isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1)
    {error : ℝ} (herror : 0 ≤ error)
    (profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile)
    (hnash : (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) error profile) :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward)
      (withdrawalFutureJoinOutsiderMaxWeight deleted reward kind certificate pivot * error)
      (quittingLiftDeletedProfile reward deleted profile) := by
  exact isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds deleted reward
    (fun outside => (certificate outside).positiveSingletonWeight pivot)
    (fun outside child => (certificate outside).positiveSingletonWeight_nonneg pivot child
      (childWithOutsider_singleton_positive deleted reward outside pivot hpivot))
    (withdrawalFutureJoinOutsiderMaxWeight deleted reward kind certificate pivot)
    (le_max_left _ _)
    (fun outside =>
      withdrawalFutureJoinOutsiderWeight_le_maxWeight
        deleted reward kind certificate pivot outside)
    herror profile
    (fun outside => quittingLiftDeletedProfile_outsideDebt_le_of_withdrawalFutureJoin
      deleted reward outside (kind outside) (certificate outside) pivot hpivot profile) hnash

/-- Every specified actual child UE target extends to one fixed parent target.
Every accuracy witness is the literal quiet lift of an actual child profile. -/
theorem exists_uniformPayoffWitnesses_eq_on_child_of_withdrawalFutureJoinFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1)
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
      none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ (profile : (quittingGame
              (quittingDeleteReward reward deleted)).BehaviorProfile) (threshold : ℕ),
            ∀ horizon, threshold ≤ horizon →
              (quittingGame reward).IsεHorizonNash none horizon ε
                  (quittingLiftDeletedProfile reward deleted profile) ∧
                ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                  (quittingLiftDeletedProfile reward deleted profile) who - payoff who| ≤ ε := by
  exact exists_uniformPayoffWitnesses_eq_on_image_of_terminalNash_lift
    reward (quittingDeleteReward reward deleted) (fun who => who.1)
    (quittingLiftDeletedProfile reward deleted)
    (withdrawalFutureJoinOutsiderMaxWeight deleted reward kind certificate pivot)
    (fun profile who => quittingTerminalPayoff_liftDeletedProfile reward deleted profile who)
    (fun herror profile hnash => isεAsymptoticNash_quietLift_of_withdrawalFutureJoinFamily
      deleted reward kind certificate pivot hpivot herror profile hnash) target htarget

/-- Project actual quiet witnesses to the usual fixed-target UE conclusion. -/
theorem exists_uniformEquilibriumPayoff_eq_on_child_of_withdrawalFutureJoinFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1)
    (target : Payoff (QuittingChildPlayer deleted))
    (htarget : (quittingGame (quittingDeleteReward reward deleted)).IsUniformEquilibriumPayoff
      none target) :
    ∃ payoff : Payoff α,
      (∀ who : QuittingChildPlayer deleted, payoff who.1 = target who) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hcoordinates, hwitnesses⟩ :=
    exists_uniformPayoffWitnesses_eq_on_child_of_withdrawalFutureJoinFamily
      deleted reward kind certificate pivot hpivot target htarget
  refine ⟨payoff, hcoordinates, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

/-- Literal reward data supply every Fin4 child target internally. -/
theorem quittingGame_exists_uniformPayoffWitnesses_of_finFour_withdrawalFutureJoinFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {A : Finset (Fin 4) // A.Nonempty} → Payoff (Fin 4))
    (kind : {who : Fin 4 // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1) :
    ∃ payoff : Payoff (Fin 4),
      ∀ ε : ℝ, 0 < ε →
        ∃ (profile : (quittingGame
            (quittingDeleteReward reward deleted)).BehaviorProfile) (threshold : ℕ),
          ∀ horizon, threshold ≤ horizon →
            (quittingGame reward).IsεHorizonNash none horizon ε
                (quittingLiftDeletedProfile reward deleted profile) ∧
              ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
                (quittingLiftDeletedProfile reward deleted profile) who - payoff who| ≤ ε := by
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  obtain ⟨target, htarget⟩ :=
    quittingDeleteReward_finFour_exists_uniformEquilibriumPayoff deleted reward
  obtain ⟨payoff, _, hwitnesses⟩ :=
    exists_uniformPayoffWitnesses_eq_on_child_of_withdrawalFutureJoinFamily
      deleted reward kind certificate pivot hpivot target htarget
  exact ⟨payoff, hwitnesses⟩

/-- Actual Fin4 uniform equilibrium from omitted-Never withdrawal rows. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_finFour_withdrawalFutureJoinFamily
    (deleted : Fin 4 → Prop) [DecidablePred deleted]
    [Nonempty {who : Fin 4 // deleted who}]
    (reward : {A : Finset (Fin 4) // A.Nonempty} → Payoff (Fin 4))
    (kind : {who : Fin 4 // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : Fin 4 // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot.1) pivot.1) :
    ∃ payoff : Payoff (Fin 4), (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨payoff, hwitnesses⟩ :=
    quittingGame_exists_uniformPayoffWitnesses_of_finFour_withdrawalFutureJoinFamily
      deleted reward kind certificate pivot hpivot
  refine ⟨payoff, fun ε hε => ?_⟩
  obtain ⟨profile, threshold, hwitness⟩ := hwitnesses ε hε
  exact ⟨quittingLiftDeletedProfile reward deleted profile, threshold, hwitness⟩

/-- A low-player child with a nonnegative singleton selects original-game
quiet profiles with vanishing full regret and joint Never. The finite constants
are selected from the original certificates before the requested scale. -/
theorem exists_quietProfiles_smallExploitability_smallNever_of_withdrawalFutureJoinFamily
    (deleted : α → Prop) [DecidablePred deleted]
    [Nonempty {who : α // deleted who}]
    (reward : {A : Finset α // A.Nonempty} → Payoff α)
    (kind : {who : α // deleted who} → WithdrawalFutureJoinKind)
    (certificate : ∀ outside : {who : α // deleted who},
      WithdrawalFutureJoinRewardCertificate (kind outside)
        (quittingChildWithOutsiderReward reward deleted outside))
    (hcard : Fintype.card (QuittingChildPlayer deleted) ≤ 3)
    (pivot : QuittingChildPlayer deleted)
    (hpivot : 0 ≤ reward (quittingSingletonTerminal pivot.1) pivot.1) :
    let : Nonempty α := ⟨pivot.1⟩
    ∃ factor residual : ℝ, 1 ≤ factor ∧ 0 ≤ residual ∧
      (∀ outside, (∑ who, (certificate outside).debtWeight who) ≤ factor) ∧
      (∀ outside, (certificate outside).neverExcess ≤ residual) ∧
      ∀ delta : ℝ, 0 < delta →
        ∃ profile : (quittingGame (quittingDeleteReward reward deleted)).BehaviorProfile,
          quittingTerminalExploitability reward
              (quittingLiftDeletedProfile reward deleted profile) ≤
            factor * (delta + delta ^ 2) + residual * delta ∧
          (∏ who, (quittingBehaviorStoppingLaw
            (quittingDeleteReward reward deleted) (profile who) none).toReal) ≤ delta := by
  let : Nonempty α := ⟨pivot.1⟩
  let : Nonempty (QuittingChildPlayer deleted) := ⟨pivot⟩
  let weight := fun outside : {who : α // deleted who} =>
    ∑ who, (certificate outside).debtWeight who
  let factor := max 1 (Finset.univ.sup' Finset.univ_nonempty weight)
  let residual := max 0 (Finset.univ.sup' Finset.univ_nonempty
    (fun outside => (certificate outside).neverExcess))
  have hfactor : 1 ≤ factor := le_max_left _ _
  have hresidual : 0 ≤ residual := le_max_left _ _
  have hweight : ∀ outside, (∑ who, (certificate outside).debtWeight who) ≤ factor := by
    intro outside
    exact (Finset.le_sup' (f := weight) (Finset.mem_univ outside)).trans (le_max_right _ _)
  have hexcess : ∀ outside, (certificate outside).neverExcess ≤ residual := by
    intro outside
    exact (Finset.le_sup' (f := fun outside => (certificate outside).neverExcess)
      (Finset.mem_univ outside)).trans (le_max_right _ _)
  refine ⟨factor, residual, hfactor, hresidual, hweight, hexcess, ?_⟩
  intro delta hdelta
  have hsingleton : 0 ≤ quittingDeleteReward reward deleted
      (quittingSingletonTerminal pivot) pivot := by
    change 0 ≤ reward _ _
    have heq : quittingExtendDeletedCoalition deleted (quittingSingletonTerminal pivot) =
        quittingSingletonTerminal pivot.1 := by
      congr 1
    rw [heq]
    exact hpivot
  obtain ⟨profile, hchild, hnever⟩ :=
    exists_terminalProfile_smallExploitability_smallNever_of_nonnegativeSingleton
      (quittingDeleteReward reward deleted) hcard pivot hsingleton hdelta
  let jointNever := ∏ who, (quittingBehaviorStoppingLaw
    (quittingDeleteReward reward deleted) (profile who) none).toReal
  have hjoint : 0 ≤ jointNever := Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hnash := isεAsymptoticNash_quietLift_of_outsideTerminalDebtBounds_add
    deleted reward (fun outside => (certificate outside).debtWeight)
    (fun outside who => (certificate outside).debtWeight_nonneg who)
    factor hfactor hweight (residual * jointNever) (mul_nonneg hresidual hjoint)
    (add_nonneg hdelta.le (sq_nonneg delta)) profile
    (fun outside =>
      (quittingLiftDeletedProfile_outsideDebt_le_add_neverExcess_of_withdrawalFutureJoin
        deleted reward outside (kind outside) (certificate outside) profile).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hexcess outside) hjoint)))
    (isεAsymptoticNash_of_quittingTerminalExploitability_le profile hchild)
  refine ⟨profile, ?_, hnever⟩
  exact (quittingTerminalExploitability_le_of_isεAsymptoticNash reward
    (quittingLiftDeletedProfile reward deleted profile)
    (add_nonneg (mul_nonneg (le_trans zero_le_one hfactor)
      (add_nonneg hdelta.le (sq_nonneg delta))) (mul_nonneg hresidual hjoint)) hnash).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnever hresidual))

end GameTheory
