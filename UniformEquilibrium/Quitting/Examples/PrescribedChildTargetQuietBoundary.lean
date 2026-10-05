import UniformEquilibrium.Quitting.Paths.SoloStoppingLawPayoff
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass
import UniformEquilibrium.Quitting.Terminal.TerminalPayoffRewardOrder
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability
import UniformEquilibrium.Quitting.Paths.SureExitSet
import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderDebt

/-! # Selecting a quiet target does not preserve an arbitrary child target

Players 1 and 2 receive one only when the other child quits alone.
Player 0 receives one at every terminal coalition; player 3 receives zero.
Every actual profile with outsiders 0 and 3 literally Never satisfies
`1 ≤ 3 * exploitability + payoff 1 + payoff 2`. Thus a vanishing-regret
quiet family cannot deliver the child target `(0, 0)`.
-/

noncomputable section

namespace GameTheory.PrescribedChildTargetQuietBoundary

open StochasticGame Filter
open QuittingSureSetOwnerRepair

def reward (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) : ℝ :=
  if who = 0 then 1
  else if who = 1 then if terminal.1 = {2} then 1 else 0
  else if who = 2 then if terminal.1 = {1} then 1 else 0
  else 0

/-- Quietness is a condition on the actual full stopping laws. -/
def Quiet (profile : (quittingGame reward).BehaviorProfile) : Prop :=
  quittingBehaviorStoppingLaw reward (profile 0) = PMF.pure none ∧
    quittingBehaviorStoppingLaw reward (profile 3) = PMF.pure none

def deleted (who : Fin 4) : Prop := who = 0 ∨ who = 3

instance : DecidablePred deleted := fun _ => inferInstanceAs (Decidable (_ ∨ _))

private theorem optionOutsideReward_constant (outside : {who : Fin 4 // deleted who})
    (terminal : {S : Finset (Option (QuittingChildPlayer deleted)) // S.Nonempty}) :
    quittingChildWithOutsiderReward reward deleted outside terminal none =
      if outside.1 = 0 then 1 else 0 := by
  change reward _ outside.1 = _
  rcases outside.2 with h | h <;> simp [reward, h]

/-- Each of the five original F/J operations has a zero-weight certificate
for each literal outsider. No Never inequality is assumed. -/
def certificate (outside : {who : Fin 4 // deleted who}) (kind : WithdrawalFutureJoinKind) :
    WithdrawalFutureJoinRewardCertificate kind
      (quittingChildWithOutsiderReward reward deleted outside) where
  advanceWeight := 0
  withdrawalWeight := 0
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by simp
  future_row := by
    intro A hA
    cases kind <;> simp [optionOutsideReward_constant, WithdrawalFutureJoinKind.futureWeight]
  join_row := by
    intro A hA
    simp [optionOutsideReward_constant]

/-- The restricted child's all-Never profile is an exact equilibrium. -/
theorem childAllNever_exactNash :
    (quittingGame (quittingDeleteReward reward deleted)).IsεAsymptoticNash
      (quittingTerminalPayoff (quittingDeleteReward reward deleted)) 0
      (quittingAlwaysContinueProfile (quittingDeleteReward reward deleted)) := by
  rw [← quittingStationaryProfile_pureSetRoot_empty]
  apply (isεAsymptoticNash_pureSetRoot_iff (quittingDeleteReward reward deleted) ∅ 0).mpr
  intro who
  have hzero : quittingDeleteReward reward deleted (quittingSingletonTerminal who) who = 0 := by
    rw [quittingDeleteReward_singletonTerminal]
    have h0 : who.1 ≠ 0 := fun h => who.2 (Or.inl h)
    have h3 : who.1 ≠ 3 := fun h => who.2 (Or.inr h)
    rcases who with ⟨value, hvalue⟩
    fin_cases value <;> simp_all [reward, quittingSingletonTerminal]
  simp only [Finset.insert_empty, Finset.erase_empty, quittingSetReward_empty, add_zero]
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty who)]
  change max (quittingDeleteReward reward deleted (quittingSingletonTerminal who) who) 0 ≤ 0
  rw [hzero]
  norm_num

/-- That exact restricted-child equilibrium delivers the zero target. -/
theorem childAllNever_payoff_zero (who : QuittingChildPlayer deleted) :
    quittingTerminalPayoff (quittingDeleteReward reward deleted)
      (quittingAlwaysContinueProfile (quittingDeleteReward reward deleted)) who = 0 :=
  quittingTerminalPayoff_quittingAlwaysContinue _ who

private theorem neverAtom_le_one
    (profile : (quittingGame reward).BehaviorProfile) (who : Fin 4) :
    (quittingBehaviorStoppingLaw reward (profile who) none).toReal ≤ 1 := by
  exact (ENNReal.toReal_le_toReal
    (PMF.apply_ne_top (quittingBehaviorStoppingLaw reward (profile who)) none)
    (by norm_num)).mpr (PMF.coe_le_one _ _)

/-- The actual joint-Never mass is the product of the two child Never atoms. -/
theorem liveMass_eq_childNeverProduct
    (profile : (quittingGame reward).BehaviorProfile) (hquiet : Quiet profile) :
    quittingLiveMassLimit reward profile =
      (quittingBehaviorStoppingLaw reward (profile 1) none).toReal *
        (quittingBehaviorStoppingLaw reward (profile 2) none).toReal := by
  change quittingTerminalOutcomeMass reward profile none = _
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (quittingBehaviorStoppingLaw reward (profile 0) none).toReal *
    ((quittingBehaviorStoppingLaw reward (profile 1) none).toReal *
      ((quittingBehaviorStoppingLaw reward (profile 2) none).toReal *
        ((quittingBehaviorStoppingLaw reward (profile 3) none).toReal * 1))) = _
  rw [hquiet.1, hquiet.2]
  simp

/-- A child who changes to Never receives the other child's finite-quit mass. -/
theorem firstChild_neverDeviation_payoff
    (profile : (quittingGame reward).BehaviorProfile) (hquiet : Quiet profile) :
    quittingTerminalPayoff reward
      (Function.update profile 1
        (quittingStoppingLawBehaviorStrategy reward 1 (PMF.pure none))) 1 =
      1 - (quittingBehaviorStoppingLaw reward (profile 2) none).toReal := by
  rw [quittingTerminalPayoff_soloStoppingLaw_eq reward _ 2 1]
  · simp [reward, quittingSingletonTerminal]
  · intro who hwho
    fin_cases who
    · simpa using hquiet.1
    · simp
    · exact (hwho rfl).elim
    · simpa using hquiet.2

/-- The second child's Never deviation has the symmetric actual payoff. -/
theorem secondChild_neverDeviation_payoff
    (profile : (quittingGame reward).BehaviorProfile) (hquiet : Quiet profile) :
    quittingTerminalPayoff reward
      (Function.update profile 2
        (quittingStoppingLawBehaviorStrategy reward 2 (PMF.pure none))) 2 =
      1 - (quittingBehaviorStoppingLaw reward (profile 1) none).toReal := by
  rw [quittingTerminalPayoff_soloStoppingLaw_eq reward _ 1 2]
  · simp [reward, quittingSingletonTerminal]
  · intro who hwho
    fin_cases who
    · simpa using hquiet.1
    · exact (hwho rfl).elim
    · simp
    · simpa using hquiet.2

private theorem outsiderQuitZero_payoff
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingTerminalPayoff reward
      (Function.update profile 0
        (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))) 0 =
      1 := by
  rw [quittingTerminalPayoff_eq_constant_mul_absorption reward _ 0 1
    (by intro terminal; simp [reward])]
  have hzero : quittingLiveMassLimit reward
      (Function.update profile 0
        (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))) = 0 := by
    change quittingTerminalOutcomeMass reward _ none = 0
    rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
    simp
  rw [hzero]
  norm_num

/-- The constant-payoff outsider's unrestricted cap is one and its debt
is the full profile's joint-Never mass, whether or not the profile is quiet. -/
theorem outsiderDebt_eq_liveMass (profile : (quittingGame reward).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap reward profile 0 -
      quittingTerminalPayoff reward profile 0 = quittingLiveMassLimit reward profile := by
  have hcap : quittingBehaviorDeviationPayoffCap reward profile 0 = 1 := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply le_antisymm
    · apply quittingBestReplyValue_le
      intro deviation
      rw [quittingTerminalPayoff_eq_constant_mul_absorption reward _ 0 1
        (by intro terminal; simp [reward])]
      have hnonneg := quittingLiveMassLimit_nonneg reward (Function.update profile 0 deviation)
      linarith
    · have h := le_quittingBestReplyValue reward profile 0
        (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))
      rw [outsiderQuitZero_payoff profile] at h
      exact h
  rw [hcap, quittingTerminalPayoff_eq_constant_mul_absorption reward profile 0 1
    (by intro terminal; simp [reward])]
  ring

/-- A quantitative obstruction for actual unrestricted behavioral regret.
No finite-support, deadline, or attained-response hypothesis is needed. -/
theorem one_le_three_exploitability_add_childPayoffs
    (profile : (quittingGame reward).BehaviorProfile) (hquiet : Quiet profile) :
    1 ≤ 3 * quittingTerminalExploitability reward profile +
      quittingTerminalPayoff reward profile 1 + quittingTerminalPayoff reward profile 2 := by
  have hnash := isεAsymptoticNash_of_quittingTerminalExploitability_le profile (le_refl _)
  have hfirst := hnash 1
    (quittingStoppingLawBehaviorStrategy reward 1 (PMF.pure none))
  have hsecond := hnash 2
    (quittingStoppingLawBehaviorStrategy reward 2 (PMF.pure none))
  have houtside := hnash 0
    (quittingStoppingLawBehaviorStrategy reward 0 (PMF.pure (some 0)))
  rw [firstChild_neverDeviation_payoff profile hquiet] at hfirst
  rw [secondChild_neverDeviation_payoff profile hquiet] at hsecond
  rw [outsiderQuitZero_payoff profile,
    quittingTerminalPayoff_eq_constant_mul_absorption reward profile 0 1
      (by intro terminal; simp [reward]),
    liveMass_eq_childNeverProduct profile hquiet] at houtside
  have hproduct := mul_nonneg
    (sub_nonneg.mpr (neverAtom_le_one profile 1))
    (sub_nonneg.mpr (neverAtom_le_one profile 2))
  nlinarith

/-- In particular, an exactly zero delivered child target forces regret
at least one third, even though the child itself can have target zero. -/
theorem exploitability_ge_third_of_zero_childPayoffs
    (profile : (quittingGame reward).BehaviorProfile) (hquiet : Quiet profile)
    (hfirst : quittingTerminalPayoff reward profile 1 = 0)
    (hsecond : quittingTerminalPayoff reward profile 2 = 0) :
    (1 : ℝ) / 3 ≤ quittingTerminalExploitability reward profile := by
  have h := one_le_three_exploitability_add_childPayoffs profile hquiet
  rw [hfirst, hsecond] at h
  linarith

/-- The same actual quiet family cannot have vanishing full regret and
both child payoff coordinates tending to zero. -/
theorem not_tendsto_zero_regret_and_childPayoffs
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hquiet : ∀ n, Quiet (profiles n))
    (hregret : Tendsto (fun n => quittingTerminalExploitability reward (profiles n))
      atTop (nhds 0))
    (hfirst : Tendsto (fun n => quittingTerminalPayoff reward (profiles n) 1)
      atTop (nhds 0))
    (hsecond : Tendsto (fun n => quittingTerminalPayoff reward (profiles n) 2)
      atTop (nhds 0)) : False := by
  have hlimit := ((hregret.const_mul 3).add hfirst).add hsecond
  have hbound : (1 : ℝ) ≤ 0 := by
    apply ge_of_tendsto (by simpa using hlimit)
    exact Eventually.of_forall fun n =>
      one_le_three_exploitability_add_childPayoffs (profiles n) (hquiet n)
  norm_num at hbound

/-- A fixed target with both child coordinates zero cannot have quiet
uniform-equilibrium witnesses. The original witness profiles are retained
when taking the finite-horizon payoff limits. -/
theorem no_quiet_uniformWitnesses_extending_zeroChild
    (target : Payoff (Fin 4)) (hfirst : target 1 = 0) (hsecond : target 2 = 0) :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∃ (profile : (quittingGame reward).BehaviorProfile) (threshold : ℕ),
        Quiet profile ∧ ∀ horizon, threshold ≤ horizon →
          (quittingGame reward).IsεHorizonNash none horizon ε profile ∧
            ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
              profile who - target who| ≤ ε) := by
  intro hwitnesses
  obtain ⟨profile, threshold, hquiet, hwitness⟩ := hwitnesses (1 / 10) (by norm_num)
  have huniform : (quittingGame reward).IsUniformεEquilibrium none (1 / 10) profile :=
    ⟨threshold, fun horizon h => (hwitness horizon h).1⟩
  have hterminal := (quittingGame reward).isεAsymptoticNash_of_isUniformεEquilibrium
    none (quittingTerminalPayoff reward) huniform
    (fun selected who => tendsto_finiteAveragePayoff_quittingGame reward selected who)
  have hregret := quittingTerminalExploitability_le_of_isεAsymptoticNash
    reward profile (by norm_num : (0 : ℝ) ≤ 1 / 10) hterminal
  have hdelivery (who : Fin 4) :
      |quittingTerminalPayoff reward profile who - target who| ≤ 1 / 10 := by
    apply le_of_tendsto
      (((tendsto_finiteAveragePayoff_quittingGame reward profile who).sub
        tendsto_const_nhds).abs)
    exact eventually_atTop.mpr
      ⟨threshold, fun horizon h => (hwitness horizon h).2 who⟩
  have hpayoff1 := (abs_le.mp (hdelivery 1)).2
  have hpayoff2 := (abs_le.mp (hdelivery 2)).2
  rw [hfirst] at hpayoff1
  rw [hsecond] at hpayoff2
  have hbound := one_le_three_exploitability_add_childPayoffs profile hquiet
  linarith

/-- Selecting child payoff `(0, 1)` gives an exact parent equilibrium,
with player 1 quitting surely at the initial date. -/
theorem firstChildQuit_exactNash :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (quittingPureSetRoot {1})) := by
  apply (isεAsymptoticNash_pureSetRoot_iff reward {1} 0).mpr
  intro who
  fin_cases who <;> norm_num [quittingSetReward, reward]

/-- The reversed child choice gives a separate exact parent equilibrium. -/
theorem secondChildQuit_exactNash :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward (quittingPureSetRoot {2})) := by
  apply (isεAsymptoticNash_pureSetRoot_iff reward {2} 0).mpr
  intro who
  fin_cases who <;> norm_num [quittingSetReward, reward]

/-- The two alternative equilibrium child targets are literal terminal payoffs. -/
theorem alternative_childPayoffs :
    (quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot {1})) 1 = 0 ∧
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot {1})) 2 = 1) ∧
    (quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot {2})) 1 = 1 ∧
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward (quittingPureSetRoot {2})) 2 = 0) := by
  simp [quittingTerminalPayoff_pureSetRoot, quittingSetReward, reward]

/-- Both alternative exact equilibria retain literal Never outsider laws. -/
theorem alternative_equilibria_quiet :
    Quiet (quittingStationaryProfile reward (quittingPureSetRoot {1})) ∧
      Quiet (quittingStationaryProfile reward (quittingPureSetRoot {2})) := by
  have hnever (child : Fin 4) (hchild0 : child ≠ 0) (hchild3 : child ≠ 3)
      (outside : Fin 4) (houtside : outside = 0 ∨ outside = 3) :
      quittingBehaviorStoppingLaw reward
        (quittingStationaryProfile reward (quittingPureSetRoot {child}) outside) =
        PMF.pure none := by
    have hne : outside ≠ child := by
      rcases houtside with h | h <;> subst outside <;> exact Ne.symm (by assumption)
    have hstrategy : quittingStationaryProfile reward (quittingPureSetRoot {child}) outside =
        quittingPureTimeBehaviorStrategy reward outside none := by
      funext time history
      change quittingPureSetRoot {child} outside = PMF.pure false
      simp [quittingPureSetRoot, quittingSetAction, hne]
    rw [hstrategy]
    exact quittingBehaviorStoppingLaw_pureTime_never reward outside
  constructor <;> constructor
  · exact hnever 1 (by decide) (by decide) 0 (Or.inl rfl)
  · exact hnever 1 (by decide) (by decide) 3 (Or.inr rfl)
  · exact hnever 2 (by decide) (by decide) 0 (Or.inl rfl)
  · exact hnever 2 (by decide) (by decide) 3 (Or.inr rfl)

end GameTheory.PrescribedChildTargetQuietBoundary
