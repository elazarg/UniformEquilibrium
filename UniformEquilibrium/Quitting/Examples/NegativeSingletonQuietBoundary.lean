import UniformEquilibrium.Quitting.Classification.QuietExtension.WithdrawalFutureJoinRaw
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockMultipleOutsiderDebt
import UniformEquilibrium.Quitting.Terminal.TerminalPayoffRewardOrder
import UniformEquilibrium.Quitting.Terminal.TerminalExploitability
import UniformEquilibrium.Quitting.Paths.ProfileNeverMass

/-! # A negative singleton obstructs quiet sources, not parent equilibrium

One child receives minus one at every terminal coalition; every outsider
receives one. All original finite F/J rows admit zero weights, but every
actual quiet profile has unrestricted terminal exploitability at least one half.
This includes the literal Fin4 table with one child and three outsiders.
-/

noncomputable section

namespace GameTheory.NegativeSingletonQuietBoundary

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def reward (child : ι) (_ : {S : Finset ι // S.Nonempty}) (who : ι) : ℝ :=
  if who = child then -1 else 1

omit [Fintype ι] in
private theorem optionOutsideReward_eq_one (child : ι)
    (outside : {who : ι // who ≠ child})
    (terminal : {S : Finset (Option (QuittingChildPlayer (· ≠ child))) // S.Nonempty}) :
    quittingChildWithOutsiderReward (reward child) (· ≠ child) outside terminal none = 1 := by
  change (if outside.1 = child then (-1 : ℝ) else 1) = 1
  simp [outside.2]

/-- Every original five-kind F/J certificate passes with zero weights. -/
def certificate (child : ι) (outside : {who : ι // who ≠ child})
    (kind : WithdrawalFutureJoinKind) :
    WithdrawalFutureJoinRewardCertificate kind
      (quittingChildWithOutsiderReward (reward child) (· ≠ child) outside) where
  advanceWeight := 0
  withdrawalWeight := 0
  advanceWeight_nonneg := by simp
  withdrawalWeight_nonneg := by simp
  future_row := by
    intro A hA
    cases kind <;> simp [optionOutsideReward_eq_one, WithdrawalFutureJoinKind.futureWeight]
  join_row := by
    intro A hA
    simp [optionOutsideReward_eq_one]

private theorem liveMass_eq_zero_of_none_zero
    (child : ι) (profile : (quittingGame (reward child)).BehaviorProfile) (who : ι)
    (hlaw : quittingBehaviorStoppingLaw (reward child) (profile who) none = 0) :
    quittingLiveMassLimit (reward child) profile = 0 := by
  change quittingTerminalOutcomeMass (reward child) profile none = 0
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
  exact Finset.prod_eq_zero (Finset.mem_univ who) (by rw [hlaw]; simp)

private theorem quitZero_payoff (child who : ι) (hwho : who ≠ child)
    (profile : (quittingGame (reward child)).BehaviorProfile) :
    quittingTerminalPayoff (reward child)
      (Function.update profile who
        (quittingStoppingLawBehaviorStrategy (reward child) who (PMF.pure (some 0)))) who =
      1 := by
  rw [quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ who 1
    (by intro terminal; simp [reward, hwho])]
  have hzero := liveMass_eq_zero_of_none_zero child
    (Function.update profile who
      (quittingStoppingLawBehaviorStrategy (reward child) who (PMF.pure (some 0)))) who
    (by simp)
  rw [hzero]
  norm_num

private theorem childNever_payoff_eq_zero (child : ι)
    (profile : (quittingGame (reward child)).BehaviorProfile)
    (hquiet : ∀ who, who ≠ child →
      quittingBehaviorStoppingLaw (reward child) (profile who) = PMF.pure none) :
    quittingTerminalPayoff (reward child)
      (Function.update profile child
        (quittingStoppingLawBehaviorStrategy (reward child) child (PMF.pure none))) child = 0 := by
  have hneverLive : quittingLiveMassLimit (reward child)
      (Function.update profile child
        (quittingStoppingLawBehaviorStrategy (reward child) child (PMF.pure none))) = 1 := by
    change quittingTerminalOutcomeMass (reward child) _ none = 1
    rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none]
    have hlaws (who : ι) : quittingBehaviorStoppingLaw (reward child)
        (Function.update profile child
          (quittingStoppingLawBehaviorStrategy (reward child) child (PMF.pure none)) who) =
        PMF.pure none := by
      by_cases hwho : who = child
      · subst who
        simp
      · rw [Function.update_of_ne hwho, hquiet who hwho]
    simp_rw [hlaws]
    simp
  rw [quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ child (-1)
    (by intro terminal; simp [reward]), hneverLive]
  ring

/-- The child's complete deviation debt is exactly its finite-absorption
probability in the actual quiet profile. -/
theorem childDebt_eq_absorption (child : ι)
    (profile : (quittingGame (reward child)).BehaviorProfile)
    (hquiet : ∀ who, who ≠ child →
      quittingBehaviorStoppingLaw (reward child) (profile who) = PMF.pure none) :
    quittingBehaviorDeviationPayoffCap (reward child) profile child -
        quittingTerminalPayoff (reward child) profile child =
      1 - quittingLiveMassLimit (reward child) profile := by
  have hcap : quittingBehaviorDeviationPayoffCap (reward child) profile child = 0 := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply le_antisymm
    · apply quittingBestReplyValue_le
      intro deviation
      unfold quittingTerminalPayoff
      apply Finset.sum_nonpos
      intro terminal _
      simpa [reward] using quittingAbsorbedMassLimit_nonneg (reward child)
        (Function.update profile child deviation) terminal
    · have h := le_quittingBestReplyValue (reward child) profile child
        (quittingStoppingLawBehaviorStrategy (reward child) child (PMF.pure none))
      rw [childNever_payoff_eq_zero child profile hquiet] at h
      exact h
  rw [hcap, quittingTerminalPayoff_eq_constant_mul_absorption (reward child) profile child (-1)
    (by intro terminal; simp [reward])]
  ring

/-- Every outsider's complete deviation debt is exactly the actual joint-Never
probability. The cap one is attained by the legal Quit0 replacement. -/
theorem outsideDebt_eq_never (child outside : ι) (houtside : outside ≠ child)
    (profile : (quittingGame (reward child)).BehaviorProfile) :
    quittingBehaviorDeviationPayoffCap (reward child) profile outside -
        quittingTerminalPayoff (reward child) profile outside =
      quittingLiveMassLimit (reward child) profile := by
  have hcap : quittingBehaviorDeviationPayoffCap (reward child) profile outside = 1 := by
    rw [quittingBehaviorDeviationPayoffCap_eq_bestReplyValue]
    apply le_antisymm
    · apply quittingBestReplyValue_le
      intro deviation
      rw [quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ outside 1
        (by intro terminal; simp [reward, houtside])]
      have hnonneg := quittingLiveMassLimit_nonneg (reward child)
        (Function.update profile outside deviation)
      linarith
    · have h := le_quittingBestReplyValue (reward child) profile outside
        (quittingStoppingLawBehaviorStrategy (reward child) outside (PMF.pure (some 0)))
      rw [quitZero_payoff child outside houtside profile] at h
      exact h
  rw [hcap, quittingTerminalPayoff_eq_constant_mul_absorption (reward child) profile outside 1
    (by intro terminal; simp [reward, houtside])]
  ring

/-- In a quiet profile the unique child's literal Never atom is the whole
parent's joint-Never probability. -/
theorem jointNever_eq_childNever (child : ι)
    (profile : (quittingGame (reward child)).BehaviorProfile)
    (hquiet : ∀ who, who ≠ child →
      quittingBehaviorStoppingLaw (reward child) (profile who) = PMF.pure none) :
    quittingLiveMassLimit (reward child) profile =
      (quittingBehaviorStoppingLaw (reward child) (profile child) none).toReal := by
  change quittingTerminalOutcomeMass (reward child) profile none = _
  rw [quittingTerminalOutcomeMass_none_eq_prod_stoppingLaw_none,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ child)]
  have hothers : (∏ who ∈ Finset.univ.erase child,
      (quittingBehaviorStoppingLaw (reward child) (profile who) none).toReal) = 1 := by
    apply Finset.prod_eq_one
    intro who hwho
    rw [hquiet who (Finset.ne_of_mem_erase hwho)]
    simp
  rw [hothers, mul_one]

/-- The two complete debt coordinates are exactly the child's finite and
Never probabilities, with no restricted-deviation approximation. -/
theorem debts_eq_childClockMasses (child outside : ι) (houtside : outside ≠ child)
    (profile : (quittingGame (reward child)).BehaviorProfile)
    (hquiet : ∀ who, who ≠ child →
      quittingBehaviorStoppingLaw (reward child) (profile who) = PMF.pure none) :
    quittingBehaviorDeviationPayoffCap (reward child) profile child -
        quittingTerminalPayoff (reward child) profile child =
      1 - (quittingBehaviorStoppingLaw (reward child) (profile child) none).toReal ∧
    quittingBehaviorDeviationPayoffCap (reward child) profile outside -
        quittingTerminalPayoff (reward child) profile outside =
      (quittingBehaviorStoppingLaw (reward child) (profile child) none).toReal := by
  rw [childDebt_eq_absorption child profile hquiet,
    outsideDebt_eq_never child outside houtside profile,
    jointNever_eq_childNever child profile hquiet]
  exact ⟨rfl, rfl⟩

/-- The half-regret obstruction holds for every actual profile in which all
players other than the unique child have the literal Never law. -/
theorem exploitability_ge_half (child outside : ι) (houtside : outside ≠ child)
    (profile : (quittingGame (reward child)).BehaviorProfile)
    (hquiet : ∀ who, who ≠ child →
      quittingBehaviorStoppingLaw (reward child) (profile who) = PMF.pure none) :
    let : Nonempty ι := ⟨child⟩
    (1 / 2 : ℝ) ≤ quittingTerminalExploitability (reward child) profile := by
  let : Nonempty ι := ⟨child⟩
  have hchild := quittingTerminalDeviationDebt_le_exploitability (reward child) profile child
  have houtsideGain := quittingTerminalDeviationDebt_le_exploitability
    (reward child) profile outside
  change quittingBehaviorDeviationPayoffCap (reward child) profile child -
    quittingTerminalPayoff (reward child) profile child ≤ _ at hchild
  change quittingBehaviorDeviationPayoffCap (reward child) profile outside -
    quittingTerminalPayoff (reward child) profile outside ≤ _ at houtsideGain
  rw [childDebt_eq_absorption child profile hquiet] at hchild
  rw [outsideDebt_eq_never child outside houtside profile] at houtsideGain
  linarith

/-- In particular every actual deletion lift with one negative child has
half-regret, even though all original F/J certificates exist. -/
theorem quietLift_exploitability_ge_half (child outside : ι) (houtside : outside ≠ child)
    (profile : (quittingGame (quittingDeleteReward (reward child) (· ≠ child))).BehaviorProfile) :
    let : Nonempty ι := ⟨child⟩
    (1 / 2 : ℝ) ≤ quittingTerminalExploitability (reward child)
      (quittingLiftDeletedProfile (reward child) (· ≠ child) profile) := by
  let : Nonempty ι := ⟨child⟩
  apply exploitability_ge_half child outside houtside
  intro who hwho
  exact quittingBehaviorStoppingLaw_liftDeletedProfile_of_deleted
    (reward child) (· ≠ child) profile hwho

/-- A parent equilibrium in which an outsider quits at date zero and all
other players choose Never. It is deliberately not a quiet child lift. -/
def outsiderQuitProfile (child outside : ι) :
    (quittingGame (reward child)).BehaviorProfile :=
  quittingStoppingLawProfile (reward child)
    (fun who => if who = outside then PMF.pure (some 0) else PMF.pure none)

/-- The same table has an exact parent terminal equilibrium against every
behavioral replacement. The obstruction is to quiet sources, not equilibrium. -/
theorem outsiderQuitProfile_exactNash (child outside : ι) (houtside : outside ≠ child) :
    (quittingGame (reward child)).IsεAsymptoticNash (quittingTerminalPayoff (reward child))
      0 (outsiderQuitProfile child outside) := by
  have hbaseLive : quittingLiveMassLimit (reward child) (outsiderQuitProfile child outside) =
      0 := liveMass_eq_zero_of_none_zero child _ outside (by simp [outsiderQuitProfile])
  intro who deviation
  by_cases hwho : who = outside
  · subst who
    rw [quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ outside 1
        (by intro terminal; simp [reward, houtside]),
      quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ outside 1
        (by intro terminal; simp [reward, houtside]), hbaseLive]
    have hnonneg := quittingLiveMassLimit_nonneg (reward child)
      (Function.update (outsiderQuitProfile child outside) outside deviation)
    linarith
  · have hupdatedLive : quittingLiveMassLimit (reward child)
        (Function.update (outsiderQuitProfile child outside) who deviation) = 0 := by
      apply liveMass_eq_zero_of_none_zero child _ outside
      rw [Function.update_of_ne (Ne.symm hwho)]
      simp [outsiderQuitProfile]
    rw [quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ who
        (if who = child then -1 else 1) (by intro terminal; rfl),
      quittingTerminalPayoff_eq_constant_mul_absorption (reward child) _ who
        (if who = child then -1 else 1) (by intro terminal; rfl),
      hbaseLive, hupdatedLive]
    simp

/-- The literal four-player instance has one negative child and three quiet
outsiders. It is a quiet-source counterexample, not a UE counterexample. -/
theorem finFour_quietLift_exploitability_ge_half
    (profile : (quittingGame
      (quittingDeleteReward (reward (1 : Fin 4)) (· ≠ 1))).BehaviorProfile) :
    (1 / 2 : ℝ) ≤ quittingTerminalExploitability (reward (1 : Fin 4))
      (quittingLiftDeletedProfile (reward (1 : Fin 4)) (· ≠ 1) profile) :=
  quietLift_exploitability_ge_half (1 : Fin 4) 0 (by decide) profile

end GameTheory.NegativeSingletonQuietBoundary
