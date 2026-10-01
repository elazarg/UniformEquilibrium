import MathUE.ProbabilityMassFunction.StoppingLawLateIndicators
import UniformEquilibrium.Quitting.Paths.StoppingLawOperationalDistance
import UniformEquilibrium.Quitting.Paths.FirstStoppingOutcomeCoalition
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Stationary.BestResponse

/-! # A signed two-player family without exact terminal Nash

Every behavioral strategy, including Never and all history-dependent deviations,
is retained. The family has a strict singleton deficit but a negative singleton.
No failure of approximate terminal or uniform equilibrium existence is asserted.
-/

noncomputable section

namespace GameTheory.SignedTwoPlayerExactNashNonattainment

open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard
open _root_.Math.ProbabilityMassFunction

def reward (delta : ℝ) : {S : Finset (Fin 2) // S.Nonempty} → Payoff (Fin 2) :=
  fun terminal =>
    if terminal.1 = {0} then ![1, -1]
    else if terminal.1 = {1} then ![1 - delta, delta - 1]
    else ![-1, 1]

theorem singleton_zero (delta : ℝ) :
    reward delta (quittingSingletonTerminal 0) 0 = 1 := by
  norm_num [reward, quittingSingletonTerminal]

theorem singleton_one (delta : ℝ) :
    reward delta (quittingSingletonTerminal 1) 1 = delta - 1 := by
  norm_num [reward, quittingSingletonTerminal]

private theorem reward_neg (delta : ℝ)
    (terminal : {S : Finset (Fin 2) // S.Nonempty}) :
    reward delta terminal 1 = -reward delta terminal 0 := by
  unfold reward
  split_ifs <;> simp [neg_sub]

theorem terminal_payoff_neg (delta : ℝ)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    quittingTerminalPayoff (reward delta) profile 1 =
      -quittingTerminalPayoff (reward delta) profile 0 := by
  unfold quittingTerminalPayoff
  simp_rw [reward_neg, mul_neg]
  exact Finset.sum_neg_distrib (s := Finset.univ)
    (fun terminal : {S : Finset (Fin 2) // S.Nonempty} =>
      quittingAbsorbedMassLimit (reward delta) profile terminal * reward delta terminal 0)

/-- The deficit holds for all actual profiles, not only stationary or finite words. -/
theorem strict_singleton_deficit (delta : ℝ)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    ∃ who, quittingTerminalPayoff (reward delta) profile who ≤
      reward delta (quittingSingletonTerminal who) who - delta / 2 := by
  have hzero := terminal_payoff_neg delta profile
  by_cases hle : quittingTerminalPayoff (reward delta) profile 0 ≤ 1 - delta / 2
  · exact ⟨0, by simpa only [singleton_zero] using hle⟩
  · refine ⟨1, ?_⟩
    rw [singleton_one]
    linarith

theorem strict_singleton_deficit_positive (delta : ℝ) (hdelta : 0 < delta) :
    0 < delta / 2 ∧
      ∀ profile : (quittingGame (reward delta)).BehaviorProfile, ∃ who,
        quittingTerminalPayoff (reward delta) profile who ≤
          reward delta (quittingSingletonTerminal who) who - delta / 2 := by
  exact ⟨by positivity, strict_singleton_deficit delta⟩

private theorem pure_date_value (delta : ℝ) (choice : Option ℕ) (time : ℕ) :
    quittingTerminalPayoff (reward delta)
      (quittingPureTimeProfileBehavior (reward delta) ![choice, some time]) 1 =
      -1 + delta * stoppingLawTailIndicator time choice +
        (2 - delta) * (if choice = some time then 1 else 0) := by
  rw [quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome]
  cases choice with
  | none =>
      have hout : quittingFirstStoppingOutcome (![none, some time] : Fin 2 → Option ℕ) =
          some ⟨{1}, by simp⟩ := by
        apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
          _ {1} (by simp) time
        · intro player hplayer
          have heq : player = 1 := Finset.mem_singleton.mp hplayer
          subst player
          rfl
        · intro player hplayer
          fin_cases player
          · change (time : WithTop ℕ) < ⊤
            simp
          · simp at hplayer
      rw [hout]
      norm_num [quittingTerminalOutcomeReward, reward, stoppingLawTailIndicator]
      ring
  | some date =>
      rcases lt_trichotomy date time with hbefore | rfl | hafter
      · have hout : quittingFirstStoppingOutcome
            (![some date, some time] : Fin 2 → Option ℕ) = some ⟨{0}, by simp⟩ := by
          apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
            _ {0} (by simp) date
          · intro player hplayer
            have heq : player = 0 := Finset.mem_singleton.mp hplayer
            subst player
            rfl
          · intro player hplayer
            fin_cases player
            · simp at hplayer
            · change (date : WithTop ℕ) < time
              exact_mod_cast hbefore
        rw [hout]
        norm_num [quittingTerminalOutcomeReward, reward, stoppingLawTailIndicator,
          hbefore, hbefore.ne]
      · have hout : quittingFirstStoppingOutcome
            (![some date, some date] : Fin 2 → Option ℕ) =
            some ⟨{0, 1}, by simp⟩ := by
          apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
            _ {0, 1} (by simp) date
          · intro player _
            fin_cases player <;> rfl
          · intro player hplayer
            fin_cases player <;> simp at hplayer
        have hnotZero : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
        have hnotOne : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
        rw [hout]
        norm_num [quittingTerminalOutcomeReward, reward, stoppingLawTailIndicator,
          hnotZero, hnotOne]
      · have hout : quittingFirstStoppingOutcome
            (![some date, some time] : Fin 2 → Option ℕ) = some ⟨{1}, by simp⟩ := by
          apply quittingFirstStoppingOutcome_eq_coalition_of_strictly_later
            _ {1} (by simp) time
          · intro player hplayer
            have heq : player = 1 := Finset.mem_singleton.mp hplayer
            subst player
            rfl
          · intro player hplayer
            fin_cases player
            · change (time : WithTop ℕ) < date
              exact_mod_cast hafter
            · simp at hplayer
        rw [hout]
        norm_num [quittingTerminalOutcomeReward, reward, stoppingLawTailIndicator,
          not_lt_of_ge hafter.le, hafter.ne']
        ring

private theorem pure_profile_update (delta : ℝ)
    (profile : (quittingGame (reward delta)).BehaviorProfile)
    (choice : Option ℕ) (time : ℕ) :
    Function.update
      (Function.update profile 1
        (quittingPureTimeBehaviorStrategy (reward delta) 1 (some time))) 0
      (quittingPureTimeBehaviorStrategy (reward delta) 0 choice) =
      quittingPureTimeProfileBehavior (reward delta) ![choice, some time] := by
  funext who
  fin_cases who <;> simp [quittingPureTimeProfileBehavior]

/-- The literal Quit-at-time identity for an arbitrary original opponent clock. -/
theorem quit_at_time_payoff (delta : ℝ)
    (profile : (quittingGame (reward delta)).BehaviorProfile) (time : ℕ) :
    quittingTerminalPayoff (reward delta)
      (Function.update profile 1
        (quittingPureTimeBehaviorStrategy (reward delta) 1 (some time))) 1 =
      -1 + delta * StoppingLaw.survival
        (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time +
        (2 - delta) * StoppingLaw.finiteMass
          (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time := by
  rw [quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
    (reward delta) _ 0 1]
  simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp_rw [pure_profile_update, pure_date_value]
  have h := expect_stoppingLaw_late_affine
    (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time time
    (fun _ => (-1 : ℝ)) (earlyBound := 1) (by intro choice; norm_num) 1 delta 2 delta
  simpa [StoppingLaw.finiteMass, add_assoc] using h

/-- The stationary security strategies use actual independent Boolean roots. -/
def securityRoot (owner : Fin 2) (probability : ℝ)
    (hnonneg : 0 ≤ probability) (hunit : probability ≤ 1) : Fin 2 → PMF Bool :=
  quittingSoloStationaryRoot owner (bernoulliBool probability hnonneg hunit)

def securityStrategy (delta : ℝ) (owner : Fin 2) (probability : ℝ)
    (hnonneg : 0 ≤ probability) (hunit : probability ≤ 1) :
    (quittingGame (reward delta)).BehaviorStrategy owner :=
  quittingStationaryProfile (reward delta)
    (securityRoot owner probability hnonneg hunit) owner

private theorem security_update_zero (delta probability : ℝ)
    (hnonneg : 0 ≤ probability) (hunit : probability ≤ 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    Function.update profile 1 (securityStrategy delta 1 probability hnonneg hunit) =
      Function.update
        (quittingStationaryProfile (reward delta)
          (securityRoot 1 probability hnonneg hunit)) 0 (profile 0) := by
  funext who
  fin_cases who <;> simp [securityStrategy]

private theorem security_update_one (delta probability : ℝ)
    (hnonneg : 0 ≤ probability) (hunit : probability ≤ 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    Function.update profile 0 (securityStrategy delta 0 probability hnonneg hunit) =
      Function.update
        (quittingStationaryProfile (reward delta)
          (securityRoot 0 probability hnonneg hunit)) 1 (profile 1) := by
  funext who
  fin_cases who <;> simp [securityStrategy]

private theorem security_cap_zero (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < 1) :
    quittingStationaryUnilateralCap (reward delta)
      (securityRoot 1 (delta / 2) (by positivity) (by linarith)) 0 = 1 - delta := by
  have hquit : quittingStationaryFixedOpponentsQuitValue (reward delta)
      (securityRoot 1 (delta / 2) (by positivity) (by linarith)) 0 = 1 - delta := by
    unfold securityRoot
    rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
      (reward delta) (by decide)]
    have hnotZero : ({1, 0} : Finset (Fin 2)) ≠ {0} := by decide
    have hnotOne : ({1, 0} : Finset (Fin 2)) ≠ {1} := by decide
    norm_num [quittingSoloReward, quittingSingletonCollisionReward,
      quittingSingletonTerminal, reward, hnotZero, hnotOne]
    ring
  unfold securityRoot
  rw [quittingStationaryUnilateralCap_solo_other (reward delta) (by decide)
      (bernoulliBool (delta / 2) (by positivity) (by linarith))
      (by simpa using (show 0 < delta / 2 by positivity))]
  change max
    (quittingStationaryFixedOpponentsQuitValue (reward delta)
      (securityRoot 1 (delta / 2) (by positivity) (by linarith)) 0)
    (quittingSoloReward (reward delta) 1 0) = _
  rw [hquit]
  norm_num [quittingSoloReward, quittingSingletonTerminal, reward]

private theorem security_cap_one (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < 1) (probability : ℝ)
    (hpositive : 0 < probability) (hunit : probability ≤ 1) :
    quittingStationaryUnilateralCap (reward delta)
      (securityRoot 0 probability hpositive.le hunit) 1 =
      delta - 1 + (2 - delta) * probability := by
  unfold securityRoot
  rw [quittingStationaryUnilateralCap_solo_other (reward delta) (by decide)
      (bernoulliBool probability hpositive.le hunit) (by simpa using hpositive),
    quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
      (reward delta) (by decide)]
  have hnotZero : ({0, 1} : Finset (Fin 2)) ≠ {0} := by decide
  have hnotOne : ({0, 1} : Finset (Fin 2)) ≠ {1} := by decide
  norm_num [quittingSoloReward, quittingSingletonCollisionReward,
    quittingSingletonTerminal, reward, hnotZero, hnotOne]
  have horder : -1 ≤ (1 - probability) * (delta - 1) + probability := by
    have hp : 0 ≤ (2 - delta) * probability := mul_nonneg (by linarith) hpositive.le
    nlinarith
  rw [max_eq_left horder]
  ring

/-- Player 1's fixed hazard delta/2 caps every player-0 response, including Never. -/
theorem stationary_one_security (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    quittingTerminalPayoff (reward delta)
      (Function.update profile 1
        (securityStrategy delta 1 (delta / 2) (by positivity) (by linarith))) 0 ≤
      1 - delta := by
  rw [security_update_zero]
  have h := quittingTerminalPayoff_update_stationary_le_unilateralCap (reward delta)
    (securityRoot 1 (delta / 2) (by positivity) (by linarith)) 0 (profile 0)
    (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
      (by decide) _ (by simp; positivity))
  rwa [security_cap_zero delta hdelta hsmall] at h

/-- Player 0's positive stationary hazard gives the near-value security bound. -/
theorem stationary_zero_security (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < 1) (probability : ℝ)
    (hpositive : 0 < probability) (hunit : probability ≤ 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    1 - delta - (2 - delta) * probability ≤
      quittingTerminalPayoff (reward delta)
        (Function.update profile 0
          (securityStrategy delta 0 probability hpositive.le hunit)) 0 := by
  have h := quittingTerminalPayoff_update_stationary_le_unilateralCap (reward delta)
    (securityRoot 0 probability hpositive.le hunit) 1 (profile 1)
    (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
      (by decide) _ (by simpa using hpositive))
  rw [security_cap_one delta hdelta hsmall probability hpositive hunit] at h
  rw [← security_update_one delta probability hpositive.le hunit profile,
    terminal_payoff_neg] at h
  linarith

theorem exact_nash_payoff (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta < 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile)
    (hnash : (quittingGame (reward delta)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward delta)) 0 profile) :
    quittingTerminalPayoff (reward delta) profile 0 = 1 - delta ∧
      quittingTerminalPayoff (reward delta) profile 1 = delta - 1 := by
  have hone := stationary_one_security delta hdelta hsmall profile
  have hnashOne := hnash 1
    (securityStrategy delta 1 (delta / 2) (by positivity) (by linarith))
  rw [terminal_payoff_neg delta profile] at hnashOne
  have hnegative := terminal_payoff_neg delta
    (Function.update profile 1
      (securityStrategy delta 1 (delta / 2) (by positivity) (by linarith)))
  have hupper : quittingTerminalPayoff (reward delta) profile 0 ≤ 1 - delta := by
    linarith
  have hlower : 1 - delta ≤ quittingTerminalPayoff (reward delta) profile 0 := by
    apply le_of_forall_pos_le_add
    intro error herror
    let probability := min 1 (error / (2 - delta))
    have hden : 0 < 2 - delta := by linarith
    have hpositive : 0 < probability := lt_min (by norm_num) (div_pos herror hden)
    have hunit : probability ≤ 1 := min_le_left _ _
    have hcharge : (2 - delta) * probability ≤ error := by
      have h := min_le_right (1 : ℝ) (error / (2 - delta))
      dsimp only [probability]
      exact (mul_le_mul_of_nonneg_left h hden.le).trans_eq
        (mul_div_cancel₀ error hden.ne')
    have hsecurity := stationary_zero_security delta hdelta hsmall
      probability hpositive hunit profile
    have hdeviation := hnash 0
      (securityStrategy delta 0 probability hpositive.le hunit)
    linarith
  have hvalue := le_antisymm hupper hlower
  exact ⟨hvalue, by rw [terminal_payoff_neg, hvalue]; ring⟩

/-- Exact Nash would force every finite atom of the original player-0 clock to vanish. -/
theorem finite_atoms_zero_of_exact_nash (delta : ℝ)
    (hdelta : 0 < delta) (hsmall : delta < 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile)
    (hnash : (quittingGame (reward delta)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward delta)) 0 profile) :
    ∀ time, StoppingLaw.finiteMass
      (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time = 0 := by
  have hvalue := (exact_nash_payoff delta hdelta hsmall profile hnash).2
  intro time
  induction time using Nat.strong_induction_on with
  | h time ih =>
      have hsurvival : StoppingLaw.survival
          (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time = 1 := by
        unfold StoppingLaw.survival
        have hsum : (∑ date ∈ Finset.range time,
            StoppingLaw.finiteMass
              (quittingBehaviorStoppingLaw (reward delta) (profile 0)) date) = 0 := by
          apply Finset.sum_eq_zero
          intro date hdate
          exact ih date (Finset.mem_range.mp hdate)
        rw [hsum]
        ring
      have hdate := hnash 1
        (quittingPureTimeBehaviorStrategy (reward delta) 1 (some time))
      rw [quit_at_time_payoff, hsurvival, hvalue] at hdate
      have hmass := StoppingLaw.finiteMass_nonneg
        (quittingBehaviorStoppingLaw (reward delta) (profile 0)) time
      have hcoefficient : 0 < 2 - delta := by linarith
      nlinarith

theorem clock_pure_never_of_exact_nash (delta : ℝ)
    (hdelta : 0 < delta) (hsmall : delta < 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile)
    (hnash : (quittingGame (reward delta)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward delta)) 0 profile) :
    quittingBehaviorStoppingLaw (reward delta) (profile 0) = PMF.pure none := by
  have hatoms := finite_atoms_zero_of_exact_nash delta hdelta hsmall profile hnash
  have htotal := StoppingLaw.none_add_tsum_finiteMass
    (quittingBehaviorStoppingLaw (reward delta) (profile 0))
  simp_rw [hatoms] at htotal
  simp only [tsum_zero, add_zero] at htotal
  apply _root_.Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro choice
  cases choice with
  | none => simpa using htotal
  | some time => simpa [StoppingLaw.finiteMass] using hatoms time

/-- No exact terminal Nash exists even in the complete behavioral strategy class. -/
theorem not_exact_terminal_nash (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta < 1)
    (profile : (quittingGame (reward delta)).BehaviorProfile) :
    ¬(quittingGame (reward delta)).IsεAsymptoticNash
      (quittingTerminalPayoff (reward delta)) 0 profile := by
  intro hnash
  have hvalue := (exact_nash_payoff delta hdelta hsmall profile hnash).2
  have hclock := clock_pure_never_of_exact_nash delta hdelta hsmall profile hnash
  have hdeviation := hnash 1
    (quittingPureTimeBehaviorStrategy (reward delta) 1 none)
  have hzero : quittingTerminalPayoff (reward delta)
      (Function.update profile 1
        (quittingPureTimeBehaviorStrategy (reward delta) 1 none)) 1 = 0 := by
    rw [quittingTerminalPayoff_eq_expect_behaviorStoppingLaw_pureTime
      (reward delta) _ 0 1]
    simp only [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), hclock, expect_pure]
    have hprofile :
        Function.update
          (Function.update profile 1 (quittingPureTimeBehaviorStrategy (reward delta) 1 none))
          0 (quittingPureTimeBehaviorStrategy (reward delta) 0 none) =
          quittingPureTimeProfileBehavior (reward delta) (fun _ => none) := by
      funext who
      fin_cases who <;> simp [quittingPureTimeProfileBehavior]
    rw [hprofile, quittingTerminalPayoff_pureTimeProfileBehavior_eq_firstStoppingOutcome,
      quittingFirstStoppingOutcome_all_never]
    rfl
  rw [hzero, hvalue] at hdeviation
  linarith

end GameTheory.SignedTwoPlayerExactNashNonattainment
