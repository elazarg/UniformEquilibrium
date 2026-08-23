/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterfactualAtomExternalityRegression

/-!
# Finite literal reset circulation does not by itself leave a debt fiber

This two-player quitting table realizes the matching-pennies best-response
cycle using only deterministic quitting dates zero and one.  Four literal
profiles recur exactly.  Every edge is a legal one-player self update, gives
its mover the full behavioral best-response value, kills that mover's debt,
and transfers the same positive amount to the other player.  Total terminal
semantic debt remains constant throughout the cycle.

The example is deliberately fenced from the terminal exploitability witness: no global
minimum or provenance from a terminal exploitability witness is asserted for the four
vertices.  It shows that finiteness, exact profile recurrence,
literal strategic signs, and constant-debt transport do not compile a reset
cycle to an exact Nash--Bellman cycle.  A valid closure theorem must use the
global-minimum provenance at more than the four recurrent vertices (or add a
state-matched Nash--Bellman/punishment hypothesis).
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

namespace FiniteResetCirculationRegression

abbrev Player := Bool
abbrev p : Player := false
abbrev q : Player := true

/-- Matching is worth `1` to `p` and `-1` to `q`; a singleton quitter gives
the opposite payoff.  Continuing together until date one therefore plays
the missing `(Continue, Continue)` cell of matching pennies. -/
def reward : {S : Finset Player // S.Nonempty} → Payoff Player :=
  fun terminal who =>
    if terminal.val = (Finset.univ : Finset Player) then
      if who = p then 1 else -1
    else if who = p then -1 else 1

def quitAt (who : Player) (time : ℕ) :
    (quittingGame reward).BehaviorStrategy who :=
  quittingPureTimeBehaviorStrategy reward who (some time)

/-- `(Continue, Continue)` at date zero, followed by a sure joint quit. -/
def A : (quittingGame reward).BehaviorProfile := fun who => quitAt who 1

/-- Only `q` quits at date zero. -/
def B : (quittingGame reward).BehaviorProfile :=
  Function.update A q (quitAt q 0)

/-- Both players quit at date zero. -/
def C : (quittingGame reward).BehaviorProfile :=
  Function.update B p (quitAt p 0)

/-- Only `p` quits at date zero. -/
def D : (quittingGame reward).BehaviorProfile :=
  Function.update C q (quitAt q 1)

theorem D_update_p_eq_A : Function.update D p (quitAt p 1) = A := by
  funext who
  cases who <;> simp [A, B, C, D, p, q]

theorem reward_bound (terminal : {S : Finset Player // S.Nonempty})
    (who : Player) : |reward terminal who| ≤ 1 := by
  unfold reward
  split_ifs <;> norm_num

theorem profileLiveRoot_A (time : ℕ) (who : Player) :
    quittingProfileLiveRoot reward A time who =
      if time = 1 then PMF.pure true else PMF.pure false := by
  simp [A, quitAt, quittingProfileLiveRoot, quittingPureTimeBehaviorStrategy,
    quittingPureTimeHazard]

theorem profileLiveRoot_A_zero :
    quittingProfileLiveRoot reward A 0 = fun _ => PMF.pure false := by
  funext who
  simp [profileLiveRoot_A]

theorem profileLiveRoot_A_one :
    quittingProfileLiveRoot reward A 1 = fun _ => PMF.pure true := by
  funext who
  simp [profileLiveRoot_A]

theorem profileLiveRoot_B (time : ℕ) (who : Player) :
    quittingProfileLiveRoot reward B time who =
      if who = q then
        if time = 0 then PMF.pure true else PMF.pure false
      else if time = 1 then PMF.pure true else PMF.pure false := by
  cases who <;>
    simp [B, A, quitAt, quittingProfileLiveRoot,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard, q]

theorem profileLiveRoot_C (time : ℕ) (who : Player) :
    quittingProfileLiveRoot reward C time who =
      if time = 0 then PMF.pure true else PMF.pure false := by
  cases who <;>
    simp [C, B, quitAt, quittingProfileLiveRoot,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard, p, q]

theorem profileLiveRoot_D (time : ℕ) (who : Player) :
    quittingProfileLiveRoot reward D time who =
      if who = p then
        if time = 0 then PMF.pure true else PMF.pure false
      else if time = 1 then PMF.pure true else PMF.pure false := by
  cases who <;>
    simp [D, C, B, quitAt, quittingProfileLiveRoot,
      quittingPureTimeBehaviorStrategy, quittingPureTimeHazard, p, q]

theorem payoff_A (who : Player) :
    quittingTerminalPayoff reward A who = if who = p then 1 else -1 := by
  have hself : Function.update A who (quitAt who 1) = A := by
    funext player
    by_cases hplayer : player = who
    · subst player
      simp [A]
    · simp [A, hplayer]
  rw [← hself]
  unfold quitAt
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  simp [quittingPureTimeHazard]
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  cases who <;>
    unfold quittingFixedOpponentsContinueReward
      quittingFixedOpponentsContinueMass
      quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff <;>
    simp_rw [Math.PMFProduct.expect_pmfPi_bool] <;>
    simp [profileLiveRoot_A_zero, profileLiveRoot_A_one,
      quittingPureTimeHazard, quittingStationaryContinueMass,
      quittingAllContinueAction, expect_eq_sum, reward, p,
      quittingRootPayoff, quittingQuitters,
      Finset.ext_iff]

theorem payoff_B (who : Player) :
    quittingTerminalPayoff reward B who = if who = p then -1 else 1 := by
  cases who
  · have hself : Function.update B p (quitAt p 1) = B := by
      funext player
      cases player <;> simp [B, A, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsContinueReward
      quittingFixedOpponentsContinueMass
      quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_B, quittingPureTimeHazard,
      quittingStationaryContinueMass, quittingAllContinueAction,
      expect_eq_sum, reward, p, q, quittingRootPayoff, quittingQuitters,
      Finset.ext_iff]
  · have hself : Function.update B q (quitAt q 0) = B := by
      funext player
      cases player <;> simp [B, A, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_B, quittingPureTimeHazard, expect_eq_sum,
      reward, p, q, quittingRootPayoff, quittingQuitters, Finset.ext_iff]

theorem payoff_C (who : Player) :
    quittingTerminalPayoff reward C who = if who = p then 1 else -1 := by
  cases who
  · have hself : Function.update C p (quitAt p 0) = C := by
      funext player
      cases player <;> simp [C, B, p, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_C, quittingPureTimeHazard, expect_eq_sum,
      reward, p, quittingRootPayoff, quittingQuitters, Finset.ext_iff]
  · have hself : Function.update C q (quitAt q 0) = C := by
      funext player
      cases player <;> simp [C, B, p, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_C, quittingPureTimeHazard, expect_eq_sum,
      reward, p, q, quittingRootPayoff, quittingQuitters, Finset.ext_iff]

theorem payoff_D (who : Player) :
    quittingTerminalPayoff reward D who = if who = p then -1 else 1 := by
  cases who
  · have hself : Function.update D p (quitAt p 0) = D := by
      funext player
      cases player <;> simp [D, C, B, p, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
      quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_D, quittingPureTimeHazard, expect_eq_sum,
      reward, p, quittingRootPayoff, quittingQuitters, Finset.ext_iff]
  · have hself : Function.update D q (quitAt q 1) = D := by
      funext player
      cases player <;> simp [D, C, B, p, q]
    rw [← hself]
    unfold quitAt
    rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
    unfold quittingRootSequencePureTimeTerminalValue
    rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
    unfold quittingFixedOpponentsContinueReward
      quittingFixedOpponentsContinueMass
      quittingRootAbsorbingContribution quittingRootExpectedPayoff
    rw [Math.PMFProduct.expect_pmfPi_bool]
    simp [profileLiveRoot_D, quittingPureTimeHazard,
      quittingStationaryContinueMass, quittingAllContinueAction,
      expect_eq_sum, reward, p, q, quittingRootPayoff, quittingQuitters,
      Finset.ext_iff]

theorem bestResponseValue_eq_one_of_update_payoff
    (profile : (quittingGame reward).BehaviorProfile) (who : Player)
    (target : (quittingGame reward).BehaviorStrategy who)
    (hpayoff : quittingTerminalPayoff reward
      (Function.update profile who target) who = 1) :
    quittingContinuationBestResponseValue reward profile who = 1 := by
  apply le_antisymm
  · exact le_of_abs_le (abs_quittingContinuationBestResponseValue_le
      reward profile who (M := 1) reward_bound)
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward profile who target
    rw [hpayoff] at hlower
    exact hlower

theorem bestResponseValue_A (who : Player) :
    quittingContinuationBestResponseValue reward A who = 1 := by
  cases who
  · apply bestResponseValue_eq_one_of_update_payoff A p (A p)
    rw [Function.update_eq_self, payoff_A]
    simp [p]
  · apply bestResponseValue_eq_one_of_update_payoff A q (quitAt q 0)
    change quittingTerminalPayoff reward B q = 1
    rw [payoff_B]
    simp [p, q]

theorem bestResponseValue_B (who : Player) :
    quittingContinuationBestResponseValue reward B who = 1 := by
  cases who
  · apply bestResponseValue_eq_one_of_update_payoff B p (quitAt p 0)
    change quittingTerminalPayoff reward C p = 1
    rw [payoff_C]
    simp [p]
  · apply bestResponseValue_eq_one_of_update_payoff B q (B q)
    rw [Function.update_eq_self, payoff_B]
    simp [p, q]

theorem bestResponseValue_C (who : Player) :
    quittingContinuationBestResponseValue reward C who = 1 := by
  cases who
  · apply bestResponseValue_eq_one_of_update_payoff C p (C p)
    rw [Function.update_eq_self, payoff_C]
    simp [p]
  · apply bestResponseValue_eq_one_of_update_payoff C q (quitAt q 1)
    change quittingTerminalPayoff reward D q = 1
    rw [payoff_D]
    simp [p, q]

theorem bestResponseValue_D (who : Player) :
    quittingContinuationBestResponseValue reward D who = 1 := by
  cases who
  · apply bestResponseValue_eq_one_of_update_payoff D p (quitAt p 1)
    rw [D_update_p_eq_A, payoff_A]
    simp [p]
  · apply bestResponseValue_eq_one_of_update_payoff D q (D q)
    rw [Function.update_eq_self, payoff_D]
    simp [p, q]

theorem debt_A (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward A) who =
      if who = p then 0 else 2 := by
  rw [quittingTerminalSemanticDebt]
  change quittingContinuationBestResponseValue reward A who -
    quittingTerminalPayoff reward A who = _
  rw [bestResponseValue_A, payoff_A]
  cases who <;> norm_num [p]

theorem debt_B (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward B) who =
      if who = p then 2 else 0 := by
  rw [quittingTerminalSemanticDebt]
  change quittingContinuationBestResponseValue reward B who -
    quittingTerminalPayoff reward B who = _
  rw [bestResponseValue_B, payoff_B]
  cases who <;> norm_num [p]

theorem debt_C (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward C) who =
      if who = p then 0 else 2 := by
  rw [quittingTerminalSemanticDebt]
  change quittingContinuationBestResponseValue reward C who -
    quittingTerminalPayoff reward C who = _
  rw [bestResponseValue_C, payoff_C]
  cases who <;> norm_num [p]

theorem debt_D (who : Player) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward D) who =
      if who = p then 2 else 0 := by
  rw [quittingTerminalSemanticDebt]
  change quittingContinuationBestResponseValue reward D who -
    quittingTerminalPayoff reward D who = _
  rw [bestResponseValue_D, payoff_D]
  cases who <;> norm_num [p]

theorem totalDebt_A : quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward A) = 2 := by
  simp [quittingTerminalSemanticDebtSum, debt_A, p]

theorem totalDebt_B : quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward B) = 2 := by
  simp [quittingTerminalSemanticDebtSum, debt_B, p]

theorem totalDebt_C : quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward C) = 2 := by
  simp [quittingTerminalSemanticDebtSum, debt_C, p]

theorem totalDebt_D : quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward D) = 2 := by
  simp [quittingTerminalSemanticDebtSum, debt_D, p]

/-- **Finite reset-circulation regression.**

The four profiles form an exact literal cycle.  Each edge is a legal update
by the displayed mover, earns exactly the source debt `2`, kills that debt,
and creates debt `2` on the other player.  Thus even full strategic signs and
exact profile recurrence allow `p → q → p` circulation on one constant
positive debt fiber. -/
theorem exact_literal_fullBestResponse_cycle_preserves_totalDebt :
    B = Function.update A q (quitAt q 0) ∧
    C = Function.update B p (quitAt p 0) ∧
    D = Function.update C q (quitAt q 1) ∧
    A = Function.update D p (quitAt p 1) ∧
    quittingTerminalPayoff reward B q -
        quittingTerminalPayoff reward A q = 2 ∧
    quittingTerminalPayoff reward C p -
        quittingTerminalPayoff reward B p = 2 ∧
    quittingTerminalPayoff reward D q -
        quittingTerminalPayoff reward C q = 2 ∧
    quittingTerminalPayoff reward A p -
        quittingTerminalPayoff reward D p = 2 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward A) q = 2 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward B) q = 0 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward B) p = 2 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward C) p = 0 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward C) q = 2 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward D) q = 0 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward D) p = 2 ∧
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward A) p = 0 ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward A) = 2 ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward B) = 2 ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward C) = 2 ∧
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward D) = 2 := by
  refine ⟨rfl, rfl, rfl, D_update_p_eq_A.symm, ?_⟩
  simp [payoff_A, payoff_B, payoff_C, payoff_D,
    debt_A, debt_B, debt_C, debt_D,
    totalDebt_A, totalDebt_B, totalDebt_C, totalDebt_D, p, q]
  norm_num

/-! ## Explicit fence from the positive global-minimum hypothesis -/

def never : (quittingGame reward).BehaviorProfile :=
  quittingAlwaysContinueProfile reward

theorem never_payoff (who : Player) :
    quittingTerminalPayoff reward never who = 0 := by
  exact quittingTerminalPayoff_quittingAlwaysContinue reward who

/-- If `q` never quits, every unilateral deviation by `p` has nonpositive
payoff: a finite terminal coalition can only be the losing singleton `{p}`.
-/
theorem never_p_deviation_payoff_nonpos
    (deviation : (quittingGame reward).BehaviorStrategy p) :
    quittingTerminalPayoff reward
        (Function.update never p deviation) p ≤ 0 := by
  let deviated := Function.update never p deviation
  have hq : Function.update deviated q
      (quittingPureTimeBehaviorStrategy reward q none) = deviated := by
    funext who
    cases who
    · simp [deviated, p, q]
    · apply funext
      intro time
      apply funext
      intro history
      simp [deviated, never, quittingAlwaysContinueProfile,
        StochasticGame.stationaryBehaviorProfile,
        quittingPureTimeBehaviorStrategy, quittingPureTimeHazard, p, q]
      rfl
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward deviated) p]
  unfold quittingTerminalRewardMoment
  apply Finset.sum_nonpos
  intro outcome _houtcome
  cases outcome with
  | none => simp [quittingTerminalOutcomeReward]
  | some terminal =>
      by_cases hqmem : q ∈ terminal.val
      · have hmass : quittingTerminalOutcomeMass reward deviated
            (some terminal) = 0 := by
          rw [← hq]
          exact quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
            reward deviated q terminal hqmem
        rw [hmass]
        simp
      · have hterminal : terminal.val = {p} := by
          have hpmem : p ∈ terminal.val := by
            by_contra hp
            have hempty : terminal.val = ∅ := by
              ext who
              cases who
              · constructor
                · exact fun hm => (hp hm).elim
                · intro hm
                  simp at hm
              · constructor
                · exact fun hm => (hqmem hm).elim
                · intro hm
                  simp at hm
            exact terminal.property.ne_empty hempty
          ext who
          cases who
          · constructor
            · intro _hm
              simp
            · intro _htrue
              exact hpmem
          · constructor
            · exact fun hm => (hqmem hm).elim
            · intro hfalse
              simp at hfalse
        have hreward : reward terminal p = -1 := by
          have hne : ({p} : Finset Player) ≠ Finset.univ := by decide
          have hnot : terminal.val ≠ (Finset.univ : Finset Player) := by
            rw [hterminal]
            exact hne
          unfold reward
          rw [if_neg hnot, if_pos rfl]
        rw [quittingTerminalOutcomeReward, hreward]
        exact mul_nonpos_of_nonneg_of_nonpos
          ((quittingTerminalOutcomeMass_mem_stdSimplex reward deviated).1
            (some terminal)) (by norm_num)

theorem never_bestResponseValue_p :
    quittingContinuationBestResponseValue reward never p = 0 := by
  apply le_antisymm
  · unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact Set.range_nonempty _
    · rintro value ⟨deviation, rfl⟩
      exact never_p_deviation_payoff_nonpos deviation
  · have hlower := quittingTerminalPayoff_update_le_continuationBestResponseValue
      reward never p (never p)
    rw [Function.update_eq_self, never_payoff] at hlower
    exact hlower

theorem never_q_quit_payoff :
    quittingTerminalPayoff reward
        (Function.update never q (quitAt q 0)) q = 1 := by
  unfold quitAt
  rw [quittingTerminalPayoff_update_pureTimeBehaviorStrategy]
  unfold quittingRootSequencePureTimeTerminalValue
  rw [quittingRootSequenceHazardTerminalValue_eq_hazardBellman]
  unfold quittingFixedOpponentsQuitValue quittingRootAbsorbingContribution
    quittingRootExpectedPayoff
  rw [Math.PMFProduct.expect_pmfPi_bool]
  have hroot : quittingProfileLiveRoot reward never 0 =
      fun _ => PMF.pure false := by
    funext who
    simp [never, quittingAlwaysContinueProfile, quittingProfileLiveRoot,
      StochasticGame.stationaryBehaviorProfile]
    rfl
  rw [hroot]
  simp [never,
    quittingPureTimeHazard, expect_eq_sum, reward, p, q,
    quittingRootPayoff, quittingQuitters, Finset.ext_iff]

theorem never_bestResponseValue_q :
    quittingContinuationBestResponseValue reward never q = 1 := by
  exact bestResponseValue_eq_one_of_update_payoff never q (quitAt q 0)
    never_q_quit_payoff

/-- The recurrent fiber has debt `2`, but the literal Never profile has debt
`1`.  Hence this exact circulation does not satisfy the positive-global-
minimum provenance required in the counterexample pipeline. -/
theorem never_totalDebt_eq_one :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward never) = 1 := by
  unfold quittingTerminalSemanticDebtSum
  rw [Fintype.sum_bool]
  simp only [quittingTerminalSemanticDebt]
  change (quittingContinuationBestResponseValue reward never true -
      quittingTerminalPayoff reward never true) +
    (quittingContinuationBestResponseValue reward never false -
      quittingTerminalPayoff reward never false) = 1
  rw [show true = q by rfl, show false = p by rfl,
    never_bestResponseValue_p, never_bestResponseValue_q,
    never_payoff, never_payoff]
  norm_num

end FiniteResetCirculationRegression

end GameTheory
