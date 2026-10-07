import UniformEquilibrium.Quitting.Cycles.PairedCycleEquilibrium

/-! # Exact two-pair cycles from passive endpoint tests

The schedule labels all four players, and every hazard is proper. Own-phase
values and their post-phase continuations are computed from the actual reward
table using the canonical paired affine formulas. Active indifference,
prescribed policy, root Nash and deleted-opponent contraction are derived.
Only passive Continue identities and passive Quit upper bounds remain inputs.
There are no phase-floor, reward-sign or raw-region hypotheses.
-/

noncomputable section

namespace GameTheory.PairedCycle

open Math.PairedAffine

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def twoPairActiveValue (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ) : Payoff ι :=
  fun player => activeValue (singleton reward player) (jointReward reward schedule player)
    (q (schedule.partner player))

def twoPairPostValue (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ) : Payoff ι :=
  fun player => postValue (singleton reward player) (partnerReward reward schedule player)
    (jointReward reward schedule player) (q (schedule.partner player))

def twoPairPhaseValue (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ) (phase : Fin 2) : Payoff ι :=
  fun player => if phase = schedule.phase player then twoPairActiveValue reward schedule q player
    else twoPairPostValue reward schedule q player

omit [Fintype ι] [DecidableEq ι] in
theorem properUnitBounds (q : ι → ℝ) (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ player, q player ∈ Set.Icc (0 : ℝ) 1 :=
  fun player => ⟨(hproper player).1.le, (hproper player).2.le⟩

private theorem rotate_two_ne (phase : Fin 2) : finRotate 2 phase ≠ phase := by
  fin_cases phase <;> decide

private theorem rotate_two_eq_of_ne {phase active : Fin 2} (hne : phase ≠ active) :
    finRotate 2 phase = active := by
  fin_cases phase <;> fin_cases active <;> first | rfl | exact (hne rfl).elim

omit [Fintype ι] in
@[simp] theorem twoPairPhaseValue_active
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ) (player : ι) :
    twoPairPhaseValue reward schedule q (schedule.phase player) player =
      twoPairActiveValue reward schedule q player := by
  simp only [twoPairPhaseValue, ite_true]

omit [Fintype ι] in
@[simp] theorem twoPairPhaseValue_post
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ) (player : ι) :
    twoPairPhaseValue reward schedule q (finRotate 2 (schedule.phase player)) player =
      twoPairPostValue reward schedule q player := by
  simp only [twoPairPhaseValue, rotate_two_ne, ite_false]

theorem twoPair_active_endpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1) (player : ι) :
    quittingRootQuitPayoff reward
        (twoPairPhaseValue reward schedule q (finRotate 2 (schedule.phase player)))
        (cycle schedule q (properUnitBounds q hproper) (schedule.phase player)) player =
      twoPairActiveValue reward schedule q player ∧
    quittingRootContinuePayoff reward
        (twoPairPhaseValue reward schedule q (finRotate 2 (schedule.phase player)))
        (cycle schedule q (properUnitBounds q hproper) (schedule.phase player)) player =
      twoPairActiveValue reward schedule q player := by
  constructor
  · exact cycle_quit_active reward schedule q (properUnitBounds q hproper) _ player
  · rw [cycle_continue_active, twoPairPhaseValue_post]
    exact continue_eq_active _ _ _ _ (ne_of_lt (hproper (schedule.partner player)).2)

/-- Passive tests supply the exact policy and Nash points at both phases.
No root Nash or policy-evaluation certificate is an input. -/
theorem twoPair_policy_and_nash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1)
    (hcontinue : ∀ player,
      quittingRootContinuePayoff reward
        (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player = twoPairPostValue reward schedule q player)
    (hquit : ∀ player,
      quittingRootQuitPayoff reward (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player ≤
        twoPairPostValue reward schedule q player) :
    (∀ phase, twoPairPhaseValue reward schedule q phase =
      quittingRootSuccessorPayoff reward (twoPairPhaseValue reward schedule q (finRotate 2 phase))
        (cycle schedule q (properUnitBounds q hproper) phase)) ∧
    (∀ phase, IsεQuittingRootNash reward (twoPairPhaseValue reward schedule q (finRotate 2 phase))
      0 (cycle schedule q (properUnitBounds q hproper) phase)) := by
  have hendpoints (phase : Fin 2) (player : ι) :
      quittingRootQuitPayoff reward (twoPairPhaseValue reward schedule q (finRotate 2 phase))
          (cycle schedule q (properUnitBounds q hproper) phase) player ≤
        twoPairPhaseValue reward schedule q phase player ∧
      quittingRootContinuePayoff reward (twoPairPhaseValue reward schedule q (finRotate 2 phase))
          (cycle schedule q (properUnitBounds q hproper) phase) player =
        twoPairPhaseValue reward schedule q phase player := by
    by_cases hphase : phase = schedule.phase player
    · subst phase
      simpa only [twoPairPhaseValue_active] using
        ⟨(twoPair_active_endpoints reward schedule q hproper player).1.le,
          (twoPair_active_endpoints reward schedule q hproper player).2⟩
    · have hpassive : phase = finRotate 2 (schedule.phase player) :=
        (rotate_two_eq_of_ne (Ne.symm hphase)).symm
      have hnext := rotate_two_eq_of_ne hphase
      rw [hnext, hpassive, twoPairPhaseValue_post]
      exact ⟨hquit player, hcontinue player⟩
  have hpolicy (phase : Fin 2) : twoPairPhaseValue reward schedule q phase =
      quittingRootSuccessorPayoff reward (twoPairPhaseValue reward schedule q (finRotate 2 phase))
        (cycle schedule q (properUnitBounds q hproper) phase) := by
    funext player
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    by_cases hphase : phase = schedule.phase player
    · subst phase
      obtain ⟨hactiveQuit, hactiveContinue⟩ :=
        twoPair_active_endpoints reward schedule q hproper player
      rw [hactiveQuit, hactiveContinue, twoPairPhaseValue_active]
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (cycle schedule q (properUnitBounds q hproper) (schedule.phase player)) player
      calc
        twoPairActiveValue reward schedule q player =
            ((cycle schedule q (properUnitBounds q hproper) (schedule.phase player) player
              false).toReal +
            (cycle schedule q (properUnitBounds q hproper) (schedule.phase player) player
              true).toReal) * twoPairActiveValue reward schedule q player := by rw [hsum, one_mul]
        _ = _ := by ring
    · rw [cycle_outside schedule q (properUnitBounds q hproper) hphase]
      simp only [PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, ENNReal.toReal_zero,
        zero_mul, ENNReal.toReal_one, one_mul, zero_add]
      exact (hendpoints phase player).2.symm
  refine ⟨hpolicy, ?_⟩
  intro phase
  rw [← isεQuittingRootEndpointNash_iff_isεQuittingRootNash,
    isεQuittingRootEndpointNash_iff_purePayoff_le]
  intro player
  rw [← congrFun (hpolicy phase) player, add_zero]
  exact ⟨(hendpoints phase player).1, (hendpoints phase player).2.le⟩

theorem twoPair_isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1)
    (hcontinue : ∀ player,
      quittingRootContinuePayoff reward
        (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player = twoPairPostValue reward schedule q player)
    (hquit : ∀ player,
      quittingRootQuitPayoff reward (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player ≤ twoPairPostValue reward schedule q player)
    (initial : Fin 2) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (twoPairPhaseValue reward schedule q initial) := by
  obtain ⟨hpolicy, hnash⟩ := twoPair_policy_and_nash reward schedule q hproper hcontinue hquit
  have hcontracts := cycle_opponents_contract schedule q (properUnitBounds q hproper)
    (fun player => (hproper player).1)
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff reward
    (cycle schedule q (properUnitBounds q hproper)) (twoPairPhaseValue reward schedule q)
    hpolicy hcontracts
  rw [congrFun hvalue initial]
  exact isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate reward
    (cycle schedule q (properUnitBounds q hproper)) (twoPairPhaseValue reward schedule q)
    initial hpolicy hnash hcontracts

theorem twoPair_exact_terminal_and_fixedProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (schedule : Schedule ι 2) (q : ι → ℝ)
    (hproper : ∀ player, q player ∈ Set.Ioo (0 : ℝ) 1)
    (hcontinue : ∀ player,
      quittingRootContinuePayoff reward
        (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player = twoPairPostValue reward schedule q player)
    (hquit : ∀ player,
      quittingRootQuitPayoff reward (twoPairPhaseValue reward schedule q (schedule.phase player))
        (cycle schedule q (properUnitBounds q hproper)
          (finRotate 2 (schedule.phase player))) player ≤ twoPairPostValue reward schedule q player)
    (initial : Fin 2) :
    quittingTerminalPayoff reward
        (quittingCyclicBehaviorProfile reward
          (cycle schedule q (properUnitBounds q hproper)) initial) =
      twoPairPhaseValue reward schedule q initial ∧
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingCyclicBehaviorProfile reward
        (cycle schedule q (properUnitBounds q hproper)) initial) ∧
    (∀ ε : ℝ, 0 < ε → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon ε
            (quittingCyclicBehaviorProfile reward
              (cycle schedule q (properUnitBounds q hproper)) initial) ∧
          ∀ player, |(quittingGame reward).finiteAveragePayoff none horizon
              (quittingCyclicBehaviorProfile reward
                (cycle schedule q (properUnitBounds q hproper)) initial) player -
            twoPairPhaseValue reward schedule q initial player| ≤ ε) ∧
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (twoPairPhaseValue reward schedule q initial) := by
  obtain ⟨hpolicy, hnash⟩ :=
    twoPair_policy_and_nash reward schedule q hproper hcontinue hquit
  have hcontracts := cycle_opponents_contract schedule q (properUnitBounds q hproper)
    (fun player => (hproper player).1)
  have hvalue := eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff reward
    (cycle schedule q (properUnitBounds q hproper)) (twoPairPhaseValue reward schedule q)
    hpolicy hcontracts
  have hterminal :
      quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward
            (cycle schedule q (properUnitBounds q hproper)) initial) =
        twoPairPhaseValue reward schedule q initial :=
    (quittingTerminalPayoff_cyclicBehaviorProfile reward _ initial).trans
      (congrFun hvalue initial).symm
  have hexact := isZeroAsymptoticNash_quittingCyclicBehaviorProfile_of_certificate
    reward (cycle schedule q (properUnitBounds q hproper))
    (twoPairPhaseValue reward schedule q) initial hpolicy hnash hcontracts
  refine ⟨hterminal, hexact, ?_,
    twoPair_isUniformEquilibriumPayoff reward schedule q hproper hcontinue hquit initial⟩
  simpa only [hterminal] using
    quittingGame_fixedProfile_uniformPayoffWitnesses_of_terminalNash_exact
      reward _ hexact

end GameTheory.PairedCycle
