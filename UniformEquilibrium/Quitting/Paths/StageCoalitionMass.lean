/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment

/-! # Chronological stage-coalition masses -/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact stage atoms -/

/-- The unique Boolean action whose quitter set is the displayed terminal
coalition. -/
def quittingTerminalCoalitionAction
    (terminal : {S : Finset ι // S.Nonempty}) : ι → Bool :=
  fun who => decide (who ∈ terminal.val)

@[simp] theorem quittingQuitters_terminalCoalitionAction
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingQuitters (quittingTerminalCoalitionAction terminal) = terminal.val := by
  ext who
  simp [quittingQuitters, quittingTerminalCoalitionAction]

@[simp] theorem quittingTerminalCoalitionAction_mk_quitters
    (action : ι → Bool) (hnonempty : (quittingQuitters action).Nonempty) :
    quittingTerminalCoalitionAction
        (⟨quittingQuitters action, hnonempty⟩ :
          {S : Finset ι // S.Nonempty}) = action := by
  funext who
  cases haction : action who <;>
    simp [quittingTerminalCoalitionAction, quittingQuitters, haction]

/-- Conditional product-law mass of a coalition at the canonical live row. -/
def quittingLiveRowCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  (((quittingGame reward).stageActionDist profile
      (quittingLiveHist reward time))
    (quittingTerminalCoalitionAction terminal)).toReal

/-- Unconditional probability of reaching a live row and absorbing there at
the displayed coalition. -/
def quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  quittingLiveMass reward profile time *
    quittingLiveRowCoalitionMass reward profile time terminal

theorem quittingLiveRowCoalitionMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingLiveRowCoalitionMass reward profile time terminal :=
  ENNReal.toReal_nonneg

theorem quittingStageCoalitionMass_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    0 ≤ quittingStageCoalitionMass reward profile time terminal :=
  mul_nonneg (quittingLiveMass_nonneg reward profile time)
    (quittingLiveRowCoalitionMass_nonneg reward profile time terminal)

omit [DecidableEq ι] in
@[simp] theorem quittingAbsorbedMass_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile 0 terminal = 0 := by
  unfold quittingAbsorbedMass StochasticGame.expectedStateValue
  rw [(quittingGame reward).histDist_zero, expect_pure]
  change quittingAbsorbedIndicator reward terminal none = 0
  simp [quittingAbsorbedIndicator]

/-- Exact one-step absorption recurrence for one terminal coalition. -/
theorem quittingAbsorbedMass_succ_eq_add_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile (time + 1) terminal =
      quittingAbsorbedMass reward profile time terminal +
        quittingStageCoalitionMass reward profile time terminal := by
  classical
  letI : Finite (quittingGame reward).State :=
    inferInstanceAs (Finite (Option {S : Finset ι // S.Nonempty}))
  letI : ∀ player : ι, Finite ((quittingGame reward).Act player) :=
    fun _ => inferInstanceAs (Finite Bool)
  unfold quittingAbsorbedMass
  rw [(quittingGame reward).expectedStateValue_succ]
  calc
    expect ((quittingGame reward).histDist profile none time) (fun history =>
        expect ((quittingGame reward).stageActionDist profile history)
          (fun action => expect
            ((quittingGame reward).transition history.2 action)
              (quittingAbsorbedIndicator reward terminal))) =
      expect ((quittingGame reward).histDist profile none time) (fun history =>
        quittingAbsorbedIndicator reward terminal history.2 +
          quittingLiveRowCoalitionMass reward profile time terminal *
            quittingLiveIndicator reward history.2) := by
        apply Math.ProbabilityMassFunction.expect_congr_on_support
        intro history hsupported
        cases hstate : history.2 with
        | none =>
            have heq :=
              eq_quittingLiveHist_of_mem_support_histDist_of_snd_eq_none
                reward profile history hsupported hstate
            subst history
            rw [show quittingAbsorbedIndicator reward terminal none = 0 by
              simp [quittingAbsorbedIndicator]]
            simp only [zero_add, quittingLiveIndicator_none, mul_one]
            unfold quittingLiveRowCoalitionMass
            rw [Math.Probability.apply_toReal_eq_expect_indicator]
            apply congrArg
              (expect ((quittingGame reward).stageActionDist profile
                (quittingLiveHist reward time)))
            funext action
            by_cases haction :
                action = quittingTerminalCoalitionAction terminal
            · subst action
              rw [if_pos rfl]
              have hnonempty :
                  (quittingQuitters
                    (quittingTerminalCoalitionAction terminal)).Nonempty := by
                rw [quittingQuitters_terminalCoalitionAction]
                exact terminal.property
              rw [quittingGame_transition_none, dif_pos (by
                simpa [quittingQuitters] using hnonempty)]
              change expect (PMF.pure (some
                (⟨quittingQuitters
                    (quittingTerminalCoalitionAction terminal), hnonempty⟩ :
                  {S : Finset ι // S.Nonempty})))
                    (quittingAbsorbedIndicator reward terminal) = 1
              simp [quittingAbsorbedIndicator]
            · rw [if_neg haction]
              by_cases hnonempty : (quittingQuitters action).Nonempty
              · rw [quittingGame_transition_none, dif_pos (by
                  simpa [quittingQuitters] using hnonempty)]
                have hterminal :
                    (⟨quittingQuitters action, hnonempty⟩ :
                        {S : Finset ι // S.Nonempty}) ≠ terminal := by
                  intro heq
                  apply haction
                  calc
                    action = quittingTerminalCoalitionAction
                        (⟨quittingQuitters action, hnonempty⟩ :
                          {S : Finset ι // S.Nonempty}) :=
                      (quittingTerminalCoalitionAction_mk_quitters
                        action hnonempty).symm
                    _ = quittingTerminalCoalitionAction terminal := by
                      rw [heq]
                change expect (PMF.pure (some
                  (⟨quittingQuitters action, hnonempty⟩ :
                    {S : Finset ι // S.Nonempty})))
                      (quittingAbsorbedIndicator reward terminal) = 0
                rw [expect_pure]
                unfold quittingAbsorbedIndicator
                rw [if_neg]
                intro heq
                exact hterminal (Option.some.inj heq)
              · rw [quittingGame_transition_none, dif_neg (by
                  simpa [quittingQuitters] using hnonempty)]
                simp [quittingAbsorbedIndicator]
        | some absorbed =>
            by_cases heq : absorbed = terminal
            · subst absorbed
              simp [quittingGame, quittingAbsorbedIndicator,
                quittingLiveIndicator]
            · simp [quittingGame, quittingAbsorbedIndicator,
                quittingLiveIndicator, heq]
    _ = quittingAbsorbedMass reward profile time terminal +
        quittingLiveRowCoalitionMass reward profile time terminal *
          quittingLiveMass reward profile time := by
      rw [expect_add, expect_const_mul,
        quittingLiveMass_eq_expectedStateValue]
      rfl
    _ = quittingAbsorbedMass reward profile time terminal +
        quittingStageCoalitionMass reward profile time terminal := by
      rw [quittingStageCoalitionMass]
      ring

/-- Finite time disintegration into chronological stage atoms. -/
theorem quittingAbsorbedMass_eq_sum_stageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) : ∀ cutoff : ℕ,
    quittingAbsorbedMass reward profile cutoff terminal =
      ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal := by
  intro cutoff
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [quittingAbsorbedMass_succ_eq_add_stageCoalitionMass,
        Finset.sum_range_succ, ih]

/-- Infinite disintegration of one terminal-coalition mass. -/
theorem hasSum_quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    HasSum (fun time => quittingStageCoalitionMass reward profile time terminal)
      (quittingAbsorbedMassLimit reward profile terminal) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun time => quittingStageCoalitionMass_nonneg reward profile time terminal)]
  simpa only [← quittingAbsorbedMass_eq_sum_stageCoalitionMass] using
    tendsto_quittingAbsorbedMass reward profile terminal

theorem tsum_quittingStageCoalitionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset ι // S.Nonempty}) :
    ∑' time, quittingStageCoalitionMass reward profile time terminal =
      quittingAbsorbedMassLimit reward profile terminal :=
  (hasSum_quittingStageCoalitionMass reward profile terminal).tsum_eq

/-- Complete terminal-law disintegration: Never is the live boundary and a
finite coalition is the sum of its chronological stage atoms. -/
theorem quittingTerminalOutcomeMass_eq_timeDisintegration
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalOutcomeMass reward profile outcome =
      match outcome with
      | none => quittingLiveMassLimit reward profile
      | some terminal =>
          ∑' time, quittingStageCoalitionMass reward profile time terminal := by
  cases outcome with
  | none => rfl
  | some terminal =>
      simpa [quittingTerminalOutcomeMass] using
        (tsum_quittingStageCoalitionMass reward profile terminal).symm

/-- Every chronological coalition atom is dominated by the matching actual
terminal-law atom of the same profile. -/
theorem quittingStageCoalitionMass_le_terminalOutcomeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal ≤
      quittingTerminalOutcomeMass reward profile (some terminal) := by
  change quittingStageCoalitionMass reward profile time terminal ≤
    quittingAbsorbedMassLimit reward profile terminal
  rw [← tsum_quittingStageCoalitionMass reward profile terminal]
  exact (hasSum_quittingStageCoalitionMass reward profile terminal).summable.le_tsum
    time (fun other _hne =>
      quittingStageCoalitionMass_nonneg reward profile other terminal)

end GameTheory
