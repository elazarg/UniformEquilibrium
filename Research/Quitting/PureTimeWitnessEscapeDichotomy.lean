/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.General.PureTimeWitnessNormalForm
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing

/-!
# Escaping pure-time witnesses are Never-funded or locally profitable

For a moving sequence of opponent plans, normalize one selected pure-time
witness.  It is fixed finite, literal Never, or its finite quit time tends to
infinity.  The third mode is not a genuinely new payoff obstruction.

The exact pure-time transport identity writes its gain over a prescribed
value as

```text
(Never payoff - prescribed value)
  + opponent survival to the selected date * local Quit-minus-Continue gap.
```

If the total gain has a positive floor, a further subsequence therefore has
either half that floor in literal Never gain at every row, or half that floor
in a local endpoint gap at dates tending to infinity.  The latter dates are
reached with positive opponent survival.

This theorem normalizes an already selected approximate best response.  It
does not select a common best-response witness for simultaneous reset
vertices, and the late local endpoint still has to be attached to a
state-matched continuation.
-/

noncomputable section

namespace GameTheory

open Filter
open Experiments.PureTimeWitnessNormalForm

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A uniformly profitable selected pure-time witness has, after one strict
subsequence, exactly one of four explicit descriptions: fixed finite,
literal Never, escaping but Never-funded, or escaping with a late profitable
endpoint.  The last endpoint dates tend to infinity and retain positive
opponent survival. -/
theorem exists_pureTimeWitness_fixed_never_or_escapingDichotomy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ℕ → ι → PMF Bool) (who : ι)
    (quitTime : ℕ → Option ℕ) (prescribed : ℕ → ℝ)
    (eta : ℝ) (heta : 0 < eta)
    (hgain : ∀ n,
      eta ≤
        quittingRootSequencePureTimeTerminalValue reward (roots n) who
            (quitTime n) 0 - prescribed n) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
      ((∃ time : ℕ, ∀ n, quitTime (subseq n) = some time) ∨
        (∀ n, quitTime (subseq n) = none) ∨
        (∃ time : ℕ → ℕ,
          Tendsto time atTop atTop ∧
          (∀ n, quitTime (subseq n) = some (time n)) ∧
          ((∀ n,
              eta / 2 ≤
                quittingRootSequencePureTimeTerminalValue reward
                    (roots (subseq n)) who none 0 - prescribed (subseq n)) ∨
            (∀ n,
              eta / 2 ≤
                quittingRootEndpointDifference reward
                  (fun _ ↦
                    quittingRootSequencePureTimeTerminalValue reward
                      (roots (subseq n)) who none (time n + 1))
                  (roots (subseq n) (time n)) who ∧
              0 < quittingOpponentSurvivalWeight
                (roots (subseq n)) who 0 (time n))))) := by
  rcases exists_strictMono_hasNormalForm quitTime with
    ⟨φ, hφ, hnormal⟩
  rcases hnormal with ⟨fixed, hfixed⟩ | hnever | ⟨time, htime, hquit⟩
  · exact ⟨φ, hφ, Or.inl ⟨fixed, hfixed⟩⟩
  · exact ⟨φ, hφ, Or.inr (Or.inl hnever)⟩
  · let neverFunded : ℕ → Prop := fun n ↦
      eta / 2 ≤
        quittingRootSequencePureTimeTerminalValue reward
            (roots (φ n)) who none 0 - prescribed (φ n)
    let lateEndpoint : ℕ → Prop := fun n ↦
      eta / 2 ≤
          quittingRootEndpointDifference reward
            (fun _ ↦
              quittingRootSequencePureTimeTerminalValue reward
                (roots (φ n)) who none (time n + 1))
            (roots (φ n) (time n)) who ∧
        0 < quittingOpponentSurvivalWeight
          (roots (φ n)) who 0 (time n)
    have hpointwise : ∀ n, neverFunded n ∨ lateEndpoint n := by
      intro n
      have hexact :=
        quittingRootSequencePureTimeTerminalValue_some_sub_none_eq
          reward (roots (φ n)) who 0 (time n)
      simp only [Nat.zero_add] at hexact
      have hselected := hgain (φ n)
      have hquitn : quitTime (φ n) = some (time n) := by
        simpa [Function.comp_def] using hquit n
      rw [hquitn] at hselected
      by_cases hneverFloor : neverFunded n
      · exact Or.inl hneverFloor
      · right
        have hproduct :
            eta / 2 <
              quittingOpponentSurvivalWeight
                  (roots (φ n)) who 0 (time n) *
                quittingRootEndpointDifference reward
                  (fun _ ↦
                    quittingRootSequencePureTimeTerminalValue reward
                      (roots (φ n)) who none (time n + 1))
                  (roots (φ n) (time n)) who := by
          dsimp only [neverFunded] at hneverFloor
          linarith
        have hweight0 := quittingOpponentSurvivalWeight_nonneg
          (roots (φ n)) who 0 (time n)
        have hweight1 := quittingOpponentSurvivalWeight_le_one
          (roots (φ n)) who 0 (time n)
        have hhalfPos : 0 < eta / 2 := half_pos heta
        have hweightPos : 0 < quittingOpponentSurvivalWeight
            (roots (φ n)) who 0 (time n) := by
          by_contra hnot
          have hzero := le_antisymm (le_of_not_gt hnot) hweight0
          rw [hzero, zero_mul] at hproduct
          linarith
        have hendpointPos : 0 <
            quittingRootEndpointDifference reward
              (fun _ ↦
                quittingRootSequencePureTimeTerminalValue reward
                  (roots (φ n)) who none (time n + 1))
              (roots (φ n) (time n)) who := by
          nlinarith
        have hproductLeEndpoint :
            quittingOpponentSurvivalWeight
                (roots (φ n)) who 0 (time n) *
              quittingRootEndpointDifference reward
                (fun _ ↦
                  quittingRootSequencePureTimeTerminalValue reward
                    (roots (φ n)) who none (time n + 1))
                (roots (φ n) (time n)) who ≤
              quittingRootEndpointDifference reward
                (fun _ ↦
                  quittingRootSequencePureTimeTerminalValue reward
                    (roots (φ n)) who none (time n + 1))
                (roots (φ n) (time n)) who := by
          nlinarith
        exact ⟨le_trans (le_of_lt hproduct) hproductLeEndpoint, hweightPos⟩
    by_cases hneverFrequently : ∃ᶠ n in atTop, neverFunded n
    · rcases extraction_of_frequently_atTop hneverFrequently with
        ⟨ψ, hψ, hneverψ⟩
      refine ⟨φ ∘ ψ, hφ.comp hψ, Or.inr (Or.inr ⟨time ∘ ψ, ?_, ?_, ?_⟩)⟩
      · exact htime.comp hψ.tendsto_atTop
      · intro n
        exact hquit (ψ n)
      · left
        exact hneverψ
    · have hlateEventually : ∀ᶠ n in atTop, lateEndpoint n :=
        (not_frequently.mp hneverFrequently).mono fun n hn ↦
          (hpointwise n).resolve_left hn
      rcases extraction_of_eventually_atTop hlateEventually with
        ⟨ψ, hψ, hlateψ⟩
      refine ⟨φ ∘ ψ, hφ.comp hψ, Or.inr (Or.inr ⟨time ∘ ψ, ?_, ?_, ?_⟩)⟩
      · exact htime.comp hψ.tendsto_atTop
      · intro n
        exact hquit (ψ n)
      · right
        exact hlateψ

end GameTheory
