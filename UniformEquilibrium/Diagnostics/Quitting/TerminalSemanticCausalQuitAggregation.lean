/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.CausalQuitConvexHull
import UniformEquilibrium.Quitting.Cycles.PureTimeExtremality

/-!
# Exact causal account for finite Quit-direction deviations

Moving a fraction of one player's Continue mass to Quit at chronologically
ordered rows produces a causal recursion. The current signed Quit advantage
is collected at the current modification rate, while every later term is
discounted by the probability of refusing the current modification.

This identity uses the literal signed row advantage. It makes no claim that
an eventwise positive-part account lower-bounds that advantage.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Recursive gain account for moving baseline Continue probability toward
Quit. The row gap uses the literal baseline continuation value. -/
def quittingFiniteCausalQuitGain
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline : ℕ → PMF Bool) (lambda : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | start, fuel + 1 =>
      let baselineTail := quittingFiniteHazardValue
        quitValue continueReward continueMass baseline (start + 1) fuel
      lambda start * (baseline start false).toReal *
          (quitValue start -
            (continueReward start + continueMass start * baselineTail)) +
        (1 - lambda start) * (baseline start false).toReal *
          continueMass start *
            quittingFiniteCausalQuitGain quitValue continueReward continueMass
              baseline lambda (start + 1) fuel

/-- Chronological hazards underlying the finite causal Quit account.  Each
row first records termination by the baseline player's existing Quit mass,
then the new conditional Quit fraction, then termination by the opponents.
Only the middle hazard carries the row gain. -/
def quittingFiniteCausalQuitProbabilities
    (continueMass : ℕ → ℝ) (baseline : ℕ → PMF Bool)
    (lambda : ℕ → ℝ) : ℕ → ℕ → List ℝ
  | _, 0 => []
  | start, fuel + 1 =>
      (1 - (baseline start false).toReal) ::
        lambda start ::
          (1 - continueMass start) ::
            quittingFiniteCausalQuitProbabilities continueMass baseline lambda
              (start + 1) fuel

/-- Row gains aligned with `quittingFiniteCausalQuitProbabilities`; the two
termination hazards at each row carry zero gain. -/
def quittingFiniteCausalQuitRowGains
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline : ℕ → PMF Bool) : ℕ → ℕ → List ℝ
  | _, 0 => []
  | start, fuel + 1 =>
      0 ::
        (quitValue start -
          (continueReward start + continueMass start *
            quittingFiniteHazardValue quitValue continueReward continueMass
              baseline (start + 1) fuel)) ::
          0 ::
            quittingFiniteCausalQuitRowGains
              quitValue continueReward continueMass baseline (start + 1) fuel

private theorem zipWith_mul_map_left_sum
    (scale : ℝ) (weights gains : List ℝ) :
    (List.zipWith (· * ·) (weights.map (scale * ·)) gains).sum =
      scale * (List.zipWith (· * ·) weights gains).sum := by
  induction weights generalizing gains with
  | nil => simp
  | cons weight weights ih =>
      cases gains with
      | nil => simp
      | cons gain gains =>
          simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]
          ring

/-- The recursive causal Quit account is exactly the generic causal weighted
sum after inserting the two zero-gain termination hazards at every row. -/
theorem quittingFiniteCausalQuitGain_eq_causalWeights
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline : ℕ → PMF Bool) (lambda : ℕ → ℝ) :
    ∀ start fuel,
      quittingFiniteCausalQuitGain quitValue continueReward continueMass
          baseline lambda start fuel =
        (List.zipWith (· * ·)
          (causalQuitWeights
            (quittingFiniteCausalQuitProbabilities
              continueMass baseline lambda start fuel))
          (quittingFiniteCausalQuitRowGains
            quitValue continueReward continueMass baseline start fuel)).sum := by
  intro start fuel
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteCausalQuitGain,
        quittingFiniteCausalQuitProbabilities,
        quittingFiniteCausalQuitRowGains, causalQuitWeights]
  | succ fuel ih =>
      simp only [quittingFiniteCausalQuitGain,
        quittingFiniteCausalQuitProbabilities,
        quittingFiniteCausalQuitRowGains, causalQuitWeights, List.map_cons,
        List.zipWith_cons_cons, List.sum_cons]
      rw [zipWith_mul_map_left_sum, zipWith_mul_map_left_sum,
        zipWith_mul_map_left_sum]
      rw [← ih (start + 1)]
      ring

/-- The hazards in the causal representation are admissible whenever the
inserted Quit fractions and opponent continuation factors are admissible. -/
theorem quittingFiniteCausalQuitProbabilities_mem_Icc
    (continueMass : ℕ → ℝ) (baseline : ℕ → PMF Bool)
    (lambda : ℕ → ℝ) (start fuel : ℕ)
    (hcontinueMass : ∀ time, start ≤ time → time < start + fuel →
      continueMass time ∈ Set.Icc (0 : ℝ) 1)
    (hlambda : ∀ time, start ≤ time → time < start + fuel →
      lambda time ∈ Set.Icc (0 : ℝ) 1) :
    ∀ probability,
      probability ∈ quittingFiniteCausalQuitProbabilities
        continueMass baseline lambda start fuel →
      probability ∈ Set.Icc (0 : ℝ) 1 := by
  induction fuel generalizing start with
  | zero =>
      simp [quittingFiniteCausalQuitProbabilities]
  | succ fuel ih =>
      intro probability hprobability
      simp only [quittingFiniteCausalQuitProbabilities, List.mem_cons] at hprobability
      rcases hprobability with rfl | rfl | rfl | htail
      · have hbaseline0 : 0 ≤ (baseline start false).toReal :=
          ENNReal.toReal_nonneg
        have hbaseline1 : (baseline start false).toReal ≤ 1 :=
          ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one _ _)
        exact ⟨sub_nonneg.mpr hbaseline1, sub_le_self 1 hbaseline0⟩
      · exact hlambda start (by omega) (by omega)
      · have hcontinue := hcontinueMass start (by omega) (by omega)
        exact ⟨sub_nonneg.mpr hcontinue.2, sub_le_self 1 hcontinue.1⟩
      · apply ih (start + 1)
        · intro time htimeLower htimeUpper
          exact hcontinueMass time (by omega) (by omega)
        · intro time htimeLower htimeUpper
          exact hlambda time (by omega) (by omega)
        · exact htail

/-- A common nonnegative upper bound on the represented signed row gains
bounds the complete finite causal Quit account. -/
theorem quittingFiniteCausalQuitGain_le
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline : ℕ → PMF Bool) (lambda : ℕ → ℝ)
    (start fuel : ℕ) (upper : ℝ)
    (hcontinueMass : ∀ time, start ≤ time → time < start + fuel →
      continueMass time ∈ Set.Icc (0 : ℝ) 1)
    (hlambda : ∀ time, start ≤ time → time < start + fuel →
      lambda time ∈ Set.Icc (0 : ℝ) 1)
    (hupperNonneg : 0 ≤ upper)
    (hrowGain : ∀ gain ∈ quittingFiniteCausalQuitRowGains
      quitValue continueReward continueMass baseline start fuel,
      gain ≤ upper) :
    quittingFiniteCausalQuitGain quitValue continueReward continueMass
        baseline lambda start fuel ≤ upper := by
  rw [quittingFiniteCausalQuitGain_eq_causalWeights]
  exact zipWith_sum_le_of_causalQuitWeights
    (quittingFiniteCausalQuitProbabilities
      continueMass baseline lambda start fuel)
    (quittingFiniteCausalQuitRowGains
      quitValue continueReward continueMass baseline start fuel)
    upper
    (quittingFiniteCausalQuitProbabilities_mem_Icc
      continueMass baseline lambda start fuel hcontinueMass hlambda)
    hupperNonneg hrowGain

/-- **Exact finite causal-convexification identity.** If `modified` is
obtained by moving the fraction `lambda t` of the baseline Continue mass to
Quit at every row, then its finite payoff gain is exactly the causal account
above. -/
theorem quittingFiniteHazardValue_sub_eq_causalQuitGain
    (quitValue continueReward continueMass : ℕ → ℝ)
    (baseline modified : ℕ → PMF Bool) (lambda : ℕ → ℝ)
    (hquit : ∀ time,
      (modified time true).toReal =
        (baseline time true).toReal +
          lambda time * (baseline time false).toReal)
    (hcontinue : ∀ time,
      (modified time false).toReal =
        (1 - lambda time) * (baseline time false).toReal) :
    ∀ start fuel,
      quittingFiniteHazardValue quitValue continueReward continueMass
          modified start fuel -
        quittingFiniteHazardValue quitValue continueReward continueMass
          baseline start fuel =
      quittingFiniteCausalQuitGain quitValue continueReward continueMass
        baseline lambda start fuel := by
  intro start fuel
  induction fuel generalizing start with
  | zero => simp [quittingFiniteHazardValue, quittingFiniteCausalQuitGain]
  | succ fuel ih =>
      rw [quittingFiniteHazardValue, quittingFiniteHazardValue,
        quittingFiniteCausalQuitGain, hquit, hcontinue]
      have htail := ih (start + 1)
      have htailEq :
          quittingFiniteHazardValue quitValue continueReward continueMass
              modified (start + 1) fuel =
            quittingFiniteHazardValue quitValue continueReward continueMass
                baseline (start + 1) fuel +
              quittingFiniteCausalQuitGain quitValue continueReward
                continueMass baseline lambda (start + 1) fuel := by
        linarith
      rw [htailEq]
      ring

/-- The exact finite causal identity for a player in a quitting game against
fixed opponent roots. -/
theorem quittingFiniteRootPayoff_sub_eq_causalQuitGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    (baseline modified : ℕ → PMF Bool) (lambda : ℕ → ℝ)
    (hquit : ∀ time,
      (modified time true).toReal =
        (baseline time true).toReal +
          lambda time * (baseline time false).toReal)
    (hcontinue : ∀ time,
      (modified time false).toReal =
        (1 - lambda time) * (baseline time false).toReal)
    (start fuel : ℕ) :
    quittingFiniteRootPayoff reward roots who modified start fuel -
        quittingFiniteRootPayoff reward roots who baseline start fuel =
      quittingFiniteCausalQuitGain
        (quittingFixedOpponentsQuitValue reward roots who)
        (quittingFixedOpponentsContinueReward reward roots who)
        (quittingFixedOpponentsContinueMass roots who)
        baseline lambda start fuel := by
  rw [quittingFiniteRootPayoff_eq_hazardValue,
    quittingFiniteRootPayoff_eq_hazardValue]
  exact quittingFiniteHazardValue_sub_eq_causalQuitGain
    _ _ _ baseline modified lambda hquit hcontinue start fuel

end GameTheory
