/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Research.Quitting.CirculantTrichotomy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PeriodicBlockProfile
import UniformEquilibrium.Quitting.Cycles.SoloPeriodicBlockCompiler

/-!
# Constant-step cyclic equilibria of five-player rotation-symmetric tables

Fix five players indexed by `ZMod 5` and a quitting table whose singleton and
two-element rows are rotation symmetric:

* `reward {owner} who = s + m (owner - who)` — a common solo self value `s` and
  a *margin* `m d` depending only on the distance from receiver to quitter;
* `reward {owner, who} who = s + J (owner - who)` for `owner ≠ who` — a *join
  margin* `J d` depending only on the same distance.

Nothing is assumed about coalitions of size three or more.

For a step `c` the *constant-step profile* schedules player `c * k` at phase
`k` of a period-five cycle and gives every scheduled player the same quit
probability `1 - q`.  `stepSlack` is the resulting displayed value measured
from `s`, indexed by the number of phases elapsed since the player's own
quitting phase, and `stepAnchor` is the cubic whose vanishing at `q` closes the
cycle.  `isSoloPeriodicCertificate_constantStep` records that the anchor
equation and four floor inequalities — one per elapsed phase — supply every
obligation of `GameTheory.SoloPeriodicBlockCompiler.IsSoloPeriodicCertificate`,
so the profile realizes `stepValue … 0` as a uniform-equilibrium payoff.

The step is carried together with a companion `c'` satisfying `c * c' = -1`,
which is the reindexing that sends a player to its elapsed-phase coordinate.

## Main definitions

* `stepAnchor` — the constant-step anchor cubic `m c + m (2c) q + m (3c) q² +
  m (4c) q³`
* `stepSlack` — the displayed value measured from `s`
* `stepSchedule`, `stepValue` — the schedule and displayed value path

## Main results

* `stepSlack_rec` — the one-phase value recursion, valid exactly at an anchor
  root
* `isSoloPeriodicCertificate_constantStep` — the finite certificate
* `isUniformEquilibriumPayoff_constantStep` — the uniform-equilibrium payoff
* `isEmpty_counterexampleRegime_constantStep` — the emptiness of the
  counterexample regime
-/

noncomputable section

namespace GameTheory
namespace CirculantConstantStepCycle

open Math.Probability Math.ProbabilityMassFunction
open SoloPeriodicBlockCompiler

/-! ## Elementary arithmetic of the five-cycle -/

theorem zmod_five_cases (t : ZMod 5) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
  revert t
  decide

/-- The four margins along the progression of a nonzero step total the sum of
all margins, the margin at zero being zero. -/
theorem sum_stepMargin (m : ZMod 5 → ℝ) (hm0 : m 0 = 0) {c : ZMod 5} (hc : c ≠ 0) :
    m c + m (2 * c) + m (3 * c) + m (4 * c) = ∑ e, m e := by
  have hsum : (∑ e : ZMod 5, m e) = m 0 + m 1 + m 2 + m 3 + m 4 :=
    Fin.sum_univ_five (fun e : ZMod 5 => m e)
  rcases zmod_five_cases c with h | h | h | h | h
  · exact absurd h hc
  · subst h
    rw [hsum, show (2 : ZMod 5) * 1 = 2 from by decide,
      show (3 : ZMod 5) * 1 = 3 from by decide,
      show (4 : ZMod 5) * 1 = 4 from by decide, hm0]
    ring
  · subst h
    rw [hsum, show (2 : ZMod 5) * 2 = 4 from by decide,
      show (3 : ZMod 5) * 2 = 1 from by decide,
      show (4 : ZMod 5) * 2 = 3 from by decide, hm0]
    ring
  · subst h
    rw [hsum, show (2 : ZMod 5) * 3 = 1 from by decide,
      show (3 : ZMod 5) * 3 = 4 from by decide,
      show (4 : ZMod 5) * 3 = 2 from by decide, hm0]
    ring
  · subst h
    rw [hsum, show (2 : ZMod 5) * 4 = 3 from by decide,
      show (3 : ZMod 5) * 4 = 2 from by decide,
      show (4 : ZMod 5) * 4 = 1 from by decide, hm0]
    ring

/-! ## The constant-step anchor and its slack sequence -/

variable (m : ZMod 5 → ℝ) (c : ZMod 5) (q : ℝ)

/-- The constant-step anchor cubic `m c + m (2c) q + m (3c) q² + m (4c) q³`. -/
def stepAnchor : ℝ := Math.cubicAnchor (m c) (m (2 * c)) (m (3 * c)) (m (4 * c)) q

theorem stepAnchor_eq :
    stepAnchor m c q =
      m c + m (2 * c) * q + m (3 * c) * q ^ 2 + m (4 * c) * q ^ 3 := rfl

/-- The constant-step anchor is the `constantStepAnchor` of
`Research/Quitting/CirculantTrichotomy.lean` written multiplicatively. -/
theorem stepAnchor_eq_constantStepAnchor :
    stepAnchor m c q = QuittingLCPClassification.constantStepAnchor m c q := by
  rw [stepAnchor, QuittingLCPClassification.constantStepAnchor]
  norm_num [nsmul_eq_mul]

/-- **The anchor root.**  A step of negative margin on a table of positive
margin sum has an anchor root strictly between zero and one. -/
theorem exists_stepAnchor_root (hm0 : m 0 = 0) {c : ZMod 5} (hc : c ≠ 0)
    (hneg : m c < 0) (hsum : 0 < ∑ e, m e) :
    ∃ q ∈ Set.Ioo (0 : ℝ) 1, stepAnchor m c q = 0 :=
  Math.exists_cubicAnchor_root_mem_Ioo hneg
    (by rw [sum_stepMargin m hm0 hc]; exact hsum)

/-- **A located anchor root.**  An anchor negative at the left endpoint of an
interval and positive at the right vanishes strictly between them.  Locating a
root on a prescribed side of a point is what the floor inequalities that read
the root itself need. -/
theorem exists_stepAnchor_root_mem_Ioo {lo hi : ℝ} (hle : lo ≤ hi)
    (hlo : stepAnchor m c lo < 0) (hhi : 0 < stepAnchor m c hi) :
    ∃ q ∈ Set.Ioo lo hi, stepAnchor m c q = 0 :=
  Math.exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos hle hlo hhi

/-- **A located anchor root, right endpoint admitted.**  An anchor negative at
the left endpoint and nonnegative at the right vanishes past the left endpoint
and no later than the right one. -/
theorem exists_stepAnchor_root_mem_Ioc {lo hi : ℝ} (hle : lo ≤ hi)
    (hlo : stepAnchor m c lo < 0) (hhi : 0 ≤ stepAnchor m c hi) :
    ∃ q ∈ Set.Ioc lo hi, stepAnchor m c q = 0 :=
  Math.exists_cubicAnchor_root_mem_Ioc_of_neg_of_nonneg hle hlo hhi

/-- The displayed value of the constant-step profile, measured from the solo
self value and indexed by the number of phases elapsed since the player's own
quitting phase. -/
def stepSlack (t : ZMod 5) : ℝ :=
  if t = 2 then (1 - q) * (m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c))
  else if t = 3 then (1 - q) * (m (3 * c) + q * m (4 * c))
  else if t = 4 then (1 - q) * m (4 * c)
  else 0

@[simp] theorem stepSlack_zero : stepSlack m c q 0 = 0 := by
  rw [stepSlack, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

@[simp] theorem stepSlack_one : stepSlack m c q 1 = 0 := by
  rw [stepSlack, if_neg (by decide), if_neg (by decide), if_neg (by decide)]

@[simp] theorem stepSlack_two :
    stepSlack m c q 2 =
      (1 - q) * (m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c)) := by
  rw [stepSlack, if_pos rfl]

@[simp] theorem stepSlack_three :
    stepSlack m c q 3 = (1 - q) * (m (3 * c) + q * m (4 * c)) := by
  rw [stepSlack, if_neg (by decide), if_pos rfl]

@[simp] theorem stepSlack_four : stepSlack m c q 4 = (1 - q) * m (4 * c) := by
  rw [stepSlack, if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- **The one-phase value recursion.**  At an anchor root the slack sequence
satisfies the backward recursion of the constant-step profile at every elapsed
phase; the phase-one instance is exactly the anchor equation. -/
theorem stepSlack_rec (hm0 : m 0 = 0) (hroot : stepAnchor m c q = 0) (t : ZMod 5) :
    stepSlack m c q t = (1 - q) * m (c * t) + q * stepSlack m c q (t + 1) := by
  rw [stepAnchor_eq] at hroot
  rcases zmod_five_cases t with h | h | h | h | h <;> subst h
  · rw [mul_zero, hm0, stepSlack_zero, show (0 : ZMod 5) + 1 = 1 from by decide,
      stepSlack_one]
    ring
  · rw [mul_one, stepSlack_one, show (1 : ZMod 5) + 1 = 2 from by decide,
      stepSlack_two]
    linear_combination (q - 1) * hroot
  · rw [show c * 2 = 2 * c from mul_comm c 2, stepSlack_two,
      show (2 : ZMod 5) + 1 = 3 from by decide, stepSlack_three]
    ring
  · rw [show c * 3 = 3 * c from mul_comm c 3, stepSlack_three,
      show (3 : ZMod 5) + 1 = 4 from by decide, stepSlack_four]
    ring
  · rw [show c * 4 = 4 * c from mul_comm c 4, stepSlack_four,
      show (4 : ZMod 5) + 1 = 0 from by decide, stepSlack_zero]
    ring

/-! ## The profile -/

variable (s : ℝ) (c' : ZMod 5)

/-- The constant-step schedule: player `c * k` quits at phase `k`. -/
def stepSchedule : Fin 5 → ZMod 5 := fun k ↦ c * ((k : ℕ) : ZMod 5)

/-- The displayed value path of the constant-step profile.  The elapsed-phase
coordinate of player `who` at stage `k` is `k + c' * who`. -/
def stepValue : Fin 6 → Payoff (ZMod 5) :=
  fun stage who ↦ s + stepSlack m c q (((stage : ℕ) : ZMod 5) + c' * who)

@[simp] theorem stepValue_zero_apply (who : ZMod 5) :
    stepValue m c q s c' 0 who = s + stepSlack m c q (c' * who) := by
  rw [stepValue]
  norm_num

theorem stepValue_last :
    stepValue m c q s c' (Fin.last 5) = stepValue m c q s c' 0 := by
  funext who
  rw [stepValue, stepValue,
    show ((((Fin.last 5 : Fin 6)) : ℕ) : ZMod 5) = ((((0 : Fin 6)) : ℕ) : ZMod 5)
      from by decide]

/-- The Boolean law of the profile: every scheduled player quits with the same
probability `1 - q`. -/
def stepCoin (h0 : 0 ≤ q) (h1 : q ≤ 1) : Fin 5 → PMF Bool :=
  fun _ ↦ quittingHazardCoin (1 - q) (by linarith) (by linarith)

@[simp] theorem stepCoin_true (h0 : 0 ≤ q) (h1 : q ≤ 1) (k : Fin 5) :
    (stepCoin q h0 h1 k true).toReal = 1 - q := by
  rw [stepCoin, quittingHazardCoin_true_toReal]

@[simp] theorem stepCoin_false (h0 : 0 ≤ q) (h1 : q ≤ 1) (k : Fin 5) :
    (stepCoin q h0 h1 k false).toReal = q := by
  rw [stepCoin, quittingHazardCoin_false_toReal]
  ring

/-! ## The certificate -/

/-- The rotation-symmetric shape of the singleton and two-element rows used by
the constant-step certificate. -/
structure IsCirculantPairTable
    (reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5))
    (s : ℝ) (m J : ZMod 5 → ℝ) : Prop where
  /-- The margin at distance zero vanishes. -/
  margin_zero : m 0 = 0
  /-- Singleton rows are the solo self value shifted by the margin. -/
  singleton : ∀ owner who : ZMod 5,
    reward (quittingSingletonTerminal owner) who = s + m (owner - who)
  /-- Two-element rows are the solo self value shifted by the join margin. -/
  pair : ∀ owner who : ZMod 5, owner ≠ who →
    reward ⟨{owner, who}, Finset.insert_nonempty owner {who}⟩ who =
      s + J (owner - who)

variable {m J : ZMod 5 → ℝ} {c c' : ZMod 5} {q s : ℝ}
  {reward : {S : Finset (ZMod 5) // S.Nonempty} → Payoff (ZMod 5)}

/-- Every displayed value of the constant-step profile is a convex combination
of singleton rows, hence inside the canonical reward box. -/
theorem abs_stepValue_le (htable : IsCirculantPairTable reward s m J)
    (h0 : 0 ≤ q) (h1 : q ≤ 1) (stage : Fin 6) (who : ZMod 5) :
    |stepValue m c q s c' stage who| ≤ quittingRewardBound reward := by
  have hrow : ∀ d : ZMod 5, |s + m d| ≤ quittingRewardBound reward := by
    intro d
    have hentry := abs_reward_le_quittingRewardBound reward
      (quittingSingletonTerminal d) (0 : ZMod 5)
    rwa [htable.singleton, sub_zero] at hentry
  have hself : |s| ≤ quittingRewardBound reward := by
    have hzero := hrow 0
    rwa [htable.margin_zero, add_zero] at hzero
  have hmix : ∀ a b : ℝ, |a| ≤ quittingRewardBound reward →
      |b| ≤ quittingRewardBound reward →
      |(1 - q) * a + q * b| ≤ quittingRewardBound reward := by
    intro a b ha hb
    have h1q : (0 : ℝ) ≤ 1 - q := by linarith
    calc |(1 - q) * a + q * b| ≤ |(1 - q) * a| + |q * b| := abs_add_le _ _
      _ = (1 - q) * |a| + q * |b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1q, abs_of_nonneg h0]
      _ ≤ (1 - q) * quittingRewardBound reward + q * quittingRewardBound reward := by
          nlinarith
      _ = quittingRewardBound reward := by ring
  have hfour : |s + stepSlack m c q 4| ≤ quittingRewardBound reward := by
    have hstep := hmix (s + m (4 * c)) s (hrow _) hself
    rw [stepSlack_four, show s + (1 - q) * m (4 * c)
      = (1 - q) * (s + m (4 * c)) + q * s from by ring]
    exact hstep
  have hthree : |s + stepSlack m c q 3| ≤ quittingRewardBound reward := by
    have hstep := hmix (s + m (3 * c)) (s + stepSlack m c q 4) (hrow _) hfour
    rw [stepSlack_four] at hstep
    rw [stepSlack_three, show s + (1 - q) * (m (3 * c) + q * m (4 * c))
      = (1 - q) * (s + m (3 * c)) + q * (s + (1 - q) * m (4 * c)) from by ring]
    exact hstep
  have htwo : |s + stepSlack m c q 2| ≤ quittingRewardBound reward := by
    have hstep := hmix (s + m (2 * c)) (s + stepSlack m c q 3) (hrow _) hthree
    rw [stepSlack_three] at hstep
    rw [stepSlack_two, show s + (1 - q) * (m (2 * c) + q * m (3 * c)
        + q ^ 2 * m (4 * c))
      = (1 - q) * (s + m (2 * c))
        + q * (s + (1 - q) * (m (3 * c) + q * m (4 * c))) from by ring]
    exact hstep
  rw [stepValue]
  rcases zmod_five_cases (((stage : ℕ) : ZMod 5) + c' * who) with h | h | h | h | h <;>
    rw [h]
  · simpa using hself
  · simpa using hself
  · exact htwo
  · exact hthree
  · exact hfour

/-- **The finite certificate of a constant-step cyclic profile.**  The anchor
equation and the four floor inequalities supply every obligation of the
single-quitter periodic compiler. -/
theorem isSoloPeriodicCertificate_constantStep
    (htable : IsCirculantPairTable reward s m J)
    (hcc' : c * c' = -1) (hs : 0 ≤ s)
    (h0 : 0 < q) (h1 : q < 1) (hroot : stepAnchor m c q = 0)
    (hfloor₁ : J c ≤ 0)
    (hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c))
    (hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c))
    (hfloor₄ : J (4 * c) ≤ m (4 * c)) :
    IsSoloPeriodicCertificate reward (stepSchedule c) (stepCoin q h0.le h1.le)
      (stepValue m c q s c') := by
  have hp : (0 : ℝ) < 1 - q := by linarith
  have hslack : ∀ t : ZMod 5,
      stepSlack m c q t = (1 - q) * m (c * t) + q * stepSlack m c q (t + 1) :=
    stepSlack_rec m c q htable.margin_zero hroot
  have hfloor : ∀ t : ZMod 5, t ≠ 0 → (1 - q) * J (c * t) ≤ stepSlack m c q t := by
    intro t ht
    rcases zmod_five_cases t with h | h | h | h | h
    · exact absurd h ht
    · rw [h, mul_one, stepSlack_one]
      nlinarith
    · rw [h, show c * 2 = 2 * c from mul_comm c 2, stepSlack_two]
      exact mul_le_mul_of_nonneg_left hfloor₂ hp.le
    · rw [h, show c * 3 = 3 * c from mul_comm c 3, stepSlack_three]
      exact mul_le_mul_of_nonneg_left hfloor₃ hp.le
    · rw [h, show c * 4 = 4 * c from mul_comm c 4, stepSlack_four]
      exact mul_le_mul_of_nonneg_left hfloor₄ hp.le
  have hdist : ∀ (k : Fin 5) (who : ZMod 5),
      c * (((k : ℕ) : ZMod 5) + c' * who) = stepSchedule c k - who := by
    intro k who
    rw [stepSchedule, mul_add, ← mul_assoc, hcc']
    ring
  have hcast : ∀ k : Fin 5,
      (((Fin.castSucc k : Fin 6) : ℕ) : ZMod 5) = ((k : ℕ) : ZMod 5) := by
    intro k
    rw [Fin.val_castSucc]
  have hnext : ∀ (k : Fin 5) (who : ZMod 5),
      (((Fin.succ k : Fin 6) : ℕ) : ZMod 5) + c' * who =
        ((k : ℕ) : ZMod 5) + c' * who + 1 := by
    intro k who
    rw [Fin.val_succ]
    push_cast
    ring
  refine ⟨abs_stepValue_le htable h0.le h1.le, stepValue_last m c q s c', ?_, ?_, ?_,
    ⟨0, ?_⟩, ?_⟩
  · intro k who
    rw [stepValue, stepValue, stepCoin_true, stepCoin_false, htable.singleton,
      hnext k who, hcast k, ← hdist k who,
      hslack (((k : ℕ) : ZMod 5) + c' * who)]
    ring
  · intro k
    rw [stepValue, htable.singleton, sub_self, htable.margin_zero, add_zero]
    have hzero : (((Fin.succ k : Fin 6) : ℕ) : ZMod 5) + c' * stepSchedule c k = 1 := by
      rw [Fin.val_succ, stepSchedule, ← mul_assoc, mul_comm c' c, hcc']
      push_cast
      ring
    rw [hzero, stepSlack_one, add_zero]
  · intro k who hne
    rw [stepCoin_true, stepCoin_false, htable.singleton, htable.singleton,
      htable.pair _ _ (Ne.symm hne), stepValue, hnext k who,
      ← hdist k who, sub_self, htable.margin_zero, add_zero]
    have hkey := hfloor (((k : ℕ) : ZMod 5) + c' * who) (by
      intro hcontra
      apply hne
      have hzero : c * (((k : ℕ) : ZMod 5) + c' * who) = 0 := by
        rw [hcontra, mul_zero]
      rw [hdist k who] at hzero
      linear_combination -hzero)
    rw [hslack (((k : ℕ) : ZMod 5) + c' * who)] at hkey
    nlinarith
  · rw [stepCoin_true]
    linarith
  · intro who
    rw [htable.singleton, sub_self, htable.margin_zero, add_zero]
    exact hs

/-- **The constant-step cyclic uniform-equilibrium payoff.** -/
theorem isUniformEquilibriumPayoff_constantStep
    (htable : IsCirculantPairTable reward s m J)
    (hcc' : c * c' = -1) (hs : 0 ≤ s)
    (h0 : 0 < q) (h1 : q < 1) (hroot : stepAnchor m c q = 0)
    (hfloor₁ : J c ≤ 0)
    (hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c))
    (hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c))
    (hfloor₄ : J (4 * c) ≤ m (4 * c)) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (stepValue m c q s c' 0) :=
  isUniformEquilibriumPayoff_of_soloPeriodicBlock
    (isSoloPeriodicCertificate_constantStep htable hcc' hs h0 h1 hroot
      hfloor₁ hfloor₂ hfloor₃ hfloor₄)

/-- **A table with a constant-step cyclic equilibrium is in no counterexample
regime.** -/
theorem isEmpty_counterexampleRegime_constantStep
    (htable : IsCirculantPairTable reward s m J)
    (hcc' : c * c' = -1) (hs : 0 ≤ s)
    (h0 : 0 < q) (h1 : q < 1) (hroot : stepAnchor m c q = 0)
    (hfloor₁ : J c ≤ 0)
    (hfloor₂ : J (2 * c) ≤ m (2 * c) + q * m (3 * c) + q ^ 2 * m (4 * c))
    (hfloor₃ : J (3 * c) ≤ m (3 * c) + q * m (4 * c))
    (hfloor₄ : J (4 * c) ≤ m (4 * c)) :
    IsEmpty (QuittingCounterexampleRegime reward) :=
  isEmpty_counterexampleRegime_of_soloPeriodicBlock
    (isSoloPeriodicCertificate_constantStep htable hcc' hs h0 h1 hroot
      hfloor₁ hfloor₂ hfloor₃ hfloor₄)

end CirculantConstantStepCycle
end GameTheory
