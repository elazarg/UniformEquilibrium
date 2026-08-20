/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Fink.LimitCorrectedTarget

/-!
# Indexed Fink calendars and public capstones

Slow-calendar combinatorics, indexed switching bounds, selectable
calendar interfaces, and the end-to-end indexed fixed-point compilers.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- Read a discounted fixed-point family according to the calendar index
selector `κ`. -/
def indexedFinkDiscount (β : ℕ → ℝ) (κ : ℕ → ℕ) (t : ℕ) : ℝ := β (κ t)

/-- Stationary profile scheduled at time `t` by the index selector `κ`. -/
def indexedFinkProfile (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : ℕ → G.finkDomain U) (κ : ℕ → ℕ) :
    ℕ → G.StationaryMixedProfile :=
  fun t => G.finkProfile (z (κ t))

/-- Continuation values scheduled at time `t` by `κ`. -/
def indexedFinkValue (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    {U : ℝ} (z : ℕ → G.finkDomain U) (κ : ℕ → ℕ) :
    ℕ → G.State → Payoff ι :=
  fun t => G.finkValue (z (κ t))

/-- Natural uniform bound on the scaled bias of discounted fixed point `n`. -/
def finkScaledBiasBound (β : ℕ → ℝ) (U : ℝ) (n : ℕ) : ℝ :=
  (β n / (1 - β n)) * U

/-- Activation times for a slow calendar.  Layer `n` is not activated before
calendar time `n * |B n|`, and consecutive activation times are distinct. -/
noncomputable def slowCalendarStart (B : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => max (slowCalendarStart B n + 1)
      (Nat.ceil (((n + 1 : ℕ) : ℝ) * |B (n + 1)|))

theorem strictMono_slowCalendarStart (B : ℕ → ℝ) :
    StrictMono (slowCalendarStart B) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [slowCalendarStart]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem slowCalendarStart_cost_le (B : ℕ → ℝ) (n : ℕ) :
    (n : ℝ) * |B n| ≤ (slowCalendarStart B n : ℝ) := by
  cases n with
  | zero => simp [slowCalendarStart]
  | succ n =>
      rw [slowCalendarStart]
      exact (Nat.le_ceil _).trans (by
        exact_mod_cast (le_max_right
          (slowCalendarStart B n + 1)
          (Nat.ceil ((((n + 1 : ℕ) : ℝ) * |B (n + 1)|)))))

/-- The slow unit-step calendar is the greatest layer whose activation time
has arrived. -/
noncomputable def slowUnitStepCalendar (B : ℕ → ℝ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun n => slowCalendarStart B n ≤ t) t

@[simp] theorem slowUnitStepCalendar_zero (B : ℕ → ℝ) :
    slowUnitStepCalendar B 0 = 0 := by
  simp [slowUnitStepCalendar]

theorem slowCalendarStart_slowUnitStepCalendar_le
    (B : ℕ → ℝ) (t : ℕ) :
    slowCalendarStart B (slowUnitStepCalendar B t) ≤ t := by
  exact Nat.findGreatest_spec (P := fun n => slowCalendarStart B n ≤ t)
    (Nat.zero_le t) (by simp [slowCalendarStart])

theorem slowUnitStepCalendar_slowCalendarStart
    (B : ℕ → ℝ) (n : ℕ) :
    slowUnitStepCalendar B (slowCalendarStart B n) = n := by
  apply le_antisymm
  · let k := slowUnitStepCalendar B (slowCalendarStart B n)
    have hkStart : slowCalendarStart B k ≤ slowCalendarStart B n :=
      slowCalendarStart_slowUnitStepCalendar_le B (slowCalendarStart B n)
    by_contra hnot
    have hnk : n < k := Nat.lt_of_not_ge hnot
    have hlt := strictMono_slowCalendarStart B hnk
    omega
  · have hnStart : n ≤ slowCalendarStart B n :=
      (strictMono_slowCalendarStart B).id_le n
    exact Nat.le_findGreatest hnStart le_rfl

/-- Calendar layer `n` occupies exactly the half-open activation interval
from its own start time to the next layer's start time. -/
theorem slowUnitStepCalendar_eq_iff
    (B : ℕ → ℝ) (t n : ℕ) :
    slowUnitStepCalendar B t = n ↔
      slowCalendarStart B n ≤ t ∧ t < slowCalendarStart B (n + 1) := by
  constructor
  · intro hν
    constructor
    · simpa only [hν] using slowCalendarStart_slowUnitStepCalendar_le B t
    · by_contra hnot
      have hnext : slowCalendarStart B (n + 1) ≤ t :=
        Nat.le_of_not_gt hnot
      have hnextT : n + 1 ≤ t :=
        (strictMono_slowCalendarStart B).id_le (n + 1) |>.trans hnext
      have hle : n + 1 ≤ slowUnitStepCalendar B t :=
        Nat.le_findGreatest hnextT hnext
      rw [hν] at hle
      omega
  · rintro ⟨hstart, hnext⟩
    have hnt : n ≤ t :=
      (strictMono_slowCalendarStart B).id_le n |>.trans hstart
    have hnle : n ≤ slowUnitStepCalendar B t :=
      Nat.le_findGreatest hnt hstart
    apply le_antisymm
    · by_contra hnot
      have hnextle : n + 1 ≤ slowUnitStepCalendar B t := by omega
      have hmono := (strictMono_slowCalendarStart B).monotone hnextle
      have hgreatest := slowCalendarStart_slowUnitStepCalendar_le B t
      omega
    · exact hnle

/-- Number of calendar stages for which one slow-calendar layer is held. -/
noncomputable def slowCalendarBlockLength (B : ℕ → ℝ) (n : ℕ) : ℕ :=
  slowCalendarStart B (n + 1) - slowCalendarStart B n

theorem slowCalendarStart_add_blockLength (B : ℕ → ℝ) (n : ℕ) :
    slowCalendarStart B n + slowCalendarBlockLength B n =
      slowCalendarStart B (n + 1) := by
  unfold slowCalendarBlockLength
  exact Nat.add_sub_of_le
    (strictMono_slowCalendarStart B (Nat.lt_succ_self n)).le

/-- Sharp adjacent switching charge obtained by centering the scaled Fink
bias at a target vector `W`.  The first term is the actual relative-bias
change; the second is only the change of discount scale applied to `W`. -/
def indexedFinkRelativeSwitchError (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (κ : ℕ → ℕ) (t : ℕ) : ℝ :=
  ‖G.finkRelativeBias (β (κ (t + 1))) W (z (κ (t + 1))) -
      G.finkRelativeBias (β (κ t)) W (z (κ t))‖ +
    |β (κ (t + 1)) / (1 - β (κ (t + 1))) -
      β (κ t) / (1 - β (κ t))| * U

/-- Charge zero while an indexed schedule stays on one fixed point and the
sum of the adjacent bias bounds when it switches. -/
def indexedFinkSwitchError (β : ℕ → ℝ) (U : ℝ) (κ : ℕ → ℕ)
    (t : ℕ) : ℝ :=
  if κ (t + 1) = κ t then 0
  else finkScaledBiasBound β U (κ (t + 1)) +
    finkScaledBiasBound β U (κ t)

/-- The exact quantitative calendar-selection property required to amortize
scaled Fink biases while keeping accumulated harmonic/excessive drift
negligible. -/
def IsIndexedFinkCalendarSelectable (β : ℕ → ℝ) (U : ℝ)
    (q r : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            indexedFinkSwitchError β U κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤ η

/-- Calendar selectability with the sharp centered adjacent-switch charge.
Unlike `IsIndexedFinkCalendarSelectable`, this interface can exploit
cancellation between neighboring scaled discounted values. -/
def IsIndexedFinkRelativeCalendarSelectable (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (q r : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ∑ k ∈ Finset.range t, r (κ k)) ≤ η

/-- Calendar selectability in the exact cancellation-aware form produced by
the verified reference hierarchy.  The correction is read on the same
calendar as the Fink fixed points; its endpoint norms are paid once, while
its canonical adjacent step error is accumulated by the potential telescope. -/
def IsIndexedFinkCorrectedCalendarSelectable (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) {U₀ : ℝ}
    (z : ℕ → G.finkDomain U₀) (W : G.State → Payoff ι)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ (κ : ℕ → ℕ) (T₀ : ℕ),
    ∀ T, T₀ ≤ T → 0 < T ∧
      ((finkScaledBiasBound β U (κ 0) +
            finkScaledBiasBound β U (κ T)) / (T : ℝ) +
          (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
            G.indexedFinkRelativeSwitchError β U z W κ t ≤ η) ∧
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        (q (κ t) + ‖R (κ 0)‖ + ‖R (κ t)‖ +
          ∑ k ∈ Finset.range t,
            G.finkCorrectedTargetStepError W (R ∘ κ) (z ∘ κ) k) ≤ η

/-- Indexed Fink fixed points form a calendar-time Bellman schedule. -/
theorem isDiscountedStationaryBellmanSchedule_indexedFink
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (κ : ℕ → ℕ) :
    G.IsDiscountedStationaryBellmanSchedule
      (indexedFinkDiscount β κ) (G.indexedFinkProfile z κ)
        (G.indexedFinkValue z κ) := by
  intro t
  exact G.isDiscountedStationaryBellmanEq_of_finkMap_fixedPoint
    (β (κ t)) U (hβ0 (κ t)) (hβ1 (κ t)).le hpay
      (z (κ t)) (hfix (κ t))

/-- The scheduled bias of an indexed fixed point obeys its natural scaled
cube bound. -/
theorem abs_scheduledFinkBias_indexed_le
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (z : ℕ → G.finkDomain U)
    (κ : ℕ → ℕ) (t : ℕ) (s : G.State) (who : ι) :
    |G.scheduledFinkBias (indexedFinkDiscount β κ)
        (G.indexedFinkValue z κ) t s who| ≤
      finkScaledBiasBound β U (κ t) := by
  have hratio : 0 ≤ β (κ t) / (1 - β (κ t)) :=
    div_nonneg (hβ0 (κ t)) (by linarith [hβ1 (κ t)])
  rw [scheduledFinkBias]
  change |(β (κ t) / (1 - β (κ t))) * G.finkValue (z (κ t)) s who| ≤ _
  rw [abs_mul, abs_of_nonneg hratio]
  exact mul_le_mul_of_nonneg_left (G.abs_finkValue_le (z (κ t)) s who) hratio

/-- The centered adjacent charge is a valid switching-error bound.  This is
the exact dictionary between absolute scheduled biases and the relative
biases controlled by the finite Fink hierarchy. -/
theorem isScheduledFinkSwitchBound_indexed_relative
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (z : ℕ → G.finkDomain U)
    (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U) (κ : ℕ → ℕ) :
    G.IsScheduledFinkSwitchBound (indexedFinkDiscount β κ)
      (G.indexedFinkValue z κ)
      (G.indexedFinkRelativeSwitchError β U z W κ) := by
  intro t s who
  let a₁ := β (κ (t + 1)) / (1 - β (κ (t + 1)))
  let a₀ := β (κ t) / (1 - β (κ t))
  let J₁ := G.finkRelativeBias (β (κ (t + 1))) W (z (κ (t + 1)))
  let J₀ := G.finkRelativeBias (β (κ t)) W (z (κ t))
  have hdecomp :
      G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) (t + 1) s who -
        G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) t s who =
      (J₁ - J₀) s who + (a₁ - a₀) * W s who := by
    simp only [scheduledFinkBias, indexedFinkDiscount, indexedFinkValue,
      J₁, J₀, a₁, a₀, finkRelativeBias, Pi.sub_apply]
    ring
  have hstate : ‖(J₁ - J₀) s‖ ≤ ‖J₁ - J₀‖ := by
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg (J₁ - J₀))).mp le_rfl s
  have hcoord : |(J₁ - J₀) s who| ≤ ‖J₁ - J₀‖ := by
    have hplayer : ‖(J₁ - J₀) s who‖ ≤ ‖(J₁ - J₀) s‖ := by
      exact (pi_norm_le_iff_of_nonneg
        (norm_nonneg ((J₁ - J₀) s))).mp le_rfl who
    simpa only [Real.norm_eq_abs] using hplayer.trans hstate
  have hscale : |(a₁ - a₀) * W s who| ≤ |a₁ - a₀| * U := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hW s who) (abs_nonneg _)
  rw [hdecomp]
  calc
    |(J₁ - J₀) s who + (a₁ - a₀) * W s who| ≤
        |(J₁ - J₀) s who| + |(a₁ - a₀) * W s who| :=
      abs_add_le _ _
    _ ≤ ‖J₁ - J₀‖ + |a₁ - a₀| * U :=
      add_le_add hcoord hscale
    _ = G.indexedFinkRelativeSwitchError β U z W κ t := by
      rfl

/-- The adjacent-bias charge is a valid switching-error bound for every
indexed Fink schedule. -/
theorem isScheduledFinkSwitchBound_indexed
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι]
    [∀ i, Fintype (G.Act i)]
    (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1) (z : ℕ → G.finkDomain U)
    (κ : ℕ → ℕ) :
    G.IsScheduledFinkSwitchBound (indexedFinkDiscount β κ)
      (G.indexedFinkValue z κ) (indexedFinkSwitchError β U κ) := by
  intro t s who
  by_cases hκ : κ (t + 1) = κ t
  · simp [indexedFinkSwitchError, hκ, scheduledFinkBias,
      indexedFinkDiscount, indexedFinkValue]
  · have hnext := G.abs_scheduledFinkBias_indexed_le
      β U hβ0 hβ1 z κ (t + 1) s who
    have hcurrent := G.abs_scheduledFinkBias_indexed_le
      β U hβ0 hβ1 z κ t s who
    calc
      |G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) (t + 1) s who -
        G.scheduledFinkBias (indexedFinkDiscount β κ)
          (G.indexedFinkValue z κ) t s who| ≤
          |G.scheduledFinkBias (indexedFinkDiscount β κ)
            (G.indexedFinkValue z κ) (t + 1) s who| +
          |G.scheduledFinkBias (indexedFinkDiscount β κ)
            (G.indexedFinkValue z κ) t s who| := abs_sub _ _
      _ ≤ finkScaledBiasBound β U (κ (t + 1)) +
          finkScaledBiasBound β U (κ t) := add_le_add hnext hcurrent
      _ = indexedFinkSwitchError β U κ t := by
        simp [indexedFinkSwitchError, hκ]

/-- Conditional indexed-family bridge to a uniform equilibrium payoff.  All
game-theoretic verification is discharged here; the remaining hypothesis is
the quantitative calendar selection condition balancing scaled biases against
the accumulated harmonic/excessive residuals. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (q r : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hharmonic : ∀ n s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r n)
    (hexcessive : ∀ n s who (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z n) s) who d))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤
        W s who + r n)
    (hselect : IsIndexedFinkCalendarSelectable β U q r) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_harmonicTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ, indexedFinkSwitchError β U κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (fun t => q (κ t)), (fun t => r (κ t)), T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed β U hβ0 hβ1 z κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact hharmonic (κ t) s who
  · intro t s who d
    exact hexcessive (κ t) s who d
  · exact hκ

/-- Sharp centered-switch version of the indexed-family bridge.  Its only
schedule cost is the actual adjacent relative-bias motion plus the adjacent
change of discount scale on the bounded target `W`. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints_relativeSwitch
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U) (q r : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hharmonic : ∀ n s who,
      |expect (pmfPi (G.finkProfile (z n) s)) (fun a =>
          expect (G.transition s a) (fun s' => W s' who)) - W s who| ≤ r n)
    (hexcessive : ∀ n s who (d : PMF (G.Act who)),
      expect (pmfPi (Function.update (G.finkProfile (z n) s) who d))
          (fun a => expect (G.transition s a) (fun s' => W s' who)) ≤
        W s who + r n)
    (hselect : G.IsIndexedFinkRelativeCalendarSelectable
      β U z W q r) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_harmonicTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ,
    G.indexedFinkRelativeSwitchError β U z W κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (fun t => q (κ t)), (fun t => r (κ t)), T₀,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed_relative β U z W hW κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact hharmonic (κ t) s who
  · intro t s who d
    exact hexcessive (κ t) s who d
  · exact hκ

/-- End-to-end bridge from the corrected calendar produced by the reference
hierarchy to a uniform equilibrium payoff.  All Bellman, switching,
on-profile, mixed-deviation, and history-dependent verification is discharged
here; only `IsIndexedFinkCorrectedCalendarSelectable` remains quantitative. -/
theorem isUniformEquilibriumPayoff_of_indexedFinkFixedPoints_correctedTarget
    (G : StochasticGame ι) [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (s₀ : G.State) (β : ℕ → ℝ) (U : ℝ) (hβ0 : ∀ n, 0 ≤ β n)
    (hβ1 : ∀ n, β n < 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : ℕ → G.finkDomain U) (W : G.State → Payoff ι)
    (hW : ∀ s who, |W s who| ≤ U)
    (R : ℕ → G.State → Payoff ι) (q : ℕ → ℝ)
    (hfix : ∀ n,
      G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n)
    (hclose : ∀ n s who, |G.finkValue (z n) s who - W s who| ≤ q n)
    (hselect : G.IsIndexedFinkCorrectedCalendarSelectable
      β U z W R q) :
    G.IsUniformEquilibriumPayoff s₀ (W s₀) := by
  apply G.isUniformEquilibriumPayoff_of_scheduledFink_correctedTarget s₀ W
  intro η hη
  obtain ⟨κ, T₀, hκ⟩ := hselect η hη
  refine ⟨indexedFinkDiscount β κ, G.indexedFinkProfile z κ,
    G.indexedFinkValue z κ, R ∘ κ,
    G.indexedFinkRelativeSwitchError β U z W κ,
    (fun t => finkScaledBiasBound β U (κ t)),
    (q ∘ κ), (fun t => ‖R (κ t)‖),
    (fun t => G.finkCorrectedTargetStepError W (R ∘ κ) (z ∘ κ) t),
    T₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact G.isDiscountedStationaryBellmanSchedule_indexedFink
      β U hβ0 hβ1 hpay z hfix κ
  · exact fun t => hβ1 (κ t)
  · exact G.isScheduledFinkSwitchBound_indexed_relative β U z W hW κ
  · exact G.abs_scheduledFinkBias_indexed_le β U hβ0 hβ1 z κ
  · intro t s who
    exact hclose (κ t) s who
  · intro t s who
    exact G.abs_finkBiasCoordinate_le_norm (R (κ t)) s who
  · intro t s who
    exact G.abs_fink_correctedTarget_onProfile_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who
  · intro t s who dev
    exact G.fink_correctedTarget_mixedDeviation_step_le_stepError
      W (R ∘ κ) (z ∘ κ) t s who dev
  · exact hκ

end StochasticGame
end GameTheory
