/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib

/-!
# Entropy production of a stationary edge flow

For a finite Markov chain, the stationary entropy-production rate is written as
stationary entropy-production rate of a finite Markov chain as

`EP(P, π) = ∑_{x,y} F(x,y) log (F(x,y) / F(y,x))`, where `F(x,y) = π(x) P(x,y)`

is the stationary edge flow, and claims it is nonnegative and vanishes at detailed balance.
Numerical evidence near detailed balance in a biased cyclic chain motivates this
file. It upgrades that observation to a machine-checked theorem, working with edge
flows directly (no measure-theoretic
`klDiv`, no stationarity equation `∑ₓ F x y = ∑ₓ F y x`, no total-mass normalization) to keep the
argument elementary.

## Setup and the honest boundary of the junk-value formalization

`EP` is defined for an arbitrary edge-weight function `F : S → S → ℝ` on a finite type `S`,

`EP F = ∑ x, ∑ y, F x y * Real.log (F x y / F y x)`,

using Lean/Mathlib's junk conventions `a / 0 = 0` and `Real.log 0 = 0`. **This is the one
place a naive reading of the survey formula goes wrong.** Physically, a directed edge `x → y`
that carries flow while the reverse edge `y → x` carries none should contribute `+∞` to entropy
production (the reversed path is *never* observed, which is maximally informative), not `0`.
But under the stated junk conventions, a term with `F x y > 0 = F y x` evaluates to
`F x y * Real.log (F x y / 0) = F x y * Real.log 0 = F x y * 0 = 0` — silently the *wrong* value.
Worse, its mirror term `F y x * Real.log (F y x / F x y) = 0 * Real.log 0 = 0` is *also* `0`
rather than reflecting any deficit, so nothing elsewhere in the sum compensates: a chain with
`F x y > 0 = F y x` on one edge and detailed balance everywhere else would make the naive,
`hsym`-free reading of `EP` equal `0`, not `+∞`, silently erasing genuine irreversibility. We
therefore impose the **support-symmetry** hypothesis

`hsym : ∀ x y, F y x = 0 → F x y = 0`

(the reversed flow is absolutely continuous with respect to the forward flow, edgewise) on every
theorem that needs it. Without `hsym`, the formalized `EP` is *not* the physical entropy
production and its nonnegativity can fail; `hsym` is the price of using real-number junk values
instead of `EReal`/`ENNReal`, and it is exactly the "detailed-balance-support" condition under
which the survey's claim is honest.

We also state nonnegativity of `F` (`hF0`) directly on `F` rather than deriving it from
`0 ≤ π` and `0 ≤ P`: this is the more general and more elementary route (it applies to any
nonnegative edge weighting, not just products), and it is all `EP_nonneg` actually needs. The
canonical instance — `F` arising as the stationary edge flow `π(x) P(x,y)` of a chain with
nonnegative stationary weights `π` and nonnegative kernel `P` — is recorded separately as
`stationaryEdgeFlow` together with `stationaryEdgeFlow_nonneg`, so that `hF0` is a one-line
`mul_nonneg` away whenever it is needed in that shape.

## What is proved

* `EP_nonneg` : `0 ≤ EP F` given `hF0` and `hsym`. Route: the termwise bound
  `F x y - F y x ≤ F x y * Real.log (F x y / F y x)` (from `Real.one_sub_inv_le_log_of_pos`,
  i.e. `log t ≥ 1 - 1/t`, applied to `t = F x y / F y x`), summed over all ordered pairs and
  combined with `∑ x, ∑ y, (F x y - F y x) = 0` (a pure re-indexing fact, `Finset.sum_comm`,
  needing no hypothesis on `F` at all). No total-mass or stationarity hypothesis is used.
* `EP_eq_zero_of_detailedBalance` : if `∀ x y, F x y = F y x` then `EP F = 0` (every ratio is
  `1`, `Real.log 1 = 0`; the `F x y = F y x = 0` terms are handled by the junk convention
  `0 * Real.log 0 = 0`, which is exactly the physically correct value `0` in that case since
  there is no flow on either direction of the edge to begin with).
* `EP_pair_form` : the symmetrized "current × affinity" rewrite
  `EP F = (1/2) * ∑ x, ∑ y, (F x y - F y x) * Real.log (F x y / F y x)`. This turns out to hold
  **unconditionally** — no `hF0`, no `hsym` — because the key step, `Real.log (a / b)
  = -Real.log (b / a)`, holds for *all* reals `a, b` under the junk conventions (`Real.log_inv`
  and `inv_div` are both unconditional). This is a genuine strengthening of the brief, which
  anticipated needing `hsym` here; we record the stronger statement and note the weakening
  nowhere occurs.
* `detailedBalance_of_EP_eq_zero` : the converse, `EP F = 0 → ∀ x y, F x y = F y x`, given only
  `hF0` and `hsym` (no separate strict-positivity hypothesis on `π`, unlike the brief's
  anticipated statement — the case `F y x = 0` is handled directly by `hsym`, and the case
  `F y x > 0, F x y = 0` is ruled out automatically because it would force a *strictly positive*
  contribution to `EP`, contradicting `EP F = 0`). The equality case of the termwise log bound
  (`Real.log t = 1 - 1/t → t = 1` for `t > 0`) is handled via the strict companion inequality
  `Real.log_lt_sub_one_of_pos`. This is item 3 from the brief, proved in the stronger
  hsym-and-hF0-only form rather than dropped.

## Nonclaims

* **No monitoring or strategic consequence.** This file proves a scalar inequality about a
  static edge flow; it says nothing about detection, punishment, or credibility debt. The
  scale fence between a linear deviation and its (generically quadratic) information signature
  has a single-observation core in the companion binary-KL development, while
  the process-level picture (current, entropy production, tilted pressure, and
  linear debt all scaling near
  detailed balance) is not revisited or strengthened here.
* **No connection to `condEntropy` or Mathlib's `klDiv`.** `EP` is defined and proved directly on
  `Finset.sum`, with no detour through conditional entropy or measure-theoretic KL divergence
  (unlike `InformationTheory.gibbs_sum_log_ratio_nonneg_of_ac`, whose statement was consulted but
  whose proof route was not reused, since that lemma is normalized (`∑ p = 1`, `∑ q ≤ 1`) for a
  single probability-mass-function pair, while `EP` is an unnormalized double sum over edges).
* **No stationarity equation.** `π` and `P` never appear except in the docstring-only
  `stationaryEdgeFlow` definition; nothing here assumes `∀ y, ∑ x, F x y = ∑ x, F y x`
  (stationarity of `π` under `P`).
-/


noncomputable section

namespace Research.EntropyProduction

variable {S : Type} [Fintype S]

/-! ## The canonical instance: edge flow from stationary weights and a kernel -/

/-- The stationary edge flow `F(x,y) = π(x) P(x,y)` of a chain with stationary law `π` and
transition kernel `P`. Recorded for documentation purposes and to ground `hF0` in the main
theorems below; the main theorems are stated for an arbitrary `F : S → S → ℝ`, not specifically
for this product form. -/
def stationaryEdgeFlow (π : S → ℝ) (P : S → S → ℝ) : S → S → ℝ := fun x y => π x * P x y

omit [Fintype S] in
/-- `hF0` is immediate for the canonical instance when `π` and `P` are themselves nonnegative. -/
theorem stationaryEdgeFlow_nonneg {π : S → ℝ} {P : S → S → ℝ}
    (hπ0 : ∀ x, 0 ≤ π x) (hP0 : ∀ x y, 0 ≤ P x y) :
    ∀ x y, 0 ≤ stationaryEdgeFlow π P x y :=
  fun x y => mul_nonneg (hπ0 x) (hP0 x y)

/-! ## Entropy production -/

/-- Entropy production of an edge-weight function `F`, in the finite edge-flow form of
the finite edge-flow form:

`EP F = ∑ x, ∑ y, F x y * Real.log (F x y / F y x)`.

Meaningful (as the physical entropy production) only under the support-symmetry hypothesis
`hsym` used throughout this file; see the module docstring. -/
def EP (F : S → S → ℝ) : ℝ :=
  ∑ x, ∑ y, F x y * Real.log (F x y / F y x)

/-! ## Elementary log lemmas -/

/-- `Real.log (a / b) = -Real.log (b / a)` for *all* reals `a, b`, no positivity needed: both
`Real.log_inv` and `inv_div` are unconditional under the junk conventions `x⁻¹ = 0` at `x = 0`
and `Real.log 0 = 0`. This is the engine behind `EP_pair_form`. -/
private theorem log_div_eq_neg_log_div_swap (a b : ℝ) :
    Real.log (a / b) = -Real.log (b / a) := by
  rw [← Real.log_inv, inv_div]

/-- The termwise bound behind Gibbs' inequality, tolerant of `b = 0` under the absolute-continuity
hypothesis `hab`: for `a, b ≥ 0` with `b = 0 → a = 0`, `a - b ≤ a * Real.log (a / b)`. When
`b = 0` (hence `a = 0` by `hab`) both sides are `0`. When `a = 0 < b` the right side is `0`
and the left side is `-b ≤ 0`. When `a, b > 0` this is `Real.one_sub_inv_le_log_of_pos` applied
to `t = a / b`, rearranged. -/
private theorem sub_le_mul_log_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) : a - b ≤ a * Real.log (a / b) := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · have ha0 : a = 0 := hab hb0.symm
    simp [ha0, ← hb0]
  · rcases ha.eq_or_lt with ha0 | hapos
    · simpa [← ha0] using hb
    · have ht : 0 < a / b := div_pos hapos hbpos
      have hlog : 1 - (a / b)⁻¹ ≤ Real.log (a / b) := Real.one_sub_inv_le_log_of_pos ht
      rw [inv_div] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog hapos.le
      have heq : a * (1 - b / a) = a - b := by
        field_simp
      rw [heq] at hmul
      exact hmul

/-! ## A re-indexing fact needed by both directions -/

/-- Summing an antisymmetrized edge weight over all ordered pairs gives `0`: purely a
re-indexing fact (`Finset.sum_comm`), true for *any* `F`, with no hypotheses at all. -/
theorem sum_diff_eq_zero (F : S → S → ℝ) : ∑ x, ∑ y, (F x y - F y x) = (0 : ℝ) := by
  have hswap : ∑ x, ∑ y, F y x = ∑ x, ∑ y, F x y := Finset.sum_comm
  simp_rw [Finset.sum_sub_distrib]
  rw [hswap, sub_self]

/-! ## Nonnegativity -/

/-- Entropy production is nonnegative. No total-mass or stationarity hypothesis is used: the
proof is purely the termwise Gibbs-style bound `sub_le_mul_log_div`, summed and combined with
`sum_diff_eq_zero`. -/
theorem EP_nonneg (F : S → S → ℝ) (hF0 : ∀ x y, 0 ≤ F x y)
    (hsym : ∀ x y, F y x = 0 → F x y = 0) : 0 ≤ EP F := by
  have hterm : ∀ x y, F x y - F y x ≤ F x y * Real.log (F x y / F y x) :=
    fun x y => sub_le_mul_log_div (hF0 x y) (hF0 y x) (hsym x y)
  have hsum : ∑ x, ∑ y, (F x y - F y x) ≤ ∑ x, ∑ y, F x y * Real.log (F x y / F y x) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
  rw [sum_diff_eq_zero] at hsum
  exact hsum

/-! ## Vanishing at detailed balance -/

/-- Entropy production vanishes at detailed balance (`F x y = F y x` for every edge). -/
theorem EP_eq_zero_of_detailedBalance (F : S → S → ℝ) (hdb : ∀ x y, F x y = F y x) :
    EP F = 0 := by
  have hterm : ∀ x y, F x y * Real.log (F x y / F y x) = 0 := by
    intro x y
    rcases eq_or_ne (F y x) 0 with h0 | hne
    · have hxy0 : F x y = 0 := by rw [hdb x y, h0]
      simp [hxy0]
    · have h1 : F x y / F y x = 1 := by rw [hdb x y]; exact div_self hne
      simp [h1]
  change ∑ x, ∑ y, F x y * Real.log (F x y / F y x) = 0
  simp [hterm]

/-! ## The current-times-affinity form -/

/-- The symmetrized "current × affinity" rewrite of entropy production. Holds unconditionally
(no `hF0`, no `hsym`): the brief anticipated needing support symmetry here, but the log-flip
identity `log_div_eq_neg_log_div_swap` needs no hypothesis, so neither does this. -/
theorem EP_pair_form (F : S → S → ℝ) :
    EP F = (1 / 2) * ∑ x, ∑ y, (F x y - F y x) * Real.log (F x y / F y x) := by
  have hpt : ∀ x y, (F x y - F y x) * Real.log (F x y / F y x)
      = F x y * Real.log (F x y / F y x) + F y x * Real.log (F y x / F x y) := by
    intro x y
    rw [log_div_eq_neg_log_div_swap (F x y) (F y x)]
    ring
  have hcomm : ∑ x, ∑ y, F y x * Real.log (F y x / F x y)
      = ∑ x, ∑ y, F x y * Real.log (F x y / F y x) := Finset.sum_comm
  change ∑ x, ∑ y, F x y * Real.log (F x y / F y x)
      = (1 / 2) * ∑ x, ∑ y, (F x y - F y x) * Real.log (F x y / F y x)
  simp_rw [hpt, Finset.sum_add_distrib, hcomm]
  ring

/-! ## The converse -/

/-- Equality case of `Real.one_sub_inv_le_log_of_pos`: if `Real.log t = 1 - t⁻¹` for `t > 0`,
then `t = 1`. Proved via the strict companion `Real.log_lt_sub_one_of_pos` applied to `t⁻¹`. -/
private theorem eq_one_of_one_sub_inv_eq_log {t : ℝ} (ht : 0 < t)
    (heq : Real.log t = 1 - t⁻¹) : t = 1 := by
  by_contra hne
  have hne' : t⁻¹ ≠ 1 := inv_eq_one.not.mpr hne
  have hstrict : Real.log t⁻¹ < t⁻¹ - 1 :=
    Real.log_lt_sub_one_of_pos (inv_pos.2 ht) hne'
  rw [Real.log_inv] at hstrict
  linarith

/-- Equality case of `sub_le_mul_log_div`: if `a * Real.log (a / b) = a - b` (together with
`a, b ≥ 0` and support symmetry `hab`) then `a = b`. -/
private theorem eq_of_diff_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) (heq : a * Real.log (a / b) = a - b) : a = b := by
  rcases hb.eq_or_lt with hb0 | hbpos
  · have ha0 : a = 0 := hab hb0.symm
    rw [ha0, ← hb0]
  · rcases ha.eq_or_lt with ha0 | hapos
    · exfalso
      have ha0' : a = 0 := ha0.symm
      rw [ha0'] at heq
      simp at heq
      linarith
    · have ht : 0 < a / b := div_pos hapos hbpos
      have hane : a ≠ 0 := ne_of_gt hapos
      have hrw : a * (1 - b / a) = a - b := by field_simp
      have hcancel : a * Real.log (a / b) = a * (1 - b / a) := heq.trans hrw.symm
      have hlogeq : Real.log (a / b) = 1 - b / a := mul_left_cancel₀ hane hcancel
      have hlogeq' : Real.log (a / b) = 1 - (a / b)⁻¹ := by
        rw [inv_div]; exact hlogeq
      have ht1 : a / b = 1 := eq_one_of_one_sub_inv_eq_log ht hlogeq'
      exact (div_eq_one_iff_eq hbpos.ne').mp ht1

/-- The converse of `EP_nonneg`: if entropy production vanishes, the flow is in detailed
balance. Proved under only `hF0` and `hsym` — no separate strict-positivity hypothesis is
needed, strengthening the brief's anticipated statement (see the module docstring). -/
theorem detailedBalance_of_EP_eq_zero (F : S → S → ℝ) (hF0 : ∀ x y, 0 ≤ F x y)
    (hsym : ∀ x y, F y x = 0 → F x y = 0) (hEP : EP F = 0) :
    ∀ x y, F x y = F y x := by
  have hdiff_nonneg : ∀ x y, 0 ≤ F x y * Real.log (F x y / F y x) - (F x y - F y x) := by
    intro x y
    linarith [sub_le_mul_log_div (hF0 x y) (hF0 y x) (hsym x y)]
  have hsum_diff :
      ∑ x, ∑ y, (F x y * Real.log (F x y / F y x) - (F x y - F y x)) = EP F := by
    have hswap : ∑ x, ∑ y, F y x = ∑ x, ∑ y, F x y := Finset.sum_comm
    change ∑ x, ∑ y, (F x y * Real.log (F x y / F y x) - (F x y - F y x))
        = ∑ x, ∑ y, F x y * Real.log (F x y / F y x)
    simp_rw [Finset.sum_sub_distrib]
    rw [hswap]
    ring
  have hsum0 :
      ∑ x, ∑ y, (F x y * Real.log (F x y / F y x) - (F x y - F y x)) = 0 := by
    rw [hsum_diff, hEP]
  have houter := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun y _ => hdiff_nonneg x y)).1 hsum0
  intro x y
  have hinner := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => hdiff_nonneg x y)).1 (houter x (Finset.mem_univ x))
  have h0 := hinner y (Finset.mem_univ y)
  have heq : F x y * Real.log (F x y / F y x) = F x y - F y x := by linarith
  exact eq_of_diff_eq_zero (hF0 x y) (hF0 y x) (hsym x y) heq

end Research.EntropyProduction
