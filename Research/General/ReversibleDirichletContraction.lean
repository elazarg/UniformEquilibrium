import Mathlib

/-!
# Reversible Dirichlet contraction (Physics.md §7, upgrading E27)

This file formalizes the reversible Dirichlet-form identity and the uniform
`L2(π)` contraction under arbitrary switching of lazy reversible kernels that
share an invariant law `π` and a common spectral gap `γ`.  It upgrades the
exhaustive two-kernel experiment E27 (`experiments/common_reversible_dirichlet.py`)
to a general finite-state theorem.

Setup: a finite state space `S`, a strictly positive weight `π`, and a
row-stochastic kernel `P` that is reversible with respect to `π`
(`π x * P x y = π y * P y x` for all `x y`).  The Dirichlet energy of `P` is

  `E_P(f,f) = (1/2) * Σ_x Σ_y π x * P x y * (f y - f x)^2`,

and it equals `⟨f,fα_π - ⟨f,Pfα_π`.  A spectral-gap hypothesis
`γ * ‖f‖²_π ≤ E_P(f,f)` for mean-zero `f` then controls `⟨f,Pfα_π`.  For a
*lazy* kernel `P = (1/2)(I+Q)` with `Q` itself reversible and stochastic,
`P` is additionally positive semidefinite on `L2(π)`, which upgrades the
Poisson-type bound on `⟨f,Pfα_π` to a genuine norm contraction
`‖Pf‖²_π ≤ (1-γ)‖f‖²_π`.  Composing arbitrarily many such kernels (sharing
`π` and a *common* `γ`) contracts every mean-zero mode geometrically,
regardless of the switching schedule.

Nonclaims: laziness is essential for the norm-contraction statement — a
spectral gap alone bounds `⟨f,Pfα_π` but does not control the negative part
of the spectrum of a non-lazy reversible `P`, so `‖Pf‖²_π ≤ (1-γ)‖f‖²_π` can
fail without it.  This file contains no game content.  It also does not
address controlled kernels that fail to share one invariant law: E27's own
caveat that "general controlled kernels need not share an invariant law or
reversibility" is unaddressed here, by design.
-/

namespace Research.ReversibleDirichletContraction

open scoped BigOperators

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The `π`-weighted inner product `⟨f,gα_π = Σ_x π x * f x * g x`. -/
def wip (π : S → ℝ) (f g : S → ℝ) : ℝ := ∑ x, π x * f x * g x

/-- The `π`-weighted squared norm `‖f‖²_π = ⟨f,fα_π`. -/
def wnormSq (π : S → ℝ) (f : S → ℝ) : ℝ := wip π f f

/-- The action of a kernel on a function: `(Pf)(x) = Σ_y P x y * f y`. -/
def act (P : S → S → ℝ) (f : S → ℝ) : S → ℝ := fun x => ∑ y, P x y * f y

/-- The Dirichlet energy of a kernel `P` at `f`:
`E_P(f,f) = (1/2) * Σ_x Σ_y π x * P x y * (f y - f x)^2`. -/
noncomputable def dirichlet (π : S → ℝ) (P : S → S → ℝ) (f : S → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * P x y * (f y - f x) ^ 2

omit [DecidableEq S] in
/-- Reversibility plus row-stochasticity forces `π` to be the (left) invariant
law of `P`: `Σ_x π x * P x y = π y`. -/
theorem invariant_of_reversible (π : S → ℝ) (P : S → S → ℝ)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (y : S) : ∑ x, π x * P x y = π y := by
  have step : ∑ x, π x * P x y = ∑ x, π y * P y x :=
    Finset.sum_congr rfl fun x _ => hrev x y
  rw [step, ← Finset.mul_sum, hP1 y, mul_one]

omit [DecidableEq S] in
/-- The reversible Dirichlet identity: `E_P(f,f) = ‖f‖²_π - ⟨f,Pfα_π`. -/
theorem dirichlet_eq (π : S → ℝ) (P : S → S → ℝ)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (f : S → ℝ) :
    dirichlet π P f = wnormSq π f - wip π f (act P f) := by
  have hinv : ∀ y, ∑ x, π x * P x y = π y := invariant_of_reversible π P hP1 hrev
  have hA : ∑ x, ∑ y, π x * P x y * (f y) ^ 2 = wnormSq π f := by
    rw [Finset.sum_comm]
    have step : ∀ y : S, ∑ x, π x * P x y * (f y) ^ 2 = (∑ x, π x * P x y) * (f y) ^ 2 :=
      fun y => (Finset.sum_mul _ _ _).symm
    simp_rw [step, hinv]
    unfold wnormSq wip
    exact Finset.sum_congr rfl fun x _ => by ring
  have hB : ∑ x, ∑ y, π x * P x y * f x * f y = wip π f (act P f) := by
    unfold wip act
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hC : ∑ x, ∑ y, π x * P x y * (f x) ^ 2 = wnormSq π f := by
    have step : ∀ x : S, ∑ y, π x * P x y * (f x) ^ 2 = π x * (f x) ^ 2 := by
      intro x
      have hstep : ∑ y, π x * P x y * (f x) ^ 2 = (∑ y, P x y) * (π x * (f x) ^ 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun y _ => by ring
      rw [hstep, hP1 x, one_mul]
    simp_rw [step]
    unfold wnormSq wip
    exact Finset.sum_congr rfl fun x _ => by ring
  have inner : ∀ x : S, ∑ y, π x * P x y * (f y - f x) ^ 2
      = (∑ y, π x * P x y * (f y) ^ 2) - 2 * (∑ y, π x * P x y * f x * f y)
        + (∑ y, π x * P x y * (f x) ^ 2) := by
    intro x
    have pointwise : ∀ y : S, π x * P x y * (f y - f x) ^ 2
        = π x * P x y * (f y) ^ 2 - 2 * (π x * P x y * f x * f y) + π x * P x y * (f x) ^ 2 := by
      intro y; ring
    simp_rw [pointwise]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have outer :
      ∑ x, ((∑ y, π x * P x y * (f y) ^ 2) - 2 * (∑ y, π x * P x y * f x * f y)
        + (∑ y, π x * P x y * (f x) ^ 2))
      = (∑ x, ∑ y, π x * P x y * (f y) ^ 2) - 2 * (∑ x, ∑ y, π x * P x y * f x * f y)
        + (∑ x, ∑ y, π x * P x y * (f x) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold dirichlet
  simp_rw [inner]
  rw [outer, hA, hB, hC]
  ring

omit [DecidableEq S] in
/-- Under a common spectral gap `γ`, mean-zero functions satisfy
`⟨f,Pfα_π ≤ (1-γ)‖f‖²_π`. -/
theorem wip_act_le_of_gap (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hgap : ∀ f : S → ℝ, ∑ x, π x * f x = 0 → γ * wnormSq π f ≤ dirichlet π P f)
    (f : S → ℝ) (hf0 : ∑ x, π x * f x = 0) :
    wip π f (act P f) ≤ (1 - γ) * wnormSq π f := by
  have heq := dirichlet_eq π P hP1 hrev f
  have hg := hgap f hf0
  linarith

omit [DecidableEq S] in
/-- Reversibility (via invariance of `π`) shows `act P` preserves the
mean-zero subspace. -/
theorem act_preserves_meanZero (π : S → ℝ) (P : S → S → ℝ)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (f : S → ℝ) (hf0 : ∑ x, π x * f x = 0) :
    ∑ x, π x * act P f x = 0 := by
  have hinv : ∀ y, ∑ x, π x * P x y = π y := invariant_of_reversible π P hP1 hrev
  have step1 : ∑ x, π x * act P f x = ∑ x, ∑ y, π x * P x y * f y := by
    unfold act
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have step2 : ∑ x, ∑ y, π x * P x y * f y = ∑ y, π y * f y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hinv y, Finset.sum_mul]
  rw [step1, step2, hf0]

omit [DecidableEq S] in
/-- `act P` is self-adjoint for `wip π` when `P` is reversible with respect
to `π`. -/
theorem wip_act_symm (π : S → ℝ) (P : S → S → ℝ)
    (hrev : ∀ x y, π x * P x y = π y * P y x)
    (f g : S → ℝ) :
    wip π (act P f) g = wip π f (act P g) := by
  have lhs : wip π (act P f) g = ∑ x, ∑ y, π x * P x y * f y * g x := by
    unfold wip act
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  have rhs : wip π f (act P g) = ∑ x, ∑ y, π x * P x y * g y * f x := by
    unfold wip act
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have swap1 : ∑ x, ∑ y, π x * P x y * f y * g x = ∑ x, ∑ y, π y * P y x * g x * f y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hrev x y]; ring
  have swap2 : ∑ x, ∑ y, π y * P y x * g x * f y = ∑ x, ∑ y, π x * P x y * g y * f x := by
    rw [Finset.sum_comm]
  rw [lhs, rhs, swap1, swap2]

omit [DecidableEq S] in
/-- Discrete weighted Jensen/Cauchy-Schwarz inequality: for a probability
weight `w` (nonnegative, summing to one), `(Σ w*v)^2 ≤ Σ w*v^2`.  Proved
directly from the nonnegativity of `Σ_y Σ_z w y * w z * (v y - v z)^2`. -/
theorem sq_sum_le_sum_sq_of_prob (w v : S → ℝ)
    (hw0 : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) :
    (∑ y, w y * v y) ^ 2 ≤ ∑ y, w y * (v y) ^ 2 := by
  have hTA : ∑ y, ∑ z, w y * w z * (v y) ^ 2 = ∑ y, w y * (v y) ^ 2 := by
    have step : ∀ y : S, ∑ z, w y * w z * (v y) ^ 2 = (w y * (v y) ^ 2) * ∑ z, w z := by
      intro y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    simp_rw [step, hw1, mul_one]
  have hTC : ∑ y, ∑ z, w y * w z * (v z) ^ 2 = ∑ y, w y * (v y) ^ 2 := by
    rw [Finset.sum_comm]
    have step : ∀ z : S, ∑ y, w y * w z * (v z) ^ 2 = (w z * (v z) ^ 2) * ∑ y, w y := by
      intro z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    simp_rw [step, hw1, mul_one]
  have hTB : ∑ y, ∑ z, w y * w z * v y * v z = (∑ y, w y * v y) ^ 2 := by
    have step : ∀ y : S, ∑ z, w y * w z * v y * v z = (w y * v y) * ∑ z, w z * v z := by
      intro y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    simp_rw [step]
    rw [← Finset.sum_mul, pow_two]
  have hnonneg : 0 ≤ ∑ y, ∑ z, w y * w z * (v y - v z) ^ 2 := by
    refine Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ => ?_
    have hwyz : 0 ≤ w y * w z := mul_nonneg (hw0 y) (hw0 z)
    positivity
  have hsplit : ∑ y, ∑ z, w y * w z * (v y - v z) ^ 2
      = 2 * (∑ y, ∑ z, w y * w z * (v y) ^ 2) - 2 * (∑ y, ∑ z, w y * w z * v y * v z) := by
    have inner : ∀ y : S, ∑ z, w y * w z * (v y - v z) ^ 2
        = ∑ z, w y * w z * (v y) ^ 2 - 2 * (∑ z, w y * w z * v y * v z)
          + ∑ z, w y * w z * (v z) ^ 2 := by
      intro y
      have pointwise : ∀ z : S, w y * w z * (v y - v z) ^ 2
          = w y * w z * (v y) ^ 2 - 2 * (w y * w z * v y * v z) + w y * w z * (v z) ^ 2 := by
        intro z; ring
      simp_rw [pointwise]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp_rw [inner]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hTC, ← hTA]
    ring
  linarith [hnonneg, hsplit, hTA, hTB]

omit [DecidableEq S] in
/-- For any reversible stochastic `Q` (sharing `π`), `act Q` does not increase
the `π`-weighted norm. -/
theorem wnormSq_act_le (π : S → ℝ) (Q : S → S → ℝ) (hπ : ∀ x, 0 < π x)
    (hQ0 : ∀ x y, 0 ≤ Q x y) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (hQrev : ∀ x y, π x * Q x y = π y * Q y x)
    (f : S → ℝ) :
    wnormSq π (act Q f) ≤ wnormSq π f := by
  have hinv : ∀ y, ∑ x, π x * Q x y = π y := invariant_of_reversible π Q hQ1 hQrev
  have step1 : wnormSq π (act Q f) ≤ ∑ x, ∑ y, π x * Q x y * (f y) ^ 2 := by
    unfold wnormSq wip act
    refine Finset.sum_le_sum fun x _ => ?_
    have hjensen : (∑ y, Q x y * f y) ^ 2 ≤ ∑ y, Q x y * (f y) ^ 2 :=
      sq_sum_le_sum_sq_of_prob (Q x) f (hQ0 x) (hQ1 x)
    have hπx : 0 ≤ π x := le_of_lt (hπ x)
    have hexpand :
        π x * (∑ y, Q x y * f y) * (∑ y, Q x y * f y) =
          π x * (∑ y, Q x y * f y) ^ 2 := by
      ring
    rw [hexpand]
    calc π x * (∑ y, Q x y * f y) ^ 2 ≤ π x * ∑ y, Q x y * (f y) ^ 2 :=
          mul_le_mul_of_nonneg_left hjensen hπx
      _ = ∑ y, π x * Q x y * (f y) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  have step2 : ∑ x, ∑ y, π x * Q x y * (f y) ^ 2 = wnormSq π f := by
    rw [Finset.sum_comm]
    have hstep : ∀ y : S, ∑ x, π x * Q x y * (f y) ^ 2 = (∑ x, π x * Q x y) * (f y) ^ 2 :=
      fun y => (Finset.sum_mul _ _ _).symm
    simp_rw [hstep, hinv]
    unfold wnormSq wip
    exact Finset.sum_congr rfl fun x _ => by ring
  linarith [step1, step2]

/-- A lazy kernel `P = (1/2)(I+Q)` acts as `(1/2)(f + Qf)` pointwise. -/
theorem act_lazy_eq (P Q : S → S → ℝ)
    (hPQ : ∀ x y, P x y = (1 / 2) * (if x = y then 1 else 0) + (1 / 2) * Q x y)
    (f : S → ℝ) (x : S) :
    act P f x = (1 / 2) * (f x + act Q f x) := by
  unfold act
  have step : ∀ y : S, P x y * f y
      = (1 / 2) * ((if x = y then (1 : ℝ) else 0) * f y) + (1 / 2) * (Q x y * f y) := by
    intro y; rw [hPQ x y]; ring
  simp_rw [step]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hind : ∑ y, (if x = y then (1 : ℝ) else 0) * f y = f x := by simp
  rw [hind, mul_add]

/-- Laziness upgrades the Poisson-type bound `⟨f,Pfα_π` into a genuine norm
bound: `‖Pf‖²_π ≤ ⟨f,Pfα_π`.  Algebraically, with `P = (1/2)(I+Q)`,
`4(⟨f,Pfα_π - ‖Pf‖²_π) = ‖f‖²_π - ‖Qf‖²_π ≥ 0` by `wnormSq_act_le`. -/
theorem wnormSq_act_le_wip_act_of_lazy (π : S → ℝ) (P Q : S → S → ℝ) (hπ : ∀ x, 0 < π x)
    (hQ0 : ∀ x y, 0 ≤ Q x y) (hQ1 : ∀ x, ∑ y, Q x y = 1)
    (hQrev : ∀ x y, π x * Q x y = π y * Q y x)
    (hPQ : ∀ x y, P x y = (1 / 2) * (if x = y then 1 else 0) + (1 / 2) * Q x y)
    (f : S → ℝ) :
    wnormSq π (act P f) ≤ wip π f (act P f) := by
  have hPeq : ∀ x, act P f x = (1 / 2) * (f x + act Q f x) := act_lazy_eq P Q hPQ f
  have hQle : wnormSq π (act Q f) ≤ wnormSq π f := wnormSq_act_le π Q hπ hQ0 hQ1 hQrev f
  have pointwise : ∀ x : S,
      π x * f x * act P f x - π x * (act P f x) * (act P f x)
      = (1 / 4) * (π x * f x * f x) - (1 / 4) * (π x * (act Q f x) * (act Q f x)) := by
    intro x; rw [hPeq x]; ring
  have lhs_eq : wip π f (act P f) - wnormSq π (act P f)
      = ∑ x, (π x * f x * act P f x - π x * (act P f x) * (act P f x)) := by
    unfold wnormSq wip
    rw [← Finset.sum_sub_distrib]
  have rhs_split : ∑ x, (π x * f x * act P f x - π x * (act P f x) * (act P f x))
      = ∑ x, ((1 / 4) * (π x * f x * f x) - (1 / 4) * (π x * (act Q f x) * (act Q f x))) :=
    Finset.sum_congr rfl fun x _ => pointwise x
  have rhs_eq : ∑ x, ((1 / 4) * (π x * f x * f x) - (1 / 4) * (π x * (act Q f x) * (act Q f x)))
      = (1 / 4) * (wnormSq π f - wnormSq π (act Q f)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    unfold wnormSq wip
    ring
  have key :
      wip π f (act P f) - wnormSq π (act P f) =
        (1 / 4) * (wnormSq π f - wnormSq π (act Q f)) := by
    rw [lhs_eq, rhs_split, rhs_eq]
  linarith [key, hQle]

/-- Main lazy contraction theorem: for a lazy, reversible, row-stochastic `P`
sharing `π` with a common spectral gap `γ`, mean-zero functions contract in
`L2(π)` by a factor of `1-γ`. -/
theorem wnormSq_act_le_of_lazy_of_gap (π : S → ℝ) (P : S → S → ℝ) (γ : ℝ)
    (hπ : ∀ x, 0 < π x)
    (hP1 : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∃ Q : S → S → ℝ, (∀ x y, 0 ≤ Q x y) ∧ (∀ x, ∑ y, Q x y = 1) ∧
      (∀ x y, π x * Q x y = π y * Q y x) ∧
      ∀ x y, P x y = (1 / 2) * (if x = y then 1 else 0) + (1 / 2) * Q x y)
    (hgap : ∀ f : S → ℝ, ∑ x, π x * f x = 0 → γ * wnormSq π f ≤ dirichlet π P f)
    (f : S → ℝ) (hf0 : ∑ x, π x * f x = 0) :
    wnormSq π (act P f) ≤ (1 - γ) * wnormSq π f := by
  obtain ⟨Q, hQ0, hQ1, hQrev, hPQ⟩ := hlazy
  have hpsd : wnormSq π (act P f) ≤ wip π f (act P f) :=
    wnormSq_act_le_wip_act_of_lazy π P Q hπ hQ0 hQ1 hQrev hPQ f
  have hgapbound : wip π f (act P f) ≤ (1 - γ) * wnormSq π f :=
    wip_act_le_of_gap π P γ hP1 hrev hgap f hf0
  linarith [hpsd, hgapbound]

/-- Iterated action of a time-varying sequence of kernels:
`actSeq Ps 0 f = f` and `actSeq Ps (n+1) f = act (Ps n) (actSeq Ps n f)`. -/
def actSeq (Ps : ℕ → S → S → ℝ) : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | n + 1, f => act (Ps n) (actSeq Ps n f)

/-- Uniform contraction under arbitrary switching: if every kernel in the
sequence `Ps` is lazy, row-stochastic, and reversible with the same `π`, and
they share a common spectral gap `γ ∈ [0,1]`, then every mean-zero mode
contracts geometrically with rate `1-γ`, regardless of the switching
schedule. -/
theorem wnormSq_iterSwitch_le (π : S → ℝ) (Ps : ℕ → S → S → ℝ) (γ : ℝ)
    (hπ : ∀ x, 0 < π x)
    (hP1 : ∀ n x, ∑ y, Ps n x y = 1)
    (hrev : ∀ n x y, π x * Ps n x y = π y * Ps n y x)
    (hlazy : ∀ n, ∃ Q : S → S → ℝ, (∀ x y, 0 ≤ Q x y) ∧ (∀ x, ∑ y, Q x y = 1) ∧
      (∀ x y, π x * Q x y = π y * Q y x) ∧
      ∀ x y, Ps n x y = (1 / 2) * (if x = y then 1 else 0) + (1 / 2) * Q x y)
    (hgap : ∀ n, ∀ f : S → ℝ, ∑ x, π x * f x = 0 → γ * wnormSq π f ≤ dirichlet π (Ps n) f)
    (_hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (f : S → ℝ) (hf0 : ∑ x, π x * f x = 0) (n : ℕ) :
    wnormSq π (actSeq Ps n f) ≤ (1 - γ) ^ n * wnormSq π f := by
  have main : ∀ m : ℕ, (∑ x, π x * actSeq Ps m f x = 0) ∧
      wnormSq π (actSeq Ps m f) ≤ (1 - γ) ^ m * wnormSq π f := by
    intro m
    induction m with
    | zero => refine ⟨hf0, ?_⟩; simp [actSeq]
    | succ m ih =>
        obtain ⟨ihmz, ihnorm⟩ := ih
        have hmz' : ∑ x, π x * act (Ps m) (actSeq Ps m f) x = 0 :=
          act_preserves_meanZero π (Ps m) (hP1 m) (hrev m) (actSeq Ps m f) ihmz
        have hcontract :
            wnormSq π (act (Ps m) (actSeq Ps m f)) ≤ (1 - γ) * wnormSq π (actSeq Ps m f) :=
          wnormSq_act_le_of_lazy_of_gap π (Ps m) γ hπ (hP1 m) (hrev m) (hlazy m) (hgap m)
            (actSeq Ps m f) ihmz
        refine ⟨hmz', ?_⟩
        have hnonneg1mγ : (0 : ℝ) ≤ 1 - γ := by linarith
        calc wnormSq π (actSeq Ps (m + 1) f)
            = wnormSq π (act (Ps m) (actSeq Ps m f)) := by rw [actSeq]
          _ ≤ (1 - γ) * wnormSq π (actSeq Ps m f) := hcontract
          _ ≤ (1 - γ) * ((1 - γ) ^ m * wnormSq π f) :=
              mul_le_mul_of_nonneg_left ihnorm hnonneg1mγ
          _ = (1 - γ) ^ (m + 1) * wnormSq π f := by ring
  exact (main n).2

end Research.ReversibleDirichletContraction
