/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.BigOperators.Field
import MathUE.AnalyticOrderComparison
import MathUE.PMFProduct.CoalitionMass

/-!
# Valuations of the independence model along a monomial curve

`Math.PMFProduct.coalitionMass x S = (∏ i ∈ S, x i) * ∏ i ∈ Sᶜ, (1 - x i)` is the
mass that the product of independent Bernoulli marginals `x` puts on the event
"exactly the coordinates in `S` act". As a function of `x` it is the Bernstein
parameterization of the independence model: the binary independence model of
algebraic statistics, the Segre (toric) parameterization of the simplex on `2 ^ ι`
(Sullivant, *Algebraic Statistics*, Ch. 6). This file studies its behaviour along
the one-parameter monomial curve

`x i = p ^ α i`, `α : ι → ℕ`,

as `p ↓ 0`. Substituting a monomial curve for the parameters is a tropical
degeneration; the induced order of vanishing is the valuation, or tropicalization,
of the coordinate.

## Main definitions

* `powerHazard α p` — the monomial curve `i ↦ p ^ α i`; also called a one-parameter
  degeneration, or a rate hierarchy with exponents `α`.
* `coalitionValuation α S = ∑ i ∈ S, α i` — the valuation of the coalition
  coordinate; the tropicalization of `coalitionMass` in the all-small chart.
* `coalitionCofactor α S p = ∏ i ∈ Sᶜ, (1 - p ^ α i)` — the unit cofactor.

## Main results

* `coalitionMass_powerHazard` — the *exact* factorization
  `coalitionMass (powerHazard α p) S = p ^ coalitionValuation α S * coalitionCofactor α S p`.
  Everything below is a corollary of this identity together with
  `tendsto_coalitionCofactor_one`, which says the cofactor is a unit at `p = 0`.
* `tendsto_coalitionMass_div_nhds_zero` and `tendsto_coalitionMass_div_atTop` — the
  comparison principle: strictly larger valuation means asymptotically negligible mass.
* `tendsto_sum_coalitionMass_div_nhds_zero` — leading-coalition selection (leading-term
  extraction): within a finite family of coalitions, the total mass of the
  non-minimizing members is negligible against the mass of a minimizer.
* `coalitionLeadingOrderJet` — the same data packaged as a `Math.LeadingOrderJet`, which
  exposes the normalized-share statements of `MathUE/AnalyticOrderComparison.lean`
  (`Math.LeadingOrderJet.tendsto_div_sum` and friends) for coalition masses.

## Scope

Exponents are natural numbers, which keeps the whole development elementary: the
valuation is a natural number and `p ^ α i` is an ordinary monomial. The statements
are the same over a Hahn or Puiseux valued field with real exponents, with `p ^ α i`
read as `Real.rpow` and the valuation taking values in the ordered value group; that
generality is not developed here.

Coordinates with `α i = 0` are not silently excluded. Such a coordinate contributes a
unit factor `p ^ 0 = 1` when it lies inside the coalition, but a vanishing factor
`1 - p ^ 0 = 0` when it lies outside, which annihilates the coalition mass identically
(`coalitionMass_powerHazard_eq_zero_of_exponent_eq_zero`). The asymptotic statements
therefore carry the explicit hypothesis that the exponents are nonzero off the
coalitions being compared.

Varying `α` partitions exponent space into the polyhedral fan of subset-sum
comparisons, the tropical variety of the model; only the fixed-`α` consequences are
formalized here.
-/

namespace Math.PMFProduct

open Filter Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The monomial curve and its valuation -/

/-- The one-parameter monomial curve `i ↦ p ^ α i` in the parameter space of the
independence model. Also called a tropical degeneration, a rate hierarchy with
exponents `α`, or a hazard family with `x i ≍ p ^ α i`. -/
def powerHazard (α : ι → ℕ) (p : ℝ) : ι → ℝ := fun i => p ^ α i

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma powerHazard_apply (α : ι → ℕ) (p : ℝ) (i : ι) :
    powerHazard α p i = p ^ α i := rfl

/-- The valuation of the coalition coordinate `S` along `powerHazard α`: the order of
vanishing at `p = 0` of `coalitionMass (powerHazard α p) S`, whenever the exponents off
`S` are nonzero. Also called the tropicalization of the Bernstein coordinate. -/
def coalitionValuation (α : ι → ℕ) (S : Finset ι) : ℕ := ∑ i ∈ S, α i

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma coalitionValuation_empty (α : ι → ℕ) :
    coalitionValuation α (∅ : Finset ι) = 0 := by
  simp [coalitionValuation]

omit [Fintype ι] [DecidableEq ι] in
/-- The valuation is monotone in the coalition: enlarging a coalition can only make its
mass vanish to higher order. -/
lemma coalitionValuation_le_of_subset (α : ι → ℕ) {S T : Finset ι} (hST : S ⊆ T) :
    coalitionValuation α S ≤ coalitionValuation α T :=
  Finset.sum_le_sum_of_subset hST

/-- The unit cofactor of the coalition coordinate `S` along `powerHazard α`: the part of
the mass that survives dividing out the leading monomial. -/
def coalitionCofactor (α : ι → ℕ) (S : Finset ι) (p : ℝ) : ℝ := ∏ i ∈ Sᶜ, (1 - p ^ α i)

/-! ## The exact leading-order factorization -/

/-- **Leading-order factorization.** Along the monomial curve the coalition mass is
*exactly* its leading monomial times the cofactor. No error term and no hypothesis: the
asymptotic statements below are corollaries of this identity together with
`tendsto_coalitionCofactor_one`. -/
theorem coalitionMass_powerHazard (α : ι → ℕ) (S : Finset ι) (p : ℝ) :
    coalitionMass (powerHazard α p) S
      = p ^ coalitionValuation α S * coalitionCofactor α S p := by
  rw [coalitionMass, coalitionValuation, coalitionCofactor]
  simp only [powerHazard_apply]
  rw [Finset.prod_pow_eq_pow_sum]

/-- A coordinate outside `S` with exponent `0` never stays put, so it annihilates the
cofactor. -/
theorem coalitionCofactor_eq_zero_of_exponent_eq_zero {α : ι → ℕ} {S : Finset ι} {i : ι}
    (hi : i ∈ Sᶜ) (hαi : α i = 0) (p : ℝ) : coalitionCofactor α S p = 0 :=
  Finset.prod_eq_zero hi (by simp [hαi])

/-- The degenerate case made explicit: a coordinate outside `S` with exponent `0` acts
with probability `1` along the whole curve, so `S` carries no mass at all. -/
theorem coalitionMass_powerHazard_eq_zero_of_exponent_eq_zero {α : ι → ℕ} {S : Finset ι}
    {i : ι} (hi : i ∈ Sᶜ) (hαi : α i = 0) (p : ℝ) :
    coalitionMass (powerHazard α p) S = 0 := by
  rw [coalitionMass_powerHazard, coalitionCofactor_eq_zero_of_exponent_eq_zero hi hαi,
    mul_zero]

/-- Off the degenerate case, the cofactor is a genuine unit: it takes the value `1` at
`p = 0`. -/
theorem coalitionCofactor_zero {α : ι → ℕ} {S : Finset ι} (hα : ∀ i ∈ Sᶜ, α i ≠ 0) :
    coalitionCofactor α S 0 = 1 :=
  Finset.prod_eq_one fun i hi => by rw [zero_pow (hα i hi), sub_zero]

/-- The cofactor is a polynomial in `p`, hence analytic at `0`. -/
theorem analyticAt_coalitionCofactor (α : ι → ℕ) (S : Finset ι) :
    AnalyticAt ℝ (coalitionCofactor α S) 0 :=
  Finset.analyticAt_fun_prod _ fun i _ =>
    analyticAt_const.sub (analyticAt_id.pow (α i))

/-- The cofactor tends to `1` as the curve parameter tends to `0`: it contributes no
order of vanishing, so the valuation is carried entirely by the leading monomial. -/
theorem tendsto_coalitionCofactor_one {α : ι → ℕ} {S : Finset ι} (hα : ∀ i ∈ Sᶜ, α i ≠ 0) :
    Tendsto (coalitionCofactor α S) (𝓝 (0 : ℝ)) (𝓝 1) := by
  have h := (analyticAt_coalitionCofactor α S).continuousAt
  rw [ContinuousAt, coalitionCofactor_zero hα] at h
  exact h

/-- On `(0, 1)` the cofactor is strictly positive, so the coalition mass is strictly
positive there. -/
theorem coalitionCofactor_pos {α : ι → ℕ} {S : Finset ι} {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hα : ∀ i ∈ Sᶜ, α i ≠ 0) : 0 < coalitionCofactor α S p :=
  Finset.prod_pos fun i hi => by
    have : p ^ α i < 1 := pow_lt_one₀ hp0.le hp1 (hα i hi)
    linarith

theorem coalitionMass_powerHazard_pos {α : ι → ℕ} {S : Finset ι} {p : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hα : ∀ i ∈ Sᶜ, α i ≠ 0) : 0 < coalitionMass (powerHazard α p) S := by
  rw [coalitionMass_powerHazard]
  exact mul_pos (pow_pos hp0 _) (coalitionCofactor_pos hp0 hp1 hα)

/-! ## The comparison principle -/

/-- The ratio of two coalition masses along the curve is *exactly* a monomial times a
ratio of cofactors, for every `p > 0`. The identity also holds when the denominator's
cofactor vanishes, both sides then being `0`. -/
theorem coalitionMass_powerHazard_div {α : ι → ℕ} {S T : Finset ι} {p : ℝ} (hp : p ≠ 0)
    (hle : coalitionValuation α S ≤ coalitionValuation α T) :
    coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S
      = p ^ (coalitionValuation α T - coalitionValuation α S) *
        (coalitionCofactor α T p / coalitionCofactor α S p) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [coalitionMass_powerHazard, coalitionMass_powerHazard, hd, Nat.add_sub_cancel_left,
    pow_add, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ hp), mul_div_assoc]

/-- **Comparison principle.** A coalition of strictly larger valuation carries
asymptotically negligible mass. The hypotheses are exactly what is needed: the
exponents off `S` and off `T` must be nonzero, or one of the two masses is identically
zero (`coalitionMass_powerHazard_eq_zero_of_exponent_eq_zero`). -/
theorem tendsto_coalitionMass_div_nhds_zero {α : ι → ℕ} {S T : Finset ι}
    (hS : ∀ i ∈ Sᶜ, α i ≠ 0) (hT : ∀ i ∈ Tᶜ, α i ≠ 0)
    (hlt : coalitionValuation α S < coalitionValuation α T) :
    Tendsto (fun p : ℝ => coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcongr : ∀ᶠ p in 𝓝[>] (0 : ℝ),
      p ^ (coalitionValuation α T - coalitionValuation α S) *
          (coalitionCofactor α T p / coalitionCofactor α S p)
        = coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (coalitionMass_powerHazard_div (ne_of_gt hp) hlt.le).symm
  refine Tendsto.congr' hcongr ?_
  have hpow : Tendsto (fun p : ℝ => p ^ (coalitionValuation α T - coalitionValuation α S))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_pow_nhdsGT_zero (by omega)
  have hratio : Tendsto (fun p : ℝ => coalitionCofactor α T p / coalitionCofactor α S p)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h : Tendsto (coalitionCofactor α T / coalitionCofactor α S) (𝓝 (0 : ℝ)) (𝓝 (1 / 1)) :=
      (tendsto_coalitionCofactor_one hT).div (tendsto_coalitionCofactor_one hS) one_ne_zero
    rw [div_one] at h
    exact Tendsto.congr (fun p => rfl) (h.mono_left nhdsWithin_le_nhds)
  simpa using hpow.mul hratio

/-- The same comparison read the other way round: the mass of the lower-valuation
coalition dominates without bound. -/
theorem tendsto_coalitionMass_div_atTop {α : ι → ℕ} {S T : Finset ι}
    (hS : ∀ i ∈ Sᶜ, α i ≠ 0) (hT : ∀ i ∈ Tᶜ, α i ≠ 0)
    (hlt : coalitionValuation α S < coalitionValuation α T) :
    Tendsto (fun p : ℝ => coalitionMass (powerHazard α p) S / coalitionMass (powerHazard α p) T)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hlt1 : ∀ᶠ p in 𝓝[>] (0 : ℝ), p < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpos : ∀ᶠ p in 𝓝[>] (0 : ℝ),
      coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hlt1] with p hp0 hp1
    exact div_pos (coalitionMass_powerHazard_pos hp0 hp1 hT)
      (coalitionMass_powerHazard_pos hp0 hp1 hS)
  have hwithin : Tendsto
      (fun p : ℝ => coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_coalitionMass_div_nhds_zero hS hT hlt, hpos⟩
  exact (tendsto_inv_nhdsGT_zero.comp hwithin).congr fun p => inv_div _ _

/-! ## Leading-coalition selection -/

/-- **Leading-coalition selection.** Within a finite family `F` of coalitions, let `S₀`
minimize the valuation. Then the total mass of every member whose valuation is not
minimal is asymptotically negligible against the mass of `S₀`. This is leading-term
extraction for the independence model: only the minimizers of `coalitionValuation`
survive the degeneration.

Varying `α`, the resulting partition of exponent space by subset-sum comparisons is a
polyhedral fan; that geometry is outside the scope of this file. -/
theorem tendsto_sum_coalitionMass_div_nhds_zero {α : ι → ℕ} {F : Finset (Finset ι)}
    {S₀ : Finset ι} (hS₀ : ∀ i ∈ S₀ᶜ, α i ≠ 0)
    (hα : ∀ T ∈ F, ∀ i ∈ Tᶜ, α i ≠ 0)
    (hmin : ∀ T ∈ F, coalitionValuation α S₀ ≤ coalitionValuation α T) :
    Tendsto (fun p : ℝ =>
        (∑ T ∈ F.filter fun T => coalitionValuation α T ≠ coalitionValuation α S₀,
            coalitionMass (powerHazard α p) T) /
          coalitionMass (powerHazard α p) S₀)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simp_rw [Finset.sum_div]
  have h : Tendsto (fun p : ℝ =>
      ∑ T ∈ F.filter fun T => coalitionValuation α T ≠ coalitionValuation α S₀,
        coalitionMass (powerHazard α p) T / coalitionMass (powerHazard α p) S₀)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑ _T ∈ F.filter fun T => coalitionValuation α T ≠ coalitionValuation α S₀, (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun T hT => ?_
    rw [Finset.mem_filter] at hT
    exact tendsto_coalitionMass_div_nhds_zero hS₀ (hα T hT.1)
      (lt_of_le_of_ne (hmin T hT.1) (Ne.symm hT.2))
  simpa using h

/-! ## Packaging as a leading-order jet

The factorization above is exactly the data of a `Math.LeadingOrderJet` for a finite
family of coalitions, which is how the normalized-share statements of
`MathUE/AnalyticOrderComparison.lean` become available for coalition masses. -/

variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-- The least valuation attained by a finite nonempty family of coalitions. -/
def familyCoalitionValuation (α : ι → ℕ) (sel : κ → Finset ι) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty fun k => coalitionValuation α (sel k)

omit [Fintype ι] [DecidableEq ι] in
theorem familyCoalitionValuation_le (α : ι → ℕ) (sel : κ → Finset ι) (k : κ) :
    familyCoalitionValuation α sel ≤ coalitionValuation α (sel k) :=
  Finset.inf'_le _ (Finset.mem_univ k)

omit [Fintype ι] [DecidableEq ι] in
theorem exists_familyCoalitionValuation_eq (α : ι → ℕ) (sel : κ → Finset ι) :
    ∃ k, familyCoalitionValuation α sel = coalitionValuation α (sel k) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := κ))
    fun k => coalitionValuation α (sel k)
  exact ⟨k, hk⟩

/-- **The leading-order jet of a finite family of coalitions.** The common power factored
out is the least valuation in the family, and the cofactor of a member is a unit exactly
when that member attains it. This makes the whole `Math.LeadingOrderJet` interface —
`Math.leadingSet`, `Math.LeadingOrderJet.tendsto_div_sum`,
`Math.LeadingOrderJet.tendsto_div_sum_nhds_zero` — available for coalition masses. -/
noncomputable def coalitionLeadingOrderJet (α : ι → ℕ) (sel : κ → Finset ι)
    (hα : ∀ k, ∀ i ∈ (sel k)ᶜ, α i ≠ 0) :
    LeadingOrderJet fun k p => coalitionMass (powerHazard α p) (sel k) where
  order := familyCoalitionValuation α sel
  cofactor k p :=
    p ^ (coalitionValuation α (sel k) - familyCoalitionValuation α sel) *
      coalitionCofactor α (sel k) p
  analytic_cofactor k :=
    (analyticAt_id.pow _).mul (analyticAt_coalitionCofactor α (sel k))
  factor_eq k := by
    filter_upwards with p
    rw [coalitionMass_powerHazard, ← mul_assoc, ← pow_add,
      Nat.add_sub_cancel' (familyCoalitionValuation_le α sel k)]
  exists_leading := by
    obtain ⟨k, hk⟩ := exists_familyCoalitionValuation_eq α sel
    refine ⟨k, ?_⟩
    rw [← hk, Nat.sub_self, pow_zero, one_mul, coalitionCofactor_zero (hα k)]
    exact one_ne_zero

@[simp] theorem coalitionLeadingOrderJet_order (α : ι → ℕ) (sel : κ → Finset ι)
    (hα : ∀ k, ∀ i ∈ (sel k)ᶜ, α i ≠ 0) :
    (coalitionLeadingOrderJet α sel hα).order = familyCoalitionValuation α sel := rfl

/-- The leading set of the family is exactly the set of valuation minimizers: the
tropical reading of `Math.leadingSet`. -/
theorem mem_leadingSet_coalitionMass_iff (α : ι → ℕ) (sel : κ → Finset ι)
    (hα : ∀ k, ∀ i ∈ (sel k)ᶜ, α i ≠ 0) (k : κ) :
    k ∈ leadingSet (fun k p => coalitionMass (powerHazard α p) (sel k)) ↔
      coalitionValuation α (sel k) = familyCoalitionValuation α sel := by
  rw [(coalitionLeadingOrderJet α sel hα).mem_leadingSet_iff k]
  constructor
  · intro hk
    by_contra hne
    have hlt : familyCoalitionValuation α sel < coalitionValuation α (sel k) :=
      lt_of_le_of_ne (familyCoalitionValuation_le α sel k) (Ne.symm hne)
    exact hk (by
      simp only [coalitionLeadingOrderJet]
      rw [zero_pow (by omega), zero_mul])
  · intro hk
    simp only [coalitionLeadingOrderJet]
    rw [hk, Nat.sub_self, pow_zero, one_mul, coalitionCofactor_zero (hα k)]
    exact one_ne_zero

end Math.PMFProduct
