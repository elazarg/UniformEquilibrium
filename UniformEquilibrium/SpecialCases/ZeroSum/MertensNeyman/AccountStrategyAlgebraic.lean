/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.SpecialCases.ZeroSum.MertensNeyman.AccountStrategyPuiseux
import GameTheory.Concepts.Stochastic.ZeroSum.DiscountedShapleyAlgebraic
import GameTheory.Concepts.Stochastic.Transform.Payoff.AffinePayoff
import MathUE.AlgebraicSelection
import MathUE.WeierstrassCurve

/-!
# Algebraic Shapley and selection capstones for the account controller

This module assembles the algebraic discounted-value and Puiseux selection
interfaces into the final uniform-equilibrium conclusions.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MertensNeymanAccount

open Filter Math.Probability Math.PMFProduct Topology

theorem isUniformEquilibriumPayoff_of_puiseux_discountedValue_of_value_zeroSum
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hVzs : ∀ lam z, v lam z 1 = -v lam z 0)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then target s₀ else -target s₀) := by
  have hrow :
      G.IsOneSidedGuaranteeCertificate s₀ 0 (target s₀) :=
    rowAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
      target s₀ hpayLower hpayUpper hvalueLower hvalueUpper
      hF hzs hVzs hβ hlam0 hderiv hbound hlimit
  have hpayLowerOne : ∀ z a, -1 ≤ G.stagePayoff z a 1 := by
    intro z a
    rw [hzs z a]
    nlinarith [hpayUpper z a]
  have hpayUpperOne : ∀ z a, G.stagePayoff z a 1 ≤ 0 := by
    intro z a
    rw [hzs z a]
    nlinarith [hpayLower z a]
  have hvalueLowerOne : ∀ lam z, -1 ≤ v lam z 1 := by
    intro lam z
    rw [hVzs lam z]
    nlinarith [hvalueUpper lam z]
  have hvalueUpperOne : ∀ lam z, v lam z 1 ≤ 0 := by
    intro lam z
    rw [hVzs lam z]
    nlinarith [hvalueLower lam z]
  have hderivOne : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 1) (-v' z lam) lam := by
    intro z lam hlam hlam0
    apply (hderiv z lam hlam hlam0).neg.congr_of_eventuallyEq
    filter_upwards [] with u
    exact hVzs u z
  have hboundOne : ∀ z lam, 0 < lam → lam < lam0 z →
      |-v' z lam| ≤ lam ^ (β z - 1) / lam0 z := by
    intro z lam hlam hlam0
    simpa using hbound z lam hlam hlam0
  have hlimitOne : ∀ z,
      Tendsto (fun lam => v lam z 1)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (-target z)) := by
    intro z
    simpa only [hVzs] using (hlimit z).neg
  have hcol :
      G.IsOneSidedGuaranteeCertificate s₀ 1 (-target s₀) := by
    simpa using
      colAccount_isOneSidedGuaranteeCertificate_of_puiseux_of_tendsto
        (fun z => -target z) s₀
        hpayLowerOne hpayUpperOne
        hvalueLowerOne hvalueUpperOne
        hF hzs hVzs hβ hlam0 hderivOne hboundOne hlimitOne
  exact isUniformEquilibriumPayoff_of_oneSidedGuarantees
    hzs s₀ (target s₀) hrow hcol

/-- Conditional two-player zero-sum uniform-value theorem from a discounted
Bellman family and a Puiseux envelope for player zero.

No separate zero-sum hypothesis on the selected value family is needed.
On the natural rate domain, every zero-sum discounted Bellman equilibrium
has antisymmetric values by
`IsDiscountedStationaryBellmanEq.value_zeroSum`; outside that domain the
unused player-one coordinate is normalized to the negative of player zero. -/
theorem isUniformEquilibriumPayoff_of_puiseux_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    {β lam0 : G.State → ℝ} {v' : G.State → ℝ → ℝ}
    (target : G.State → ℝ) (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hβ : ∀ z, 0 < β z) (hlam0 : ∀ z, 0 < lam0 z)
    (hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam)
    (hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (β z - 1) / lam0 z)
    (hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (target z))) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then target s₀ else -target s₀) := by
  let vz : ℝ → G.State → Payoff (Fin 2) :=
    fun lam z who => if who = 0 then v lam z 0 else -v lam z 0
  have hvz_zero (lam : ℝ) (z : G.State) : vz lam z 0 = v lam z 0 := by
    simp [vz]
  have hvz_one (lam : ℝ) (z : G.State) : vz lam z 1 = -vz lam z 0 := by
    simp [vz]
  have hFz : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (vz lam) := by
    intro lam hlam hlam1
    have hEq := hF lam hlam hlam1
    have hEqzs :
        ∀ z, v lam z 1 = -v lam z 0 :=
      hEq.value_zeroSum (by linarith) (by linarith) hzs
    have hvz : vz lam = v lam := by
      funext z who
      fin_cases who
      · exact hvz_zero lam z
      · change -v lam z 0 = v lam z 1
        exact (hEqzs z).symm
    rwa [hvz]
  apply
    isUniformEquilibriumPayoff_of_puiseux_discountedValue_of_value_zeroSum
      (v := vz) target s₀ hpayLower hpayUpper
  · intro lam z
    simpa [hvz_zero] using hvalueLower lam z
  · intro lam z
    simpa [hvz_zero] using hvalueUpper lam z
  · exact hFz
  · exact hzs
  · exact hvz_one
  · exact hβ
  · exact hlam0
  · intro z lam hlam hlam0'
    simpa only [hvz_zero] using hderiv z lam hlam hlam0'
  · exact hbound
  · intro z
    simpa only [hvz_zero] using hlimit z

/-- A genuine coordinatewise Puiseux reparameterization discharges both
analytic hypotheses of the zero-sum account theorem.

For every state coordinate, `v(λ) = g(λ^q)` with `q > 0`, a regular factor
continuous at zero, and a bounded derivative of that factor supplies:

* the account derivative envelope, by
  `Math.puiseuxDerivativeEnvelope_of_rpow_reparam`;
* the right limit `g(0)`, by `Math.tendsto_zero_of_rpow_reparam`.

This theorem makes the Puiseux data and discounted Bellman family sufficient;
it does not require a separate game-facing convergence or derivative
estimate. -/
theorem isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      v lam z 0 = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0)
            (g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))) lam ∧
          |g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))| ≤
            lam ^ (q z - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_rpow_reparam
      (hq z) (hρ z) (hK z)
      (hreparam z) (hgderiv z) (hgbound z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  let v' : G.State → ℝ → ℝ := fun z lam =>
    g' z (lam ^ q z) * (q z * lam ^ (q z - 1))
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (q z - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g z 0)) := by
    intro z
    exact Math.tendsto_zero_of_rpow_reparam
      (hq z) (hρ z) (hreparam z) (hgcontinuous z)
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => g z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hq hlam0 hderiv hbound hlimit

/-- A coordinatewise algebraic branch that becomes regular after a positive
power reparameterization yields the zero-sum uniform payoff.

Unlike `isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue`, this
theorem does not ask for a derivative function or a derivative bound for the
regular factors. A polynomial relation with a simple limiting root supplies
that calculus data through
`Math.puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root`. -/
theorem isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (P : G.State → Polynomial (Polynomial ℝ))
    (q ρw ρg : G.State → ℝ)
    (g : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρw : ∀ z, 0 < ρw z)
    (hρg : ∀ z, 0 < ρg z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρw z) →
      v lam z 0 = g z (lam ^ q z))
    (hgcontinuousAt : ∀ z, ContinuousAt (g z) 0)
    (hgcontinuousOn : ∀ z,
      ContinuousOn (g z) (Set.Ioo 0 (ρg z)))
    (hgroot : ∀ z t, t ∈ Set.Ioo (0 : ℝ) (ρg z) →
      Math.bivEval (P z) t (g z t) = 0)
    (hgregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (g z 0) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  let g' : G.State → ℝ → ℝ := fun z t =>
    -(Math.bivEval (Math.bivDerivLam (P z)) t (g z t)) /
      Math.bivEval (Polynomial.derivative (P z)) t (g z t)
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0)
            (g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))) lam ∧
          |g' z (lam ^ q z) *
              (q z * lam ^ (q z - 1))| ≤
            lam ^ (q z - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_regular_reparam_polynomial_root
      (P := P z) (w := fun lam => v lam z 0) (g := g z)
      (hq z) (hρw z) (hρg z)
      (hreparam z) (hgcontinuousAt z) (hgcontinuousOn z)
      (hgroot z) (hgregular z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  let v' : G.State → ℝ → ℝ := fun z lam =>
    g' z (lam ^ q z) * (q z * lam ^ (q z - 1))
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ (q z - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (g z 0)) := by
    intro z
    exact Math.tendsto_zero_of_rpow_reparam
      (hq z) (hρw z) (hreparam z) (hgcontinuousAt z)
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => g z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs hq hlam0 hderiv hbound hlimit

/-- Regular algebraic discounted-value branches yield the zero-sum
uniform payoff without a Newton--Puiseux construction.

If each selected value coordinate extends continuously to `λ = 0`, remains a
root of a bivariate polynomial for positive small rates, and is a simple root
at `(0, v(0))`, then
`Math.puiseuxDerivativeEnvelope_of_regular_polynomial_root` supplies the
account envelope with exponent `1`. Continuity supplies the limit. Coordinates
singular at the limiting point do not satisfy this theorem's regularity
hypothesis. -/
theorem isUniformEquilibriumPayoff_of_regular_algebraic_discountedValue
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {x : ℝ → G.StationaryMixedProfile}
    {v : ℝ → G.State → Payoff (Fin 2)}
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hvalueLower : ∀ lam z, 0 ≤ v lam z 0)
    (hvalueUpper : ∀ lam z, v lam z 0 ≤ 1)
    (hF : ∀ lam, 0 < lam → lam ≤ 1 →
      G.IsDiscountedStationaryBellmanEq
        (1 - lam) (x lam) (v lam))
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hcontinuousAt : ∀ z,
      ContinuousAt (fun lam => v lam z 0) 0)
    (hcontinuousOn : ∀ z,
      ContinuousOn (fun lam => v lam z 0)
        (Set.Ioo 0 (ρ z)))
    (hroot : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) lam (v lam z 0) = 0)
    (hregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (v 0 z 0) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then v 0 s₀ 0 else -v 0 s₀ 0) := by
  let v' : G.State → ℝ → ℝ := fun z lam =>
    -(Math.bivEval (Math.bivDerivLam (P z)) lam (v lam z 0)) /
      Math.bivEval (Polynomial.derivative (P z)) lam (v lam z 0)
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ lam, 0 < lam → lam < lam0 →
        HasDerivAt (fun u => v u z 0) (v' z lam) lam ∧
          |v' z lam| ≤ lam ^ ((1 : ℝ) - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_regular_polynomial_root
      (hρ z) (hcontinuousAt z) (hcontinuousOn z)
      (hroot z) (hregular z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  have hderiv : ∀ z lam, 0 < lam → lam < lam0 z →
      HasDerivAt (fun u => v u z 0) (v' z lam) lam := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').1
  have hbound : ∀ z lam, 0 < lam → lam < lam0 z →
      |v' z lam| ≤ lam ^ ((1 : ℝ) - 1) / lam0 z := by
    intro z lam hlam hlam0'
    exact (hEnvelope z lam hlam hlam0').2
  have hlimit : ∀ z,
      Tendsto (fun lam => v lam z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (v 0 z 0)) := by
    intro z
    exact (hcontinuousAt z).tendsto.mono_left inf_le_left
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (fun z => v 0 z 0) s₀
    hpayLower hpayUpper hvalueLower hvalueUpper
    hF hzs (fun _ => zero_lt_one) hlam0
    hderiv hbound hlimit

/-- The canonical rate-parameterized discounted Shapley payoff admits one
stationary Bellman profile at every natural rate `0 < λ ≤ 1`. The fixed-rate
profile is supplied by the Fink–Shapley identification theorem; finite choice
assembles the profiles into a total family. -/
theorem exists_discountedShapleyRateBellmanProfileFamily
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    ∃ x : ℝ → G.StationaryMixedProfile,
      ∀ lam, 0 < lam → lam ≤ 1 →
        G.IsDiscountedStationaryBellmanEq
          (1 - lam) (x lam) (G.discountedShapleyRatePayoff lam) := by
  have hpayAbs : ∀ s a who, |G.stagePayoff s a who| ≤ (1 : ℝ) := by
    intro s a who
    fin_cases who
    · change |G.stagePayoff s a 0| ≤ 1
      rw [abs_le]
      exact ⟨by linarith [hpayLower s a], hpayUpper s a⟩
    · change |G.stagePayoff s a 1| ≤ 1
      rw [hzs s a, abs_neg, abs_le]
      exact ⟨by linarith [hpayLower s a], hpayUpper s a⟩
  let x₀ : G.StationaryMixedProfile :=
    fun _ who =>
      PMF.pure (Classical.choice (inferInstance : Nonempty (G.Act who)))
  have hex (lam : ℝ) :
      ∃ x : G.StationaryMixedProfile,
        0 < lam → lam ≤ 1 →
          G.IsDiscountedStationaryBellmanEq
            (1 - lam) x (G.discountedShapleyRatePayoff lam) := by
    by_cases hlam : 0 < lam ∧ lam ≤ 1
    · obtain ⟨x, hx⟩ :=
        G.exists_isDiscountedStationaryBellmanEq_discountedShapleyValue
          (discountFactorOfRate_lt_one hlam.1)
          1 zero_le_one hpayAbs hzs
      have hvalue :
          (fun s who =>
            if who = 0 then
              G.discountedShapleyValue
                (discountFactorOfRate_lt_one hlam.1) s
            else
              -G.discountedShapleyValue
                (discountFactorOfRate_lt_one hlam.1) s) =
            G.discountedShapleyRatePayoff lam := by
        funext s who
        fin_cases who <;>
          simp [discountedShapleyRatePayoff,
            G.discountedShapleyRateValue_eq hlam.1]
      rw [coe_discountFactorOfRate hlam.2, hvalue] at hx
      exact ⟨x, fun _ _ => hx⟩
    · exact ⟨x₀, fun hlam0 hlam1 => (hlam ⟨hlam0, hlam1⟩).elim⟩
  choose x hx using hex
  exact ⟨x, hx⟩

/-- A bounded canonical discounted-value coordinate has a right limit when it
lies on a nondegenerate bivariate algebraic branch. Positive-rate continuity
and boundedness are supplied by the Shapley fixed-point theory. -/
theorem exists_discountedShapleyRateValue_limit_of_polynomial_root
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hP : ∀ z, P z ≠ 0)
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hRv : ∀ z,
      Polynomial.resultant (P z)
        (Polynomial.derivative (P z)) ≠ 0)
    (hRlam : ∀ z,
      Polynomial.resultant (P z)
        (Math.bivDerivLam (P z)) ≠ 0) :
    ∃ L : G.State → ℝ, ∀ z,
      Tendsto
        (fun l => G.discountedShapleyRateValue l z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z)) := by
  have hexists (z : G.State) :
      ∃ L : ℝ,
        Tendsto
          (fun l => G.discountedShapleyRateValue l z)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 L) := by
    have hcontinuous :
        ContinuousOn
          (fun l => G.discountedShapleyRateValue l z)
          (Set.Ioo (0 : ℝ) (ρ z)) :=
      (G.continuousOn_discountedShapleyRateValue_apply
        hzs hpayLower hpayUpper z).mono (by
          intro l hl
          exact ⟨hl.1, hl.2.le.trans (hρle z)⟩)
    apply Math.exists_tendsto_nhdsWithin_zero_of_polynomial_root
      (hρ z) hcontinuous
      (hP z) (hroot z) (hRv z) (hRlam z)
      (C := (1 : ℝ))
    intro l _hl
    rw [abs_le]
    constructor
    · have hnonneg :=
        G.discountedShapleyRateValue_nonneg
          hzs hpayLower l z
      linarith
    · exact G.discountedShapleyRateValue_le_one
        hzs hpayLower hpayUpper l z
  choose L hL using hexists
  exact ⟨L, hL⟩

/-- Coordinatewise bivariate relations for the canonical discounted Shapley
value reduce to distinguished formal equations centered at a proposed endpoint.

Taking primitive parts removes parameter-only factors. Weierstrass preparation
then supplies a distinguished polynomial times a formal unit, while the
centered canonical branch continues to satisfy the primitive equation on a
smaller positive-rate interval. -/
theorem exists_weierstrassFactorizations_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ L : G.State → ℝ)
    (hρ : ∀ z, 0 < ρ z)
    (hP : ∀ z, P z ≠ 0)
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0) :
    ∃ (f : G.State → Polynomial (PowerSeries ℝ))
        (h : G.State → PowerSeries (PowerSeries ℝ))
        (r : G.State → ℝ),
      ∀ z,
        (Math.bivPolynomialToIteratedPowerSeries
          (Math.translateBivPolynomialValue (P z) (L z)).primPart
            ).IsWeierstrassFactorization (f z) (h z) ∧
        r z ∈ Set.Ioc (0 : ℝ) (ρ z) ∧
        ∀ l ∈ Set.Ioo (0 : ℝ) (r z),
          Math.bivEval
              (Math.translateBivPolynomialValue (P z) (L z)).primPart
              l (G.discountedShapleyRateValue l z - L z) = 0 := by
  have hexists (z : G.State) :
      ∃ (fz : Polynomial (PowerSeries ℝ))
          (hz : PowerSeries (PowerSeries ℝ)) (rz : ℝ),
        (Math.bivPolynomialToIteratedPowerSeries
          (Math.translateBivPolynomialValue (P z) (L z)).primPart
            ).IsWeierstrassFactorization fz hz ∧
        rz ∈ Set.Ioc (0 : ℝ) (ρ z) ∧
        ∀ l ∈ Set.Ioo (0 : ℝ) rz,
          Math.bivEval
              (Math.translateBivPolynomialValue (P z) (L z)).primPart
              l (G.discountedShapleyRateValue l z - L z) = 0 :=
    Math.exists_weierstrassFactorization_and_centered_primitive_branch_on_Ioo
      (P z) (hP z)
      (w := fun l => G.discountedShapleyRateValue l z)
      (L z) (ρ z) (hρ z) (hroot z)
  choose f h r hdata using hexists
  exact ⟨f, h, r, hdata⟩

/-- Regular coordinatewise algebraic branches of the canonical discounted
Shapley value produce the zero-sum uniform payoff.

The stationary Bellman family, value bounds, and positive-rate continuity are
constructed internally. The hypotheses retain only the coordinate equations,
their right limits, and simplicity of the limiting roots. -/
theorem isUniformEquilibriumPayoff_of_regular_algebraic_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ L : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hlimit : ∀ z,
      Tendsto
        (fun l => G.discountedShapleyRateValue l z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z)))
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hregular : ∀ z,
      Math.bivEval (Polynomial.derivative (P z)) 0 (L z) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then L s₀ else -L s₀) := by
  let g : G.State → ℝ → ℝ := fun z l =>
    if 0 < l then G.discountedShapleyRateValue l z else L z
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  have h :=
    isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedValue
      P (fun _ => (1 : ℝ)) ρ ρ g s₀
      hpayLower hpayUpper
      (fun l z =>
        G.discountedShapleyRateValue_nonneg hzs hpayLower l z)
      (fun l z =>
        G.discountedShapleyRateValue_le_one
          hzs hpayLower hpayUpper l z)
      hx hzs (fun _ => zero_lt_one) hρ hρ
      (by
        intro z l hl
        simp [g, hl.1])
      (by
        intro z
        rw [Metric.continuousAt_iff]
        intro ε hε
        obtain ⟨δ, hδ, hclose⟩ :=
          (Metric.tendsto_nhdsWithin_nhds.mp (hlimit z)) ε hε
        refine ⟨δ, hδ, ?_⟩
        intro l hl
        by_cases hl0 : 0 < l
        · simpa [g, hl0] using hclose hl0 hl
        · simpa [g, hl0] using hε)
      (by
        intro z
        refine ((G.continuousOn_discountedShapleyRateValue_apply
          hzs hpayLower hpayUpper z).mono ?_).congr ?_
        · intro l hl
          exact ⟨hl.1, hl.2.le.trans (hρle z)⟩
        · intro l hl
          simp [g, hl.1])
      (by
        intro z l hl
        simpa [g, hl.1] using hroot z l hl)
      (by
        intro z
        simpa [g] using hregular z)
  simpa [g] using h

/-- A ramified simple polynomial factor for every canonical discounted
Shapley coordinate produces the zero-sum uniform payoff.

This is the canonical game-facing Newton--Puiseux endpoint: the hypotheses
describe only the positive-power reparameterization and its regular algebraic
factor. The factor derivative, account envelope, value bounds, and stationary
Bellman family are derived internally. -/
theorem isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (q ρw ρg : G.State → ℝ)
    (g : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρw : ∀ z, 0 < ρw z)
    (hρg : ∀ z, 0 < ρg z)
    (hreparam : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρw z) →
      G.discountedShapleyRateValue l z = g z (l ^ q z))
    (hgcontinuousAt : ∀ z, ContinuousAt (g z) 0)
    (hgcontinuousOn : ∀ z,
      ContinuousOn (g z) (Set.Ioo 0 (ρg z)))
    (hgroot : ∀ z t, t ∈ Set.Ioo (0 : ℝ) (ρg z) →
      Math.bivEval (P z) t (g z t) = 0)
    (hgregular : ∀ z,
      Math.bivEval
        (Polynomial.derivative (P z)) 0 (g z 0) ≠ 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who =>
        if who = 0 then g s₀ 0 else -g s₀ 0) := by
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  exact
    isUniformEquilibriumPayoff_of_regular_reparam_algebraic_discountedValue
      P q ρw ρg g s₀ hpayLower hpayUpper
      (fun l z =>
        G.discountedShapleyRateValue_nonneg hzs hpayLower l z)
      (fun l z =>
        G.discountedShapleyRateValue_le_one
          hzs hpayLower hpayUpper l z)
      hx hzs hq hρw hρg
      (fun z l hl => by simpa using hreparam z l hl)
      hgcontinuousAt hgcontinuousOn hgroot hgregular

/-- An analytic Puiseux reparameterization of every canonical discounted
Shapley coordinate produces the zero-sum uniform payoff.

This theorem consumes the literal output of the classical convergent
Newton--Puiseux expansion. Analyticity supplies the factor derivative,
its local bound, and continuity at the origin; the canonical Shapley theory
supplies the Bellman family and value bounds. -/
theorem isUniformEquilibriumPayoff_of_analytic_reparam_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (q ρ : G.State → ℝ)
    (g : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hreparam : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      G.discountedShapleyRateValue l z = g z (l ^ q z))
    (hganalytic : ∀ z, AnalyticAt ℝ (g z) 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who =>
        if who = 0 then g s₀ 0 else -g s₀ 0) := by
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  have hEnvelope : ∀ z, ∃ lam0 : ℝ, 0 < lam0 ∧
      ∀ l, 0 < l → l < lam0 →
        HasDerivAt
            (fun u => G.discountedShapleyRateValue u z)
            (deriv (g z) (l ^ q z) *
              (q z * l ^ (q z - 1))) l ∧
          |deriv (g z) (l ^ q z) *
              (q z * l ^ (q z - 1))| ≤
            l ^ (q z - 1) / lam0 := by
    intro z
    exact Math.puiseuxDerivativeEnvelope_of_analytic_rpow_reparam
      (hq z) (hρ z) (hreparam z) (hganalytic z)
  choose lam0 hlam0 hEnvelope using hEnvelope
  let v' : G.State → ℝ → ℝ := fun z l =>
    deriv (g z) (l ^ q z) *
      (q z * l ^ (q z - 1))
  have hderiv : ∀ z l, 0 < l → l < lam0 z →
      HasDerivAt
        (fun u => G.discountedShapleyRatePayoff u z 0)
        (v' z l) l := by
    intro z l hl hl0
    simpa only [discountedShapleyRatePayoff_zero] using
      (hEnvelope z l hl hl0).1
  have hbound : ∀ z l, 0 < l → l < lam0 z →
      |v' z l| ≤ l ^ (q z - 1) / lam0 z := by
    intro z l hl hl0
    exact (hEnvelope z l hl hl0).2
  have hlimit : ∀ z,
      Tendsto
        (fun l => G.discountedShapleyRatePayoff l z 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (g z 0)) := by
    intro z
    simpa only [discountedShapleyRatePayoff_zero] using
      Math.tendsto_zero_of_rpow_reparam
        (hq z) (hρ z) (hreparam z)
        (hganalytic z).continuousAt
  exact isUniformEquilibriumPayoff_of_puiseux_discountedValue
    (v := G.discountedShapleyRatePayoff)
    (x := x) (β := q) (lam0 := lam0) (v' := v')
    (fun z => g z 0) s₀ hpayLower hpayUpper
    (fun l z =>
      G.discountedShapleyRateValue_nonneg
        hzs hpayLower l z)
    (fun l z =>
      G.discountedShapleyRateValue_le_one
        hzs hpayLower hpayUpper l z)
    hx hzs hq hlam0 hderiv hbound hlimit

/-- The analytic Puiseux boundary for an arbitrary finite zero-sum payoff
scale.

An absolute bound `C` defines the positive affine normalization
`normalizedZeroSumPayoff`, whose row payoffs lie in `[0,1]`. An analytic
ramified representation of that normalized game's canonical discounted
Shapley value therefore yields a uniform payoff for the original game. -/
theorem isUniformEquilibriumPayoff_of_normalized_analytic_reparam_discountedShapleyRateValue
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (C : ℝ)
    (hC : ∀ z a, |G.stagePayoff z a 0| ≤ C)
    (q ρ : G.State → ℝ)
    (g : G.State → ℝ → ℝ)
    (s₀ : G.State)
    (hzs : G.IsZeroSum)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hreparam : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      (G.normalizedZeroSumPayoff C).discountedShapleyRateValue l z =
        g z (l ^ q z))
    (hganalytic : ∀ z, AnalyticAt ℝ (g z) 0) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who =>
        if who = 0 then (2 * C + 1) * g s₀ 0 - C
        else -((2 * C + 1) * g s₀ 0 - C)) := by
  let a : G.JointAct :=
    fun i => Classical.choice (inferInstance : Nonempty (G.Act i))
  have hC0 : 0 ≤ C :=
    (abs_nonneg (G.stagePayoff s₀ a 0)).trans (hC s₀ a)
  have hc : 0 < 1 / (2 * C + 1) :=
    normalizedZeroSumPayoff_scale_pos hC0
  have hnorm :
      (G.normalizedZeroSumPayoff C).IsUniformEquilibriumPayoff s₀
        (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) :=
    isUniformEquilibriumPayoff_of_analytic_reparam_discountedShapleyRateValue
      (G.normalizedZeroSumPayoff C) q ρ g s₀
      (G.normalizedZeroSumPayoff_stagePayoff_zero_nonneg C hC)
      (G.normalizedZeroSumPayoff_stagePayoff_zero_le_one C hC)
      (G.normalizedZeroSumPayoff_isZeroSum C hzs)
      hq hρ hreparam hganalytic
  have hback :=
    G.isUniformEquilibriumPayoff_of_affinePayoff
      (1 / (2 * C + 1)) hc
      (fun who => if who = 0 then C / (2 * C + 1)
        else -C / (2 * C + 1))
      s₀ (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) hnorm
  convert hback using 1
  funext who
  fin_cases who
  · simp
    field_simp
  · simp
    field_simp
    ring

/-- Nondegenerate coordinate polynomials reduce the canonical zero-sum
discounted-value problem to an explicit endpoint dichotomy: either every
limiting root is simple and the account construction yields a uniform payoff,
or a named state has a singular limiting root. -/
theorem discountedShapleyRateValue_regular_or_singular_limit
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (P : G.State → Polynomial (Polynomial ℝ))
    (ρ : G.State → ℝ)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (hρ : ∀ z, 0 < ρ z)
    (hρle : ∀ z, ρ z ≤ 1)
    (hP : ∀ z, P z ≠ 0)
    (hroot : ∀ z l, l ∈ Set.Ioo (0 : ℝ) (ρ z) →
      Math.bivEval (P z) l
        (G.discountedShapleyRateValue l z) = 0)
    (hRv : ∀ z,
      Polynomial.resultant (P z)
        (Polynomial.derivative (P z)) ≠ 0)
    (hRlam : ∀ z,
      Polynomial.resultant (P z)
        (Math.bivDerivLam (P z)) ≠ 0) :
    (∃ L : G.State → ℝ,
        (∀ z,
          Tendsto
            (fun l => G.discountedShapleyRateValue l z)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L z))) ∧
        G.IsUniformEquilibriumPayoff s₀
          (fun who => if who = 0 then L s₀ else -L s₀)) ∨
      ∃ (L : G.State → ℝ) (z : G.State),
        (∀ y,
          Tendsto
            (fun l => G.discountedShapleyRateValue l y)
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (L y))) ∧
        Math.bivEval
          (Polynomial.derivative (P z)) 0 (L z) = 0 := by
  obtain ⟨L, hL⟩ :=
    exists_discountedShapleyRateValue_limit_of_polynomial_root
      G hpayLower hpayUpper hzs P ρ hρ hρle hP
      hroot hRv hRlam
  by_cases hregular : ∀ z,
      Math.bivEval
        (Polynomial.derivative (P z)) 0 (L z) ≠ 0
  · left
    exact ⟨L, hL,
      isUniformEquilibriumPayoff_of_regular_algebraic_discountedShapleyRateValue
        G P ρ L s₀ hpayLower hpayUpper hzs
        hρ hρle hL hroot hregular⟩
  · right
    simp only [not_forall, not_not] at hregular
    obtain ⟨z, hz⟩ := hregular
    exact ⟨L, z, hL, hz⟩

/-- A sufficient discounted-value selection package for the two-player
zero-sum account construction.

It contains a stationary discounted Bellman family on the natural rate domain
and a coordinatewise Puiseux reparameterization of player zero's value.
The analytic account envelope and limiting payoff are deliberately absent:
they are derived from these fields by
`isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue`.

Its fields state the Bewley--Kohlberg/Newton--Puiseux selection interface used
by the verification theorem below. -/
structure PuiseuxDiscountedValueSelection
    (G : StochasticGame (Fin 2))
    [Finite G.State] [∀ i, Finite (G.Act i)] where
  x : ℝ → G.StationaryMixedProfile
  v : ℝ → G.State → Payoff (Fin 2)
  q : G.State → ℝ
  ρ : G.State → ℝ
  K : G.State → ℝ
  g : G.State → ℝ → ℝ
  g' : G.State → ℝ → ℝ
  valueLower : ∀ lam z, 0 ≤ v lam z 0
  valueUpper : ∀ lam z, v lam z 0 ≤ 1
  bellman : ∀ lam, 0 < lam → lam ≤ 1 →
    G.IsDiscountedStationaryBellmanEq
      (1 - lam) (x lam) (v lam)
  exponent_pos : ∀ z, 0 < q z
  radius_pos : ∀ z, 0 < ρ z
  derivativeBound_nonneg : ∀ z, 0 ≤ K z
  reparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
    v lam z 0 = g z (lam ^ q z)
  regular_continuousAt_zero : ∀ z, ContinuousAt (g z) 0
  regular_hasDerivAt : ∀ z lam,
    lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z)
  regular_derivative_bound : ∀ z lam,
    lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z

/-- Construct the complete semantic selection package from a coordinatewise
Puiseux reparameterization of the canonical discounted Shapley value.

The stationary Bellman family and the `[0,1]` value bounds are derived
internally. Thus the remaining input is exactly the
Bewley–Kohlberg/Newton–Puiseux branch data for the canonical row value. -/
theorem exists_puiseuxDiscountedValueSelection_of_discountedShapleyRateValue_reparam
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      G.discountedShapleyRateValue lam z = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    ∃ S : PuiseuxDiscountedValueSelection G,
      S.v = G.discountedShapleyRatePayoff ∧ S.g = g := by
  obtain ⟨x, hx⟩ :=
    exists_discountedShapleyRateBellmanProfileFamily G
      hpayLower hpayUpper hzs
  refine ⟨{
    x := x
    v := G.discountedShapleyRatePayoff
    q := q
    ρ := ρ
    K := K
    g := g
    g' := g'
    valueLower := ?_
    valueUpper := ?_
    bellman := hx
    exponent_pos := hq
    radius_pos := hρ
    derivativeBound_nonneg := hK
    reparam := ?_
    regular_continuousAt_zero := hgcontinuous
    regular_hasDerivAt := hgderiv
    regular_derivative_bound := hgbound
  }, rfl, rfl⟩
  · intro lam z
    simpa using
      G.discountedShapleyRateValue_nonneg hzs hpayLower lam z
  · intro lam z
    simpa using
      G.discountedShapleyRateValue_le_one
        hzs hpayLower hpayUpper lam z
  · intro z lam hlam
    simpa using hreparam z lam hlam

/-- A `PuiseuxDiscountedValueSelection` produces the normalized zero-sum
uniform payoff. -/
theorem PuiseuxDiscountedValueSelection.isUniformEquilibriumPayoff
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (S : PuiseuxDiscountedValueSelection G)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then S.g s₀ 0 else -S.g s₀ 0) := by
  exact isUniformEquilibriumPayoff_of_puiseux_reparam_discountedValue
    S.q S.ρ S.K S.g S.g' s₀
    hpayLower hpayUpper S.valueLower S.valueUpper
    S.bellman hzs
    S.exponent_pos S.radius_pos S.derivativeBound_nonneg
    S.reparam S.regular_continuousAt_zero
    S.regular_hasDerivAt S.regular_derivative_bound

/-- A coordinatewise Puiseux reparameterization of the canonical discounted
Shapley value is sufficient for the normalized zero-sum uniform payoff.

All stationary-profile, Bellman, value-bound, and zero-sum-identification
data are constructed internally. This is the direct game-facing
Bewley–Kohlberg/Newton–Puiseux boundary. -/
theorem isUniformEquilibriumPayoff_of_discountedShapleyRateValue_reparam
    (G : StochasticGame (Fin 2))
    [Fintype G.State] [∀ i, Fintype (G.Act i)]
    [∀ i, Nonempty (G.Act i)]
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum)
    (q ρ K : G.State → ℝ)
    (g g' : G.State → ℝ → ℝ)
    (hq : ∀ z, 0 < q z)
    (hρ : ∀ z, 0 < ρ z)
    (hK : ∀ z, 0 ≤ K z)
    (hreparam : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      G.discountedShapleyRateValue lam z = g z (lam ^ q z))
    (hgcontinuous : ∀ z, ContinuousAt (g z) 0)
    (hgderiv : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      HasDerivAt (g z) (g' z (lam ^ q z)) (lam ^ q z))
    (hgbound : ∀ z lam, lam ∈ Set.Ioo (0 : ℝ) (ρ z) →
      |g' z (lam ^ q z)| ≤ K z) :
    G.IsUniformEquilibriumPayoff s₀
      (fun who => if who = 0 then g s₀ 0 else -g s₀ 0) := by
  obtain ⟨S, _hSv, hSg⟩ :=
    exists_puiseuxDiscountedValueSelection_of_discountedShapleyRateValue_reparam
      G hpayLower hpayUpper hzs q ρ K g g'
      hq hρ hK hreparam hgcontinuous hgderiv hgbound
  have h := S.isUniformEquilibriumPayoff
    s₀ hpayLower hpayUpper hzs
  rwa [hSg] at h

/-- Existence-facing zero-sum wrapper from a discounted-value selection
package. -/
theorem exists_uniformEquilibriumPayoff_of_puiseuxDiscountedValueSelection
    {G : StochasticGame (Fin 2)}
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (S : PuiseuxDiscountedValueSelection G)
    (s₀ : G.State)
    (hpayLower : ∀ z a, 0 ≤ G.stagePayoff z a 0)
    (hpayUpper : ∀ z a, G.stagePayoff z a 0 ≤ 1)
    (hzs : G.IsZeroSum) :
    ∃ u : Payoff (Fin 2), G.IsUniformEquilibriumPayoff s₀ u := by
  exact ⟨fun who =>
      if who = 0 then S.g s₀ 0 else -S.g s₀ 0,
    S.isUniformEquilibriumPayoff s₀ hpayLower hpayUpper hzs⟩

end MertensNeymanAccount
end StochasticGame
end GameTheory
