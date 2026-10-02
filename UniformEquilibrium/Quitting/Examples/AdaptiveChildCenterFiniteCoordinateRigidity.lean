import Mathlib.Tactic.FunProp
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterQuantileRegret

/-! # Rigidity of the finite coordinates from actual source inequalities

Compactness is used only in the four-dimensional cube of anchor mass and
active conditional probabilities. No stopping law or calendar is compactified.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology

theorem continuous_activePayoff (active : Fin 3) :
    Continuous (fun q : Fin 3 → ℝ => activePayoff q active) := by
  fin_cases active
  · change Continuous (fun q : Fin 3 → ℝ => q 0 + 2 * (1 - q 0) * q 2)
    fun_prop
  · change Continuous (fun q : Fin 3 → ℝ => q 1 * (2 * q 0 - 1))
    fun_prop
  · change Continuous (fun q : Fin 3 → ℝ => q 2 * (2 * q 1 - 1))
    fun_prop

theorem continuous_activeEndpointPayoff (active : Fin 3) (quit : Bool) :
    Continuous (fun q : Fin 3 → ℝ => activeEndpointPayoff q active quit) := by
  cases quit
  · fin_cases active
    · change Continuous (fun q : Fin 3 → ℝ => 2 * q 2)
      fun_prop
    · exact continuous_const
    · exact continuous_const
  · fin_cases active
    · exact continuous_const
    · change Continuous (fun q : Fin 3 → ℝ => 2 * q 0 - 1)
      fun_prop
    · change Continuous (fun q : Fin 3 → ℝ => 2 * q 1 - 1)
      fun_prop

/-- Every convergent finite-coordinate subsequence has the same fair limit.
The positive anchor limit is proved before invoking unconditional Nash
uniqueness. The sharper actual player-zero estimate then identifies its mass.
-/
theorem finite_coordinate_cluster_rigidity
    (p error accuracy : ℕ → ℝ) (q : ℕ → Fin 3 → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (haccuracy : Tendsto accuracy atTop (nhds 0))
    {anchorLimit : ℝ} {activeLimit : Fin 3 → ℝ}
    (hp : Tendsto p atTop (nhds anchorLimit))
    (hq : Tendsto q atTop (nhds activeLimit))
    (hpBounds : 0 ≤ anchorLimit ∧ anchorLimit ≤ 1)
    (hqBounds : ∀ active, 0 ≤ activeLimit active ∧ activeLimit active ≤ 1)
    (hregret : ∀ᶠ index in atTop, ∀ active quit,
      p index * (activeEndpointPayoff (q index) active quit - activePayoff (q index) active)
        ≤ error index + 24 * accuracy index)
    (hfloor : ∀ᶠ index in atTop, 1 - error index ≤ 2 * p index + 14 * accuracy index)
    (hsharp : ∀ᶠ index in atTop,
      1 - error index ≤ p index * activePayoff (q index) 0 + 14 * accuracy index) :
    anchorLimit = 1 ∧ activeLimit = fun _ => 1 / 2 := by
  have hfloorLimit : 1 ≤ 2 * anchorLimit := by
    have hlimit := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub herror)
      ((hp.const_mul 2).add (haccuracy.const_mul 14)) hfloor
    simpa only [sub_zero, mul_zero, add_zero] using hlimit
  have hpPositive : 0 < anchorLimit := by linarith
  have hg (active : Fin 3) :
      Tendsto (fun index => activePayoff (q index) active)
        atTop (nhds (activePayoff activeLimit active)) :=
    ((continuous_activePayoff active).tendsto activeLimit).comp hq
  have hv (active : Fin 3) (quit : Bool) :
      Tendsto (fun index => activeEndpointPayoff (q index) active quit)
        atTop (nhds (activeEndpointPayoff activeLimit active quit)) :=
    ((continuous_activeEndpointPayoff active quit).tendsto activeLimit).comp hq
  have hendpoint (active : Fin 3) (quit : Bool) :
      activeEndpointPayoff activeLimit active quit ≤ activePayoff activeLimit active := by
    have hlimit : anchorLimit *
        (activeEndpointPayoff activeLimit active quit - activePayoff activeLimit active) ≤ 0 := by
      have hle := le_of_tendsto_of_tendsto
        (hp.mul ((hv active quit).sub (hg active)))
        (herror.add (haccuracy.const_mul 24))
        (hregret.mono fun index hindex => hindex active quit)
      simpa only [mul_zero, add_zero] using hle
    by_contra hnot
    have hpositive := mul_pos hpPositive (sub_pos.mpr (lt_of_not_ge hnot))
    linarith
  obtain ⟨hzero, hone, htwo⟩ := unique_active_probabilities_of_endpoint_inequalities
    (activeLimit 0) (activeLimit 1) (activeLimit 2)
    (hqBounds 0) (hqBounds 1) (hqBounds 2)
    (by simpa [activeEndpointPayoff, activeQuitPayoff, activePayoff] using hendpoint 0 true)
    (by simpa [activeEndpointPayoff, activeContinuePayoff, activePayoff]
      using hendpoint 0 false)
    (by simpa [activeEndpointPayoff, activeQuitPayoff, activePayoff] using hendpoint 1 true)
    (by simpa [activeEndpointPayoff, activeContinuePayoff, activePayoff]
      using hendpoint 1 false)
    (by simpa [activeEndpointPayoff, activeQuitPayoff, activePayoff] using hendpoint 2 true)
    (by simpa [activeEndpointPayoff, activeContinuePayoff, activePayoff]
      using hendpoint 2 false)
  have hfair : activeLimit = fun _ => 1 / 2 := by
    funext active
    fin_cases active <;> assumption
  have hsharpLimit : 1 ≤ anchorLimit * activePayoff activeLimit 0 := by
    have hle := le_of_tendsto_of_tendsto
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub herror)
      ((hp.mul (hg 0)).add (haccuracy.const_mul 14)) hsharp
    simpa only [sub_zero, mul_zero, add_zero] using hle
  rw [hfair] at hsharpLimit
  norm_num [activePayoff] at hsharpLimit
  exact ⟨le_antisymm hpBounds.2 hsharpLimit, hfair⟩

/-- Compact unique-cluster convergence upgrades the estimates to the entire
finite-coordinate sequence, not merely to a favorably selected subsequence.
-/
theorem finite_coordinate_rigidity
    (p error accuracy : ℕ → ℝ) (q : ℕ → Fin 3 → ℝ)
    (herror : Tendsto error atTop (nhds 0))
    (haccuracy : Tendsto accuracy atTop (nhds 0))
    (hbounds : ∀ᶠ index in atTop,
      (0 ≤ p index ∧ p index ≤ 1) ∧ ∀ active, 0 ≤ q index active ∧ q index active ≤ 1)
    (hregret : ∀ᶠ index in atTop, ∀ active quit,
      p index * (activeEndpointPayoff (q index) active quit - activePayoff (q index) active)
        ≤ error index + 24 * accuracy index)
    (hfloor : ∀ᶠ index in atTop, 1 - error index ≤ 2 * p index + 14 * accuracy index)
    (hsharp : ∀ᶠ index in atTop,
      1 - error index ≤ p index * activePayoff (q index) 0 + 14 * accuracy index) :
    Tendsto (fun index => (p index, q index)) atTop (nhds (1, fun _ => 1 / 2)) := by
  have hcompact : IsCompact
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : Fin 3 → ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hcarrier : ∀ᶠ index in atTop,
      (p index, q index) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : Fin 3 → ℝ) 1 := by
    filter_upwards [hbounds] with index hindex
    exact ⟨hindex.1, ⟨fun active => (hindex.2 active).1,
      fun active => (hindex.2 active).2⟩⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt hcarrier
  rintro ⟨anchorLimit, activeLimit⟩ hlimit hcluster
  obtain ⟨subsequence, hmono, htendsto⟩ := hcluster.tendsto_subseq
  have hp : Tendsto (p ∘ subsequence) atTop (nhds anchorLimit) :=
    continuous_fst.tendsto (anchorLimit, activeLimit) |>.comp htendsto
  have hq : Tendsto (q ∘ subsequence) atTop (nhds activeLimit) :=
    continuous_snd.tendsto (anchorLimit, activeLimit) |>.comp htendsto
  obtain ⟨hpFair, hqFair⟩ := finite_coordinate_cluster_rigidity
    (p ∘ subsequence) (error ∘ subsequence) (accuracy ∘ subsequence) (q ∘ subsequence)
    (herror.comp hmono.tendsto_atTop) (haccuracy.comp hmono.tendsto_atTop) hp hq
    hlimit.1 (fun active => ⟨hlimit.2.1 active, hlimit.2.2 active⟩)
    (hmono.tendsto_atTop.eventually hregret)
    (hmono.tendsto_atTop.eventually hfloor)
    (hmono.tendsto_atTop.eventually hsharp)
  exact Prod.ext hpFair hqFair

end GameTheory.AdaptiveChildCenter
