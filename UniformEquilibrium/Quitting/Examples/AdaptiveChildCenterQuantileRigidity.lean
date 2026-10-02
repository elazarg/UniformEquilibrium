import MathUE.PositiveVanishingSquareScale
import UniformEquilibrium.Quitting.Examples.AdaptiveChildCenterFiniteCoordinateRigidity

/-! # Actual quantile rigidity for every approximate parent sequence

The accuracy and first-crossing dates are produced from the original actual
profiles. Complete stopping laws keep every finite tail and Never atom. The
only compact coordinates are those handled in the finite-coordinate owner.
-/

noncomputable section

namespace GameTheory.AdaptiveChildCenter

open Filter Topology
open _root_.Math.Probability _root_.Math.Probability.DiscreteHazard.StoppingLaw

/-- The packet's canonical scale, without a positive-exploitability premise. -/
def quantileAccuracy (profiles : ℕ → (quittingGame reward).BehaviorProfile) : ℕ → ℝ :=
  _root_.Math.positiveVanishingSquareScale
    (fun index => quittingTerminalExploitability reward (profiles index))

theorem quantileAccuracy_pos
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (index : ℕ) :
    0 < quantileAccuracy profiles index :=
  _root_.Math.positiveVanishingSquareScale_pos _ index

theorem exploitability_le_quantileAccuracy_sq
    (profiles : ℕ → (quittingGame reward).BehaviorProfile) (index : ℕ) :
    quittingTerminalExploitability reward (profiles index) ≤ quantileAccuracy profiles index ^ 2 :=
  _root_.Math.error_le_positiveVanishingSquareScale_sq
    (fun other => quittingTerminalExploitability reward (profiles other)) index

theorem tendsto_quantileAccuracy
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) :
    Tendsto (quantileAccuracy profiles) atTop (nhds 0) :=
  _root_.Math.tendsto_positiveVanishingSquareScale _ herror

/-- After a finite prefix, each selected date is the actual first crossing.
No finite bound, monotonicity, or convergence of these dates is asserted.
-/
theorem exists_actual_firstCrossing_sequence
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) :
    ∃ cutoff : ℕ → ℕ, ∀ᶠ index in atTop,
      stoppingLawFirstCrossing? (quittingBehaviorStoppingLaws reward (profiles index) 3)
        (1 - quantileAccuracy profiles index) = some (cutoff index) ∧
      quantileAccuracy profiles index <
        survival (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff index) ∧
      survival (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff index + 1)
        ≤ quantileAccuracy profiles index ∧
      ∀ active : Fin 3,
        1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index) ≤
          quittingTerminalExploitability reward (profiles index) / quantileAccuracy profiles index ∧
        1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index) ≤ quantileAccuracy profiles index ∧
        1 - quantileAccuracy profiles index ≤
          survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index) ∧
        0 < survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
          (cutoff index) := by
  classical
  have hexists : ∀ index, ∃ cutoff, quantileAccuracy profiles index < 1 →
      stoppingLawFirstCrossing? (quittingBehaviorStoppingLaws reward (profiles index) 3)
        (1 - quantileAccuracy profiles index) = some cutoff ∧
      quantileAccuracy profiles index <
        survival (quittingBehaviorStoppingLaws reward (profiles index) 3) cutoff ∧
      survival (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff + 1)
        ≤ quantileAccuracy profiles index ∧
      ∀ active : Fin 3,
        1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc) cutoff ≤
          quittingTerminalExploitability reward (profiles index) / quantileAccuracy profiles index ∧
        1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc) cutoff ≤
          quantileAccuracy profiles index ∧
        1 - quantileAccuracy profiles index ≤
          survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc) cutoff ∧
        0 < survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
          cutoff := by
    intro index
    by_cases hsmall : quantileAccuracy profiles index < 1
    · obtain ⟨cutoff, hcutoff⟩ := exists_actual_quantile_source (profiles index)
        (le_refl _) (quantileAccuracy_pos profiles index) hsmall
        (exploitability_le_quantileAccuracy_sq profiles index)
      exact ⟨cutoff, fun _ => hcutoff⟩
    · exact ⟨0, fun hcontradiction => (hsmall hcontradiction).elim⟩
  choose cutoff hcutoff using hexists
  refine ⟨cutoff, ?_⟩
  have hsmall : ∀ᶠ index in atTop, quantileAccuracy profiles index < 1 :=
    (tendsto_order.1 (tendsto_quantileAccuracy profiles herror)).2 1 zero_lt_one
  filter_upwards [hsmall] with index hindex
  exact hcutoff index hindex

/-- Every parent approximate-Nash sequence concentrates on an actual anchor
row with fair active conditional probabilities. This uses no support cutoff,
interior original profile, favorable limit profile, or independently chosen law.
-/
theorem exists_actual_quantile_rigidity
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (herror : Tendsto (fun index => quittingTerminalExploitability reward (profiles index))
      atTop (nhds 0)) :
    ∃ cutoff : ℕ → ℕ,
      (∀ᶠ index in atTop,
        stoppingLawFirstCrossing? (quittingBehaviorStoppingLaws reward (profiles index) 3)
          (1 - quantileAccuracy profiles index) = some (cutoff index) ∧
        quantileAccuracy profiles index <
          survival (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff index) ∧
        survival (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff index + 1)
          ≤ quantileAccuracy profiles index ∧
        ∀ active : Fin 3,
          1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
              (cutoff index) ≤
            quittingTerminalExploitability reward (profiles index) /
              quantileAccuracy profiles index ∧
          1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
              (cutoff index) ≤ quantileAccuracy profiles index ∧
          1 - quantileAccuracy profiles index ≤
            survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
              (cutoff index) ∧
          0 < survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index)) ∧
      Tendsto (fun index =>
        finiteMass (quittingBehaviorStoppingLaws reward (profiles index) 3) (cutoff index))
        atTop (nhds 1) ∧
      Tendsto (fun index => conditionalProbabilities
        (quittingBehaviorStoppingLaws reward (profiles index)) (cutoff index))
        atTop (nhds (fun _ => 1 / 2)) ∧
      ∀ active : Fin 3,
        Tendsto (fun index =>
          1 - survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index)) atTop (nhds 0) ∧
        Tendsto (fun index =>
          survival (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index)) atTop (nhds 1) ∧
        Tendsto (fun index =>
          finiteMass (quittingBehaviorStoppingLaws reward (profiles index) active.castSucc)
            (cutoff index)) atTop (nhds (1 / 2)) := by
  obtain ⟨cutoff, hsource⟩ := exists_actual_firstCrossing_sequence profiles herror
  let laws := fun index => quittingBehaviorStoppingLaws reward (profiles index)
  let error := fun index => quittingTerminalExploitability reward (profiles index)
  let accuracy := quantileAccuracy profiles
  let p := fun index => finiteMass (laws index 3) (cutoff index)
  let q := fun index => conditionalProbabilities (laws index) (cutoff index)
  have haccuracy : Tendsto accuracy atTop (nhds 0) :=
    tendsto_quantileAccuracy profiles herror
  have hbounds : ∀ᶠ index in atTop,
      (0 ≤ p index ∧ p index ≤ 1) ∧ ∀ active, 0 ≤ q index active ∧ q index active ≤ 1 := by
    filter_upwards [hsource] with index hindex
    have hpositive : ∀ active : Fin 3,
        0 < survival (laws index active.castSucc) (cutoff index) :=
      fun active => (hindex.2.2.2 active).2.2.2
    refine ⟨⟨finiteMass_nonneg _ _, ?_⟩,
      conditionalProbabilities_bounds (laws index) (cutoff index) hpositive⟩
    simpa only [p, finiteMass, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top
        (PMF.coe_le_one (laws index 3) (some (cutoff index)))
  have hregret : ∀ᶠ index in atTop, ∀ active quit,
      p index * (activeEndpointPayoff (q index) active quit - activePayoff (q index) active)
        ≤ error index + 24 * accuracy index := by
    filter_upwards [hsource] with index hindex active quit
    exact actual_endpoint_regret_estimate (profiles index) (cutoff index)
      (fun who => (hindex.2.2.2 who).2.2.2) (le_refl _)
      (fun who => (hindex.2.2.2 who).2.1) hindex.2.2.1 active quit
  have hfloor : ∀ᶠ index in atTop, 1 - error index ≤ 2 * p index + 14 * accuracy index := by
    filter_upwards [hsource] with index hindex
    exact (one_sub_error_le_zero_payoff (profiles index) (le_refl _)).trans
      (zero_payoff_le_two_anchor_mass_add (profiles index) (cutoff index)
        (fun who => (hindex.2.2.2 who).2.2.2)
        (fun who => (hindex.2.2.2 who).2.1) hindex.2.2.1)
  have hsharp : ∀ᶠ index in atTop,
      1 - error index ≤ p index * activePayoff (q index) 0 + 14 * accuracy index := by
    filter_upwards [hsource] with index hindex
    have hguarantee := one_sub_error_le_zero_payoff (profiles index) (le_refl _)
    change 1 - error index ≤ quittingTerminalPayoff reward (profiles index) 0 at hguarantee
    have hestimate := actual_prescribed_payoff_estimate (profiles index) (cutoff index)
      (fun who => (hindex.2.2.2 who).2.2.2)
      (fun who => (hindex.2.2.2 who).2.1) hindex.2.2.1 0
    change |quittingTerminalPayoff reward (profiles index) 0 -
      p index * activePayoff (q index) 0| ≤ 14 * accuracy index at hestimate
    have hprescribed := abs_le.mp hestimate
    linarith [hprescribed.2]
  have hcoordinates := finite_coordinate_rigidity p error accuracy q herror haccuracy
    hbounds hregret hfloor hsharp
  have hp : Tendsto p atTop (nhds 1) :=
    continuous_fst.tendsto (1, fun _ : Fin 3 => (1 / 2 : ℝ)) |>.comp hcoordinates
  have hq : Tendsto q atTop (nhds (fun _ => 1 / 2)) :=
    continuous_snd.tendsto (1, fun _ : Fin 3 => (1 / 2 : ℝ)) |>.comp hcoordinates
  refine ⟨cutoff, hsource, hp, hq, ?_⟩
  intro active
  have hbeforeNonneg : ∀ index,
      0 ≤ 1 - survival (laws index active.castSucc) (cutoff index) := by
    intro index
    rw [← sum_finiteMass_range_eq_one_sub_survival]
    exact Finset.sum_nonneg fun time _ => finiteMass_nonneg _ time
  have hbefore : Tendsto
      (fun index => 1 - survival (laws index active.castSucc) (cutoff index))
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall hbeforeNonneg) ?_ haccuracy
    exact hsource.mono fun index hindex => (hindex.2.2.2 active).2.1
  have hsurvival : Tendsto
      (fun index => survival (laws index active.castSucc) (cutoff index))
      atTop (nhds 1) := by
    have hsub :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).sub hbefore
    have heq : (fun index => 1 - (1 - survival (laws index active.castSucc) (cutoff index))) =
        (fun index => survival (laws index active.castSucc) (cutoff index)) := by
      funext index
      ring
    rw [heq, sub_zero] at hsub
    exact hsub
  have hmassIdentity : ∀ᶠ index in atTop,
      finiteMass (laws index active.castSucc) (cutoff index) =
        survival (laws index active.castSucc) (cutoff index) * q index active := by
    filter_upwards [hsource] with index hindex
    dsimp only [q, conditionalProbabilities]
    exact (mul_div_cancel₀ _ (hindex.2.2.2 active).2.2.2.ne').symm
  have hmass := (hsurvival.mul (tendsto_pi_nhds.mp hq active)).congr'
    (hmassIdentity.mono fun _ hidentity => hidentity.symm)
  exact ⟨hbefore, hsurvival, by simpa only [one_mul] using hmass⟩

end GameTheory.AdaptiveChildCenter
