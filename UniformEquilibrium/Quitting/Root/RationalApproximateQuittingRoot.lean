import UniformEquilibrium.Quitting.Root.NashDefectContinuity
import UniformEquilibrium.Quitting.Root.NashExistence

/-! # Rational approximate Nash roots for finite quitting Boolean games -/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every player's Quit probability is the real cast of a rational number. -/
def IsRationalQuittingRoot (root : ι → PMF Bool) : Prop :=
  ∀ player, ∃ probability : ℚ,
    (root player true).toReal = (probability : ℝ)

/-- Every finite quitting Boolean game has a rational product root with
arbitrarily small total Nash defect. The proof uses rational density and
does not implement finite grid search. -/
theorem exists_rational_quittingRootTotalNashDefect_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) {η : ℝ} (hη : 0 < η) :
    ∃ root : ι → PMF Bool,
      IsRationalQuittingRoot root ∧
      quittingRootTotalNashDefect reward tail root < η := by
  obtain ⟨exactRoot, hexact⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) tail
  let exactSimplex := quittingSimplexOfRoot exactRoot
  choose raw hrawMono hrawBelow hrawTendsto using fun player =>
    Real.exists_seq_rat_strictMono_tendsto (exactSimplex player true)
  let probability : ι → ℕ → ℚ := fun player time =>
    max 0 (min 1 (raw player time))
  have hprobabilityZero : ∀ player time, 0 ≤ probability player time := by
    intro player time
    dsimp only [probability]
    exact le_max_left _ _
  have hprobabilityOne : ∀ player time, probability player time ≤ 1 := by
    intro player time
    dsimp only [probability]
    exact max_le (by norm_num) (min_le_left _ _)
  have hprobabilityTendsto : ∀ player,
      Tendsto (fun time => ((probability player time : ℚ) : ℝ)) atTop
        (nhds (exactSimplex player true)) := by
    intro player
    let clamp : ℝ → ℝ := fun value => max 0 (min 1 value)
    have hclampContinuous : Continuous clamp :=
      continuous_const.max (continuous_const.min continuous_id)
    have hlimitZero : 0 ≤ exactSimplex player true :=
      (exactSimplex player).property.1 true
    have hlimitOne : exactSimplex player true ≤ 1 := by
      have hsum := (exactSimplex player).property.2
      rw [Fintype.sum_bool] at hsum
      have hfalse := (exactSimplex player).property.1 false
      calc
        exactSimplex player true ≤
            exactSimplex player true + exactSimplex player false :=
          le_add_of_nonneg_right hfalse
        _ = 1 := hsum
    have hclampLimit : clamp (exactSimplex player true) =
        exactSimplex player true := by
      dsimp only [clamp]
      rw [min_eq_right hlimitOne, max_eq_right hlimitZero]
    have hraw := hrawTendsto player
    have hclamped := hclampContinuous.continuousAt.tendsto.comp hraw
    rw [hclampLimit] at hclamped
    change Tendsto (fun time => clamp ((raw player time : ℚ) : ℝ)) atTop
      (nhds (exactSimplex player true)) at hclamped
    simpa only [Function.comp_apply, probability, clamp, Rat.cast_max,
      Rat.cast_zero, Rat.cast_min, Rat.cast_one] using hclamped
  let approximate : ℕ → QuittingRootSimplex ι := fun time player =>
    ⟨fun action => if action then (probability player time : ℝ)
      else 1 - (probability player time : ℝ), by
      constructor
      · intro action
        cases action with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, sub_nonneg]
            exact_mod_cast hprobabilityOne player time
        | true =>
            simp only [↓reduceIte]
            exact_mod_cast hprobabilityZero player time
      · rw [Fintype.sum_bool]
        simp only [Bool.false_eq_true, ↓reduceIte]
        ring⟩
  have happroximate : Tendsto approximate atTop (nhds exactSimplex) := by
    rw [tendsto_pi_nhds]
    intro player
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    intro action
    cases action with
    | false =>
        have hsum := (exactSimplex player).property.2
        rw [Fintype.sum_bool] at hsum
        have hfalse : (exactSimplex player).val false =
            1 - (exactSimplex player).val true := by
          apply eq_sub_iff_add_eq.mpr
          simpa only [add_comm] using hsum
        dsimp only [approximate]
        simp only [Bool.false_eq_true, ↓reduceIte]
        change Tendsto (fun time => 1 - (probability player time : ℝ)) atTop
          (nhds ((exactSimplex player).val false))
        rw [hfalse]
        exact tendsto_const_nhds.sub (hprobabilityTendsto player)
    | true =>
        dsimp only [approximate]
        simp only [↓reduceIte]
        exact hprobabilityTendsto player
  have hpoint : Tendsto (fun time => (tail, approximate time)) atTop
      (nhds (tail, exactSimplex)) :=
    tendsto_const_nhds.prodMk_nhds happroximate
  have hdefect :=
    (continuous_quittingRootTotalNashDefect_simplex reward).continuousAt.tendsto.comp
      hpoint
  have hexactDefect : quittingRootTotalNashDefect reward tail
      (quittingRootOfSimplex exactSimplex) = 0 := by
    rw [quittingRootOfSimplex_simplexOfRoot]
    exact (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
      reward tail exactRoot).mp hexact
  change Tendsto (fun time => quittingRootTotalNashDefect reward tail
      (quittingRootOfSimplex (approximate time))) atTop
        (nhds (quittingRootTotalNashDefect reward tail
          (quittingRootOfSimplex exactSimplex))) at hdefect
  rw [hexactDefect] at hdefect
  have heventually : ∀ᶠ time in atTop,
      quittingRootTotalNashDefect reward tail
        (quittingRootOfSimplex (approximate time)) < η :=
    (tendsto_order.1 hdefect).2 _ hη
  obtain ⟨time, htime⟩ := heventually.exists
  refine ⟨quittingRootOfSimplex (approximate time), ?_, htime⟩
  intro player
  refine ⟨probability player time, ?_⟩
  exact quittingRootOfSimplex_apply_toReal (approximate time) player true

end GameTheory
