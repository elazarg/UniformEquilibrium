import MathUE.AffinePairRootCrossingAttainment
import UniformEquilibrium.Quitting.Terminal.PairMassForcingConsumer

/-! # The literal maximum of all fifteen four-player pair crossings -/

noncomputable section

namespace GameTheory

/-- The six edges of the four-player complete graph, in lexicographic order. -/
def quittingFinFourPairLabel : Fin 6 → {C : Finset (Fin 4) // C.Nonempty}
  | 0 => ⟨{0, 1}, by simp⟩
  | 1 => ⟨{0, 2}, by simp⟩
  | 2 => ⟨{0, 3}, by simp⟩
  | 3 => ⟨{1, 2}, by simp⟩
  | 4 => ⟨{1, 3}, by simp⟩
  | 5 => ⟨{2, 3}, by simp⟩

theorem quittingFinFourPairLabel_card (edge : Fin 6) :
    (quittingFinFourPairLabel edge).1.card = 2 := by
  fin_cases edge <;> decide

theorem quittingFinFourPairLabel_injective :
    Function.Injective quittingFinFourPairLabel := by decide

/-- Every actual two-player coalition occurs among the six labels. -/
theorem exists_quittingFinFourPairLabel
    (coalition : {C : Finset (Fin 4) // C.Nonempty})
    (hcard : coalition.1.card = 2) :
    ∃ edge, quittingFinFourPairLabel edge = coalition := by
  revert coalition
  decide

/-- One index for each unordered pair of distinct edges. -/
abbrev QuittingFinFourPairProjection := {edges : Fin 6 × Fin 6 // edges.1 < edges.2}

instance : Nonempty QuittingFinFourPairProjection := ⟨⟨(0, 1), by decide⟩⟩

theorem card_quittingFinFourPairProjection :
    Fintype.card QuittingFinFourPairProjection = 15 := by decide

def quittingFinFourPairCrossing (intercept slope : Fin 6 → ℝ)
    (projection : QuittingFinFourPairProjection) : ℝ :=
  Math.affinePairRootLeastCrossing
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2)

/-- The literal maximum of the fifteen pairwise least crossing values. -/
def quittingFinFourMaxPairCrossing (intercept slope : Fin 6 → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (quittingFinFourPairCrossing intercept slope)

theorem quittingFinFourPairCrossing_le_max (intercept slope : Fin 6 → ℝ)
    (projection : QuittingFinFourPairProjection) :
    quittingFinFourPairCrossing intercept slope projection ≤
      quittingFinFourMaxPairCrossing intercept slope := by
  exact Finset.le_sup' (quittingFinFourPairCrossing intercept slope) (Finset.mem_univ _)

theorem exists_quittingFinFourMaxPairCrossing_eq (intercept slope : Fin 6 → ℝ) :
    ∃ projection : QuittingFinFourPairProjection,
      quittingFinFourMaxPairCrossing intercept slope =
        quittingFinFourPairCrossing intercept slope projection := by
  obtain ⟨projection, _, hprojection⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset QuittingFinFourPairProjection).Nonempty)
    (quittingFinFourPairCrossing intercept slope)
  exact ⟨projection, hprojection⟩

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}

/-- Six affine lower bounds, imposed on the actual masses of every behavioral profile. -/
def QuittingFinFourAllPairMassForcing
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (intercept slope : Fin 6 → ℝ) : Prop :=
  ∀ (profile : (quittingGame reward).BehaviorProfile) (edge : Fin 6),
    intercept edge - slope edge * quittingTerminalExploitability reward profile ≤
      quittingBehaviorExactFiniteFirstCoalitionMass profile (quittingFinFourPairLabel edge)

private theorem projection_labels_ne (projection : QuittingFinFourPairProjection) :
    quittingFinFourPairLabel projection.1.1 ≠ quittingFinFourPairLabel projection.1.2 := by
  intro heq
  exact (ne_of_lt projection.2) (quittingFinFourPairLabel_injective heq)

/-- Every actual profile lies beyond the maximum of all fifteen crossings. -/
theorem quittingTerminalExploitability_ge_finFourMaxPairCrossing
    (intercept slope : Fin 6 → ℝ)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope)
    (profile : (quittingGame reward).BehaviorProfile) :
    quittingFinFourMaxPairCrossing intercept slope ≤
      quittingTerminalExploitability reward profile := by
  apply Finset.sup'_le
  intro projection _
  exact quittingTerminalExploitability_ge_affinePairRootLeastCrossing
    (quittingFinFourPairLabel projection.1.1) (quittingFinFourPairLabel projection.1.2)
    (quittingFinFourPairLabel_card _) (quittingFinFourPairLabel_card _)
    (projection_labels_ne projection)
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2)
    (fun source => ⟨hforcing source _, hforcing source _⟩) profile

/-- With nonnegative slopes, the maximum is exactly the first nonnegative
error at which every projected affine rectangle meets its square-root region.
This does not assert joint realizability of the six-coordinate vector. -/
theorem finFourMaxPairCrossing_le_iff_all_pair_envelopes_le_one
    (intercept slope : Fin 6 → ℝ) (hslope : ∀ edge, 0 ≤ slope edge)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope) (error : ℝ) :
    quittingFinFourMaxPairCrossing intercept slope ≤ error ↔
      0 ≤ error ∧ ∀ projection : QuittingFinFourPairProjection,
        Math.affinePairRootSum (intercept projection.1.1) (slope projection.1.1)
          (intercept projection.1.2) (slope projection.1.2) error ≤ 1 := by
  let source := quittingAlwaysContinueProfile reward
  let feasible := quittingTerminalExploitability reward source
  have hfeasible : 0 ≤ feasible := quittingTerminalExploitability_nonneg reward source
  have hroot : ∀ projection : QuittingFinFourPairProjection,
      Math.affinePairRootSum (intercept projection.1.1) (slope projection.1.1)
        (intercept projection.1.2) (slope projection.1.2) feasible ≤ 1 := by
    intro projection
    exact affinePairRootSum_exploitability_le_one_of_forcedPairMasses
      (quittingFinFourPairLabel projection.1.1) (quittingFinFourPairLabel projection.1.2)
      (quittingFinFourPairLabel_card _) (quittingFinFourPairLabel_card _)
      (projection_labels_ne projection)
      (intercept projection.1.1) (slope projection.1.1)
      (intercept projection.1.2) (slope projection.1.2)
      (fun profile => ⟨hforcing profile _, hforcing profile _⟩) source
  have hiff (projection : QuittingFinFourPairProjection) :=
    Math.mem_affinePairRootCrossingSet_iff_leastCrossing_le
      (intercept projection.1.1) (slope projection.1.1)
      (intercept projection.1.2) (slope projection.1.2) feasible error
      (hslope _) (hslope _) hfeasible (hroot projection)
  constructor
  · intro hmax
    have hall : ∀ projection : QuittingFinFourPairProjection,
        error ∈ Math.affinePairRootCrossingSet
          (intercept projection.1.1) (slope projection.1.1)
          (intercept projection.1.2) (slope projection.1.2) := by
      intro projection
      apply (hiff projection).mpr
      exact (quittingFinFourPairCrossing_le_max intercept slope projection).trans hmax
    exact ⟨(hall ⟨(0, 1), by decide⟩).1, fun projection => (hall projection).2⟩
  · rintro ⟨herror, hall⟩
    apply Finset.sup'_le
    intro projection _
    exact (hiff projection).mp ⟨herror, hall projection⟩

/-- One forbidden zero-error corner makes the maximum crossing positive. -/
theorem finFourMaxPairCrossing_pos_of_forbidden_corner
    (intercept slope : Fin 6 → ℝ)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope)
    (hcorner : ∃ projection : QuittingFinFourPairProjection,
      1 < Math.affinePairRootSum (intercept projection.1.1) (slope projection.1.1)
        (intercept projection.1.2) (slope projection.1.2) 0) :
    0 < quittingFinFourMaxPairCrossing intercept slope := by
  obtain ⟨projection, hcorner⟩ := hcorner
  have hpositive := affinePairRootLeastCrossing_pos_of_forcedPairMasses
    (quittingFinFourPairLabel projection.1.1) (quittingFinFourPairLabel projection.1.2)
    (quittingFinFourPairLabel_card _) (quittingFinFourPairLabel_card _)
    (projection_labels_ne projection)
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2) hcorner
    (fun source => ⟨hforcing source _, hforcing source _⟩)
  exact hpositive.trans_le (quittingFinFourPairCrossing_le_max intercept slope projection)

private theorem exists_maximizing_forbidden_projection
    (intercept slope : Fin 6 → ℝ)
    (hpositive : 0 < quittingFinFourMaxPairCrossing intercept slope) :
    ∃ projection : QuittingFinFourPairProjection,
      quittingFinFourMaxPairCrossing intercept slope =
        quittingFinFourPairCrossing intercept slope projection ∧
      1 < Math.affinePairRootSum (intercept projection.1.1) (slope projection.1.1)
        (intercept projection.1.2) (slope projection.1.2) 0 := by
  obtain ⟨projection, hmax⟩ := exists_quittingFinFourMaxPairCrossing_eq intercept slope
  refine ⟨projection, hmax, ?_⟩
  by_contra hnot
  have hzero := Math.affinePairRootLeastCrossing_le
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2) 0 le_rfl (le_of_not_gt hnot)
  rw [hmax] at hpositive
  exact not_lt_of_ge hzero hpositive

/-- The literal all-behavior gap is half the maximum of the fifteen crossings. -/
theorem hasTerminalExploitabilityGap_half_finFourMaxPairCrossing
    (intercept slope : Fin 6 → ℝ)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope)
    (hpositive : 0 < quittingFinFourMaxPairCrossing intercept slope) :
    HasTerminalExploitabilityGap reward (quittingFinFourMaxPairCrossing intercept slope / 2) := by
  obtain ⟨projection, hmax, hcorner⟩ :=
    exists_maximizing_forbidden_projection intercept slope hpositive
  rw [hmax]
  exact hasTerminalExploitabilityGap_half_affinePairRootLeastCrossing
    (quittingFinFourPairLabel projection.1.1) (quittingFinFourPairLabel projection.1.2)
    (quittingFinFourPairLabel_card _) (quittingFinFourPairLabel_card _)
    (projection_labels_ne projection)
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2) hcorner
    (fun source => ⟨hforcing source _, hforcing source _⟩)

/-- Every behavioral profile admits a pure finite quit time or Never gaining
at least half the literal fifteen-crossing maximum. -/
theorem exists_pureTime_gain_half_finFourMaxPairCrossing
    (intercept slope : Fin 6 → ℝ)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope)
    (hpositive : 0 < quittingFinFourMaxPairCrossing intercept slope)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who : Fin 4, ∃ quitTime : Option ℕ,
      quittingTerminalPayoff reward profile who +
          quittingFinFourMaxPairCrossing intercept slope / 2 ≤
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who := by
  obtain ⟨projection, hmax, hcorner⟩ :=
    exists_maximizing_forbidden_projection intercept slope hpositive
  rw [hmax]
  exact exists_pureTime_gain_half_affinePairRootLeastCrossing
    (quittingFinFourPairLabel projection.1.1) (quittingFinFourPairLabel projection.1.2)
    (quittingFinFourPairLabel_card _) (quittingFinFourPairLabel_card _)
    (projection_labels_ne projection)
    (intercept projection.1.1) (slope projection.1.1)
    (intercept projection.1.2) (slope projection.1.2) hcorner
    (fun source => ⟨hforcing source _, hforcing source _⟩) profile

theorem no_uniformEquilibriumPayoff_of_finFourMaxPairCrossing_pos
    (intercept slope : Fin 6 → ℝ)
    (hforcing : QuittingFinFourAllPairMassForcing reward intercept slope)
    (hpositive : 0 < quittingFinFourMaxPairCrossing intercept slope) :
    ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    (gap := quittingFinFourMaxPairCrossing intercept slope / 2) reward
  · positivity
  · exact hasTerminalExploitabilityGap_half_finFourMaxPairCrossing
      intercept slope hforcing hpositive

end GameTheory
