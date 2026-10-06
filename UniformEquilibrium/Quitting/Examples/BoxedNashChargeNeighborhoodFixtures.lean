import UniformEquilibrium.Quitting.Examples.BoxedNashChargeTripleFixture
import UniformEquilibrium.Quitting.Examples.BoxedNashChargeFullCoreFixture
import UniformEquilibrium.Quitting.Classification.BoxedQuittingNashChargeNeighborhood

/-! # Strict-slack neighborhoods of both literal boxed-charge tables

The fixed coordinate bound four is strictly above the attained maxima of both
tables. The proper-triple table has positive own singletons, while the full-core
table lies on the boundary of the nonnegative-singleton restriction.
-/

noncomputable section

namespace GameTheory.BoxedNashChargeNeighborhoodFixtures

open Filter
open scoped Topology

def tripleCoefficients : QuittingTrapChargeCoefficients
    BoxedNashChargeTripleFixture.reward {0, 1, 2} where
  delta := 2 / 5
  tau := 1 / 5
  gap := 7 / 5
  loss := 4 / 5
  delta_pos := by norm_num
  tau_pos := by norm_num
  gap_pos := by norm_num
  loss_pos := by norm_num
  card_ge_three := by decide
  singleton := by
    intro coalition hne hproper hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeTripleFixture.singleton_sums coalition hne hproper hcard
    rw [hpremium, hleave]
    norm_num
  middle := by
    intro coalition _ _ hlow hhigh
    have hsize : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hsize] at hhigh
    omega
  penultimate := by
    intro coalition hne hproper hcard
    have hsize : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hsize] at hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeTripleFixture.pair_sums coalition hne hproper hcard
    rw [hpremium, hleave]
    norm_num

theorem tripleCoefficients_strict : tripleCoefficients.Strict := by
  refine ⟨?_, ?_, ?_⟩
  · intro coalition hne hproper hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeTripleFixture.singleton_sums coalition hne hproper hcard
    rw [hpremium, hleave]
    norm_num [tripleCoefficients]
  · intro coalition _ _ hlow hhigh
    have hsize : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hsize] at hhigh
    omega
  · intro coalition hne hproper hcard
    have hsize : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide
    rw [hsize] at hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeTripleFixture.pair_sums coalition hne hproper hcard
    rw [hpremium, hleave]
    norm_num [tripleCoefficients]

theorem triple_threshold_eq : tripleCoefficients.threshold = 18 := by
  rw [tripleCoefficients.threshold_of_cardinality_three (by decide)]
  norm_num [tripleCoefficients]

theorem triple_strict_charges :
    HasStrictBoxedQuittingNashCharges BoxedNashChargeTripleFixture.reward 4 := by
  intro active htrap
  rw [BoxedNashChargeTripleFixture.trap_iff] at htrap
  subst active
  refine ⟨tripleCoefficients, tripleCoefficients_strict, ?_⟩
  rw [triple_threshold_eq]
  simp only [BoxedNashChargeTripleFixture.reward_singleton]
  norm_num [Finset.sum_insert]

def fullCoefficients : QuittingTrapChargeCoefficients
    BoxedNashChargeFullCoreFixture.reward Finset.univ where
  delta := 4
  tau := 1 / 5
  gap := 1
  loss := 3 / 2
  delta_pos := by norm_num
  tau_pos := by norm_num
  gap_pos := by norm_num
  loss_pos := by norm_num
  card_ge_three := by decide
  singleton := by
    intro coalition hne _ hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.singleton_sums coalition hne hcard
    rw [hpremium]
    constructor
    · norm_num
    · linarith
  middle := by
    intro coalition hne _ hlow hhigh
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hhigh
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.pair_sums coalition hne (by omega)
    rw [hpremium, hleave]
    norm_num
  penultimate := by
    intro coalition hne _ hcard
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.triple_sums coalition hne hcard
    rw [hpremium, hleave]
    norm_num

theorem fullCoefficients_strict : fullCoefficients.Strict := by
  refine ⟨?_, ?_, ?_⟩
  · intro coalition hne _ hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.singleton_sums coalition hne hcard
    rw [hpremium]
    constructor
    · norm_num [fullCoefficients]
    · change _ < -(1 : ℝ)
      linarith
  · intro coalition hne _ hlow hhigh
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hhigh
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.pair_sums coalition hne (by omega)
    rw [hpremium, hleave]
    norm_num
  · intro coalition hne _ hcard
    have hsize : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hsize] at hcard
    obtain ⟨hpremium, hleave⟩ :=
      BoxedNashChargeFullCoreFixture.triple_sums coalition hne hcard
    rw [hpremium, hleave]
    norm_num [fullCoefficients]

theorem full_threshold_eq : fullCoefficients.threshold = 124 * Real.sqrt 20 := by
  rw [fullCoefficients.threshold_of_cardinality_four (by decide)]
  norm_num [fullCoefficients]
  ring

theorem full_strict_charges :
    HasStrictBoxedQuittingNashCharges BoxedNashChargeFullCoreFixture.reward 4 := by
  intro active htrap
  rw [BoxedNashChargeFullCoreFixture.trap_iff] at htrap
  subst active
  refine ⟨fullCoefficients, fullCoefficients_strict, ?_⟩
  rw [full_threshold_eq]
  simp only [BoxedNashChargeFullCoreFixture.reward_singleton]
  norm_num [Fin.sum_univ_succ]
  have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)
  have hnonnegative := Real.sqrt_nonneg (20 : ℝ)
  nlinarith

theorem full_strict_charges_five :
    HasStrictBoxedQuittingNashCharges BoxedNashChargeFullCoreFixture.reward 5 := by
  intro active htrap
  rw [BoxedNashChargeFullCoreFixture.trap_iff] at htrap
  subst active
  refine ⟨fullCoefficients, fullCoefficients_strict, ?_⟩
  rw [full_threshold_eq]
  simp only [BoxedNashChargeFullCoreFixture.reward_singleton]
  norm_num [Fin.sum_univ_succ]
  have hsquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)
  have hnonnegative := Real.sqrt_nonneg (20 : ℝ)
  nlinarith

theorem eventually_triple_uniformPayoff :
    ∀ᶠ nearby in 𝓝 BoxedNashChargeTripleFixture.reward,
      ∃ payoff : Payoff (Fin 4),
        (quittingGame nearby).IsUniformEquilibriumPayoff none payoff := by
  have hpositive : ∀ᶠ nearby in 𝓝 BoxedNashChargeTripleFixture.reward,
      ∀ player, 0 < nearby (quittingSingletonTerminal player) player := by
    rw [Filter.eventually_all]
    intro player
    have hcontinuous : Continuous
        (fun nearby : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) =>
          nearby (quittingSingletonTerminal player) player) := by fun_prop
    exact hcontinuous.continuousAt.eventually_const_lt
      (BoxedNashChargeTripleFixture.singleton_positive player)
  filter_upwards
    [eventually_boxedQuittingNashCharges_of_strict_tests BoxedNashChargeTripleFixture.reward
      4 BoxedNashChargeTripleFixture.nonsingleton_participant_gap_ne_zero triple_strict_charges,
    eventually_reward_abs_lt_of_strict_bound BoxedNashChargeTripleFixture.reward 4
      (fun terminal player =>
        (BoxedNashChargeTripleFixture.reward_abs_le terminal player).trans_lt (by norm_num)),
    hpositive] with nearby hcharges hbound hsingleton
  exact exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges nearby
    (fun player => (hsingleton player).le) 4 (fun terminal player => (hbound terminal player).le)
    hcharges

theorem eventually_full_raw_charges :
    ∀ᶠ nearby in 𝓝 BoxedNashChargeFullCoreFixture.reward,
      HasBoxedQuittingNashCharges nearby 4 ∧
        (∀ terminal player, |nearby terminal player| < 4) := by
  exact (eventually_boxedQuittingNashCharges_of_strict_tests
    BoxedNashChargeFullCoreFixture.reward 4
    BoxedNashChargeFullCoreFixture.nonsingleton_participant_gap_ne_zero full_strict_charges).and
    (eventually_reward_abs_lt_of_strict_bound BoxedNashChargeFullCoreFixture.reward 4
      (fun terminal player =>
        (BoxedNashChargeFullCoreFixture.reward_abs_le terminal player).trans_lt (by norm_num)))

theorem eventually_full_uniformPayoff_on_nonnegative_singletons :
    ∀ᶠ nearby in 𝓝 BoxedNashChargeFullCoreFixture.reward,
      (∀ player, 0 ≤ nearby (quittingSingletonTerminal player) player) →
        ∃ payoff : Payoff (Fin 4),
          (quittingGame nearby).IsUniformEquilibriumPayoff none payoff := by
  filter_upwards [eventually_full_raw_charges] with nearby hraw hsingleton
  exact exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges nearby hsingleton 4
    (fun terminal player => (hraw.2 terminal player).le) hraw.1

/-- A signed analytic neighborhood with one box per nearby table, selected
before the potential and without nonnegative own singletons. -/
theorem eventually_full_potential_exclusion :
    ∀ᶠ nearby in 𝓝 BoxedNashChargeFullCoreFixture.reward,
      ∃ bound, 4 < bound ∧ bound < 6 ∧
        ∀ potential : Payoff (Fin 4) → ℝ,
          ContinuousOn potential (quittingBoxedSingletonSublevelDomain nearby bound) →
          (∀ point ∈ Math.lowerBoxBoundary
            (fun player => quittingSoloReward nearby player player) (fun _ => bound),
              DifferentiableAt ℝ potential point) →
          ¬IsQuittingFullExactRootPotential nearby bound potential := by
  filter_upwards [eventually_full_raw_charges] with nearby hraw
  simpa only [show (4 : ℝ) + 2 = 6 by norm_num] using
    exists_box_potential_exclusion_of_boxedQuittingNashCharges nearby 4
    (fun terminal player => (hraw.2 terminal player).le) hraw.1

/-- The literal fixed box five also works throughout a signed neighborhood. -/
theorem eventually_full_potential_exclusion_fixed_box :
    ∀ᶠ nearby in 𝓝 BoxedNashChargeFullCoreFixture.reward,
      ∀ potential : Payoff (Fin 4) → ℝ,
        ContinuousOn potential (quittingBoxedSingletonSublevelDomain nearby 5) →
        (∀ point ∈ Math.lowerBoxBoundary
          (fun player => quittingSoloReward nearby player player) (fun _ => (5 : ℝ)),
            DifferentiableAt ℝ potential point) →
        ¬IsQuittingFullExactRootPotential nearby 5 potential := by
  filter_upwards [eventually_full_raw_charges,
    eventually_boxedQuittingNashCharges_of_strict_tests BoxedNashChargeFullCoreFixture.reward
      5 BoxedNashChargeFullCoreFixture.nonsingleton_participant_gap_ne_zero
      full_strict_charges_five] with nearby hraw hcharges
  intro potential hcontinuous hdiff
  exact not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn nearby
    (fun terminal player => (hraw.2 terminal player).le) (by norm_num : (4 : ℝ) < 5)
    (hasBoxedSelectedSingletonSublevelReturn_of_boxedQuittingNashCharges
      nearby (fun terminal player => (hraw.2 terminal player).le) hcharges)
    potential hcontinuous hdiff

/-- Raise only the three zero own-singletons, preserving player zero. -/
def fullSingletonRaise (delta : ℝ) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal player => BoxedNashChargeFullCoreFixture.reward terminal player +
    if terminal.val = {player} ∧ player ≠ 0 then delta else 0

theorem fullSingletonRaise_zero :
    fullSingletonRaise 0 = BoxedNashChargeFullCoreFixture.reward := by
  funext terminal player
  simp [fullSingletonRaise]

theorem continuous_fullSingletonRaise : Continuous fullSingletonRaise := by
  apply continuous_pi
  intro terminal
  apply continuous_pi
  intro player
  by_cases h : terminal.val = {player} ∧ player ≠ 0
  · simp only [fullSingletonRaise, ite_eq_left h]
    exact continuous_const.add continuous_id
  · simp only [fullSingletonRaise, ite_eq_right h, add_zero]
    exact continuous_const

theorem fullSingletonRaise_singleton (delta : ℝ) (player : Fin 4) :
    fullSingletonRaise delta (quittingSingletonTerminal player) player =
      BoxedNashChargeFullCoreFixture.reward (quittingSingletonTerminal player) player +
        (if player = 0 then 0 else delta) := by
  by_cases h : player = 0
  · simp [fullSingletonRaise, h]
  simp [fullSingletonRaise, quittingSingletonTerminal]

theorem abs_fullSingletonRaise_sub_le (delta : ℝ)
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (player : Fin 4) :
    |fullSingletonRaise delta terminal player -
      BoxedNashChargeFullCoreFixture.reward terminal player| ≤ |delta| := by
  by_cases h : terminal.val = {player} ∧ player ≠ 0
  · simp [fullSingletonRaise, h]
  · simp [fullSingletonRaise, h]

/-- Every sufficiently small positive own-singleton raise produces an actual
interior UE table, with a full reward-coordinate neighborhood of UE tables. -/
theorem eventually_positive_fullSingletonRaise_uniformPayoff_neighborhood :
    ∀ᶠ delta in 𝓝 (0 : ℝ), 0 < delta →
      (∀ player, 0 < fullSingletonRaise delta (quittingSingletonTerminal player) player) ∧
      ∀ᶠ nearby in 𝓝 (fullSingletonRaise delta),
        ∃ payoff : Payoff (Fin 4),
          (quittingGame nearby).IsUniformEquilibriumPayoff none payoff := by
  have hraw : ∀ᶠ delta in 𝓝 (0 : ℝ),
      ∀ᶠ nearby in 𝓝 (fullSingletonRaise delta),
        HasBoxedQuittingNashCharges nearby 4 ∧
          (∀ terminal player, |nearby terminal player| < 4) := by
    have hnear := eventually_eventually_nhds.mpr eventually_full_raw_charges
    have hzero : Tendsto fullSingletonRaise (𝓝 0)
        (𝓝 BoxedNashChargeFullCoreFixture.reward) := by
      have h := continuous_fullSingletonRaise.tendsto (0 : ℝ)
      rw [fullSingletonRaise_zero] at h
      exact h
    exact hzero.eventually hnear
  filter_upwards [hraw] with delta hraw hdelta
  have hpositive : ∀ player,
      0 < fullSingletonRaise delta (quittingSingletonTerminal player) player := by
    intro player
    rw [fullSingletonRaise_singleton]
    by_cases hzero : player = 0
    · subst player
      norm_num [BoxedNashChargeFullCoreFixture.reward_singleton]
    rw [ite_eq_right hzero]
    have hnonnegative := BoxedNashChargeFullCoreFixture.singleton_nonnegative player
    linarith
  refine ⟨hpositive, ?_⟩
  have hnearPositive : ∀ᶠ nearby in 𝓝 (fullSingletonRaise delta),
      ∀ player, 0 < nearby (quittingSingletonTerminal player) player := by
    rw [Filter.eventually_all]
    intro player
    have hcontinuous : Continuous
        (fun nearby : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) =>
          nearby (quittingSingletonTerminal player) player) := by fun_prop
    exact hcontinuous.continuousAt.eventually_const_lt (hpositive player)
  filter_upwards [hraw, hnearPositive] with nearby hraw hpositive
  exact exists_uniformEquilibriumPayoff_of_boxedQuittingNashCharges nearby
    (fun player => (hpositive player).le) 4
    (fun terminal player => (hraw.2 terminal player).le) hraw.1

end GameTheory.BoxedNashChargeNeighborhoodFixtures
