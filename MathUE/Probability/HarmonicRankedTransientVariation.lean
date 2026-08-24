/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.PivotExcursionRenewal

/-!
# Backward-harmonic variation on a ranked transient graph

Suppose the transient support graph of a finite homogeneous Markov kernel has no directed
cycle involving two distinct transient states.  Equivalently, after choosing a topological
rank, every supported transition between distinct transient states strictly decreases rank;
self-loops remain unrestricted.

The time-dependent sharp bound is then obtained from one coupled potential.  At the current
transient state, the Bernoulli potential pays all variation accumulated through arbitrarily
many self-loops.  The integer rank pays the potential installed after a strict transition to
a lower transient state.  Thus sticky self-loops cost no occupation-time factor, and every
non-self transient move consumes at least one unit of a finite cardinality budget.

This proves Simon's sharp transient-cardinality estimate for the whole ranked class.  The
remaining case of the general theorem therefore requires a nontrivial transient directed
cycle, exactly where duration-labelled state elimination must couple several return clocks.
-/

namespace Math.Probability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- A topological ranking of the transient support graph after self-loops are removed. -/
structure TransientSelfLoopRankCertificate (kernel : Omega → PMF Omega) where
  rank : Omega → ℕ
  rank_lt_card : ∀ {state}, state ∈ finiteTransientStates kernel →
    rank state < (finiteTransientStates kernel).card
  descends : ∀ {source destination},
    source ∈ finiteTransientStates kernel →
    destination ∈ (kernel source).support →
    destination ∈ finiteTransientStates kernel →
    destination ≠ source → rank destination < rank source

/-- No mutual-reachability class contains two distinct transient states.  This is the
intrinsic graph condition behind `TransientSelfLoopRankCertificate`. -/
def HasSingletonTransientCommunicationClasses (kernel : Omega → PMF Omega) : Prop :=
  ∀ ⦃first second⦄,
    first ∈ finiteTransientStates kernel →
    second ∈ finiteTransientStates kernel →
    PMFCommunicates kernel first second → first = second

/-- Strict transient descendants of a state in the support reachability order. -/
def strictTransientFuture (kernel : Omega → PMF Omega) (source : Omega) : Finset Omega :=
  by
    classical
    exact (finiteTransientStates kernel).filter fun destination =>
      destination ≠ source ∧ PMFReachable kernel source destination

theorem mem_strictTransientFuture_iff
    (kernel : Omega → PMF Omega) (source destination : Omega) :
    destination ∈ strictTransientFuture kernel source ↔
      destination ∈ finiteTransientStates kernel ∧
        destination ≠ source ∧ PMFReachable kernel source destination := by
  classical
  simp [strictTransientFuture]

/-- Singleton transient communication classes canonically supply the required rank: the
rank of a state is the number of its strict transient descendants. -/
def transientSelfLoopRankCertificateOfSingletonClasses
    (kernel : Omega → PMF Omega)
    (singletonClasses : HasSingletonTransientCommunicationClasses kernel) :
    TransientSelfLoopRankCertificate kernel := by
  classical
  refine {
    rank := fun state => (strictTransientFuture kernel state).card
    rank_lt_card := ?_
    descends := ?_ }
  · intro state state_transient
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro destination destination_future
      exact (mem_strictTransientFuture_iff kernel state destination).mp
        destination_future |>.1
    · intro future_eq
      have state_not_future : state ∉ strictTransientFuture kernel state := by
        simp [strictTransientFuture]
      exact state_not_future (future_eq.symm ▸ state_transient)
  · intro source destination source_transient destination_support
      destination_transient destination_ne
    have support_step : PMFSupportStep kernel source destination := by
      simpa [PMFSupportStep, PMF.mem_support_iff] using destination_support
    have source_reaches_destination : PMFReachable kernel source destination :=
      Relation.ReflTransGen.single support_step
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro state state_future
      obtain ⟨state_transient, state_ne_destination, destination_reaches_state⟩ :=
        (mem_strictTransientFuture_iff kernel destination state).mp state_future
      have state_ne_source : state ≠ source := by
        intro state_eq
        subst state
        have source_eq_destination := singletonClasses source_transient
          destination_transient
          ⟨source_reaches_destination, destination_reaches_state⟩
        exact destination_ne source_eq_destination.symm
      apply (mem_strictTransientFuture_iff kernel source state).mpr
      exact ⟨state_transient, state_ne_source,
        Relation.ReflTransGen.head support_step destination_reaches_state⟩
    · intro future_eq
      have destination_mem_source_future :
          destination ∈ strictTransientFuture kernel source := by
        apply (mem_strictTransientFuture_iff kernel source destination).mpr
        exact ⟨destination_transient, destination_ne,
          source_reaches_destination⟩
      have destination_not_own_future :
          destination ∉ strictTransientFuture kernel destination := by
        simp [strictTransientFuture]
      exact destination_not_own_future
        (future_eq ▸ destination_mem_source_future)

/-- The Bernoulli self-loop account plus the remaining strict-descent budget. -/
def rankedTransientBernoulliPotential
    {kernel : Omega → PMF Omega}
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) : ℝ :=
  if state ∈ finiteTransientStates kernel then
    bernoulliVariationPotential (value state time) + certificate.rank state
  else 0

theorem rankedTransientBernoulliPotential_nonneg
    {kernel : Omega → PMF Omega}
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) :
    0 ≤ rankedTransientBernoulliPotential certificate value state time := by
  rw [rankedTransientBernoulliPotential]
  split_ifs
  · exact add_nonneg (bernoulliVariationPotential_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem bernoulliVariationPotential_le_one_of_mem_Icc
    {current : ℝ} (bounded : current ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliVariationPotential current ≤ 1 := by
  have hsqrt0 : 0 ≤ Real.sqrt (current * (1 - current)) := Real.sqrt_nonneg _
  have hsquare :
      (Real.sqrt (current * (1 - current))) ^ 2 = current * (1 - current) := by
    rw [Real.sq_sqrt (mul_nonneg bounded.1 (sub_nonneg.mpr bounded.2))]
  rw [bernoulliVariationPotential]
  nlinarith [sq_nonneg (current - (1 / 2 : ℝ))]

theorem rankedTransientBernoulliPotential_le_transientCard
    {kernel : Omega → PMF Omega}
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (state : Omega) (time : ℕ) :
    rankedTransientBernoulliPotential certificate value state time ≤
      (finiteTransientStates kernel).card := by
  rw [rankedTransientBernoulliPotential]
  split_ifs with hstate
  · have hrank := certificate.rank_lt_card hstate
    have hbernoulli := bernoulliVariationPotential_le_one_of_mem_Icc
      (bounded state time)
    have hcast : (certificate.rank state : ℝ) + 1 ≤
        ((finiteTransientStates kernel).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hrank)
    linarith
  · exact Nat.cast_nonneg _

private theorem rankedPotential_le_selfPotential_add_rank
    {kernel : Omega → PMF Omega}
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    {source : Omega} (source_transient : source ∈ finiteTransientStates kernel)
    {destination : Omega} (destination_support : destination ∈ (kernel source).support)
    (time : ℕ) :
    rankedTransientBernoulliPotential certificate value destination (time + 1) ≤
      singleTransientBernoulliPotential source value destination (time + 1) +
        certificate.rank source := by
  by_cases destination_eq : destination = source
  · subst destination
    simp [rankedTransientBernoulliPotential, source_transient,
      singleTransientBernoulliPotential, bernoulliVariationPotential]
  · rw [singleTransientBernoulliPotential]
    simp only [if_neg destination_eq, zero_add]
    rw [rankedTransientBernoulliPotential]
    split_ifs with destination_transient
    · have hrank := certificate.descends source_transient destination_support
        destination_transient destination_eq
      have hbernoulli := bernoulliVariationPotential_le_one_of_mem_Icc
        (bounded destination (time + 1))
      have hcast : (certificate.rank destination : ℝ) + 1 ≤
          (certificate.rank source : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hrank)
      linarith
    · exact Nat.cast_nonneg _

/-- One-step potential loss pays the whole conditional absolute increment. -/
theorem conditionalVariation_add_rankedTransientPotential_le
    {kernel : Omega → PMF Omega}
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (source : Omega) (time : ℕ) :
    expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|) +
      expect (kernel source) (fun successor ↦
        rankedTransientBernoulliPotential certificate value successor (time + 1)) ≤
      rankedTransientBernoulliPotential certificate value source time := by
  by_cases source_transient : source ∈ finiteTransientStates kernel
  · have hpotential :
        expect (kernel source) (fun successor ↦
            rankedTransientBernoulliPotential certificate value successor (time + 1)) ≤
          expect (kernel source) (fun successor ↦
            singleTransientBernoulliPotential source value successor (time + 1) +
              certificate.rank source) := by
      apply Math.ProbabilityMassFunction.expect_mono_on_support
      intro destination destination_support
      exact rankedPotential_le_selfPotential_add_rank certificate value harmonic.1
        source_transient destination_support time
    rw [expect_add, expect_const,
      expect_singleTransientBernoulliPotential] at hpotential
    have hpeeling := pivotLocalVariation_add_selfPotential_le
      kernel source value harmonic time
    rw [rankedTransientBernoulliPotential, if_pos source_transient]
    simp only [pivotLocalVariation, bernoulliVariationPotential] at hpeeling
    simp only [bernoulliVariationPotential]
    linarith
  · have source_recurrent : source ∈ finiteRecurrentCore kernel := by
      exact not_not.mp (mt (mem_finiteTransientStates_iff kernel source).mpr
        source_transient)
    have hvariation := expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value harmonic source_recurrent time
    have hpotential :
        expect (kernel source) (fun successor ↦
          rankedTransientBernoulliPotential certificate value successor (time + 1)) = 0 := by
      calc
        expect (kernel source) (fun successor ↦
            rankedTransientBernoulliPotential certificate value successor (time + 1)) =
            expect (kernel source) (fun _ ↦ (0 : ℝ)) := by
          apply Math.ProbabilityMassFunction.expect_congr_on_support
          intro successor successor_support
          have successor_recurrent := finiteRecurrentCore_closed kernel
            source_recurrent successor_support
          have successor_not_transient :
              successor ∉ finiteTransientStates kernel := by
            intro successor_transient
            exact ((mem_finiteTransientStates_iff kernel successor).mp
              successor_transient) successor_recurrent
          simp [rankedTransientBernoulliPotential, successor_not_transient]
        _ = 0 := expect_const _ _
    rw [hvariation, hpotential]
    simp [rankedTransientBernoulliPotential, source_transient]

/-- Sharp time-dependent variation bound when all non-self transient moves strictly descend
a finite rank.  Arbitrarily sticky transient self-loops are allowed. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_ranked
    (initial : Omega) (kernel : Omega → PMF Omega)
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      (finiteTransientStates kernel).card := by
  let potential : Omega → ℕ → ℝ :=
    rankedTransientBernoulliPotential certificate value
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (rankedTransientBernoulliPotential_nonneg certificate value)
      (conditionalVariation_add_rankedTransientPotential_le
        certificate value harmonic) horizon).trans
    (rankedTransientBernoulliPotential_le_transientCard
      certificate value harmonic.1 initial 0)

/-- Reader-facing form with Simon's coarser total-state cardinality. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_card_of_ranked
    (initial : Omega) (kernel : Omega → PMF Omega)
    (certificate : TransientSelfLoopRankCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      Fintype.card Omega := by
  exact (finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_ranked
    initial kernel certificate value harmonic horizon).trans (by
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ (finiteTransientStates kernel)))

/-- Intrinsic graph form: if every transient communication class is a singleton, the sharp
time-dependent bound is the number of transient states. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_singletonClasses
    (initial : Omega) (kernel : Omega → PMF Omega)
    (singletonClasses : HasSingletonTransientCommunicationClasses kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      (finiteTransientStates kernel).card := by
  exact finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_ranked
    initial kernel
      (transientSelfLoopRankCertificateOfSingletonClasses kernel singletonClasses)
      value harmonic horizon

/-- Simon's stated cardinality bound for kernels with no nontrivial transient communication
class. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_card_of_singletonTransientClasses
    (initial : Omega) (kernel : Omega → PMF Omega)
    (singletonClasses : HasSingletonTransientCommunicationClasses kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      Fintype.card Omega := by
  exact (finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_singletonClasses
    initial kernel singletonClasses value harmonic horizon).trans (by
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ (finiteTransientStates kernel)))

/-! ## Functional transient support, including directed cycles -/

/-- Every kernel row has at most one supported successor in the transient core.  The unique
successor may depend on the row, and the resulting transient graph may contain directed
cycles. -/
def HasAtMostOneSupportedTransientSuccessor (kernel : Omega → PMF Omega) : Prop :=
  ∀ ⦃source first second⦄,
    first ∈ (kernel source).support →
    first ∈ finiteTransientStates kernel →
    second ∈ (kernel source).support →
    second ∈ finiteTransientStates kernel → first = second

/-- The Bernoulli potential installed exactly while the chain is transient. -/
def transientBernoulliPotential
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (state : Omega) (time : ℕ) : ℝ :=
  if state ∈ finiteTransientStates kernel then
    bernoulliVariationPotential (value state time)
  else 0

theorem transientBernoulliPotential_nonneg
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (state : Omega) (time : ℕ) :
    0 ≤ transientBernoulliPotential kernel value state time := by
  simp only [transientBernoulliPotential]
  split_ifs
  · exact bernoulliVariationPotential_nonneg _
  · exact le_rfl

theorem transientBernoulliPotential_le_one
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (state : Omega) (time : ℕ) :
    transientBernoulliPotential kernel value state time ≤ 1 := by
  simp only [transientBernoulliPotential]
  split_ifs
  · exact bernoulliVariationPotential_le_one_of_mem_Icc (bounded state time)
  · norm_num

private theorem expect_transientBernoulliPotential_eq_atom
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (unique : HasAtMostOneSupportedTransientSuccessor kernel)
    {source pivot : Omega} (pivot_support : pivot ∈ (kernel source).support)
    (pivot_transient : pivot ∈ finiteTransientStates kernel) (time : ℕ) :
    expect (kernel source) (fun successor ↦
        transientBernoulliPotential kernel value successor time) =
      (kernel source pivot).toReal *
        bernoulliVariationPotential (value pivot time) := by
  calc
    expect (kernel source) (fun successor ↦
        transientBernoulliPotential kernel value successor time) =
        expect (kernel source) (fun successor ↦
          singleTransientBernoulliPotential pivot value successor time) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro successor successor_support
      by_cases successor_transient : successor ∈ finiteTransientStates kernel
      · have successor_eq := unique successor_support successor_transient
          pivot_support pivot_transient
        subst successor
        simp [transientBernoulliPotential, pivot_transient,
          singleTransientBernoulliPotential, bernoulliVariationPotential]
      · have successor_ne : successor ≠ pivot := by
          intro successor_eq
          subst successor
          exact successor_transient pivot_transient
        simp [transientBernoulliPotential, successor_transient,
          singleTransientBernoulliPotential, successor_ne]
    _ = _ := by
      rw [expect_singleTransientBernoulliPotential]
      simp [bernoulliVariationPotential]

private theorem expect_transientBernoulliPotential_eq_zero_of_no_successor
    (kernel : Omega → PMF Omega) (value : Omega → ℕ → ℝ)
    (source : Omega)
    (noTransientSuccessor : ¬∃ successor,
      successor ∈ (kernel source).support ∧
        successor ∈ finiteTransientStates kernel)
    (time : ℕ) :
    expect (kernel source) (fun successor ↦
      transientBernoulliPotential kernel value successor time) = 0 := by
  calc
    expect (kernel source) (fun successor ↦
        transientBernoulliPotential kernel value successor time) =
        expect (kernel source) (fun _ ↦ (0 : ℝ)) := by
      apply Math.ProbabilityMassFunction.expect_congr_on_support
      intro successor successor_support
      have successor_not_transient :
          successor ∉ finiteTransientStates kernel := by
        intro successor_transient
        exact noTransientSuccessor ⟨successor, successor_support,
          successor_transient⟩
      simp [transientBernoulliPotential, successor_not_transient]
    _ = 0 := expect_const _ _

/-- If each row has at most one transient successor, one Bernoulli potential pays the whole
conditional increment even when the transient graph contains directed cycles. -/
theorem conditionalVariation_add_transientBernoulliPotential_le
    (kernel : Omega → PMF Omega)
    (unique : HasAtMostOneSupportedTransientSuccessor kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (source : Omega) (time : ℕ) :
    expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|) +
      expect (kernel source) (fun successor ↦
        transientBernoulliPotential kernel value successor (time + 1)) ≤
      transientBernoulliPotential kernel value source time := by
  by_cases source_transient : source ∈ finiteTransientStates kernel
  · by_cases hasTransientSuccessor : ∃ successor,
        successor ∈ (kernel source).support ∧
          successor ∈ finiteTransientStates kernel
    · obtain ⟨pivot, pivot_support, pivot_transient⟩ := hasTransientSuccessor
      rw [expect_transientBernoulliPotential_eq_atom kernel value unique
        pivot_support pivot_transient]
      rw [transientBernoulliPotential, if_pos source_transient]
      have hpeeling := expect_abs_sub_expect_add_atom_bernoulliPotential_le
        (kernel source) pivot (fun successor ↦ value successor (time + 1))
        (fun successor ↦ harmonic.1 successor (time + 1))
      rw [← harmonic.2 source time] at hpeeling
      simpa [bernoulliVariationPotential, mul_assoc, mul_comm, mul_left_comm]
        using hpeeling
    · rw [expect_transientBernoulliPotential_eq_zero_of_no_successor
        kernel value source hasTransientSuccessor]
      rw [transientBernoulliPotential, if_pos source_transient, add_zero]
      have hpeeling := pivotLocalVariation_add_selfPotential_le
        kernel source value harmonic time
      have hselfPotential :
          0 ≤ (kernel source source).toReal *
            bernoulliVariationPotential (value source (time + 1)) :=
        mul_nonneg ENNReal.toReal_nonneg (bernoulliVariationPotential_nonneg _)
      simp only [pivotLocalVariation] at hpeeling
      linarith
  · have source_recurrent : source ∈ finiteRecurrentCore kernel := by
      exact not_not.mp (mt (mem_finiteTransientStates_iff kernel source).mpr
        source_transient)
    have hvariation := expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value harmonic source_recurrent time
    have noTransientSuccessor : ¬∃ successor,
        successor ∈ (kernel source).support ∧
          successor ∈ finiteTransientStates kernel := by
      rintro ⟨successor, successor_support, successor_transient⟩
      have successor_recurrent := finiteRecurrentCore_closed kernel
        source_recurrent successor_support
      exact ((mem_finiteTransientStates_iff kernel successor).mp
        successor_transient) successor_recurrent
    rw [hvariation,
      expect_transientBernoulliPotential_eq_zero_of_no_successor
        kernel value source noTransientSuccessor]
    simp [transientBernoulliPotential, source_transient]

/-- A genuinely cyclic sharp subcase of Simon's estimate: functional transient support has
total expected variation at most one, independently of the number of transient states. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_one_of_functionalTransientSupport
    (initial : Omega) (kernel : Omega → PMF Omega)
    (unique : HasAtMostOneSupportedTransientSuccessor kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤ 1 := by
  let potential : Omega → ℕ → ℝ := transientBernoulliPotential kernel value
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (transientBernoulliPotential_nonneg kernel value)
      (conditionalVariation_add_transientBernoulliPotential_le
        kernel unique value harmonic) horizon).trans
    (transientBernoulliPotential_le_one kernel value harmonic.1 initial 0)

/-! ## Functional layers with arbitrary downward branching -/

/-- A ranked transient condensation in which every row has at most one supported successor
on its current layer.  Transitions to lower layers may branch arbitrarily. -/
structure FunctionalTransientLayerCertificate (kernel : Omega → PMF Omega) where
  rank : Omega → ℕ
  rank_lt_card : ∀ {state}, state ∈ finiteTransientStates kernel →
    rank state < (finiteTransientStates kernel).card
  nonincreasing : ∀ {source destination},
    source ∈ finiteTransientStates kernel →
    destination ∈ (kernel source).support →
    destination ∈ finiteTransientStates kernel → rank destination ≤ rank source
  sameLayer_unique : ∀ {source first second},
    source ∈ finiteTransientStates kernel →
    first ∈ (kernel source).support →
    first ∈ finiteTransientStates kernel →
    rank first = rank source →
    second ∈ (kernel source).support →
    second ∈ finiteTransientStates kernel →
    rank second = rank source → first = second

/-- Bernoulli variation on the current transient state plus its layer rank. -/
def functionalLayerPotential
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) : ℝ :=
  if state ∈ finiteTransientStates kernel then
    bernoulliVariationPotential (value state time) + certificate.rank state
  else 0

theorem functionalLayerPotential_nonneg
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ) (state : Omega) (time : ℕ) :
    0 ≤ functionalLayerPotential certificate value state time := by
  rw [functionalLayerPotential]
  split_ifs
  · exact add_nonneg (bernoulliVariationPotential_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem functionalLayerPotential_le_transientCard
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    (state : Omega) (time : ℕ) :
    functionalLayerPotential certificate value state time ≤
      (finiteTransientStates kernel).card := by
  rw [functionalLayerPotential]
  split_ifs with state_transient
  · have hrank := certificate.rank_lt_card state_transient
    have hcast : (certificate.rank state : ℝ) + 1 ≤
        ((finiteTransientStates kernel).card : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hrank)
    have hbernoulli := bernoulliVariationPotential_le_one_of_mem_Icc
      (bounded state time)
    linarith
  · exact Nat.cast_nonneg _

private theorem functionalLayerPotential_le_sameLayerAtom_add_rank
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    {source pivot : Omega}
    (source_transient : source ∈ finiteTransientStates kernel)
    (pivot_support : pivot ∈ (kernel source).support)
    (pivot_transient : pivot ∈ finiteTransientStates kernel)
    (pivot_layer : certificate.rank pivot = certificate.rank source)
    {destination : Omega} (destination_support : destination ∈ (kernel source).support)
    (time : ℕ) :
    functionalLayerPotential certificate value destination (time + 1) ≤
      singleTransientBernoulliPotential pivot value destination (time + 1) +
        certificate.rank source := by
  by_cases destination_transient : destination ∈ finiteTransientStates kernel
  · have hrank := certificate.nonincreasing source_transient destination_support
      destination_transient
    rcases hrank.eq_or_lt with destination_layer | destination_lower
    · have destination_eq := certificate.sameLayer_unique source_transient
        destination_support destination_transient destination_layer
        pivot_support pivot_transient pivot_layer
      subst destination
      simp [functionalLayerPotential, pivot_transient,
        singleTransientBernoulliPotential, bernoulliVariationPotential,
        pivot_layer]
    · have hbernoulli := bernoulliVariationPotential_le_one_of_mem_Icc
        (bounded destination (time + 1))
      have hcast : (certificate.rank destination : ℝ) + 1 ≤
          (certificate.rank source : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr destination_lower)
      have destination_ne : destination ≠ pivot := by
        intro destination_eq
        subst destination
        omega
      simp only [functionalLayerPotential, if_pos destination_transient,
        singleTransientBernoulliPotential, if_neg destination_ne, zero_add]
      linarith
  · have destination_ne : destination ≠ pivot := by
      intro destination_eq
      subst destination
      exact destination_transient pivot_transient
    simp [functionalLayerPotential, destination_transient,
      singleTransientBernoulliPotential, destination_ne]

private theorem functionalLayerPotential_le_rank_of_no_sameLayerSuccessor
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (bounded : ∀ state time, value state time ∈ Set.Icc (0 : ℝ) 1)
    {source : Omega} (source_transient : source ∈ finiteTransientStates kernel)
    (noSameLayerSuccessor : ¬∃ destination,
      destination ∈ (kernel source).support ∧
        destination ∈ finiteTransientStates kernel ∧
          certificate.rank destination = certificate.rank source)
    {destination : Omega} (destination_support : destination ∈ (kernel source).support)
    (time : ℕ) :
    functionalLayerPotential certificate value destination (time + 1) ≤
      certificate.rank source := by
  by_cases destination_transient : destination ∈ finiteTransientStates kernel
  · have hrank := certificate.nonincreasing source_transient destination_support
      destination_transient
    have destination_lower : certificate.rank destination < certificate.rank source :=
      lt_of_le_of_ne hrank fun rank_eq =>
        noSameLayerSuccessor ⟨destination, destination_support,
          destination_transient, rank_eq⟩
    have hbernoulli := bernoulliVariationPotential_le_one_of_mem_Icc
      (bounded destination (time + 1))
    have hcast : (certificate.rank destination : ℝ) + 1 ≤
        (certificate.rank source : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr destination_lower)
    simp only [functionalLayerPotential, if_pos destination_transient]
    linarith
  · simp [functionalLayerPotential, destination_transient, Nat.cast_nonneg]

/-- The Bernoulli account pays the unique same-layer continuation; the rank account pays all
lower-layer branching. -/
theorem conditionalVariation_add_functionalLayerPotential_le
    {kernel : Omega → PMF Omega}
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (source : Omega) (time : ℕ) :
    expect (kernel source) (fun successor ↦
        |value successor (time + 1) - value source time|) +
      expect (kernel source) (fun successor ↦
        functionalLayerPotential certificate value successor (time + 1)) ≤
      functionalLayerPotential certificate value source time := by
  by_cases source_transient : source ∈ finiteTransientStates kernel
  · by_cases hasSameLayerSuccessor : ∃ pivot,
        pivot ∈ (kernel source).support ∧
          pivot ∈ finiteTransientStates kernel ∧
            certificate.rank pivot = certificate.rank source
    · obtain ⟨pivot, pivot_support, pivot_transient, pivot_layer⟩ :=
        hasSameLayerSuccessor
      have hpotential :
          expect (kernel source) (fun successor ↦
              functionalLayerPotential certificate value successor (time + 1)) ≤
            expect (kernel source) (fun successor ↦
              singleTransientBernoulliPotential pivot value successor (time + 1) +
                certificate.rank source) := by
        apply Math.ProbabilityMassFunction.expect_mono_on_support
        intro destination destination_support
        exact functionalLayerPotential_le_sameLayerAtom_add_rank
          certificate value harmonic.1 source_transient pivot_support
            pivot_transient pivot_layer destination_support time
      rw [expect_add, expect_const,
        expect_singleTransientBernoulliPotential] at hpotential
      have hpeeling := expect_abs_sub_expect_add_atom_bernoulliPotential_le
        (kernel source) pivot (fun successor ↦ value successor (time + 1))
        (fun successor ↦ harmonic.1 successor (time + 1))
      rw [← harmonic.2 source time] at hpeeling
      rw [functionalLayerPotential, if_pos source_transient]
      simp only [bernoulliVariationPotential] at hpeeling hpotential ⊢
      linarith
    · have hpotential :
          expect (kernel source) (fun successor ↦
              functionalLayerPotential certificate value successor (time + 1)) ≤
            certificate.rank source := by
        apply Math.ProbabilityMassFunction.expect_le_of_le_on_support
        intro destination destination_support
        exact functionalLayerPotential_le_rank_of_no_sameLayerSuccessor
          certificate value harmonic.1 source_transient hasSameLayerSuccessor
            destination_support time
      have hpeeling := pivotLocalVariation_add_selfPotential_le
        kernel source value harmonic time
      have hselfPotential :
          0 ≤ (kernel source source).toReal *
            bernoulliVariationPotential (value source (time + 1)) :=
        mul_nonneg ENNReal.toReal_nonneg (bernoulliVariationPotential_nonneg _)
      rw [functionalLayerPotential, if_pos source_transient]
      simp only [pivotLocalVariation] at hpeeling
      linarith
  · have source_recurrent : source ∈ finiteRecurrentCore kernel := by
      exact not_not.mp (mt (mem_finiteTransientStates_iff kernel source).mpr
        source_transient)
    have hvariation := expect_abs_increment_eq_zero_of_mem_finiteRecurrentCore
      kernel value harmonic source_recurrent time
    have hpotential :
        expect (kernel source) (fun successor ↦
          functionalLayerPotential certificate value successor (time + 1)) = 0 := by
      calc
        expect (kernel source) (fun successor ↦
            functionalLayerPotential certificate value successor (time + 1)) =
            expect (kernel source) (fun _ ↦ (0 : ℝ)) := by
          apply Math.ProbabilityMassFunction.expect_congr_on_support
          intro successor successor_support
          have successor_recurrent := finiteRecurrentCore_closed kernel
            source_recurrent successor_support
          have successor_not_transient :
              successor ∉ finiteTransientStates kernel := by
            intro successor_transient
            exact ((mem_finiteTransientStates_iff kernel successor).mp
              successor_transient) successor_recurrent
          simp [functionalLayerPotential, successor_not_transient]
        _ = 0 := expect_const _ _
    rw [hvariation, hpotential]
    simp [functionalLayerPotential, source_transient]

/-- Sharp transient-cardinality bound for functional transient layers with arbitrary
downward branching. -/
theorem finiteExpectedSpaceTimeMarkovVariation_le_transientCard_of_functionalLayers
    (initial : Omega) (kernel : Omega → PMF Omega)
    (certificate : FunctionalTransientLayerCertificate kernel)
    (value : Omega → ℕ → ℝ)
    (harmonic : IsUnitIntervalBackwardMarkovHarmonic kernel value)
    (horizon : ℕ) :
    finiteExpectedSpaceTimeMarkovVariation initial kernel value horizon ≤
      (finiteTransientStates kernel).card := by
  let potential : Omega → ℕ → ℝ := functionalLayerPotential certificate value
  exact (finiteExpectedSpaceTimeMarkovVariation_le_initialPotential
    initial kernel value potential
      (functionalLayerPotential_nonneg certificate value)
      (conditionalVariation_add_functionalLayerPotential_le
        certificate value harmonic) horizon).trans
    (functionalLayerPotential_le_transientCard
      certificate value harmonic.1 initial 0)

end

end Math.Probability
