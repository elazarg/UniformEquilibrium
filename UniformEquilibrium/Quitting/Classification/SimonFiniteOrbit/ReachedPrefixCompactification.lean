/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.FinitePrefixCompatibility
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath

/-!
# Compactification of uniformly reached purified prefixes

The reached-row purification theorem evaluates each purified row against its
actual source tail. Finite backward evaluation then makes a whole displayed
window exactly Bellman-compatible. This file records the next honest step:

* at each finite horizon, an approximate equilibrium either crosses below a
  fixed reach floor or supplies a source-matched compatible prefix;
* source-matched prefixes of every length, with one common support tolerance,
  compactify to an infinite Bellman spine whose rows are support-optimal
  against their own displayed successor values.

The fixed reach floor is substantive. Nothing here turns its exhaustion into
the stationary or instant-punishment alternative. Nor does compactness show
that the selected successor values are the infinite root sequence's terminal
payoffs when survival does not vanish. Those are separate game-semantic
adapters, not supplied hypotheses in this module.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The finite reached-window split -/

/-- At the displayed accuracy, some row before `horizon` is reached with
probability strictly below the fixed floor. The root sequence is retained. -/
def QuittingLowSurvivalApproximatePrefixAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (u accuracy : ℝ) (horizon : ℕ) : Prop :=
  ∃ (roots : ℕ → ι → PMF Bool) (stage : ℕ),
    IsεQuittingRootSequenceNash reward accuracy roots ∧
      stage < horizon ∧
      quittingJointSurvivalWeight roots 0 stage < u

/-- A source-matched finite prefix obtained by purifying one actual
approximate-equilibrium root sequence and evaluating the window backwards.

The displayed values and roots are definitions from the source sequence, so
`bellman` is an exact seam statement and `ownTailSupport` evaluates every row
against the recomputed successor in the same prefix. `originalTailSupport`
and `seam` retain the connection to the actual source tails. -/
structure QuittingSourceMatchedSupportPrefixAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M δ u : ℝ) (horizon : ℕ) where
  accuracy : ℝ
  threshold : ℝ
  displacement : ℝ
  localError : ℝ
  sourceRoots : ℕ → ι → PMF Bool
  accuracy_pos : 0 < accuracy
  threshold_pos : 0 < threshold
  displacement_pos : 0 < displacement
  scale : accuracy < u * threshold * displacement
  sourceNash : IsεQuittingRootSequenceNash reward accuracy sourceRoots
  reached : ∀ offset, offset < horizon →
    u ≤ quittingJointSurvivalWeight sourceRoots 0 offset
  originalTailSupport : ∀ offset, offset < horizon →
    IsQuittingRootSupportApproxNash reward
      (quittingRootSequenceTailVector reward sourceRoots (offset + 1))
      localError
      (quittingReachedSupportPurifiedRoots reward sourceRoots threshold offset)
  value_bounded : ∀ offset, offset ≤ horizon → ∀ who,
    |quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
      0 horizon offset who| ≤ M
  bellman : ∀ offset, offset < horizon →
    quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
        0 horizon offset =
      quittingRootSuccessorPayoff reward
        (quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
          0 horizon (offset + 1))
        (quittingReachedSupportPurifiedRoots reward sourceRoots threshold offset)
  cutoff :
    quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
        0 horizon horizon =
      quittingRootSequenceTailVector reward sourceRoots horizon
  seam : ∀ offset, offset < horizon → ∀ who,
    |quittingRootSequenceTailVector reward sourceRoots offset who -
      quittingRootSuccessorPayoff reward
        (quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
          0 horizon (offset + 1))
        (quittingReachedSupportPurifiedRoots reward sourceRoots threshold offset)
        who| ≤
      (2 * M) * ((Fintype.card ι : ℝ) * displacement) *
        ((horizon - offset : ℕ) : ℝ)
  ownTailSupport : ∀ offset, offset < horizon →
    IsQuittingRootSupportApproxNash reward
      (quittingReachedSupportPurifiedPrefixValue reward sourceRoots threshold
        0 horizon (offset + 1))
      δ
      (quittingReachedSupportPurifiedRoots reward sourceRoots threshold offset)

omit [DecidableEq ι] in
/-- Backward evaluation preserves a common absolute payoff bound when both
the terminal boundary and every quitting reward obey that bound. -/
theorem abs_quittingRootSequenceBackwardPayoff_le_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (continuation : Payoff ι) {M : ℝ}
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    ∀ start steps who,
      |quittingRootSequenceBackwardPayoff reward roots continuation
        start steps who| ≤ M := by
  intro start steps
  induction steps generalizing start with
  | zero =>
      intro who
      exact hcontinuation who
  | succ steps ih =>
      intro who
      rw [quittingRootSequenceBackwardPayoff_succ]
      exact abs_quittingRootExpectedPayoff_le_bound reward
        (quittingRootSequenceBackwardPayoff reward roots continuation
          (start + 1) steps)
        (roots start) who hreward (ih (start + 1))

/-- **Finite fixed-reach split from approximate equilibrium.** At one
horizon, choose the explicit Nash accuracy below the purification threshold.
If the selected source drops below `u`, retain that literal low-survival row.
Otherwise finite backward compatibility gives a source-matched exact prefix.

The last inequality reserves enough error for every remaining backward seam,
so each purified row is support-optimal against its own recomputed tail at the
common tolerance `δ`. -/
theorem
    lowSurvival_or_sourceMatchedSupportPrefix_of_approximateEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward)
    (horizon : ℕ) {u threshold displacement M localError δ : ℝ}
    (hu : 0 < u) (hthreshold : 0 < threshold)
    (hdisplacement : 0 < displacement) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hlocal : threshold +
      4 * M * (Fintype.card ι : ℝ) * displacement ≤ localError)
    (htotal : localError +
      (2 * M) * ((Fintype.card ι : ℝ) * displacement) * (horizon : ℝ) ≤ δ) :
    QuittingLowSurvivalApproximatePrefixAt reward u
        (u * threshold * displacement / 2) horizon ∨
      Nonempty (QuittingSourceMatchedSupportPrefixAt reward M δ u horizon) := by
  let accuracy := u * threshold * displacement / 2
  have haccuracy : 0 < accuracy := by
    dsimp only [accuracy]
    positivity
  obtain ⟨sourceRoots, hsourceNash⟩ := hequilibrium accuracy haccuracy
  by_cases hreached : ∀ offset, offset < horizon →
      u ≤ quittingJointSurvivalWeight sourceRoots 0 offset
  · have hscale : accuracy < u * threshold * displacement := by
      dsimp only [accuracy]
      have hproduct : 0 < u * threshold * displacement := by positivity
      linarith
    obtain ⟨horiginalSupport, hbellman, hcutoff, _hcontinuationClose,
        hseam, hownTailSupport⟩ :=
      reached_supportPurifiedPrefix_compatible reward sourceRoots 0 horizon
        haccuracy hu hthreshold hdisplacement hM hreward hsourceNash
        (by simpa using hreached) hscale hlocal
    refine Or.inr ⟨
      { accuracy := accuracy
        threshold := threshold
        displacement := displacement
        localError := localError
        sourceRoots := sourceRoots
        accuracy_pos := haccuracy
        threshold_pos := hthreshold
        displacement_pos := hdisplacement
        scale := hscale
        sourceNash := hsourceNash
        reached := hreached
        originalTailSupport := by simpa using horiginalSupport
        value_bounded := ?_
        bellman := by simpa using hbellman
        cutoff := by simpa using hcutoff
        seam := by simpa using hseam
        ownTailSupport := ?_ }⟩
    · intro offset _hoffset who
      unfold quittingReachedSupportPurifiedPrefixValue
      have hterminal : ∀ player,
          |quittingRootSequenceTailVector reward sourceRoots horizon player| ≤
            M := by
        intro player
        exact abs_quittingRootSequenceTerminalValue_le reward sourceRoots player
          horizon hM hreward
      simpa only [zero_add] using
        (abs_quittingRootSequenceBackwardPayoff_le_bound reward
        (quittingReachedSupportPurifiedRoots reward sourceRoots threshold)
        (quittingRootSequenceTailVector reward sourceRoots horizon)
        hreward hterminal offset (horizon - offset) who)
    · intro offset hoffset
      have hremaining :
          ((horizon - (offset + 1) : ℕ) : ℝ) ≤ (horizon : ℝ) := by
        exact_mod_cast Nat.sub_le horizon (offset + 1)
      have hcoefficient :
          0 ≤ (2 * M) * ((Fintype.card ι : ℝ) * displacement) := by
        positivity
      have hscaled := mul_le_mul_of_nonneg_left hremaining hcoefficient
      have hle : localError +
          (2 * M) * ((Fintype.card ι : ℝ) * displacement) *
            ((horizon - (offset + 1) : ℕ) : ℝ) ≤ δ := by
        linarith
      simpa only [zero_add] using
        (hownTailSupport offset hoffset).mono hle
  · push Not at hreached
    obtain ⟨stage, hstage, hsurvival⟩ := hreached
    exact Or.inl ⟨sourceRoots, stage, hsourceNash, hstage, hsurvival⟩

/-! ## Diagonal compactification of the fixed-reach branch -/

/-- **Common-prefix compactification.** Source-matched compatible prefixes
of every finite length, all with the same payoff bound and support tolerance,
select one infinite exact Bellman spine. Every selected row is evaluated
against the next value of that same spine.

The conclusion deliberately does not identify `value (time + 1)` with the
terminal payoff of the infinite suffix. Such an identification needs a
separate survival or boundary argument. -/
theorem exists_bounded_supportBellmanSpine_of_sourceMatchedPrefixes
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M δ u : ℝ)
    (hprefix : ∀ horizon,
      Nonempty (QuittingSourceMatchedSupportPrefixAt reward M δ u horizon)) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ M) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time) := by
  let lower : Payoff ι := fun _ => -M
  let box : Set (QuittingNashBellmanPoint ι) :=
    quittingCirculationPathBox M lower
  let relation : QuittingNashBellmanPoint ι →
      QuittingNashBellmanPoint ι → Prop :=
    IsQuittingCirculationPathEdge reward δ 0
  have hfinite : ∀ horizon,
      (compactFinitePrefixSolutionSet box relation horizon).Nonempty := by
    intro horizon
    obtain ⟨certificate⟩ := hprefix horizon
    let point : ℕ → QuittingNashBellmanPoint ι := fun time =>
      let offset := min time horizon
      (quittingReachedSupportPurifiedPrefixValue reward certificate.sourceRoots
          certificate.threshold 0 horizon offset,
        quittingSimplexOfRoot
          (quittingReachedSupportPurifiedRoots reward certificate.sourceRoots
            certificate.threshold offset))
    refine ⟨point, ?_, ?_⟩
    · intro time
      have hoffset : min time horizon ≤ horizon := Nat.min_le_right _ _
      apply mem_quittingCirculationPathBox_of_bounds
      · exact certificate.value_bounded (min time horizon) hoffset
      · intro who
        have hbound := certificate.value_bounded (min time horizon) hoffset who
        exact (abs_le.mp hbound).1
    · intro time
      have htime : (time : ℕ) < horizon := time.isLt
      have hcurrent : min (time : ℕ) horizon = time :=
        Nat.min_eq_left htime.le
      have hnext : min ((time : ℕ) + 1) horizon = time + 1 :=
        Nat.min_eq_left (Nat.succ_le_iff.mpr htime)
      dsimp only [point]
      rw [hcurrent, hnext]
      refine ⟨?_, ?_, ?_⟩
      · simpa only [quittingRootOfSimplex_simplexOfRoot] using
          certificate.bellman time htime
      · rw [isQuittingSimplexRootSupportApproxNash_iff,
          quittingRootOfSimplex_simplexOfRoot]
        exact certificate.ownTailSupport time htime
      · rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass,
          quittingRootOfSimplex_simplexOfRoot]
        exact quittingRootAbsorptionMass_nonneg _
  obtain ⟨point, hpoint, hedge⟩ :=
    exists_infiniteChain_of_finitePrefixes box relation
      (quittingCirculationPathBox_isCompact M lower)
      (isClosed_quittingCirculationPathEdgeGraph reward M lower δ 0)
      hfinite
  let value : ℕ → Payoff ι := fun time => (point time).1
  let roots : ℕ → ι → PMF Bool := fun time =>
    quittingRootOfSimplex (point time).2
  refine ⟨value, roots, ?_, ?_, ?_⟩
  · intro time who
    have hbox := (hpoint time).1
    exact abs_le.mpr ⟨hbox.1 who, hbox.2 who⟩
  · intro time
    exact (hedge time).1
  · intro time
    exact (isQuittingSimplexRootSupportApproxNash_iff reward
      (point (time + 1)).1 δ (point time).2).1 (hedge time).2.1

/-- In the fixed-reach branch, the finite split and compactification compose.
The hypothesis excludes only the literal low-survival alternative for the
specific horizon-dependent accuracies. It does not assert a stationary or
instant-punishment classification when that alternative occurs. -/
theorem
    exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence_of_fixedReach
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward)
    (M δ u : ℝ) (threshold displacement localError : ℕ → ℝ)
    (hu : 0 < u) (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hthreshold : ∀ horizon, 0 < threshold horizon)
    (hdisplacement : ∀ horizon, 0 < displacement horizon)
    (hlocal : ∀ horizon,
      threshold horizon +
        4 * M * (Fintype.card ι : ℝ) * displacement horizon ≤
          localError horizon)
    (htotal : ∀ horizon,
      localError horizon +
        (2 * M) * ((Fintype.card ι : ℝ) * displacement horizon) *
          (horizon : ℝ) ≤ δ)
    (hfixedReach : ∀ horizon,
      ¬QuittingLowSurvivalApproximatePrefixAt reward u
        (u * threshold horizon * displacement horizon / 2) horizon) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ M) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time) := by
  apply exists_bounded_supportBellmanSpine_of_sourceMatchedPrefixes
    reward M δ u
  intro horizon
  rcases
      lowSurvival_or_sourceMatchedSupportPrefix_of_approximateEquilibriumExistence
        reward hequilibrium horizon hu (hthreshold horizon)
        (hdisplacement horizon) hM hreward (hlocal horizon) (htotal horizon) with
    hlow | hprefix
  · exact False.elim (hfixedReach horizon hlow)
  · exact hprefix

/-! ## A canonical scale schedule -/

/-- The support-purification threshold used by the canonical finite-window
schedule. -/
def quittingSimonReachedPrefixThreshold (δ : ℝ) : ℝ :=
  δ / 4

/-- A horizon-dependent row displacement whose accumulated backward seam is
uniformly controlled. The added `1` keeps the denominator positive even when
the reward bound or player cardinality is zero. -/
def quittingSimonReachedPrefixDisplacement
    (M δ : ℝ) (horizon : ℕ) : ℝ :=
  δ / (16 * (1 + 4 * M * (Fintype.card ι : ℝ) +
    2 * M * (Fintype.card ι : ℝ) * (horizon : ℝ)))

/-- Half of the target support tolerance is reserved for local purification;
the remaining half pays all backward seams. -/
def quittingSimonReachedPrefixLocalError (δ : ℝ) : ℝ :=
  δ / 2

omit [DecidableEq ι] in
/-- The canonical horizon-dependent scales are positive and satisfy both the
local product-law error budget and the full backward-seam budget. -/
theorem quittingSimonReachedPrefixScale_spec
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (horizon : ℕ) :
    0 < quittingSimonReachedPrefixThreshold δ ∧
      0 < quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon ∧
      quittingSimonReachedPrefixThreshold δ +
          4 * M * (Fintype.card ι : ℝ) *
            quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon ≤
        quittingSimonReachedPrefixLocalError δ ∧
      quittingSimonReachedPrefixLocalError δ +
          (2 * M) * ((Fintype.card ι : ℝ) *
            quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon) *
            (horizon : ℝ) ≤ δ := by
  let card : ℝ := Fintype.card ι
  let time : ℝ := horizon
  let denominator : ℝ :=
    16 * (1 + 4 * M * card + 2 * M * card * time)
  have hcard : 0 ≤ card := by positivity
  have htime : 0 ≤ time := by positivity
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    positivity
  have hlocalCharge :
      4 * M * card * (δ / denominator) ≤ δ / 4 := by
    rw [show 4 * M * card * (δ / denominator) =
      (4 * M * card * δ) / denominator by ring]
    rw [div_le_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith [mul_nonneg hM hcard, mul_nonneg (mul_nonneg hM hcard) htime]
  have hseamCharge :
      (2 * M) * (card * (δ / denominator)) * time ≤ δ / 2 := by
    rw [show (2 * M) * (card * (δ / denominator)) * time =
      (2 * M * card * δ * time) / denominator by ring]
    rw [div_le_iff₀ hdenominator]
    dsimp only [denominator]
    nlinarith [mul_nonneg hM hcard, mul_nonneg (mul_nonneg hM hcard) htime]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quittingSimonReachedPrefixThreshold
    positivity
  · unfold quittingSimonReachedPrefixDisplacement
    change 0 < δ / denominator
    positivity
  · unfold quittingSimonReachedPrefixThreshold
    unfold quittingSimonReachedPrefixDisplacement
    unfold quittingSimonReachedPrefixLocalError
    change δ / 4 + 4 * M * card * (δ / denominator) ≤ δ / 2
    linarith
  · unfold quittingSimonReachedPrefixDisplacement
    unfold quittingSimonReachedPrefixLocalError
    change δ / 2 + (2 * M) * (card * (δ / denominator)) * time ≤ δ
    linarith

/-- **Canonical fixed-reach compactification.** Approximate-equilibrium
existence and failure of the literal low-survival alternative along the
canonical accuracy schedule produce a bounded infinite support-Bellman spine.

This is the strongest conclusion of the fixed-reach argument here. It remains
silent about how a low-survival row yields the stationary or instant branch,
and it does not identify the selected values with terminal suffix payoffs. -/
theorem
    exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence_of_canonicalFixedReach
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward)
    (M δ u : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hu : 0 < u)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hfixedReach : ∀ horizon,
      ¬QuittingLowSurvivalApproximatePrefixAt reward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon / 2)
        horizon) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ M) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time) := by
  apply
    exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence_of_fixedReach
      reward hequilibrium M δ u
      (fun _ => quittingSimonReachedPrefixThreshold δ)
      (quittingSimonReachedPrefixDisplacement (ι := ι) M δ)
      (fun _ => quittingSimonReachedPrefixLocalError δ)
      hu hM hreward
  · intro horizon
    exact (quittingSimonReachedPrefixScale_spec (ι := ι) hM hδ horizon).1
  · intro horizon
    exact (quittingSimonReachedPrefixScale_spec (ι := ι) hM hδ horizon).2.1
  · intro horizon
    exact (quittingSimonReachedPrefixScale_spec (ι := ι) hM hδ horizon).2.2.1
  · intro horizon
    exact (quittingSimonReachedPrefixScale_spec (ι := ι) hM hδ horizon).2.2.2
  · exact hfixedReach

/-- **Unconditional compactification boundary.** Approximate-equilibrium
existence yields either a literal finite low-survival source at one canonical
accuracy or an infinite bounded support-Bellman spine selected from
source-matched prefixes of every length.

The first disjunct is intentionally not renamed as a stationary or
instant-punishment witness. Producing one of those semantic branches from the
low-survival source is exactly the remaining adapter beyond this theorem. -/
theorem
    lowSurvivalPrefix_or_exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward)
    (M δ u : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ) (hu : 0 < u)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    (∃ horizon,
      QuittingLowSurvivalApproximatePrefixAt reward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon / 2)
        horizon) ∨
      ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
        (∀ time who, |value time who| ≤ M) ∧
        (∀ time, value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (roots time)) ∧
        ∀ time, IsQuittingRootSupportApproxNash reward
          (value (time + 1)) δ (roots time) := by
  by_cases hfixedReach : ∀ horizon,
      ¬QuittingLowSurvivalApproximatePrefixAt reward u
        (u * quittingSimonReachedPrefixThreshold δ *
          quittingSimonReachedPrefixDisplacement (ι := ι) M δ horizon / 2)
        horizon
  · exact Or.inr
      (exists_bounded_supportBellmanSpine_of_approximateEquilibriumExistence_of_canonicalFixedReach
        reward hequilibrium M δ u hM hδ hu hreward hfixedReach)
  · push Not at hfixedReach
    exact Or.inl hfixedReach

end GameTheory
