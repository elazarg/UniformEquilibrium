/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootDebtDescent
import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootUniqueSureLimit
import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.SureRootSingletonHandoff
import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedWitnessRegimes

/-!
# Compactification of vanishing-survival first exact roots

Carrier source points and their exact product roots admit a common convergent
subsequence.  If joint survival vanishes while the prefixed total debt has a
fixed positive floor, the limiting exact root has one unique sure quitter.
Every other finite prefix-debt coordinate tends to zero, while that owner
eventually retains half of the floor.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A subsequence on which the new root retains a fixed positive probability
of reaching its attached tail. -/
def HasPositiveFirstRootSurvivalSubsequence
    (root : ℕ → ι → PMF Bool) : Prop :=
  ∃ reach : ℝ, 0 < reach ∧ ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
    ∀ᶠ index in atTop,
      reach ≤ quittingStationaryContinueMass (root (subsequence index))

/-- The complete vanishing-survival compact subsequence.  Root Nash is passed
to the joint source/root limit rather than supplied again at the endpoint. -/
theorem exists_uniqueSureLimit_of_firstExactRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) {floor : ℝ}
    (hfloor : 0 < floor)
    (hsource : ∀ index, source index ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 0 (root index))
    (htotalFloor : ∀ index, floor ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward (root index) (source index)))
    (hsurvival : Tendsto
      (fun index => quittingStationaryContinueMass (root index))
      atTop (nhds 0)) :
    ∃ limitSource : QuittingTerminalSemanticPair ι,
      ∃ limitRoot : ι → PMF Bool,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (source ∘ subsequence) atTop (nhds limitSource) ∧
        Tendsto (fun index => quittingSimplexOfRoot (root (subsequence index)))
          atTop (nhds (quittingSimplexOfRoot limitRoot)) ∧
        limitSource ∈ quittingTerminalSemanticCarrier reward ∧
        IsεQuittingRootNash reward limitSource.1 0 limitRoot ∧
        quittingStationaryContinueMass limitRoot = 0 ∧
        ∃ owner : ι,
          limitRoot owner = PMF.pure true ∧
          (∀ other, other ≠ owner → limitRoot other ≠ PMF.pure true) ∧
          (∀ other, other ≠ owner → Tendsto (fun index =>
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPrefix reward
                (root (subsequence index)) (source (subsequence index))) other)
            atTop (nhds 0)) ∧
          ∀ᶠ index in atTop, floor / 2 ≤ quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward
              (root (subsequence index)) (source (subsequence index))) owner := by
  let data : ℕ → QuittingRootSimplex ι × QuittingTerminalSemanticPair ι :=
    fun index => (quittingSimplexOfRoot (root index), source index)
  have hdata : ∀ index, data index ∈
      (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
        quittingTerminalSemanticCarrier reward := by
    exact fun index => ⟨Set.mem_univ _, hsource index⟩
  obtain ⟨limit, hlimitMem, subsequence, hsubsequence, hlimit⟩ :=
    (isCompact_univ.prod (quittingTerminalSemanticCarrier_isCompact reward))
      |>.tendsto_subseq hdata
  let limitRoot := quittingRootOfSimplex limit.1
  have hsourceLimit : Tendsto (source ∘ subsequence) atTop (nhds limit.2) := by
    change Tendsto (Prod.snd ∘ data ∘ subsequence) atTop (nhds limit.2)
    exact continuous_snd.tendsto limit |>.comp hlimit
  have hrootLimit : Tendsto
      (fun index => quittingSimplexOfRoot (root (subsequence index))) atTop
      (nhds (quittingSimplexOfRoot limitRoot)) := by
    have hproj := continuous_fst.tendsto limit |>.comp hlimit
    change Tendsto (fun index => (data (subsequence index)).1) atTop
      (nhds limit.1) at hproj
    simpa [data, limitRoot] using hproj
  have hnashLimit : IsεQuittingRootNash reward limit.2.1 0 limitRoot := by
    rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    apply (isClosed_isZeroQuittingRootEndpointNash_simplex reward).mem_of_tendsto
      (continuous_snd.fst.tendsto limit |>.prodMk_nhds
        (continuous_fst.tendsto limit) |>.comp hlimit)
    filter_upwards with index
    simpa [data] using
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward
        (source (subsequence index)).1 (root (subsequence index))).2
          (hnash (subsequence index))
  have hsurvivalLimit : quittingStationaryContinueMass limitRoot = 0 := by
    apply tendsto_nhds_unique
      ((continuous_quittingStationaryContinueMass_simplex.tendsto limit.1).comp
        (continuous_fst.tendsto limit |>.comp hlimit))
    have h := hsurvival.comp hsubsequence.tendsto_atTop
    convert h using 1
    funext index
    simp [data, Function.comp_apply]
  have hprefixLimit : Tendsto (fun index =>
      quittingTerminalSemanticPrefix reward
        (root (subsequence index)) (source (subsequence index))) atTop
      (nhds (quittingTerminalSemanticPrefix reward limitRoot limit.2)) := by
    have h := (continuous_quittingTerminalSemanticPrefixSimplex reward).tendsto limit
      |>.comp hlimit
    change Tendsto (fun index => quittingTerminalSemanticPrefixSimplex reward
      (data (subsequence index))) atTop
      (nhds (quittingTerminalSemanticPrefixSimplex reward limit)) at h
    simpa [data, limitRoot, quittingTerminalSemanticPrefixSimplex] using h
  have htotalLimit : floor ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward limitRoot limit.2) := by
    have hsumLimit :=
      continuous_quittingTerminalSemanticDebtSum.tendsto _ |>.comp hprefixLimit
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hsumLimit
    exact Filter.Eventually.of_forall fun index => htotalFloor (subsequence index)
  have hprefixCarrier := quittingTerminalSemanticPrefix_mem_carrier reward
    limitRoot limit.2 hlimitMem.2
  have hnonneg := quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
    hprefixCarrier
  have hbound (player : ι) :
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward limitRoot limit.2) player ≤
        quittingRootOpponentContinueMass limitRoot player *
          quittingTerminalSemanticDebt limit.2 player := by
    rw [quittingTerminalSemanticDebt_prefix_eq_blockAct reward limit.2 limitRoot player
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hlimitMem.2 player)
      hnashLimit]
    exact Math.SurvivalWeightedObstruction.Block.act_le_survival_mul_debt
      (quittingTerminalSemanticDebtBlock reward limit.2 limitRoot player) ()
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hlimitMem.2 player)
  obtain ⟨owner, howner, hunique, houtside, hownerFloor⟩ :=
    uniqueSureQuitter_of_positive_prefixDebtFloor limitRoot
      (fun player => quittingTerminalSemanticDebt limit.2 player)
      (fun player => quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward limitRoot limit.2) player)
      hfloor hsurvivalLimit hnonneg hbound htotalLimit
  refine ⟨limit.2, limitRoot, subsequence, hsubsequence, hsourceLimit,
    hrootLimit, hlimitMem.2, hnashLimit, hsurvivalLimit, owner, howner,
    hunique, ?_, ?_⟩
  · intro other hne
    have h := (continuous_quittingTerminalSemanticDebt other).tendsto _
      |>.comp hprefixLimit
    convert h using 1
    · funext index
      rfl
    · simp only [houtside other hne]
  · have hhalf : floor / 2 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward limitRoot limit.2) owner := by
      linarith
    exact ((tendsto_order.1
      ((continuous_quittingTerminalSemanticDebt owner).tendsto _
        |>.comp hprefixLimit)).1 _ hhalf).mono fun _ h => h.le

/-- Every first-root sequence has, after compact root/source extraction,
either a positive-survival tail or a vanishing-survival subsequence to which
the unique-sure compactification applies. -/
theorem positiveSurvival_or_exists_uniqueSureLimit_of_firstExactRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) {floor : ℝ}
    (hfloor : 0 < floor)
    (hsource : ∀ index, source index ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 0 (root index))
    (htotalFloor : ∀ index, floor ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward (root index) (source index))) :
    HasPositiveFirstRootSurvivalSubsequence root ∨
      ∃ selector : ℕ → ℕ, StrictMono selector ∧
        Tendsto (fun index => quittingStationaryContinueMass
          (root (selector index))) atTop (nhds 0) ∧
        ∃ limitSource : QuittingTerminalSemanticPair ι,
          ∃ limitRoot : ι → PMF Bool,
          ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
            IsεQuittingRootNash reward limitSource.1 0 limitRoot ∧
            quittingStationaryContinueMass limitRoot = 0 ∧
            ∃ owner : ι,
              limitRoot owner = PMF.pure true ∧
              (∀ other, other ≠ owner →
                limitRoot other ≠ PMF.pure true) ∧
              ∀ᶠ index in atTop, floor / 2 ≤ quittingTerminalSemanticDebt
                (quittingTerminalSemanticPrefix reward
                  (root (selector (subsequence index)))
                  (source (selector (subsequence index)))) owner := by
  let mass : ℕ → Set.Icc (0 : ℝ) 1 := fun index =>
    ⟨quittingStationaryContinueMass (root index),
      quittingStationaryContinueMass_nonneg _,
      quittingStationaryContinueMass_le_one _⟩
  obtain ⟨limit, selector, hselector, hlimit⟩ := CompactSpace.tendsto_subseq mass
  have hmass : Tendsto
      (fun index => quittingStationaryContinueMass (root (selector index)))
      atTop (nhds limit.1) := by
    exact (continuous_subtype_val.tendsto limit).comp hlimit
  by_cases hzero : limit.1 = 0
  · right
    have hmassZero : Tendsto
        (fun index => quittingStationaryContinueMass (root (selector index)))
        atTop (nhds 0) := by simpa [hzero] using hmass
    refine ⟨selector, hselector, hmassZero, ?_⟩
    obtain ⟨limitSource, limitRoot, subsequence, hsubsequence, _, _, _, hnashLimit,
        hsurvivalLimit, owner, howner, hunique, _, hownerDebt⟩ :=
      exists_uniqueSureLimit_of_firstExactRoots reward
        (source ∘ selector) (root ∘ selector) hfloor
        (fun index => hsource (selector index))
        (fun index => hnash (selector index))
        (fun index => htotalFloor (selector index)) hmassZero
    exact ⟨limitSource, limitRoot, subsequence, hsubsequence, hnashLimit,
      hsurvivalLimit, owner, howner, hunique, hownerDebt⟩
  · left
    have hpositive : 0 < limit.1 := lt_of_le_of_ne limit.2.1 (Ne.symm hzero)
    refine ⟨limit.1 / 2, half_pos hpositive, selector, hselector, ?_⟩
    have hhalf : limit.1 / 2 < limit.1 := by linarith
    exact ((tendsto_order.1 hmass).1 _ hhalf).mono fun _ h => h.le

/-- A vanishing-survival first-root sequence reaches the checked stationary
same-root singleton handoff at its exact limiting root.  The handoff retains
the literal stationary source, owner repair, outside debtor, and paid row. -/
theorem QuittingTerminalExploitabilityWitness.exists_uniqueSureHandoff_of_vanishing_firstRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (source : ℕ → QuittingTerminalSemanticPair ι)
    (root : ℕ → ι → PMF Bool) {floor : ℝ}
    (hfloor : 0 < floor)
    (hsource : ∀ index, source index ∈ quittingTerminalSemanticCarrier reward)
    (hnash : ∀ index,
      IsεQuittingRootNash reward (source index).1 0 (root index))
    (htotalFloor : ∀ index, floor ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPrefix reward (root index) (source index)))
    (hsurvival : Tendsto
      (fun index => quittingStationaryContinueMass (root index))
      atTop (nhds 0)) :
    ∃ limitSource : QuittingTerminalSemanticPair ι,
      ∃ limitRoot : ι → PMF Bool,
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (source ∘ subsequence) atTop (nhds limitSource) ∧
        IsεQuittingRootNash reward limitSource.1 0 limitRoot ∧
        ∃ owner : ι,
          limitRoot owner = PMF.pure true ∧
          (∀ other, other ≠ owner → limitRoot other ≠ PMF.pure true) ∧
          (∀ other, other ≠ owner → Tendsto (fun index =>
            quittingTerminalSemanticDebt
              (quittingTerminalSemanticPrefix reward
                (root (subsequence index)) (source (subsequence index))) other)
            atTop (nhds 0)) ∧
          Filter.Eventually (fun index => floor / 2 ≤ quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward
              (root (subsequence index)) (source (subsequence index))) owner) atTop ∧
          ∃ delta : ℝ, 0 < delta ∧
            Nonempty (QuittingSingletonBaseStationaryHandoff reward owner
              (Finset.univ.erase owner)
              (quittingRootFreeMixedPoint (Finset.univ.erase owner) limitRoot)
              delta witness.terminalGap) := by
  obtain ⟨limitSource, limitRoot, subsequence, hsubsequence, hsourceLimit, _, _,
      hnashLimit, _, owner, howner, hunique, houtside, hownerDebt⟩ :=
    exists_uniqueSureLimit_of_firstExactRoots reward source root hfloor
      hsource hnash htotalFloor hsurvival
  obtain ⟨delta, hdelta, handoff⟩ :=
    witness.exists_samePoint_stationaryHandoff_of_sure_exactNash
      limitSource.1 limitRoot owner howner hnashLimit
  exact ⟨limitSource, limitRoot, subsequence, hsubsequence, hsourceLimit,
    hnashLimit, owner, howner, hunique, houtside, hownerDebt,
    delta, hdelta, handoff⟩

end GameTheory
