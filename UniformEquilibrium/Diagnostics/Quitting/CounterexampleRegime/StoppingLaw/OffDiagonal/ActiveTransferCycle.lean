/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteSerialRelation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.PreemptionCycle
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.SlopeFrontier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.SourceMatchedResetCube

/-!
# Active tangent-transfer cycles at a stopping-law frontier

When a flat stopping-law tangent has no zero-debt support entry, every
positive off-diagonal coordinate from an active debt owner lands at another
active debt owner.  Since every active owner has such a coordinate and the
active carrier is finite, the positive tangent relation contains a periodic
cycle.

This is a dynamic, profile-derived cycle in the normalized stopping-law debt
directions.  It is not the static solo-preemption cycle of the terminal reward
table.  The final theorem compresses the four stopping-law frontier branches
to positive total slope, zero-debt support entry, or an active transfer cycle.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The positive tangent-transfer relation on the active debt carrier. -/
def QuittingStoppingLawActiveTransfer
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (mover recipient : {who // who ∈ frontier.active}) : Prop :=
  0 < frontier.tangent mover recipient.1

/-- A positive-period cycle in the active stopping-law tangent-transfer
relation. -/
abbrev QuittingStoppingLawActiveTransferCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :=
  Math.FiniteSerialRelation.PeriodicCycle
    (QuittingStoppingLawActiveTransfer frontier)

/-- Reset coordinates preceding one position of an active transfer cycle. -/
def QuittingStoppingLawActiveTransferCycle.prefixWord
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier)
    (time : ℕ) : List ι :=
  (List.range time).map fun earlier ↦ (cycle.vertex earlier).1

@[simp]
theorem QuittingStoppingLawActiveTransferCycle.prefixWord_length
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier)
    (time : ℕ) :
    (cycle.prefixWord time).length = time := by
  simp [prefixWord]

/-- The active positive-debt carrier of every stopping-law frontier is
nonempty. -/
theorem QuittingCounterexampleStoppingLawFrontier.active_nonempty
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    frontier.active.Nonempty := by
  by_contra hempty
  have hactiveEmpty : frontier.active = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hdebtZero : ∀ who,
      quittingTerminalSemanticDebt frontier.base who = 0 := by
    intro who
    have hnotPositive :
        ¬0 < quittingTerminalSemanticDebt frontier.base who := by
      intro hpositive
      have hmem := (frontier.active_iff who).2 hpositive
      rw [hactiveEmpty] at hmem
      simp at hmem
    exact le_antisymm (le_of_not_gt hnotPositive)
      (quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
        frontier.base_mem who)
  have hbasePositive := frontier.base_positive
  unfold quittingTerminalSemanticDebtSum at hbasePositive
  simp only [hdebtZero, Finset.sum_const_zero] at hbasePositive
  exact (lt_irrefl 0) hbasePositive

/-- In the absence of a flat support-entry branch, every positive tangent
recipient of an active mover is itself active. -/
theorem QuittingCounterexampleStoppingLawFrontier.mem_active_of_tangent_pos_of_noEntry
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent)
    {mover : {who // who ∈ frontier.active}} {recipient : ι}
    (hpositive : 0 < frontier.tangent mover recipient) :
    recipient ∈ frontier.active := by
  by_contra hinactive
  have hdebtNonneg :
      0 ≤ quittingTerminalSemanticDebt frontier.base recipient :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward
      frontier.base_mem recipient
  have hdebtZero :
      quittingTerminalSemanticDebt frontier.base recipient = 0 := by
    apply le_antisymm
    · exact le_of_not_gt (fun hdebt ↦
        hinactive ((frontier.active_iff recipient).2 hdebt))
    · exact hdebtNonneg
  apply hnoEntry
  refine ⟨mover.1, mover.2, recipient, hdebtZero, ?_⟩
  simpa [quittingActiveDebtTangentExtension, mover.2] using hpositive

/-- If a stopping-law frontier has no zero-debt support entry, its positive
active tangent relation contains a periodic cycle. -/
theorem QuittingCounterexampleStoppingLawFrontier.nonempty_activeTransferCycle_of_noEntry
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime)
    (hnoEntry : ¬HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent) :
    Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  letI : Nonempty {who // who ∈ frontier.active} := by
    obtain ⟨who, hwho⟩ := frontier.active_nonempty
    exact ⟨⟨who, hwho⟩⟩
  apply Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial
  intro mover
  obtain ⟨recipient, _hne, hpositive⟩ :=
    frontier.exists_positiveOffDiagonal mover.2
  have hrecipient :=
    frontier.mem_active_of_tangent_pos_of_noEntry hnoEntry hpositive
  exact ⟨⟨recipient, hrecipient⟩, hpositive⟩

/-- A stopping-law active transfer cycle cannot have period one because every
active tangent diagonal is strictly negative. -/
theorem QuittingStoppingLawActiveTransferCycle.two_le_period
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier) :
    2 ≤ cycle.period := by
  apply cycle.two_le_period_of_irreflexive
  intro mover hedge
  have hdiagonal := frontier.tangent_diagonal mover
  have hdebt := (frontier.active_iff mover.1).1 mover.2
  simp only [QuittingStoppingLawActiveTransfer] at hedge
  linarith

/-- The finitely many edges of an active transfer cycle retain one uniform
positive slope along the literal stopping-law subsequence.  All edges use the
same source profile at each rank; only the active mover and its selected best
response vary with the edge. -/
theorem QuittingStoppingLawActiveTransferCycle.exists_eventually_uniformSlope
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier) :
    ∃ charge : ℝ, 0 < charge ∧
      ∀ᶠ rank in atTop, ∀ time < cycle.period,
        charge ≤ quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq rank)) (cycle.vertex time).1
          (frontier.bestResponse (cycle.vertex time) (frontier.subseq rank))
          (frontier.lambda (frontier.subseq rank))
          (frontier.lambda_pos (frontier.subseq rank)).le
          (frontier.lambda_le_one (frontier.subseq rank))
          (cycle.vertex (time + 1)).1 := by
  classical
  have hrange : (Finset.range cycle.period).Nonempty :=
    ⟨0, Finset.mem_range.mpr cycle.period_pos⟩
  obtain ⟨minimumTime, hminimumTime, hminimum⟩ :=
    Finset.exists_min_image (Finset.range cycle.period)
      (fun time ↦ frontier.tangent (cycle.vertex time)
        (cycle.vertex (time + 1)).1) hrange
  let charge := frontier.tangent (cycle.vertex minimumTime)
    (cycle.vertex (minimumTime + 1)).1 / 2
  have hminimumPositive : 0 < frontier.tangent (cycle.vertex minimumTime)
      (cycle.vertex (minimumTime + 1)).1 := by
    simpa only [QuittingStoppingLawActiveTransfer] using cycle.edge minimumTime
  have hcharge : 0 < charge := by
    exact div_pos hminimumPositive (by norm_num)
  have hchargeLt : ∀ time < cycle.period,
      charge < frontier.tangent (cycle.vertex time)
        (cycle.vertex (time + 1)).1 := by
    intro time htime
    have hle := hminimum time (Finset.mem_range.mpr htime)
    dsimp only [charge]
    linarith
  refine ⟨charge, hcharge, ?_⟩
  have heach : ∀ time ∈ Finset.range cycle.period,
      ∀ᶠ rank in atTop,
        charge ≤ quittingStoppingLawNormalizedDebtDirection reward
          (frontier.profiles (frontier.subseq rank)) (cycle.vertex time).1
          (frontier.bestResponse (cycle.vertex time) (frontier.subseq rank))
          (frontier.lambda (frontier.subseq rank))
          (frontier.lambda_pos (frontier.subseq rank)).le
          (frontier.lambda_le_one (frontier.subseq rank))
          (cycle.vertex (time + 1)).1 := by
    intro time htime
    exact (frontier.tangent_tendsto (cycle.vertex time)
      (cycle.vertex (time + 1)).1).eventually
        (Ioi_mem_nhds (hchargeLt time (Finset.mem_range.mp htime))) |>.mono
          fun _ hvalue ↦ hvalue.le
  let P : ℕ → ℕ → Prop := fun rank time ↦
    charge ≤ quittingStoppingLawNormalizedDebtDirection reward
      (frontier.profiles (frontier.subseq rank)) (cycle.vertex time).1
      (frontier.bestResponse (cycle.vertex time) (frontier.subseq rank))
      (frontier.lambda (frontier.subseq rank))
      (frontier.lambda_pos (frontier.subseq rank)).le
      (frontier.lambda_le_one (frontier.subseq rank))
      (cycle.vertex (time + 1)).1
  have gather : ∀ times : Finset ℕ,
      (∀ time ∈ times, ∀ᶠ rank in atTop, P rank time) →
        ∀ᶠ rank in atTop, ∀ time ∈ times, P rank time := by
    intro times htimes
    induction times using Finset.induction_on with
    | empty => exact Eventually.of_forall fun _ _ hmem ↦ by simp at hmem
    | @insert time times hnotMember ih =>
        have htime := htimes time (Finset.mem_insert_self time times)
        have hrest := ih fun other hother ↦
          htimes other (Finset.mem_insert_of_mem hother)
        filter_upwards [htime, hrest] with rank htimeRank hrestRank
        intro other hother
        rcases Finset.mem_insert.mp hother with rfl | hother
        · exact htimeRank
        · exact hrestRank other hother
  have hall : ∀ᶠ rank in atTop, ∀ time ∈ Finset.range cycle.period,
      charge ≤ quittingStoppingLawNormalizedDebtDirection reward
        (frontier.profiles (frontier.subseq rank)) (cycle.vertex time).1
        (frontier.bestResponse (cycle.vertex time) (frontier.subseq rank))
        (frontier.lambda (frontier.subseq rank))
        (frontier.lambda_pos (frontier.subseq rank)).le
        (frontier.lambda_le_one (frontier.subseq rank))
        (cycle.vertex (time + 1)).1 := by
    change ∀ᶠ rank in atTop, ∀ time ∈ Finset.range cycle.period, P rank time
    apply gather
    intro time htime
    exact heach time htime
  exact hall.mono fun _ hAll time htime ↦
    hAll time (Finset.mem_range.mpr htime)

/-- The uniform cycle slope is realized by literal frozen edges of one
source-matched reset cube at each selected rank.  In particular, all cycle
edges coexist at one actual source profile and one common positive reset
scale. -/
theorem QuittingStoppingLawActiveTransferCycle.exists_eventually_uniformCubeEdge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier) :
    ∃ charge : ℝ, 0 < charge ∧
      ∀ᶠ rank in atTop, ∀ time < cycle.period,
        let data := frontier.sourceMatchedResetCubeData rank
        let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward candidate)
            (cycle.vertex (time + 1)).1
        frontier.lambda (frontier.subseq rank) * charge ≤
          Math.Finset.CubicalResetIntegrability.edge
            (data.value debt) ∅ (cycle.vertex time).1 := by
  obtain ⟨charge, hcharge, heventually⟩ :=
    cycle.exists_eventually_uniformSlope
  refine ⟨charge, hcharge, ?_⟩
  filter_upwards [heventually] with rank hAll
  intro time htime
  dsimp only
  rw [frontier.sourceMatchedResetCubeData_debtEdge_eq_scale_mul_actualDirection]
  exact mul_le_mul_of_nonneg_left (hAll time htime)
    (frontier.lambda_pos (frontier.subseq rank)).le

/-- **Reached cube edge or signed square curvature.**  Traverse the cycle's
reset coordinates in order inside the literal source-matched cube.  At every
cycle position, either the reached edge retains half of the common-source
positive transfer, or one earlier reset crosses a square whose absolute
curvature exceeds the common edge budget divided by twice the period.

This is a chronological statement in the profile cube.  It is not yet a
chronological quitting-play compiler. -/
theorem QuittingStoppingLawActiveTransferCycle.exists_eventually_reachedCubeEdge_or_curvature
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (cycle : QuittingStoppingLawActiveTransferCycle frontier) :
    ∃ charge : ℝ, 0 < charge ∧
      ∀ᶠ rank in atTop, ∀ time < cycle.period,
        let data := frontier.sourceMatchedResetCubeData rank
        let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward candidate)
            (cycle.vertex (time + 1)).1
        let word := cycle.prefixWord time
        frontier.lambda (frontier.subseq rank) * charge / 2 ≤
            Math.Finset.CubicalResetIntegrability.edge
              (data.value debt)
              (Math.Finset.CubicalResetIntegrability.finalSet ∅ word)
              (cycle.vertex time).1 ∨
          Math.Finset.CubicalResetIntegrability.HasAbsSquareAboveOnEdge
            (data.value debt)
            (frontier.lambda (frontier.subseq rank) * charge /
              (2 * (cycle.period : ℝ))) ∅ word (cycle.vertex time).1 := by
  obtain ⟨charge, hcharge, heventually⟩ :=
    cycle.exists_eventually_uniformCubeEdge
  refine ⟨charge, hcharge, ?_⟩
  filter_upwards [heventually] with rank hAll
  intro time htime
  dsimp only
  let data := frontier.sourceMatchedResetCubeData rank
  let debt := fun candidate : (quittingGame reward).BehaviorProfile ↦
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward candidate)
      (cycle.vertex (time + 1)).1
  let word := cycle.prefixWord time
  let edgeFloor := frontier.lambda (frontier.subseq rank) * charge
  let threshold := edgeFloor / (2 * (cycle.period : ℝ))
  have hedgeFloor : edgeFloor ≤
      Math.Finset.CubicalResetIntegrability.edge
        (data.value debt) ∅ (cycle.vertex time).1 := by
    simpa only [data, debt, edgeFloor] using hAll time htime
  have hperiodReal : 0 < (cycle.period : ℝ) := by
    exact_mod_cast cycle.period_pos
  have hedgeFloorPos : 0 < edgeFloor := by
    exact mul_pos (frontier.lambda_pos (frontier.subseq rank)) hcharge
  have hthreshold : 0 ≤ threshold := by
    exact (div_pos hedgeFloorPos (mul_pos (by norm_num) hperiodReal)).le
  have htimeReal : (time : ℝ) ≤ (cycle.period : ℝ) := by
    exact_mod_cast Nat.le_of_lt htime
  have hwordBound : (word.length : ℝ) * threshold ≤ edgeFloor / 2 := by
    rw [show word.length = time by simp [word]]
    calc
      (time : ℝ) * threshold ≤ (cycle.period : ℝ) * threshold :=
        mul_le_mul_of_nonneg_right htimeReal hthreshold
      _ = edgeFloor / 2 := by
        dsimp only [threshold]
        field_simp [ne_of_gt hperiodReal]
  rcases
      Math.Finset.CubicalResetIntegrability.abs_edge_finalSet_sub_edge_le_or_hasAbsSquareAboveOnEdge
        (data.value debt) ∅ word (cycle.vertex time).1 threshold with
    hnear | hcurvature
  · left
    have hdiff :
        |Math.Finset.CubicalResetIntegrability.edge
              (data.value debt)
              (Math.Finset.CubicalResetIntegrability.finalSet ∅ word)
              (cycle.vertex time).1 -
            Math.Finset.CubicalResetIntegrability.edge
              (data.value debt) ∅ (cycle.vertex time).1| ≤
          edgeFloor / 2 := hnear.trans hwordBound
    have hlower := (abs_le.mp hdiff).1
    dsimp only [edgeFloor] at hlower ⊢
    linarith
  · right
    simpa only [data, debt, word, threshold, edgeFloor] using hcurvature

/-- Independently of the total tangent slope, every stopping-law frontier has
either a zero-debt support entry or a dynamic active transfer cycle.  This
reroutes the localization; it does not consume positive total slope, whose
endpoint and atom consequences remain available in parallel. -/
theorem QuittingCounterexampleStoppingLawFrontier.entry_or_activeTransferCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent ∨
      Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  by_cases hentry : HasQuittingStoppingLawFlatSupportEntry
      frontier.base frontier.active frontier.tangent
  · exact Or.inl hentry
  · exact Or.inr (frontier.nonempty_activeTransferCycle_of_noEntry hentry)

/-- The four tagged stopping-law branches compress to three semantic outcomes:
positive total slope, zero-debt support entry, or a dynamic active transfer
cycle.  The first label retains extra quantitative information despite the
independent binary rerouting above. -/
theorem QuittingCounterexampleStoppingLawFrontier.slope_or_entry_or_activeTransferCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) ∨
      HasQuittingStoppingLawFlatSupportEntry
        frontier.base frontier.active frontier.tangent ∨
      Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  rcases frontier.exhaustive_branch with hpositive |
      ⟨_hflat, hentry⟩ |
      ⟨_hflat, hnoEntry, _hcirculation⟩ |
      ⟨_hflat, hnoEntry, _hnoCirculation, _hpotential⟩
  · exact Or.inl hpositive
  · exact Or.inr (Or.inl hentry)
  · exact Or.inr (Or.inr
      (frontier.nonempty_activeTransferCycle_of_noEntry hnoEntry))
  · exact Or.inr (Or.inr
      (frontier.nonempty_activeTransferCycle_of_noEntry hnoEntry))

/-- Every counterexample regime reaches one stopping-law frontier satisfying
the compressed dynamic trichotomy. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_dynamicTrichotomy
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      (∃ mover, 0 < ∑ observer, frontier.tangent mover observer) ∨
        HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.active frontier.tangent ∨
        Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.slope_or_entry_or_activeTransferCycle⟩

/-- Every counterexample regime reaches a stopping-law frontier satisfying
the binary support-entry or active-transfer-cycle localization. -/
theorem QuittingCounterexampleRegime.exists_stoppingLaw_entry_or_activeTransferCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (regime : QuittingCounterexampleRegime reward) :
    ∃ frontier : QuittingCounterexampleStoppingLawFrontier regime,
      HasQuittingStoppingLawFlatSupportEntry
          frontier.base frontier.active frontier.tangent ∨
        Nonempty (QuittingStoppingLawActiveTransferCycle frontier) := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨frontier⟩ := regime.exists_stoppingLaw_exhaustiveFrontier
  exact ⟨frontier, frontier.entry_or_activeTransferCycle⟩

end GameTheory
