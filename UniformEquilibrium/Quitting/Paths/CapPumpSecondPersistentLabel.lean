/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Exceptional.BellmanTail
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# Bounded cap pumps and second persistent quitting labels

This file isolates the scalar cap-pump accounting on one literal sequence of
quitting roots.  The cap recursion is supplied data.  Its Continue coefficient
and absorbing reward contribution are the actual opponent-only quantities of
the roots, so the persistent label extracted below belongs to the unchanged
root chronology.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A bounded scalar cap recursion on consecutive finite nonempty blocks of
one literal quitting-root chronology.  The caps are candidate caps; no claim
that they arise from one global semantic profile is included. -/
structure QuittingBoundedCapPump
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι) (K M : ℝ) where
  length : ℕ → ℕ
  length_pos : ∀ block, 0 < length block
  cap : ℕ → ℕ → ℝ
  K_nonneg : 0 ≤ K
  M_nonneg : 0 ≤ M
  cap_bound : ∀ block offset, offset ≤ length block → |cap block offset| ≤ K
  reward_bound : ∀ terminal player, |reward terminal player| ≤ M
  cap_recursion : ∀ block offset, offset < length block →
    cap block offset = max
      (quittingFixedOpponentsQuitValue reward roots owner
        (consecutiveBlockStart length block + offset))
      (quittingFixedOpponentsContinueReward reward roots owner
          (consecutiveBlockStart length block + offset) +
        quittingFixedOpponentsContinueMass roots owner
            (consecutiveBlockStart length block + offset) *
          cap block (offset + 1))

namespace QuittingBoundedCapPump

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {roots : ℕ → ι → PMF Bool} {owner : ι} {K M : ℝ}
  (pump : QuittingBoundedCapPump reward roots owner K M)

/-- Favorable cap drop from a donated block endpoint to the next source. -/
def favorableDrop (block : ℕ) : ℝ :=
  max (pump.cap block (pump.length block) - pump.cap (block + 1) 0) 0

/-- Reverse seam rise, which can replenish a later favorable cap drop. -/
def reverseRise (block : ℕ) : ℝ :=
  max (pump.cap (block + 1) 0 - pump.cap block (pump.length block)) 0

/-- Total actual opponent-absorption charge inside one block. -/
def blockOpponentCharge (block : ℕ) : ℝ :=
  consecutiveBlockSum pump.length (quittingOpponentClockCharge roots owner) block

theorem favorableDrop_nonneg (block : ℕ) :
    0 ≤ pump.favorableDrop block :=
  le_max_right _ _

theorem reverseRise_nonneg (block : ℕ) :
    0 ≤ pump.reverseRise block :=
  le_max_right _ _

theorem blockOpponentCharge_nonneg (block : ℕ) :
    0 ≤ pump.blockOpponentCharge block := by
  unfold blockOpponentCharge consecutiveBlockSum
  exact Finset.sum_nonneg fun offset _ =>
    quittingOpponentClockCharge_nonneg roots owner _

/-- One supplied max-cap row can rise only by spending actual opponent
absorption at that row. -/
theorem row_positiveRise_le (block offset : ℕ)
    (hlength : offset < pump.length block) :
    max (pump.cap block (offset + 1) - pump.cap block offset) 0 ≤
      (K + M) * quittingOpponentClockCharge roots owner
        (consecutiveBlockStart pump.length block + offset) := by
  let time := consecutiveBlockStart pump.length block + offset
  let O := quittingFixedOpponentsContinueMass roots owner time
  let C := quittingFixedOpponentsContinueReward reward roots owner time
  let next := pump.cap block (offset + 1)
  have hO0 : 0 ≤ O := quittingStationaryContinueMass_nonneg _
  have hO1 : O ≤ 1 := quittingStationaryContinueMass_le_one _
  have hfactor : 0 ≤ 1 - O := sub_nonneg.mpr hO1
  have hnext : |next| ≤ K := by
    exact pump.cap_bound block (offset + 1) (Nat.succ_le_iff.mpr hlength)
  have hC : |C| ≤ M * (1 - O) := by
    exact abs_quittingFixedOpponentsContinueReward_le_hazard
      reward roots owner time M pump.M_nonneg
        (fun terminal => pump.reward_bound terminal owner)
  have hcontinue : C + O * next ≤ pump.cap block offset := by
    rw [pump.cap_recursion block offset hlength]
    exact le_max_right _ _
  have hrise : next - pump.cap block offset ≤ (1 - O) * next - C := by
    linarith
  have habs : |(1 - O) * next - C| ≤ (K + M) * (1 - O) := by
    calc
      |(1 - O) * next - C| ≤ |(1 - O) * next| + |C| := abs_sub _ _
      _ = (1 - O) * |next| + |C| := by
        rw [abs_mul, abs_of_nonneg hfactor]
      _ ≤ (1 - O) * K + M * (1 - O) :=
        add_le_add (mul_le_mul_of_nonneg_left hnext hfactor) hC
      _ = (K + M) * (1 - O) := by ring
  have hbound : max (next - pump.cap block offset) 0 ≤
      (K + M) * (1 - O) := by
    apply max_le
    · exact (hrise.trans (le_abs_self _)).trans habs
    · exact mul_nonneg (add_nonneg pump.K_nonneg pump.M_nonneg) hfactor
  simpa [time, O, quittingOpponentClockCharge_eq_one_sub] using hbound

/-- The signed cap rise through a block is bounded by its accumulated actual
opponent-absorption charge. -/
theorem block_rise_le (block : ℕ) :
    pump.cap block (pump.length block) - pump.cap block 0 ≤
      (K + M) * pump.blockOpponentCharge block := by
  have hsum :
      (∑ offset ∈ Finset.range (pump.length block),
          (pump.cap block (offset + 1) - pump.cap block offset)) ≤
        ∑ offset ∈ Finset.range (pump.length block),
          (K + M) * quittingOpponentClockCharge roots owner
            (consecutiveBlockStart pump.length block + offset) := by
    apply Finset.sum_le_sum
    intro offset hoffset
    have hlt := Finset.mem_range.mp hoffset
    exact (le_max_left _ _).trans (pump.row_positiveRise_le block offset hlt)
  rw [Finset.sum_range_sub] at hsum
  unfold blockOpponentCharge consecutiveBlockSum
  rw [Finset.mul_sum]
  exact hsum

private theorem positivePart_sub_reversePart (value : ℝ) :
    max value 0 - max (-value) 0 = value := by
  by_cases hvalue : 0 ≤ value
  · rw [max_eq_left hvalue, max_eq_right (neg_nonpos.mpr hvalue)]
    ring
  · have hvalue' : value ≤ 0 := le_of_not_ge hvalue
    rw [max_eq_right hvalue', max_eq_left (neg_nonneg.mpr hvalue')]
    ring

/-- Finite seam telescope: favorable drops are funded only by reverse rises,
within-block opponent absorption, and the two bounded endpoints. -/
theorem seam_telescope (blocks : ℕ) :
    (∑ block ∈ Finset.range blocks, pump.favorableDrop block) ≤
      (∑ block ∈ Finset.range blocks, pump.reverseRise block) +
        (K + M) *
          (∑ block ∈ Finset.range blocks, pump.blockOpponentCharge block) +
        2 * K := by
  let source : ℕ → ℝ := fun block => pump.cap block 0
  let endpoint : ℕ → ℝ := fun block => pump.cap block (pump.length block)
  have hparts : ∀ block,
      pump.favorableDrop block - pump.reverseRise block =
        endpoint block - source (block + 1) := by
    intro block
    unfold favorableDrop reverseRise endpoint source
    simpa only [neg_sub] using
      positivePart_sub_reversePart
        (pump.cap block (pump.length block) - pump.cap (block + 1) 0)
  have hidentity :
      (∑ block ∈ Finset.range blocks, pump.favorableDrop block) -
          (∑ block ∈ Finset.range blocks, pump.reverseRise block) =
        (∑ block ∈ Finset.range blocks, (endpoint block - source block)) +
          (source 0 - source blocks) := by
    rw [← Finset.sum_sub_distrib]
    calc
      (∑ block ∈ Finset.range blocks,
          (pump.favorableDrop block - pump.reverseRise block)) =
          ∑ block ∈ Finset.range blocks,
            (endpoint block - source (block + 1)) := by
        apply Finset.sum_congr rfl
        intro block _
        exact hparts block
      _ = ∑ block ∈ Finset.range blocks,
          ((endpoint block - source block) +
            (source block - source (block + 1))) := by
        apply Finset.sum_congr rfl
        intro block _
        ring
      _ = (∑ block ∈ Finset.range blocks, (endpoint block - source block)) +
          ∑ block ∈ Finset.range blocks,
            (source block - source (block + 1)) := by
        rw [Finset.sum_add_distrib]
      _ = _ := by rw [Math.sum_range_sub_succ]
  have hblocks :
      (∑ block ∈ Finset.range blocks, (endpoint block - source block)) ≤
        (K + M) *
          ∑ block ∈ Finset.range blocks, pump.blockOpponentCharge block := by
    calc
      _ ≤ ∑ block ∈ Finset.range blocks,
          (K + M) * pump.blockOpponentCharge block := by
        apply Finset.sum_le_sum
        intro block _
        exact pump.block_rise_le block
      _ = _ := by rw [Finset.mul_sum]
  have hboundary : source 0 - source blocks ≤ 2 * K := by
    have hfirst := pump.cap_bound 0 0 (Nat.zero_le _)
    have hlast := pump.cap_bound blocks 0 (Nat.zero_le _)
    have hfirstUpper := (abs_le.mp hfirst).2
    have hlastLower := (abs_le.mp hlast).1
    dsimp only [source] at hfirstUpper hlastLower ⊢
    linarith
  linarith

/-- Divergent favorable seam drops with summable reverse rises force a
nonsummable actual opponent-absorption block account. -/
theorem not_summable_blockOpponentCharge
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise) :
    ¬Summable pump.blockOpponentCharge := by
  intro hcharge
  apply hfavorable
  apply summable_of_sum_range_le (pump.favorableDrop_nonneg)
  intro blocks
  calc
    (∑ block ∈ Finset.range blocks, pump.favorableDrop block) ≤
        (∑ block ∈ Finset.range blocks, pump.reverseRise block) +
          (K + M) *
            (∑ block ∈ Finset.range blocks, pump.blockOpponentCharge block) +
          2 * K := pump.seam_telescope blocks
    _ ≤ (∑' block, pump.reverseRise block) +
          (K + M) * (∑' block, pump.blockOpponentCharge block) + 2 * K := by
      have hreverseLe := hreverse.sum_le_tsum (Finset.range blocks)
        (fun block _ => pump.reverseRise_nonneg block)
      have hchargeLe := hcharge.sum_le_tsum (Finset.range blocks)
        (fun block _ => pump.blockOpponentCharge_nonneg block)
      exact add_le_add
        (add_le_add hreverseLe
          (mul_le_mul_of_nonneg_left hchargeLe
            (add_nonneg pump.K_nonneg pump.M_nonneg))) le_rfl

private theorem consecutiveBlockSum_nonneg_of_nonneg
    (length : ℕ → ℕ) (stream : ℕ → ℝ)
    (hstream : ∀ time, 0 ≤ stream time) (block : ℕ) :
    0 ≤ consecutiveBlockSum length stream block := by
  unfold consecutiveBlockSum
  exact Finset.sum_nonneg fun offset _ => hstream _

private theorem summable_consecutiveBlockSum_of_summable
    (length : ℕ → ℕ) (stream : ℕ → ℝ)
    (hstream : ∀ time, 0 ≤ stream time) (hsummable : Summable stream) :
    Summable (consecutiveBlockSum length stream) := by
  apply summable_of_sum_range_le
    (consecutiveBlockSum_nonneg_of_nonneg length stream hstream)
  intro blocks
  rw [sum_consecutiveBlockSum_eq_sum_range]
  exact hsummable.sum_le_tsum _ fun time _ => hstream time

/-- A nonsummable opponent-absorption block account contains one fixed
opponent with a persistent actual marginal Quit stream. -/
theorem exists_persistentOpponent_of_not_summable_blockOpponentCharge
    (hcharge : ¬Summable pump.blockOpponentCharge) :
    ∃ opponent, opponent ≠ owner ∧
      ¬Summable (quittingMarginalQuitHazard roots opponent) := by
  classical
  by_contra hnone
  have hall : ∀ opponent, opponent ≠ owner →
      Summable (quittingMarginalQuitHazard roots opponent) := by
    intro opponent hne
    by_contra hnonsummable
    exact hnone ⟨opponent, hne, hnonsummable⟩
  let total : ℕ → ℝ := fun time =>
    ∑ opponent ∈ Finset.univ.erase owner,
      quittingMarginalQuitHazard roots opponent time
  have htotalNonneg : ∀ time, 0 ≤ total time := by
    intro time
    exact Finset.sum_nonneg fun opponent _ =>
      quittingMarginalQuitHazard_nonneg roots opponent time
  have htotal : Summable total := by
    exact summable_sum fun opponent hopponent =>
      hall opponent (Finset.ne_of_mem_erase hopponent)
  have htotalBlocks : Summable (consecutiveBlockSum pump.length total) :=
    summable_consecutiveBlockSum_of_summable
      pump.length total htotalNonneg htotal
  apply hcharge
  apply htotalBlocks.of_nonneg_of_le (pump.blockOpponentCharge_nonneg)
  intro block
  unfold blockOpponentCharge consecutiveBlockSum
  apply Finset.sum_le_sum
  intro offset _
  exact quittingOpponentClockCharge_le_sum_marginalQuitHazard
    roots owner (consecutiveBlockStart pump.length block + offset)

/-- Cap pumping produces one fixed persistent opponent on the unchanged root
chronology. -/
theorem exists_persistentOpponent
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise) :
    ∃ opponent, opponent ≠ owner ∧
      ¬Summable (quittingMarginalQuitHazard roots opponent) :=
  pump.exists_persistentOpponent_of_not_summable_blockOpponentCharge
    (pump.not_summable_blockOpponentCharge hfavorable hreverse)

/-- If the cap owner is already persistent, cap pumping produces the literal
two-persistent-label certificate for the same roots. -/
theorem hasTwoPersistent_of_owner
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise)
    (howner : ¬Summable (quittingMarginalQuitHazard roots owner)) :
    HasTwoPersistentQuittingMarginals roots := by
  obtain ⟨opponent, hne, hopponent⟩ :=
    pump.exists_persistentOpponent hfavorable hreverse
  exact ⟨owner, opponent, hne.symm, howner, hopponent⟩

omit [DecidableEq ι] in
/-- Two persistent marginal labels themselves certify that the finite player
type has at least two elements. -/
private theorem two_le_card_of_hasTwoPersistentQuittingMarginals
    {roots : ℕ → ι → PMF Bool}
    (hpersistent : HasTwoPersistentQuittingMarginals roots) :
    2 ≤ Fintype.card ι := by
  obtain ⟨first, second, hne, _, _⟩ := hpersistent
  exact Fintype.one_lt_card_iff.mpr ⟨first, second, hne⟩

/-! ## Known-mover excess -/

/-- The marginal account already assigned to a known mover through the first
`blocks` blocks. -/
def knownMoverAccount (mover : ι) (blocks : ℕ) : ℝ :=
  ∑ block ∈ Finset.range blocks,
    consecutiveBlockSum pump.length
      (quittingMarginalQuitHazard roots mover) block

/-- Marginal Quit mass outside both the cap owner and a known mover. -/
def remainingMarginalHazard
    (_pump : QuittingBoundedCapPump reward roots owner K M)
    (mover : ι) (time : ℕ) : ℝ :=
  ∑ opponent ∈ (Finset.univ.erase owner).erase mover,
    quittingMarginalQuitHazard roots opponent time

/-- Favorable seam excess after charging reverse rises, the two bounded
endpoints, and the already known mover's marginal account. -/
def knownMoverExcess (mover : ι) (blocks : ℕ) : ℝ :=
  (∑ block ∈ Finset.range blocks, pump.favorableDrop block) -
    (∑ block ∈ Finset.range blocks, pump.reverseRise block) - 2 * K -
      (K + M) * pump.knownMoverAccount mover blocks

theorem remainingMarginalHazard_nonneg (mover : ι) (time : ℕ) :
    0 ≤ pump.remainingMarginalHazard mover time := by
  unfold remainingMarginalHazard
  exact Finset.sum_nonneg fun opponent _ =>
    quittingMarginalQuitHazard_nonneg roots opponent time

private theorem opponentCharge_le_mover_add_remaining
    {mover : ι} (hne : mover ≠ owner) (time : ℕ) :
    quittingOpponentClockCharge roots owner time ≤
      quittingMarginalQuitHazard roots mover time +
        pump.remainingMarginalHazard mover time := by
  have hunion := quittingOpponentClockCharge_le_sum_marginalQuitHazard
    roots owner time
  have hmover : mover ∈ Finset.univ.erase owner := by simp [hne]
  have hsplit := Finset.sum_erase_add (Finset.univ.erase owner)
    (fun opponent => quittingMarginalQuitHazard roots opponent time) hmover
  unfold remainingMarginalHazard
  linarith

/-- Sharp finite known-mover inequality: only marginal mass outside the cap
owner and known mover can fund the displayed excess. -/
theorem knownMoverExcess_le
    {mover : ι} (hne : mover ≠ owner) (blocks : ℕ) :
    pump.knownMoverExcess mover blocks ≤
      (K + M) *
        (∑ block ∈ Finset.range blocks,
          consecutiveBlockSum pump.length
            (pump.remainingMarginalHazard mover) block) := by
  have hcharge :
      (∑ block ∈ Finset.range blocks, pump.blockOpponentCharge block) ≤
        pump.knownMoverAccount mover blocks +
          ∑ block ∈ Finset.range blocks,
            consecutiveBlockSum pump.length
              (pump.remainingMarginalHazard mover) block := by
    unfold blockOpponentCharge knownMoverAccount
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro block _
    unfold consecutiveBlockSum
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro offset _
    exact pump.opponentCharge_le_mover_add_remaining hne _
  have hscaled := mul_le_mul_of_nonneg_left hcharge
    (add_nonneg pump.K_nonneg pump.M_nonneg)
  have hseam := pump.seam_telescope blocks
  unfold knownMoverExcess
  linarith

/-- Unbounded known-mover-subtracted excess contains one fixed persistent
label outside both the cap owner and the known mover. -/
theorem exists_persistentOutside_of_knownMoverExcess
    {mover : ι} (hne : mover ≠ owner)
    (hexcess : ¬BddAbove (Set.range (pump.knownMoverExcess mover))) :
    ∃ opponent, opponent ≠ owner ∧ opponent ≠ mover ∧
      ¬Summable (quittingMarginalQuitHazard roots opponent) := by
  classical
  by_contra hnone
  have hall : ∀ opponent,
      opponent ∈ (Finset.univ.erase owner).erase mover →
        Summable (quittingMarginalQuitHazard roots opponent) := by
    intro opponent hopponent
    by_contra hnonsummable
    have hneOwner : opponent ≠ owner := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hopponent).2).1
    have hneMover : opponent ≠ mover := (Finset.mem_erase.mp hopponent).1
    exact hnone ⟨opponent, hneOwner, hneMover, hnonsummable⟩
  have hremaining : Summable (pump.remainingMarginalHazard mover) := by
    exact summable_sum fun opponent hopponent => hall opponent hopponent
  apply hexcess
  refine ⟨(K + M) * ∑' time, pump.remainingMarginalHazard mover time, ?_⟩
  rintro _ ⟨blocks, rfl⟩
  calc
    pump.knownMoverExcess mover blocks ≤
        (K + M) *
          (∑ block ∈ Finset.range blocks,
            consecutiveBlockSum pump.length
              (pump.remainingMarginalHazard mover) block) :=
      pump.knownMoverExcess_le hne blocks
    _ = (K + M) *
        (∑ time ∈ Finset.range (consecutiveBlockStart pump.length blocks),
          pump.remainingMarginalHazard mover time) := by
      rw [sum_consecutiveBlockSum_eq_sum_range]
    _ ≤ (K + M) * ∑' time, pump.remainingMarginalHazard mover time := by
      exact mul_le_mul_of_nonneg_left
        (hremaining.sum_le_tsum _ fun time _ =>
          pump.remainingMarginalHazard_nonneg mover time)
        (add_nonneg pump.K_nonneg pump.M_nonneg)

/-- A persistent known mover and unbounded mover-subtracted cap excess give
two persistent labels on the unchanged roots. -/
theorem hasTwoPersistent_of_knownMoverExcess
    {mover : ι} (hne : mover ≠ owner)
    (hmover : ¬Summable (quittingMarginalQuitHazard roots mover))
    (hexcess : ¬BddAbove (Set.range (pump.knownMoverExcess mover))) :
    HasTwoPersistentQuittingMarginals roots := by
  obtain ⟨opponent, _, hneMover, hopponent⟩ :=
    pump.exists_persistentOutside_of_knownMoverExcess hne hexcess
  exact ⟨mover, opponent, Ne.symm hneMover, hmover, hopponent⟩

/-- Owner-persistent cap pumping yields joint and every-deleted survival on
every suffix of the same literal roots. -/
theorem survival_of_owner
    (hfavorable : ¬Summable pump.favorableDrop)
    (hreverse : Summable pump.reverseRise)
    (howner : ¬Summable (quittingMarginalQuitHazard roots owner)) :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0)) := by
  have hpersistent := pump.hasTwoPersistent_of_owner hfavorable hreverse howner
  exact hpersistent.survival
    (two_le_card_of_hasTwoPersistentQuittingMarginals hpersistent)

/-- Known-mover excess yields joint and every-deleted survival on every
suffix of the same literal roots. -/
theorem survival_of_knownMoverExcess
    {mover : ι} (hne : mover ≠ owner)
    (hmover : ¬Summable (quittingMarginalQuitHazard roots mover))
    (hexcess : ¬BddAbove (Set.range (pump.knownMoverExcess mover))) :
    (∀ who start, Tendsto
      (quittingOpponentSurvivalWeight roots who start) atTop (nhds 0)) ∧
    (∀ start, Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (roots time)) start)
      atTop (nhds 0)) := by
  have hpersistent :=
    pump.hasTwoPersistent_of_knownMoverExcess hne hmover hexcess
  exact hpersistent.survival
    (two_le_card_of_hasTwoPersistentQuittingMarginals hpersistent)

end QuittingBoundedCapPump

end GameTheory
