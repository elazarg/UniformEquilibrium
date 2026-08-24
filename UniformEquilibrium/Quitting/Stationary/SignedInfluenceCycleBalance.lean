/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.DirectedTransport.NormalForms
import MathUE.DirectedTransport.SCC
import MathUE.DirectedTransport.SimpleCycleBalance
import UniformEquilibrium.Quitting.Stationary.SignedInfluenceBlock

/-!
# Cycle-balanced signed influences in quitting games

This file derives a block-triangular influence certificate directly from the
complete quitting reward table.  Every ordered pair has a fixed positive,
negative, or absent membership influence.  If every directed simple cycle of
nonabsent influences has positive sign product, SCC polarities and a forward
condensation rank produce the certificate consumed by
`SignedInfluenceBlock.lean`.
-/

noncomputable section

namespace GameTheory

open MathUE
open Math
open Math.DirectedTransport
open Math.CycleCoboundary
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Payoff gain to `who` from joining a terminal coalition.  Membership of
`who` in the displayed background is normalized away. -/
def quittingMembershipGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) (S : Finset ι) : ℝ :=
  binaryJoinGain (fun player coalition =>
    quittingSetReward reward coalition player) who S

omit [Fintype ι] in
theorem quittingMembershipGain_erase_target (who : ι) (S : Finset ι) :
    quittingMembershipGain reward who (S.erase who) =
      quittingMembershipGain reward who S := by
  have hinsert : insert who (S.erase who) = insert who S := by
    ext player
    by_cases hplayer : player = who <;> simp [hplayer]
  simp [quittingMembershipGain, binaryJoinGain, hinsert]

/-- Change in `who`'s membership gain when `other` is added.  The normalized
definition is zero when `other` is already present and ignores whether `who`
is displayed in the background. -/
def quittingPairInfluence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (other who : ι) (S : Finset ι) : ℝ :=
  quittingMembershipGain reward who (insert other S) -
    quittingMembershipGain reward who S

omit [Fintype ι] in
theorem quittingPairInfluence_erase_target {other who : ι}
    (hne : other ≠ who) (S : Finset ι) :
    quittingPairInfluence reward other who (S.erase who) =
      quittingPairInfluence reward other who S := by
  rw [quittingPairInfluence, quittingPairInfluence]
  have hinsert : insert other (S.erase who) =
      (insert other S).erase who := by
    exact (Finset.erase_insert_of_ne hne).symm
  rw [hinsert, quittingMembershipGain_erase_target,
    quittingMembershipGain_erase_target]

/-- A fixed positive ordered influence, including a strict witness. -/
def IsPositiveQuittingInfluence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (other who : ι) : Prop :=
  (∀ S, other ∉ S → who ∉ S →
      0 ≤ quittingPairInfluence reward other who S) ∧
    ∃ S, other ∉ S ∧ who ∉ S ∧
      0 < quittingPairInfluence reward other who S

/-- A fixed negative ordered influence, including a strict witness. -/
def IsNegativeQuittingInfluence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (other who : ι) : Prop :=
  (∀ S, other ∉ S → who ∉ S →
      quittingPairInfluence reward other who S ≤ 0) ∧
    ∃ S, other ∉ S ∧ who ∉ S ∧
      quittingPairInfluence reward other who S < 0

/-- An absent ordered influence. -/
def IsAbsentQuittingInfluence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (other who : ι) : Prop :=
  ∀ S, other ∉ S → who ∉ S →
    quittingPairInfluence reward other who S = 0

/-- Every distinct ordered pair is globally positive, globally negative, or
absent over the complete coalition cube. -/
def SignConsistentQuittingInfluence
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ ⦃other who⦄, other ≠ who →
    IsPositiveQuittingInfluence reward other who ∨
      IsNegativeQuittingInfluence reward other who ∨
        IsAbsentQuittingInfluence reward other who

/-- A nonabsent directed influence edge, with source the influencing player
and target the affected player. -/
def QuittingInfluenceEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  {pair : ι × ι // pair.1 ≠ pair.2 ∧
    (IsPositiveQuittingInfluence reward pair.1 pair.2 ∨
      IsNegativeQuittingInfluence reward pair.1 pair.2)}

/-- Directed graph of nonabsent ordered influences. -/
def quittingInfluenceGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    EdgeGraph ι (QuittingInfluenceEdge reward) where
  source edge := edge.1.1
  target edge := edge.1.2

/-- The sign label of an influence edge. -/
def quittingInfluenceLabel (edge : QuittingInfluenceEdge reward) : ℤ := by
  classical
  exact if IsNegativeQuittingInfluence reward edge.1.1 edge.1.2 then -1 else 1

/-- Every directed simple influence cycle has positive sign product.  Since
each edge label is `±1`, positivity is exactly equality to `1`. -/
def EveryDirectedInfluenceCyclePositive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ (base : ι)
    (cycle : (quittingInfluenceGraph reward).Walk base base),
    Math.AdditiveTransport.IsSimpleCycle cycle →
      walkLabel quittingInfluenceLabel cycle = 1

omit [Fintype ι] in
private theorem influenceWalkLabel_eq_one_or_neg_one
    {start finish : ι}
    (walk : (quittingInfluenceGraph reward).Walk start finish) :
    walkLabel quittingInfluenceLabel walk = 1 ∨
      walkLabel quittingInfluenceLabel walk = -1 := by
  induction walk with
  | nil => simp
  | concat walk edge legal ih =>
      by_cases hnegative :
          IsNegativeQuittingInfluence reward edge.1.1 edge.1.2
      · have hedgeLabel : quittingInfluenceLabel edge = -1 := by
          simp [quittingInfluenceLabel, hnegative]
        rcases ih with ih | ih <;>
          simp only [walkLabel_concat, hedgeLabel, ih] <;> norm_num
      · have hedgeLabel : quittingInfluenceLabel edge = 1 := by
          simp [quittingInfluenceLabel, hnegative]
        rcases ih with ih | ih <;>
          simp only [walkLabel_concat, hedgeLabel, ih] <;> norm_num

omit [Fintype ι] in
private theorem influence_eq_zero_of_not_edge
    (hsign : SignConsistentQuittingInfluence reward)
    {other who : ι} (hne : other ≠ who)
    (hnotEdge : ¬(IsPositiveQuittingInfluence reward other who ∨
      IsNegativeQuittingInfluence reward other who)) (S : Finset ι)
    (hother : other ∉ S) :
    quittingPairInfluence reward other who S = 0 := by
  rcases hsign hne with hpositive | hnegative | habsent
  · exact (hnotEdge (Or.inl hpositive)).elim
  · exact (hnotEdge (Or.inr hnegative)).elim
  · rw [← quittingPairInfluence_erase_target hne S]
    exact habsent (S.erase who)
      (fun hmem => hother (Finset.mem_of_mem_erase hmem)) (by simp)

omit [Fintype ι] in
private theorem influence_nonneg_of_positive
    {other who : ι} (hne : other ≠ who)
    (hpositive : IsPositiveQuittingInfluence reward other who)
    (S : Finset ι) (hother : other ∉ S) :
    0 ≤ quittingPairInfluence reward other who S := by
  rw [← quittingPairInfluence_erase_target hne S]
  exact hpositive.1 (S.erase who)
    (fun hmem => hother (Finset.mem_of_mem_erase hmem)) (by simp)

omit [Fintype ι] in
private theorem influence_nonpos_of_negative
    {other who : ι} (hne : other ≠ who)
    (hnegative : IsNegativeQuittingInfluence reward other who)
    (S : Finset ι) (hother : other ∉ S) :
    quittingPairInfluence reward other who S ≤ 0 := by
  rw [← quittingPairInfluence_erase_target hne S]
  exact hnegative.1 (S.erase who)
    (fun hmem => hother (Finset.mem_of_mem_erase hmem)) (by simp)

/-- Predecessors in the directed influence graph. -/
def quittingInfluencePredecessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun other =>
    Nonempty ((quittingInfluenceGraph reward).Walk other who)

/-- A forward condensation rank: adding an influence edge can only enlarge
the predecessor set, and enlarges it strictly across SCCs. -/
def quittingInfluenceLevel
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) : ℕ :=
  (quittingInfluencePredecessors reward who).card

private theorem influenceEdge_level_le (edge : QuittingInfluenceEdge reward) :
    quittingInfluenceLevel reward edge.1.1 ≤
      quittingInfluenceLevel reward edge.1.2 := by
  classical
  apply Finset.card_le_card
  intro predecessor hpredecessor
  rw [quittingInfluencePredecessors, Finset.mem_filter] at hpredecessor ⊢
  refine ⟨Finset.mem_univ predecessor, ?_⟩
  obtain ⟨walk⟩ := hpredecessor.2
  exact ⟨walk.append (EdgeGraph.Walk.singleton edge)⟩

private theorem influenceEdge_linked_of_level_eq
    (edge : QuittingInfluenceEdge reward)
    (hlevel : quittingInfluenceLevel reward edge.1.1 =
      quittingInfluenceLevel reward edge.1.2) :
    LinkedTo (quittingInfluenceGraph reward) edge.1.1 edge.1.2 := by
  classical
  have hsubset : quittingInfluencePredecessors reward edge.1.1 ⊆
      quittingInfluencePredecessors reward edge.1.2 := by
    intro predecessor hpredecessor
    rw [quittingInfluencePredecessors, Finset.mem_filter] at hpredecessor ⊢
    refine ⟨Finset.mem_univ predecessor, ?_⟩
    obtain ⟨walk⟩ := hpredecessor.2
    exact ⟨walk.append (EdgeGraph.Walk.singleton edge)⟩
  have heq : quittingInfluencePredecessors reward edge.1.1 =
      quittingInfluencePredecessors reward edge.1.2 := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [quittingInfluenceLevel] using hlevel.ge
  constructor
  · exact ⟨EdgeGraph.Walk.singleton edge⟩
  · have htarget : edge.1.2 ∈
        quittingInfluencePredecessors reward edge.1.2 := by
      rw [quittingInfluencePredecessors, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨.nil⟩⟩
    rw [← heq, quittingInfluencePredecessors, Finset.mem_filter] at htarget
    exact htarget.2

omit [Fintype ι] in
private theorem switched_joinGain_of_notMem
    {switched S : Finset ι} {who : ι} (hwho : who ∉ switched) :
    binaryJoinGain (quittingSwitchedSetPayoff reward switched) who S =
      quittingMembershipGain reward who
        (quittingPolaritySwitch switched S) := by
  unfold quittingMembershipGain binaryJoinGain quittingSwitchedSetPayoff
  rw [quittingPolaritySwitch_insert_of_notMem hwho,
    quittingPolaritySwitch_erase_of_notMem hwho]

omit [Fintype ι] in
private theorem switched_joinGain_of_mem
    {switched S : Finset ι} {who : ι} (hwho : who ∈ switched) :
    binaryJoinGain (quittingSwitchedSetPayoff reward switched) who S =
      -quittingMembershipGain reward who
        (quittingPolaritySwitch switched S) := by
  unfold quittingMembershipGain binaryJoinGain quittingSwitchedSetPayoff
  rw [quittingPolaritySwitch_insert_of_mem hwho,
    quittingPolaritySwitch_erase_of_mem hwho]
  ring

private theorem intUnit_ratio_eq_neg_one_iff_ne (first second : ℤˣ) :
    first * second⁻¹ = -1 ↔ first ≠ second := by
  rcases Int.units_eq_one_or first with rfl | rfl <;>
    rcases Int.units_eq_one_or second with rfl | rfl <;> simp

private theorem intUnit_eq_neg_one_iff_not_eq_one (unit : ℤˣ) :
    unit = -1 ↔ unit ≠ 1 := by
  rcases Int.units_eq_one_or unit with rfl | rfl <;> simp

private theorem intUnit_ne_iff_neg_one_iff_not_neg_one
    (first second : ℤˣ) :
    first ≠ second ↔ (first = -1 ↔ second ≠ -1) := by
  rcases Int.units_eq_one_or first with rfl | rfl <;>
    rcases Int.units_eq_one_or second with rfl | rfl <;> simp

/-- Cycle balance constructs the exact block-triangular certificate expected
by the binary equilibrium theorem. -/
def influenceBlockCertificate_of_cycleBalancedSignConsistentInfluence
    (hsign : SignConsistentQuittingInfluence reward)
    (hcycle : EveryDirectedInfluenceCyclePositive reward) :
    QuittingInfluenceBlockCertificate reward := by
  classical
  let graph := quittingInfluenceGraph reward
  have hflat : HasTrivialCycleLabels graph quittingInfluenceLabel :=
    hasTrivialCycleLabels_of_simpleCycles hcycle
  have hcomponents :
      HasSCCUnitPotentials graph quittingInfluenceLabel :=
    hasTrivialCycleLabels_iff_hasSCCUnitPotentials.mp hflat
  let representative : SCC graph → ι := fun component =>
    (ofAntisymmetrization
      (α := ReachabilityVertex graph) (· ≤ ·) component :
        ReachabilityVertex graph)
  let potential : SCC graph → ι → ℤˣ := fun component =>
    Classical.choose (show ∃ potential : ι → ℤˣ, ∀ edge,
        LinkedTo graph (representative component) (graph.source edge) →
        LinkedTo graph (representative component) (graph.target edge) →
        quittingInfluenceLabel edge =
          ((potential (graph.target edge) *
            (potential (graph.source edge))⁻¹ : ℤˣ) : ℤ) from
      hcomponents (representative component))
  have hrepresentative (component : SCC graph) :
      toSCC graph (representative component) = component := by
    exact toAntisymmetrization_ofAntisymmetrization (· ≤ ·) component
  have hpotential (component : SCC graph) (edge : QuittingInfluenceEdge reward)
      (hsource : LinkedTo graph (representative component) edge.1.1)
      (htarget : LinkedTo graph (representative component) edge.1.2) :
      quittingInfluenceLabel edge =
        ((potential component edge.1.2 *
          (potential component edge.1.1)⁻¹ : ℤˣ) : ℤ) := by
    exact Classical.choose_spec (show ∃ potential : ι → ℤˣ, ∀ edge,
        LinkedTo graph (representative component) (graph.source edge) →
        LinkedTo graph (representative component) (graph.target edge) →
        quittingInfluenceLabel edge =
          ((potential (graph.target edge) *
            (potential (graph.source edge))⁻¹ : ℤˣ) : ℤ) from
      hcomponents (representative component)) edge hsource htarget
  let switched : Finset ι := Finset.univ.filter fun who =>
    potential (toSCC graph who) who = -1
  have mem_switched_iff (who : ι) :
      who ∈ switched ↔ potential (toSCC graph who) who = -1 := by
    simp [switched]
  have edge_negative_iff_switch_diff (edge : QuittingInfluenceEdge reward)
      (hlinked : LinkedTo graph edge.1.1 edge.1.2) :
      IsNegativeQuittingInfluence reward edge.1.1 edge.1.2 ↔
        (edge.1.1 ∈ switched ↔ edge.1.2 ∉ switched) := by
    have hcomponent : toSCC graph edge.1.1 = toSCC graph edge.1.2 :=
      toSCC_eq_toSCC_iff_linkedTo.mpr hlinked
    let component := toSCC graph edge.1.1
    have hsource : LinkedTo graph (representative component) edge.1.1 := by
      apply toSCC_eq_toSCC_iff_linkedTo.mp
      rw [hrepresentative]
    have htarget : LinkedTo graph (representative component) edge.1.2 := by
      apply toSCC_eq_toSCC_iff_linkedTo.mp
      rw [hrepresentative, ← hcomponent]
    have hedgePotential := hpotential component edge hsource htarget
    have hlabel : quittingInfluenceLabel edge = -1 ↔
        IsNegativeQuittingInfluence reward edge.1.1 edge.1.2 := by
      unfold quittingInfluenceLabel
      by_cases hnegative :
          IsNegativeQuittingInfluence reward edge.1.1 edge.1.2 <;>
        simp [hnegative]
    have hratio :
        potential component edge.1.2 *
            (potential component edge.1.1)⁻¹ = -1 ↔
          IsNegativeQuittingInfluence reward edge.1.1 edge.1.2 := by
      rw [← hlabel]
      constructor
      · intro hratio
        rw [hedgePotential]
        exact congrArg (fun unit : ℤˣ => (unit : ℤ)) hratio
      · intro hnegative
        apply Units.ext
        exact hedgePotential.symm.trans hnegative
    rw [← hratio, intUnit_ratio_eq_neg_one_iff_ne, ne_comm]
    have hsourceMem : edge.1.1 ∈ switched ↔
        potential component edge.1.1 = -1 := by
      rw [mem_switched_iff]
    have htargetMem : edge.1.2 ∈ switched ↔
        potential component edge.1.2 = -1 := by
      rw [mem_switched_iff]
      exact Iff.of_eq (congrArg
        (fun component => potential component edge.1.2 = -1) hcomponent.symm)
    rw [hsourceMem, htargetMem]
    exact intUnit_ne_iff_neg_one_iff_not_neg_one _ _
  let certificate : QuittingInfluenceBlockCertificate reward :=
    { switched := switched
      triangular :=
        { level := quittingInfluenceLevel reward
          within := by
            intro who other S hne hlevel
            by_cases hotherMem : other ∈ S
            · rw [Finset.insert_eq_self.mpr hotherMem]
            · by_cases hedgeData :
                IsPositiveQuittingInfluence reward other who ∨
                  IsNegativeQuittingInfluence reward other who
              · let edge : QuittingInfluenceEdge reward :=
                  ⟨(other, who), hne.symm, hedgeData⟩
                have hlinked : LinkedTo graph other who := by
                  apply influenceEdge_linked_of_level_eq edge
                  exact hlevel.symm
                have hnegativeIff :=
                  edge_negative_iff_switch_diff edge hlinked
                change IsNegativeQuittingInfluence reward other who ↔
                  (other ∈ switched ↔ who ∉ switched) at hnegativeIff
                by_cases hwhoSwitch : who ∈ switched <;>
                  by_cases hotherSwitch : other ∈ switched
                · have hpositive :
                      IsPositiveQuittingInfluence reward other who := by
                    rcases hedgeData with hpositive | hnegative
                    · exact hpositive
                    · have hdiff := hnegativeIff.mp hnegative
                      exact (hdiff.mp hotherSwitch hwhoSwitch).elim
                  rw [switched_joinGain_of_mem hwhoSwitch,
                    switched_joinGain_of_mem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_mem hotherSwitch]
                  have hotherOriginal : other ∈
                      quittingPolaritySwitch switched S := by
                    exact mem_quittingPolaritySwitch.mpr
                      (Or.inr ⟨hotherSwitch, hotherMem⟩)
                  have hinfluence := influence_nonneg_of_positive
                    hne.symm hpositive
                    ((quittingPolaritySwitch switched S).erase other) (by simp)
                  rw [quittingPairInfluence,
                    Finset.insert_erase hotherOriginal] at hinfluence
                  linarith
                · have hnegative :
                      IsNegativeQuittingInfluence reward other who := by
                    apply hnegativeIff.mpr
                    simp [hotherSwitch, hwhoSwitch]
                  rw [switched_joinGain_of_mem hwhoSwitch,
                    switched_joinGain_of_mem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                  have hotherOriginal : other ∉
                      quittingPolaritySwitch switched S := by
                    simp [mem_quittingPolaritySwitch, hotherMem,
                      hotherSwitch]
                  have hinfluence := influence_nonpos_of_negative
                    hne.symm hnegative (quittingPolaritySwitch switched S)
                    hotherOriginal
                  rw [quittingPairInfluence] at hinfluence
                  linarith
                · have hnegative :
                      IsNegativeQuittingInfluence reward other who := by
                    apply hnegativeIff.mpr
                    simp [hotherSwitch, hwhoSwitch]
                  rw [switched_joinGain_of_notMem hwhoSwitch,
                    switched_joinGain_of_notMem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_mem hotherSwitch]
                  have hotherOriginal : other ∈
                      quittingPolaritySwitch switched S := by
                    exact mem_quittingPolaritySwitch.mpr
                      (Or.inr ⟨hotherSwitch, hotherMem⟩)
                  have hinfluence := influence_nonpos_of_negative
                    hne.symm hnegative
                    ((quittingPolaritySwitch switched S).erase other) (by simp)
                  rw [quittingPairInfluence,
                    Finset.insert_erase hotherOriginal] at hinfluence
                  linarith
                · have hpositive :
                      IsPositiveQuittingInfluence reward other who := by
                    rcases hedgeData with hpositive | hnegative
                    · exact hpositive
                    · have hdiff := hnegativeIff.mp hnegative
                      exact (hotherSwitch (hdiff.mpr hwhoSwitch)).elim
                  rw [switched_joinGain_of_notMem hwhoSwitch,
                    switched_joinGain_of_notMem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                  have hotherOriginal : other ∉
                      quittingPolaritySwitch switched S := by
                    simp [mem_quittingPolaritySwitch, hotherMem,
                      hotherSwitch]
                  have hinfluence := influence_nonneg_of_positive
                    hne.symm hpositive (quittingPolaritySwitch switched S)
                    hotherOriginal
                  rw [quittingPairInfluence] at hinfluence
                  linarith
              · have hzero := influence_eq_zero_of_not_edge
                  hsign hne.symm hedgeData
                by_cases hwhoSwitch : who ∈ switched <;>
                  by_cases hotherSwitch : other ∈ switched
                · rw [switched_joinGain_of_mem hwhoSwitch,
                    switched_joinGain_of_mem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_mem hotherSwitch]
                  have hotherOriginal : other ∈
                      quittingPolaritySwitch switched S := by
                    exact mem_quittingPolaritySwitch.mpr
                      (Or.inr ⟨hotherSwitch, hotherMem⟩)
                  have hinfluence := hzero
                    ((quittingPolaritySwitch switched S).erase other) (by simp)
                  rw [quittingPairInfluence,
                    Finset.insert_erase hotherOriginal] at hinfluence
                  linarith
                · rw [switched_joinGain_of_mem hwhoSwitch,
                    switched_joinGain_of_mem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                  have hotherOriginal : other ∉
                      quittingPolaritySwitch switched S := by
                    simp [mem_quittingPolaritySwitch, hotherMem,
                      hotherSwitch]
                  have hinfluence := hzero
                    (quittingPolaritySwitch switched S) hotherOriginal
                  rw [quittingPairInfluence] at hinfluence
                  linarith
                · rw [switched_joinGain_of_notMem hwhoSwitch,
                    switched_joinGain_of_notMem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_mem hotherSwitch]
                  have hotherOriginal : other ∈
                      quittingPolaritySwitch switched S := by
                    exact mem_quittingPolaritySwitch.mpr
                      (Or.inr ⟨hotherSwitch, hotherMem⟩)
                  have hinfluence := hzero
                    ((quittingPolaritySwitch switched S).erase other) (by simp)
                  rw [quittingPairInfluence,
                    Finset.insert_erase hotherOriginal] at hinfluence
                  linarith
                · rw [switched_joinGain_of_notMem hwhoSwitch,
                    switched_joinGain_of_notMem hwhoSwitch,
                    quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                  have hotherOriginal : other ∉
                      quittingPolaritySwitch switched S := by
                    simp [mem_quittingPolaritySwitch, hotherMem,
                      hotherSwitch]
                  have hinfluence := hzero
                    (quittingPolaritySwitch switched S) hotherOriginal
                  rw [quittingPairInfluence] at hinfluence
                  linarith
          future := by
            intro who other S hlevel
            by_cases hotherMem : other ∈ S
            · rw [Finset.insert_eq_self.mpr hotherMem]
            · have hne : other ≠ who := by
                intro heq
                subst other
                omega
              have hnotEdge :
                  ¬(IsPositiveQuittingInfluence reward other who ∨
                    IsNegativeQuittingInfluence reward other who) := by
                intro hedgeData
                let edge : QuittingInfluenceEdge reward :=
                  ⟨(other, who), hne, hedgeData⟩
                have hle := influenceEdge_level_le edge
                change quittingInfluenceLevel reward other ≤
                  quittingInfluenceLevel reward who at hle
                omega
              have hzero := influence_eq_zero_of_not_edge
                hsign hne hnotEdge
              by_cases hwhoSwitch : who ∈ switched <;>
                by_cases hotherSwitch : other ∈ switched
              · rw [switched_joinGain_of_mem hwhoSwitch,
                  switched_joinGain_of_mem hwhoSwitch,
                  quittingPolaritySwitch_insert_of_mem hotherSwitch]
                have hotherOriginal : other ∈
                    quittingPolaritySwitch switched S := by
                  exact mem_quittingPolaritySwitch.mpr
                    (Or.inr ⟨hotherSwitch, hotherMem⟩)
                have hinfluence := hzero
                  ((quittingPolaritySwitch switched S).erase other) (by simp)
                rw [quittingPairInfluence,
                  Finset.insert_erase hotherOriginal] at hinfluence
                linarith
              · rw [switched_joinGain_of_mem hwhoSwitch,
                  switched_joinGain_of_mem hwhoSwitch,
                  quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                have hotherOriginal : other ∉
                    quittingPolaritySwitch switched S := by
                  simp [mem_quittingPolaritySwitch, hotherMem,
                    hotherSwitch]
                have hinfluence := hzero
                  (quittingPolaritySwitch switched S) hotherOriginal
                rw [quittingPairInfluence] at hinfluence
                linarith
              · rw [switched_joinGain_of_notMem hwhoSwitch,
                  switched_joinGain_of_notMem hwhoSwitch,
                  quittingPolaritySwitch_insert_of_mem hotherSwitch]
                have hotherOriginal : other ∈
                    quittingPolaritySwitch switched S := by
                  exact mem_quittingPolaritySwitch.mpr
                    (Or.inr ⟨hotherSwitch, hotherMem⟩)
                have hinfluence := hzero
                  ((quittingPolaritySwitch switched S).erase other) (by simp)
                rw [quittingPairInfluence,
                  Finset.insert_erase hotherOriginal] at hinfluence
                linarith
              · rw [switched_joinGain_of_notMem hwhoSwitch,
                  switched_joinGain_of_notMem hwhoSwitch,
                  quittingPolaritySwitch_insert_of_notMem hotherSwitch]
                have hotherOriginal : other ∉
                    quittingPolaritySwitch switched S := by
                  simp [mem_quittingPolaritySwitch, hotherMem,
                    hotherSwitch]
                have hinfluence := hzero
                  (quittingPolaritySwitch switched S) hotherOriginal
                rw [quittingPairInfluence] at hinfluence
                linarith } }
  exact certificate

/-- Fixed-sign influences with positive sign on every directed simple cycle
produce a literal sure-exit coalition. -/
theorem exists_isQuittingSureExitSet_of_cycleBalancedSignConsistentInfluence
    (hsign : SignConsistentQuittingInfluence reward)
    (hcycle : EveryDirectedInfluenceCyclePositive reward) :
    ∃ S, IsQuittingSureExitSet reward S :=
  exists_isQuittingSureExitSet_of_influenceBlockCertificate
    (influenceBlockCertificate_of_cycleBalancedSignConsistentInfluence
      hsign hcycle)

/-- The constructed coalition feeds the existing unrestricted-behavior
uniform-payoff consumer. -/
theorem quittingGame_exists_uniformPayoff_of_cycleBalancedSignConsistentInfluence
    (hsign : SignConsistentQuittingInfluence reward)
    (hcycle : EveryDirectedInfluenceCyclePositive reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  quittingGame_exists_uniformPayoff_of_influenceBlockCertificate
    (influenceBlockCertificate_of_cycleBalancedSignConsistentInfluence
      hsign hcycle)

/-- Within the fixed-sign class, failure of every pure sure-exit coalition
forces a negative directed simple influence cycle. -/
theorem exists_negativeSimpleInfluenceCycle_of_no_sureExitSet
    (hsign : SignConsistentQuittingInfluence reward)
    (hnoExit : ¬∃ S, IsQuittingSureExitSet reward S) :
    ∃ (base : ι)
      (cycle : (quittingInfluenceGraph reward).Walk base base),
      Math.AdditiveTransport.IsSimpleCycle cycle ∧
        walkLabel quittingInfluenceLabel cycle = -1 := by
  by_contra hnegative
  have hcycle : EveryDirectedInfluenceCyclePositive reward := by
    intro base cycle hsimple
    rcases influenceWalkLabel_eq_one_or_neg_one cycle with hpositive | hnegativeLabel
    · exact hpositive
    · exact (hnegative ⟨base, cycle, hsimple, hnegativeLabel⟩).elim
  exact hnoExit
    (exists_isQuittingSureExitSet_of_cycleBalancedSignConsistentInfluence
      hsign hcycle)

end GameTheory

end
