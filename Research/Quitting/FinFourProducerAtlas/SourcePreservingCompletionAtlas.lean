/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import MathUE.Topology.FiniteLabelSubsequence
import Research.Quitting.FinFourProducerAtlas.SourcePreservingForcedPair

/-!
# Source-preserving completion atlas for Fin4 quitting games

The monodromy-free entrance first produces one cofinal stream of singleton
frames on one fixed minimum-law source.  The neutral frame compiler attaches
an actual forced pair, paid endpoint, and collision residual to every frame.
One simultaneous finite-label extraction fixes the singleton owner, forced
owner, payer, and payer action.  The nonnegative excess of the literal
post-date tail over the source minimum then has the priority alternative:
either it is uniformly positive on a strict subsequence, or it tends to zero.

The two resulting terminal modes retain the exact entrance, parent stream,
source chronology, full post-date behavioral spine, semantic tail, and outcome
law.  Their self-steps only delete the first row.  They are structural
capstones, not uniform-equilibrium consumers.
-/

noncomputable section

namespace GameTheory

open Filter

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {entrance : FinFourSourcePreservingSingletonEntrance source}

/-! ## Elementary sequence selection -/

/-- A finite-valued sequence is constant along one strict subsequence. -/
private theorem exists_fixed_strictMono_subsequence
    {Label : Type} [Fintype Label] (label : ℕ → Label) :
    ∃ fixed : Label, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ rank, label (subsequence rank) = fixed := by
  have hfrequent : ∃ fixed : Label, ∃ᶠ rank in atTop,
      label rank = fixed := by
    by_contra hnone
    push Not at hnone
    have hall : ∀ᶠ rank in atTop, ∀ fixed : Label,
        label rank ≠ fixed := by
      rw [eventually_all]
      exact hnone
    obtain ⟨rank, hrank⟩ := hall.exists
    exact hrank (label rank) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hmono, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hmono, hlabel⟩

/-- Priority classification of a nonnegative real sequence.  The first arm
extracts one uniformly positive subsequence.  If no positive threshold occurs
frequently, the original sequence tends to zero.  No converse exclusivity is
asserted for a sequence satisfying the first arm. -/
private theorem positive_subsequence_or_tendsto_zero
    (value : ℕ → ℝ) (hnonneg : ∀ rank, 0 ≤ value rank) :
    (∃ floor : ℝ, 0 < floor ∧ ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ rank, floor ≤ value (subsequence rank)) ∨
      Tendsto value atTop (nhds 0) := by
  by_cases hfrequent : ∃ floor : ℝ, 0 < floor ∧
      ∃ᶠ rank in atTop, floor ≤ value rank
  · obtain ⟨floor, hfloor, hfloorFrequently⟩ := hfrequent
    obtain ⟨subsequence, hsubsequence, hfloorSubsequence⟩ :=
      extraction_of_frequently_atTop hfloorFrequently
    exact Or.inl
      ⟨floor, hfloor, subsequence, hsubsequence, hfloorSubsequence⟩
  · right
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    have hnotFrequently : ¬ ∃ᶠ rank in atTop,
        epsilon ≤ value rank := by
      intro hbad
      exact hfrequent ⟨epsilon, hepsilon, hbad⟩
    rw [not_frequently, eventually_atTop] at hnotFrequently
    obtain ⟨cutoff, hcutoff⟩ := hnotFrequently
    exact ⟨cutoff, fun rank hrank ↦ by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg rank)]
      exact lt_of_not_ge (hcutoff rank hrank)⟩

/-! ## Framewise forced-pair stream -/

/-- Countable framewise choice of the actual paid row and its collision
residual.  Every row remains dependently indexed by the literal parent frame.
-/
structure FinFourSourcePreservingForcedPairStream
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  row : ∀ rank,
    FinFourSourcePreservingForcedPairPacket.ResidualCapstone
      (parent.frame rank)

namespace FinFourSourcePreservingForcedPairStream

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- The finite label stabilized by the completion atlas. -/
abbrev Label := Fin 4 × Fin 4 × Fin 4 × Bool

/-- Singleton owner, forced owner, payer, and payer endpoint action. -/
def label (stream : FinFourSourcePreservingForcedPairStream parent)
    (rank : ℕ) : Label :=
  ((stream.row rank).packet.singletonOwner,
    (stream.row rank).packet.forcedOwner,
    (stream.row rank).packet.payer,
    (stream.row rank).packet.payerAdapter.action)

/-- Every cofinal frame stream admits all forced-pair rows simultaneously. -/
theorem nonempty
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    Nonempty (FinFourSourcePreservingForcedPairStream parent) := by
  let row := fun rank ↦ Classical.choice
    ((parent.frame rank).nonempty_forcedPairResidualCapstone)
  exact ⟨⟨row⟩⟩

end FinFourSourcePreservingForcedPairStream

/-! ## One finite-label-stabilized stream -/

/-- A child of one source stream on which all four discrete row labels are
fixed.  The strict embedding is stored, so every child object remains a
literal parent object. -/
structure FinFourStabilizedForcedPairStream
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  stream : FinFourSourcePreservingForcedPairStream parent
  embedding : ℕ → ℕ
  embedding_strictMono : StrictMono embedding
  fixedLabel : FinFourSourcePreservingForcedPairStream.Label
  label_eq_fixed : ∀ rank, stream.label (embedding rank) = fixedLabel

namespace FinFourStabilizedForcedPairStream

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- The literal selected parent frame. -/
def frame (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    FinFourSourcePreservingSingletonFrame entrance :=
  parent.frame (stream.embedding rank)

/-- The actual paid row and residual at the selected parent index. -/
def row (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    FinFourSourcePreservingForcedPairPacket.ResidualCapstone
      (stream.frame rank) :=
  stream.stream.row (stream.embedding rank)

/-- The fixed singleton owner. -/
def singletonOwner
    (stream : FinFourStabilizedForcedPairStream parent) : Fin 4 :=
  stream.fixedLabel.1

/-- The fixed table-selected forced owner. -/
def forcedOwner
    (stream : FinFourStabilizedForcedPairStream parent) : Fin 4 :=
  stream.fixedLabel.2.1

/-- The fixed positive-defect payer. -/
def payer (stream : FinFourStabilizedForcedPairStream parent) : Fin 4 :=
  stream.fixedLabel.2.2.1

/-- The fixed payer endpoint action. -/
def payerAction
    (stream : FinFourStabilizedForcedPairStream parent) : Bool :=
  stream.fixedLabel.2.2.2

/-- Every selected row has the fixed singleton owner. -/
theorem row_singletonOwner
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    (stream.row rank).packet.singletonOwner = stream.singletonOwner := by
  exact congrArg Prod.fst (stream.label_eq_fixed rank)

/-- Every selected row has the fixed forced owner. -/
theorem row_forcedOwner
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    (stream.row rank).packet.forcedOwner = stream.forcedOwner := by
  exact congrArg (fun label ↦ label.2.1) (stream.label_eq_fixed rank)

/-- Every selected row has the fixed payer. -/
theorem row_payer
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    (stream.row rank).packet.payer = stream.payer := by
  exact congrArg (fun label ↦ label.2.2.1) (stream.label_eq_fixed rank)

/-- Every selected row has the fixed payer action. -/
theorem row_payerAction
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    (stream.row rank).packet.payerAdapter.action = stream.payerAction := by
  exact congrArg (fun label ↦ label.2.2.2) (stream.label_eq_fixed rank)

/-- The exact semantic tail selected by the row's collision residual. -/
def tail (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    QuittingTerminalSemanticPair (Fin 4) :=
  (stream.row rank).collision.cluster

/-- The residual cluster is the same frame's literal post-date tail. -/
theorem tail_eq_framePostDateTail
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    stream.tail rank = quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward
        (stream.frame rank).targetProfile ((stream.frame rank).stage + 1)) :=
  (stream.row rank).cluster_eq_framePostDateTail

/-- The forced-pair target keeps the frame's full post-date behavioral spine. -/
theorem forcedPair_postDateSpine_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (stream.row rank).packet.forcedAdapter.targetProfile
          ((stream.frame rank).stage + 1) =
      quittingAllContinueProfileSpine reward
        (stream.frame rank).referenceProfile
          ((stream.frame rank).stage + 1) :=
  (stream.row rank).packet.forcedPair_postDateSpine_eq_reference

/-- The paid target keeps the frame's full post-date behavioral spine. -/
theorem payerTarget_postDateSpine_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (stream.row rank).packet.payerAdapter.targetProfile
          ((stream.frame rank).stage + 1) =
      quittingAllContinueProfileSpine reward
        (stream.frame rank).referenceProfile
          ((stream.frame rank).stage + 1) :=
  (stream.row rank).packet.payerTarget_postDateSpine_eq_reference

/-- The forced-pair semantic tail is the literal reference semantic tail. -/
theorem forcedPair_postDateTail_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (stream.row rank).packet.forcedAdapter.targetProfile
            ((stream.frame rank).stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (stream.frame rank).referenceProfile
            ((stream.frame rank).stage + 1)) :=
  (stream.row rank).packet.forcedPair_postDateTail_eq_reference

/-- The paid semantic tail is the literal reference semantic tail. -/
theorem payerTarget_postDateTail_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (stream.row rank).packet.payerAdapter.targetProfile
            ((stream.frame rank).stage + 1)) =
      quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (stream.frame rank).referenceProfile
            ((stream.frame rank).stage + 1)) :=
  (stream.row rank).packet.payerTarget_postDateTail_eq_reference

/-- The forced-pair post-date full outcome law is the reference law. -/
theorem forcedPair_postDateLaw_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (stream.row rank).packet.forcedAdapter.targetProfile
            ((stream.frame rank).stage + 1)) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (stream.frame rank).referenceProfile
            ((stream.frame rank).stage + 1)) :=
  (stream.row rank).packet.forcedPair_postDateLaw_eq_reference

/-- The paid post-date full outcome law is the reference law. -/
theorem payerTarget_postDateLaw_eq_reference
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (stream.row rank).packet.payerAdapter.targetProfile
            ((stream.frame rank).stage + 1)) =
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward
          (stream.frame rank).referenceProfile
            ((stream.frame rank).stage + 1)) :=
  (stream.row rank).packet.payerTarget_postDateLaw_eq_reference

/-- The selected tail is an actual point of the semantic carrier. -/
theorem tail_mem
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    stream.tail rank ∈ quittingTerminalSemanticCarrier reward :=
  (stream.row rank).collision.cluster_mem

/-- Nonnegative excess of the actual tail debt over the source minimum. -/
def excess (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) : ℝ :=
  quittingTerminalSemanticDebtSum (stream.tail rank) -
    quittingTerminalSemanticDebtSum source.point.1

/-- Global minimality makes every displayed excess nonnegative. -/
theorem excess_nonneg
    (stream : FinFourStabilizedForcedPairStream parent) (rank : ℕ) :
    0 ≤ stream.excess rank := by
  exact sub_nonneg.mpr (source.minimum (stream.tail rank) (stream.tail_mem rank))

/-- Source ranks remain strictly increasing after label stabilization. -/
theorem sourceRank_strictMono
    (stream : FinFourStabilizedForcedPairStream parent) :
    StrictMono (fun rank ↦ (stream.frame rank).sourceRank) :=
  parent.sourceRank_strictMono.comp stream.embedding_strictMono

/-- Stabilized source ranks remain cofinal. -/
theorem sourceRank_tendsto_atTop
    (stream : FinFourStabilizedForcedPairStream parent) :
    Tendsto (fun rank ↦ (stream.frame rank).sourceRank) atTop atTop :=
  stream.sourceRank_strictMono.tendsto_atTop

/-- The retained suffix semantic pair and full outcome law still converge to
the one fixed source point. -/
theorem suffixLaw_tendsto
    (stream : FinFourStabilizedForcedPairStream parent) :
    Tendsto (fun rank ↦
      (quittingTerminalSemanticPair reward (stream.frame rank).suffixProfile,
        quittingTerminalOutcomeMass reward
          (stream.frame rank).suffixProfile)) atTop (nhds source.point) := by
  exact parent.suffixLaw_tendsto.comp stream.embedding_strictMono.tendsto_atTop

/-- Literal prefixed-source debt still converges to the fixed minimum. -/
theorem referenceDebt_tendsto
    (stream : FinFourStabilizedForcedPairStream parent) :
    Tendsto (fun rank ↦ quittingTerminalDebtSum reward
      (stream.frame rank).referenceProfile) atTop
        (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  exact parent.referenceDebt_tendsto.comp
    stream.embedding_strictMono.tendsto_atTop

/-- Reindex a stabilized stream through a further strict embedding. -/
def reindex (stream : FinFourStabilizedForcedPairStream parent)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence) :
    FinFourStabilizedForcedPairStream parent where
  stream := stream.stream
  embedding := stream.embedding ∘ subsequence
  embedding_strictMono := stream.embedding_strictMono.comp hsubsequence
  fixedLabel := stream.fixedLabel
  label_eq_fixed := fun rank ↦ stream.label_eq_fixed (subsequence rank)

/-- Every parent stream admits a simultaneous finite-label stabilization. -/
theorem nonempty
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    Nonempty (FinFourStabilizedForcedPairStream parent) := by
  obtain ⟨forced⟩ := FinFourSourcePreservingForcedPairStream.nonempty parent
  obtain ⟨fixed, embedding, hembedding, hfixed⟩ :=
    exists_fixed_strictMono_subsequence forced.label
  exact ⟨{
    stream := forced
    embedding := embedding
    embedding_strictMono := hembedding
    fixedLabel := fixed
    label_eq_fixed := hfixed
  }⟩

end FinFourStabilizedForcedPairStream

/-! ## The exact-tail priority modes -/

/-- A source-attached stabilized stream whose literal continuation tails stay
uniformly above the source minimum. -/
structure FinFourUniformEscapePacket
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  stream : FinFourStabilizedForcedPairStream parent
  floor : ℝ
  floor_pos : 0 < floor
  excess_floor : ∀ rank, floor ≤ stream.excess rank

/-- A source-attached stabilized stream whose literal continuation-tail debt
returns to the source minimum.  Strictly off-minimum tails are allowed. -/
structure FinFourMinimumReturnPacket
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  stream : FinFourStabilizedForcedPairStream parent
  excess_tendsto_zero : Tendsto stream.excess atTop (nhds 0)

namespace FinFourUniformEscapePacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- Advertised debt form of the uniform tail-excess floor. -/
theorem tailDebt_floor
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    quittingTerminalSemanticDebtSum source.point.1 + packet.floor ≤
      quittingTerminalSemanticDebtSum (packet.stream.tail rank) := by
  have hfloor := packet.excess_floor rank
  unfold FinFourStabilizedForcedPairStream.excess at hfloor
  linarith

end FinFourUniformEscapePacket

namespace FinFourMinimumReturnPacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- Advertised minimum-return form of the vanishing excess. -/
theorem tailDebt_tendsto_minimum
    (packet : FinFourMinimumReturnPacket parent) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (packet.stream.tail rank)) atTop
        (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  have hadd := packet.excess_tendsto_zero.add_const
    (quittingTerminalSemanticDebtSum source.point.1)
  simpa only [FinFourStabilizedForcedPairStream.excess, sub_add_cancel,
    zero_add] using hadd

end FinFourMinimumReturnPacket

namespace FinFourStabilizedForcedPairStream

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- Exhaustive priority dispatch of one stabilized stream. -/
theorem uniformEscape_or_minimumReturn
    (stream : FinFourStabilizedForcedPairStream parent) :
    Nonempty (FinFourUniformEscapePacket parent) ∨
      Nonempty (FinFourMinimumReturnPacket parent) := by
  rcases positive_subsequence_or_tendsto_zero stream.excess
      stream.excess_nonneg with hescape | hreturn
  · obtain ⟨floor, hfloor, subsequence, hsubsequence, hexcess⟩ := hescape
    let child := stream.reindex subsequence hsubsequence
    let packet : FinFourUniformEscapePacket parent := {
      stream := child
      floor := floor
      floor_pos := hfloor
      excess_floor := by
        intro rank
        exact hexcess rank
    }
    exact Or.inl ⟨packet⟩
  · exact Or.inr ⟨⟨stream, hreturn⟩⟩

end FinFourStabilizedForcedPairStream

namespace FinFourSourcePreservingCofinalSingletonPacket

/-- Every source-preserving cofinal singleton packet reaches one exact-tail
terminal completion mode. -/
theorem nonempty_uniformEscape_or_minimumReturn
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) :
    Nonempty (FinFourUniformEscapePacket parent) ∨
      Nonempty (FinFourMinimumReturnPacket parent) := by
  obtain ⟨stream⟩ := FinFourStabilizedForcedPairStream.nonempty parent
  exact stream.uniformEscape_or_minimumReturn

end FinFourSourcePreservingCofinalSingletonPacket

/-! ## Literal self-shifts -/

private def completionTailEmbedding (rank : ℕ) : ℕ := rank + 1

private theorem completionTailEmbedding_strictMono :
    StrictMono completionTailEmbedding := by
  intro first second hlt
  exact Nat.add_lt_add_right hlt 1

namespace FinFourUniformEscapePacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- Delete the first retained row, changing no source object or fixed label. -/
def drop (packet : FinFourUniformEscapePacket parent) :
    FinFourUniformEscapePacket parent where
  stream := packet.stream.reindex completionTailEmbedding
    completionTailEmbedding_strictMono
  floor := packet.floor
  floor_pos := packet.floor_pos
  excess_floor := fun rank ↦ packet.excess_floor (rank + 1)

/-- Row `rank` of `drop` is literally row `rank + 1` of its parent packet. -/
theorem drop_row (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    packet.drop.stream.row rank = packet.stream.row (rank + 1) := rfl

/-- The dropped frame is literally the next parent frame. -/
theorem drop_frame (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    packet.drop.stream.frame rank = packet.stream.frame (rank + 1) := rfl

/-- Dropping changes no stabilized label. -/
theorem drop_fixedLabel (packet : FinFourUniformEscapePacket parent) :
    packet.drop.stream.fixedLabel = packet.stream.fixedLabel := rfl

/-- The deterministic iterated self-shift. -/
def iterateDrop (packet : FinFourUniformEscapePacket parent) :
    ℕ → FinFourUniformEscapePacket parent
  | 0 => packet
  | rank + 1 => (iterateDrop packet rank).drop

/-- The iterated self-shift starts at the supplied packet. -/
theorem iterateDrop_zero (packet : FinFourUniformEscapePacket parent) :
    packet.iterateDrop 0 = packet := rfl

/-- Every later packet is the literal drop of its predecessor. -/
theorem iterateDrop_succ
    (packet : FinFourUniformEscapePacket parent) (rank : ℕ) :
    packet.iterateDrop (rank + 1) = (packet.iterateDrop rank).drop := rfl

end FinFourUniformEscapePacket

namespace FinFourMinimumReturnPacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- Delete the first retained row, preserving the minimum-return limit. -/
def drop (packet : FinFourMinimumReturnPacket parent) :
    FinFourMinimumReturnPacket parent where
  stream := packet.stream.reindex completionTailEmbedding
    completionTailEmbedding_strictMono
  excess_tendsto_zero := by
    exact packet.excess_tendsto_zero.comp
      completionTailEmbedding_strictMono.tendsto_atTop

/-- Row `rank` of `drop` is literally row `rank + 1` of its parent packet. -/
theorem drop_row (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.drop.stream.row rank = packet.stream.row (rank + 1) := rfl

/-- The dropped frame is literally the next parent frame. -/
theorem drop_frame (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.drop.stream.frame rank = packet.stream.frame (rank + 1) := rfl

/-- Dropping changes no stabilized label. -/
theorem drop_fixedLabel (packet : FinFourMinimumReturnPacket parent) :
    packet.drop.stream.fixedLabel = packet.stream.fixedLabel := rfl

/-- The deterministic iterated self-shift. -/
def iterateDrop (packet : FinFourMinimumReturnPacket parent) :
    ℕ → FinFourMinimumReturnPacket parent
  | 0 => packet
  | rank + 1 => (iterateDrop packet rank).drop

/-- The iterated self-shift starts at the supplied packet. -/
theorem iterateDrop_zero (packet : FinFourMinimumReturnPacket parent) :
    packet.iterateDrop 0 = packet := rfl

/-- Every later packet is the literal drop of its predecessor. -/
theorem iterateDrop_succ
    (packet : FinFourMinimumReturnPacket parent) (rank : ℕ) :
    packet.iterateDrop (rank + 1) = (packet.iterateDrop rank).drop := rfl

end FinFourMinimumReturnPacket

/-! ## Literal terminal-mode trajectories -/

/-- A literal infinite uniform-escape self-shift trajectory. -/
structure FinFourUniformEscapeTrajectory
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  initial : FinFourUniformEscapePacket parent
  packet : ℕ → FinFourUniformEscapePacket parent
  packet_zero : packet 0 = initial
  packet_succ : ∀ rank, packet (rank + 1) = (packet rank).drop

/-- A literal infinite minimum-return self-shift trajectory. -/
structure FinFourMinimumReturnTrajectory
    (parent : FinFourSourcePreservingCofinalSingletonPacket entrance) where
  initial : FinFourMinimumReturnPacket parent
  packet : ℕ → FinFourMinimumReturnPacket parent
  packet_zero : packet 0 = initial
  packet_succ : ∀ rank, packet (rank + 1) = (packet rank).drop

namespace FinFourUniformEscapePacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- The canonical literal trajectory generated by repeated `drop`. -/
def trajectory (packet : FinFourUniformEscapePacket parent) :
    FinFourUniformEscapeTrajectory parent where
  initial := packet
  packet := packet.iterateDrop
  packet_zero := packet.iterateDrop_zero
  packet_succ := packet.iterateDrop_succ

end FinFourUniformEscapePacket

namespace FinFourMinimumReturnPacket

variable {parent : FinFourSourcePreservingCofinalSingletonPacket entrance}

/-- The canonical literal trajectory generated by repeated `drop`. -/
def trajectory (packet : FinFourMinimumReturnPacket parent) :
    FinFourMinimumReturnTrajectory parent where
  initial := packet
  packet := packet.iterateDrop
  packet_zero := packet.iterateDrop_zero
  packet_succ := packet.iterateDrop_succ

end FinFourMinimumReturnPacket

/-! ## Declared completion graph -/

/-- The three regular modes of the source-preserving atlas. -/
inductive FinFourCompletionMode
  | cofinalSingleton
  | uniformEscape
  | minimumReturn
  deriving DecidableEq, Fintype

namespace FinFourCompletionMode

/-- The exact regular-edge table of the declared atlas. -/
def RegularEdge : FinFourCompletionMode → FinFourCompletionMode → Prop
  | .cofinalSingleton, .uniformEscape => True
  | .cofinalSingleton, .minimumReturn => True
  | .uniformEscape, .uniformEscape => True
  | .minimumReturn, .minimumReturn => True
  | _, _ => False

/-- The atlas has no rank-exit transition. -/
def RankExit (_source _target : FinFourCompletionMode) : Prop := False

/-- Explicit reachability table used to audit the graph closure. -/
def ExplicitReachable : FinFourCompletionMode → FinFourCompletionMode → Prop
  | .cofinalSingleton, _ => True
  | .uniformEscape, .uniformEscape => True
  | .minimumReturn, .minimumReturn => True
  | _, _ => False

/-- Actual reflexive--transitive reachability of the declared regular edge. -/
def Reachable : FinFourCompletionMode → FinFourCompletionMode → Prop :=
  Relation.ReflTransGen RegularEdge

/-- The displayed truth table is exactly the reflexive--transitive closure of
the regular-edge relation. -/
theorem reachable_iff_explicit
    (first second : FinFourCompletionMode) :
    Reachable first second ↔ ExplicitReachable first second := by
  constructor
  · intro hreach
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        cases second <;> simp [ExplicitReachable]
    | @head first middle hedge _ ih =>
        cases first <;> cases middle <;> cases second <;>
          simp [RegularEdge, ExplicitReachable] at hedge ih ⊢
  · intro hexplicit
    cases first <;> cases second
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (by simp [RegularEdge])
    · exact Relation.ReflTransGen.single (by simp [RegularEdge])
    · simp [ExplicitReachable] at hexplicit
    · exact Relation.ReflTransGen.refl
    · simp [ExplicitReachable] at hexplicit
    · simp [ExplicitReachable] at hexplicit
    · simp [ExplicitReachable] at hexplicit
    · exact Relation.ReflTransGen.refl

/-- Mutual reachability is the declared SCC equivalence. -/
def SameComponent (first second : FinFourCompletionMode) : Prop :=
  Reachable first second ∧ Reachable second first

/-- Every strongly connected component is a singleton. -/
theorem sameComponent_iff_eq (first second : FinFourCompletionMode) :
    SameComponent first second ↔ first = second := by
  rw [SameComponent, reachable_iff_explicit, reachable_iff_explicit]
  cases first <;> cases second <;> simp [ExplicitReachable]

/-- A mode is terminal when every one-step target can return to it. -/
def IsTerminal (mode : FinFourCompletionMode) : Prop :=
  ∀ target, RegularEdge mode target → Reachable target mode

/-- The two exact-tail modes, and only those modes, are terminal SCCs. -/
theorem isTerminal_iff (mode : FinFourCompletionMode) :
    IsTerminal mode ↔ mode = .uniformEscape ∨ mode = .minimumReturn := by
  cases mode with
  | cofinalSingleton =>
      constructor
      · intro hterminal
        have hreturn := hterminal .uniformEscape (by simp [RegularEdge])
        rw [reachable_iff_explicit] at hreturn
        simp [ExplicitReachable] at hreturn
      · simp
  | uniformEscape =>
      constructor
      · exact fun _ ↦ Or.inl rfl
      · intro _ target hedge
        cases target <;> simp [RegularEdge] at hedge
        exact Relation.ReflTransGen.refl
  | minimumReturn =>
      constructor
      · exact fun _ ↦ Or.inr rfl
      · intro _ target hedge
        cases target <;> simp [RegularEdge] at hedge
        exact Relation.ReflTransGen.refl

/-- Literal enumeration of all nine possible regular mode pairs. -/
theorem regularEdge_iff (first second : FinFourCompletionMode) :
    RegularEdge first second ↔
      (first = .cofinalSingleton ∧ second = .uniformEscape) ∨
      (first = .cofinalSingleton ∧ second = .minimumReturn) ∨
      (first = .uniformEscape ∧ second = .uniformEscape) ∨
      (first = .minimumReturn ∧ second = .minimumReturn) := by
  cases first <;> cases second <;> simp [RegularEdge]

end FinFourCompletionMode

/-! ## Reward-level coverage and realizability -/

/-- The actual terminal predicate of the completion atlas. -/
def FinFourCompletionTerminal
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop :=
  ∃ payoff : Payoff (Fin 4),
    (quittingGame reward).IsUniformEquilibriumPayoff none payoff

/-- The source-preserving branch outcome, dependently indexed by the exact
monodromy-free residual from which its parent stream was constructed. -/
inductive FinFourSourcePreservingCompletionOutcome
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {bound : ℝ}
    (residual : FinFourProducerResidualWithoutMonodromy reward bound) : Type
  | uniformEscape
      {source : FinFourMinimumAtomProducer reward bound}
      {entrance : FinFourSourcePreservingSingletonEntrance source}
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance)
      (residual_eq : parent.residual = residual)
      (packet : FinFourUniformEscapePacket parent)
  | minimumReturn
      {source : FinFourMinimumAtomProducer reward bound}
      {entrance : FinFourSourcePreservingSingletonEntrance source}
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance)
      (residual_eq : parent.residual = residual)
      (packet : FinFourMinimumReturnPacket parent)

/-- The strongest reward-level coverage theorem: its second arm retains the
literal entrance residual as a dependent index. -/
theorem uniformPayoff_or_sourcePreservingCompletionOutcome
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    FinFourCompletionTerminal reward ∨
      ∃ residual : FinFourProducerResidualWithoutMonodromy reward bound,
        Nonempty (FinFourSourcePreservingCompletionOutcome residual) := by
  rcases uniformPayoff_or_exists_sourcePreservingCofinalSingletonPacket
      reward hreward with hterminal | hpacket
  · exact Or.inl hterminal
  · obtain ⟨residual, source, entrance, parent, hresidual⟩ := hpacket
    rcases parent.nonempty_uniformEscape_or_minimumReturn with
        hescape | hreturn
    · obtain ⟨packet⟩ := hescape
      exact Or.inr ⟨residual,
        ⟨FinFourSourcePreservingCompletionOutcome.uniformEscape
          parent hresidual packet⟩⟩
    · obtain ⟨packet⟩ := hreturn
      exact Or.inr ⟨residual,
        ⟨FinFourSourcePreservingCompletionOutcome.minimumReturn
          parent hresidual packet⟩⟩

/-- Existence of one source-attached uniform-escape trajectory, retaining its
exact entrance residual and every literal self-shift. -/
def FinFourUniformEscapeRealizable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop :=
  ∃ (bound : ℝ)
      (residual : FinFourProducerResidualWithoutMonodromy reward bound)
      (source : FinFourMinimumAtomProducer reward bound)
      (entrance : FinFourSourcePreservingSingletonEntrance source)
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance),
    parent.residual = residual ∧
      Nonempty (FinFourUniformEscapeTrajectory parent)

/-- Existence of one source-attached minimum-return trajectory, retaining its
exact entrance residual and every literal self-shift. -/
def FinFourMinimumReturnRealizable
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) : Prop :=
  ∃ (bound : ℝ)
      (residual : FinFourProducerResidualWithoutMonodromy reward bound)
      (source : FinFourMinimumAtomProducer reward bound)
      (entrance : FinFourSourcePreservingSingletonEntrance source)
      (parent : FinFourSourcePreservingCofinalSingletonPacket entrance),
    parent.residual = residual ∧
      Nonempty (FinFourMinimumReturnTrajectory parent)

/-- Bounded Fin4 rewards either already admit a uniform-equilibrium payoff or
enter one of the two exact-tail terminal components on the same source and
entrance produced by the monodromy-free atlas. -/
theorem uniformPayoff_or_sourcePreservingUniformEscape_or_minimumReturn
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    FinFourCompletionTerminal reward ∨
      FinFourUniformEscapeRealizable reward ∨
        FinFourMinimumReturnRealizable reward := by
  rcases uniformPayoff_or_sourcePreservingCompletionOutcome reward hreward with
      hterminal | houtcome
  · exact Or.inl hterminal
  · obtain ⟨residual, ⟨outcome⟩⟩ := houtcome
    cases outcome with
    | @uniformEscape source entrance parent hresidual packet =>
        exact Or.inr (Or.inl ⟨bound, residual, source, entrance, parent,
          hresidual, ⟨packet.trajectory⟩⟩)
    | @minimumReturn source entrance parent hresidual packet =>
        exact Or.inr (Or.inr ⟨bound, residual, source, entrance, parent,
          hresidual, ⟨packet.trajectory⟩⟩)

/-- Counterexample-facing form: without a terminal payoff, the same exhaustive
construction reaches one of the two structural capstones. -/
theorem sourcePreservingUniformEscape_or_minimumReturn_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hno : ¬ FinFourCompletionTerminal reward) :
    FinFourUniformEscapeRealizable reward ∨
      FinFourMinimumReturnRealizable reward := by
  exact (uniformPayoff_or_sourcePreservingUniformEscape_or_minimumReturn
    reward hreward).resolve_left hno

/-- The still-open semantic consumer for the uniform-escape terminal mode. -/
def FinFourUniformEscapeCapstone : Prop :=
  ∀ (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)),
    FinFourUniformEscapeRealizable reward → FinFourCompletionTerminal reward

/-- The still-open semantic consumer for the minimum-return terminal mode. -/
def FinFourMinimumReturnCapstone : Prop :=
  ∀ (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)),
    FinFourMinimumReturnRealizable reward → FinFourCompletionTerminal reward

/-- If both explicitly open capstones are supplied, the bounded Fin4 theorem
follows.  This is conditional and does not prove either premise. -/
theorem finFourCompletion_of_capstones
    (hescape : FinFourUniformEscapeCapstone)
    (hreturn : FinFourMinimumReturnCapstone)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound) :
    FinFourCompletionTerminal reward := by
  rcases uniformPayoff_or_sourcePreservingUniformEscape_or_minimumReturn
      reward hreward with hterminal | hescapeOrReturn
  · exact hterminal
  · rcases hescapeOrReturn with hpacket | hpacket
    · exact hescape reward hpacket
    · exact hreturn reward hpacket

end GameTheory
