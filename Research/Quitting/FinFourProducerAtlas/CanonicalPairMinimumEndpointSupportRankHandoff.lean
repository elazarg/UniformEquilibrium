/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FinFourProducerAtlas.MaximalPrefixRayDichotomy
import Research.Quitting.StoppingLawMinimumEndpointSupportRankHandoff
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticReachedRowDebtLocalization

/-!
# Canonical Fin4 pair endpoint support-rank handoff

The minimum-return arm of one source-attached canonical pair ray has a literal
best-endpoint profile at every depth.  The source and endpoint profiles differ
only in the fixed payer's complete strategy.  Their source mover debt is the
copied endpoint gain and the endpoint kills that debt exactly.

Joint compactification therefore delegates to the generic half-mixture
support theorem.  A minimum endpoint moves once from the new half parent into
the generic tangent-family lane; an off-minimum endpoint is retained as the
literal debt-ascent alternative.  No renewable canonical-pair recursion is
asserted.
-/

noncomputable section

namespace GameTheory

open Filter Set
open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

private theorem literalRootStackProfile_opponent_eq
    (roots : List (Fin 4 → PMF Bool))
    (first second : (quittingGame reward).BehaviorProfile)
    (other : Fin 4) (hother : first other = second other) :
    quittingLiteralRootStackProfile reward roots first other =
      quittingLiteralRootStackProfile reward roots second other := by
  induction roots with
  | nil => simpa using hother
  | cons root roots ih =>
      simp only [quittingLiteralRootStackProfile_cons]
      funext time history
      cases time with
      | zero => rfl
      | succ time =>
          change quittingLiteralRootStackProfile reward roots first other time
              (Fin.tail history.1, history.2) =
            quittingLiteralRootStackProfile reward roots second other time
              (Fin.tail history.1, history.2)
          rw [ih]

/-- Copying the explicit common maximal-prefix word preserves every opponent
strategy of the payer endpoint literally. -/
theorem rayPaidTargetProfile_opponent_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) (other : Fin 4)
    (hother : other ≠ packet.payer) :
    packet.rayPaidTargetProfile index other =
      packet.rayFamily.rayProfiles index other := by
  unfold rayPaidTargetProfile QuittingCommonSemanticMarkedBaseFamily.rayProfiles
    rayFamily quittingMaximalCapSemanticPrefixProfile
  exact literalRootStackProfile_opponent_eq _ _ _ other
    ((packet.rayPaidAdapter index).targetProfile_opponent_eq other hother)

/-- Replacing the payer strategy in the source ray profile by the literal
endpoint strategy gives exactly the stored endpoint profile. -/
theorem update_rayProfile_payer_eq_rayPaidTargetProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    Function.update (packet.rayFamily.rayProfiles index) packet.payer
        (packet.rayPaidTargetProfile index packet.payer) =
      packet.rayPaidTargetProfile index :=
  update_source_with_target_mover_eq_target reward _ _ packet.payer
    (packet.rayPaidTargetProfile_opponent_eq index)

private theorem exists_rayTerminal_member_ne_payer
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    ∃ other ∈ packet.rayTerminal.val, other ≠ packet.payer := by
  apply Finset.exists_mem_ne
  rw [rayTerminal, packet.movingTerminal_card]
  norm_num

/-- Pure-pair screening identifies the conditional best-endpoint gain with
the payer's full unrestricted semantic debt at the ray source. -/
theorem raySource_payerDebt_eq_rayPaidBaseGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebt packet.raySource packet.payer =
      packet.rayPaidBaseGain index := by
  obtain ⟨other, hotherMem, hotherNe⟩ :=
    packet.exists_rayTerminal_member_ne_payer
  have hsure : quittingPureSetRoot packet.rayTerminal.val other =
      PMF.pure true := by
    simp [quittingPureSetRoot, quittingSetAction, hotherMem]
  have hlocalized :=
    quittingTerminalSemanticDebt_prefix_eq_coordinateNashDefect_of_other_sureQuitter
      reward (quittingTerminalSemanticPair reward (packet.rayTail index))
        (quittingPureSetRoot packet.rayTerminal.val) other packet.payer
        hotherNe.symm hsure
  rw [← packet.rayBaseProfile_semantic_eq index, rayBaseProfile,
    quittingTerminalSemanticPair_rootThenContinuation]
  rw [packet.rayPaidBaseGain_eq_defect,
    packet.rayPaidAdapter_sourceTail_eq_reference,
    packet.rayPaidAdapter_sourceRoot_eq]
  exact hlocalized

theorem raySource_payerDebt_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    0 < quittingTerminalSemanticDebt packet.raySource packet.payer := by
  rw [packet.raySource_payerDebt_eq_rayPaidBaseGain 0]
  exact (div_pos source.minimumDebt_pos (by norm_num)).trans_le
    (packet.rayPaidBaseGain_floor 0)

/-- Along the common exact-prefix word, the source payer's whole debt is
exactly the copied literal endpoint gain. -/
theorem rayProfile_payerDebt_eq_rayPaidGain
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles index)) packet.payer =
      packet.rayPaidGain index := by
  rw [packet.rayFamily.rayProfiles_semantic_eq,
    quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq,
    packet.rayPaidGain_eq_survival_mul,
    ← packet.raySource_payerDebt_eq_rayPaidBaseGain index]

/-- The copied best endpoint kills the payer's unrestricted whole-profile
debt, not only its marked root defect. -/
theorem rayPaidTargetProfile_payerDebt_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayPaidTargetProfile index)) packet.payer = 0 := by
  have hdebt := quittingTerminalSemanticDebt_update_self_eq_sub_payoffGain
    reward (packet.rayFamily.rayProfiles index) packet.payer
      (packet.rayPaidTargetProfile index packet.payer)
  rw [packet.update_rayProfile_payer_eq_rayPaidTargetProfile index] at hdebt
  rw [packet.rayProfile_payerDebt_eq_rayPaidGain index] at hdebt
  dsimp only [rayPaidGain] at hdebt
  linarith

/-- The copied common word reaches the literal endpoint root at its original
shifted date. -/
theorem rayPaidTargetProfile_markedRoot_eq
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingProfileLiveRoot reward (packet.rayPaidTargetProfile index) index =
      quittingProfileLiveRoot reward
        (packet.rayPaidAdapter index).targetProfile 0 := by
  calc
    quittingProfileLiveRoot reward (packet.rayPaidTargetProfile index) index =
        quittingProfileLiveRoot reward
          (quittingAllContinueProfileSpine reward
            (packet.rayPaidTargetProfile index) index) 0 := by
      simpa using (quittingProfileLiveRoot_allContinueSpine reward
        (packet.rayPaidTargetProfile index) index 0).symm
    _ = _ := by
      rw [rayPaidTargetProfile,
        quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile]

/-- The endpoint's complete post-mark behavioral tail is literally the
originating reference profile.  The copied outer word has length `index`, and
the best-endpoint override changes only the following date. -/
theorem rayPaidTargetProfile_postMarkSpine_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.rayPaidTargetProfile index) (index + 1) =
      packet.rayTail index := by
  rw [quittingAllContinueProfileSpine_add, rayPaidTargetProfile,
    quittingAllContinueProfileSpine_maximalCapSemanticPrefixProfile]
  calc
    quittingAllContinueProfileSpine reward
        (packet.rayPaidAdapter index).targetProfile 1 =
        quittingAllContinueProfileSpine reward
          (packet.rayBaseProfile index) 1 := by
      funext player time history
      simp only [quittingAllContinueProfileSpine]
      unfold quittingProfileAllContinueContinuation StochasticGame.shiftProfile
      exact congrFun
        ((packet.rayPaidAdapter index).targetProfile_at_of_ne
          (time + 1) (by omega) player)
        ((quittingGame reward).consHist
          (none, quittingAllContinueAction) history)
    _ = packet.rayTail index :=
      packet.rayBaseProfile_postMarkSpine_eq_tail index

/-- Semantic projection of the literal post-mark behavioral-tail identity. -/
theorem rayPaidTargetProfile_postMarkSemantic_eq_reference
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (packet.rayPaidTargetProfile index) (index + 1)) =
      quittingTerminalSemanticPair reward (packet.rayTail index) := by
  rw [packet.rayPaidTargetProfile_postMarkSpine_eq_reference]

/-- At every ray depth, the normalized payer defect of the literal copied
endpoint is pointwise zero for every normalization scale. -/
theorem rayPaidTargetProfile_normalizedMarkedPayerDefect_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) (scale : ℕ → ℝ) :
    (quittingLiveMass reward (packet.rayPaidTargetProfile index) index *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward
              (packet.rayPaidTargetProfile index) (index + 1))).1
          (quittingProfileLiveRoot reward
            (packet.rayPaidTargetProfile index) index) packet.payer) /
      scale index = 0 := by
  have hzero := (packet.rayPaidAdapter index).ownerMarkedDefect_eq_zero
  rw [(packet.rayPaidAdapter index).targetTail_eq_sourceTail,
    packet.rayPaidAdapter_sourceTail_eq_reference] at hzero
  rw [packet.rayPaidTargetProfile_postMarkSemantic_eq_reference,
    packet.rayPaidTargetProfile_markedRoot_eq,
    hzero, mul_zero, zero_div]

/-- Cutoff immediately after the copied marked row of each endpoint profile. -/
def canonicalEndpointCutoff
    (_packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℕ → ℕ := fun index ↦ index + 1

/-- Canonical vanishing normalization for the actual endpoint sequence. -/
def canonicalEndpointScale
    (_packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) : ℕ → ℝ := fun index ↦ 1 / ((index : ℝ) + 1)

theorem canonicalEndpointScale_pos
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    0 < packet.canonicalEndpointScale index := by
  simp only [canonicalEndpointScale]
  positivity

theorem canonicalEndpointScale_tendsto_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Tendsto packet.canonicalEndpointScale atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private theorem exists_fixed_bool_strictMono_subsequence (label : ℕ → Bool) :
    ∃ fixed : Bool, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧ ∀ index, label (subsequence index) = fixed := by
  have hfrequent : ∃ fixed : Bool, ∃ᶠ index in atTop,
      label index = fixed := by
    by_contra hnot
    push Not at hnot
    have hall : ∀ᶠ index in atTop, ∀ fixed : Bool,
        label index ≠ fixed := by
      rw [eventually_all]
      exact hnot
    obtain ⟨index, hindex⟩ := hall.exists
    exact hindex (label index) rfl
  obtain ⟨fixed, hfixed⟩ := hfrequent
  obtain ⟨subsequence, hsubsequence, hlabel⟩ :=
    extraction_of_frequently_atTop hfixed
  exact ⟨fixed, subsequence, hsubsequence, hlabel⟩

/-- The actual varying endpoint profiles form a recurrent concentrated packet
after freezing their finite routed label.  This wrapper retains the original
ray, action, routed coalition, and subsequence. -/
structure CanonicalPairEndpointConcentratedPacket
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  action : Bool
  terminal : {S : Finset (Fin 4) // S.Nonempty}
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  action_eq : ∀ rank,
    (packet.rayPaidAdapter (subsequence rank)).action = action
  terminal_eq : ∀ rank,
    (packet.rayPaidAdapter (subsequence rank)).routedTerminal = terminal
  concentrated : QuittingReprojectionConcentratedPacket reward
    packet.rayPaidTargetProfile packet.payer terminal
      packet.canonicalEndpointCutoff packet.canonicalEndpointScale
  concentrated_subseq_eq_subsequence : concentrated.subseq = subsequence
  concentrated_mark_eq_subsequence : concentrated.mark = subsequence
  concentrated_resolution_eq_rayResolution_sq :
    concentrated.resolution = packet.rayResolution ^ 2

namespace CanonicalPairEndpointConcentratedPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The selected endpoint retains the complete post-mark behavioral reference
profile at every rank of its stored subsequence. -/
theorem postMarkSpine_eq_reference
    (endpoint : CanonicalPairEndpointConcentratedPacket packet)
    (rank : ℕ) :
    quittingAllContinueProfileSpine reward
        (packet.rayPaidTargetProfile (endpoint.subsequence rank))
        (endpoint.subsequence rank + 1) =
      packet.rayTail (endpoint.subsequence rank) :=
  packet.rayPaidTargetProfile_postMarkSpine_eq_reference
    (endpoint.subsequence rank)

/-- The normalized payer defect written in the exact indexing fields of the
stored concentrated packet. -/
def normalizedMarkedPayerDefect
    (endpoint : CanonicalPairEndpointConcentratedPacket packet)
    (rank : ℕ) : ℝ :=
  (quittingLiveMass reward
        (packet.rayPaidTargetProfile (endpoint.concentrated.subseq rank))
        (endpoint.concentrated.mark rank) *
      quittingRootCoordinateNashDefect reward
        (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward
            (packet.rayPaidTargetProfile
              (endpoint.concentrated.subseq rank))
            (endpoint.concentrated.mark rank + 1))).1
        (quittingProfileLiveRoot reward
          (packet.rayPaidTargetProfile (endpoint.concentrated.subseq rank))
          (endpoint.concentrated.mark rank)) packet.payer) /
    packet.canonicalEndpointScale (endpoint.concentrated.subseq rank)

/-- Exact endpoint purification makes the stored packet's normalized payer
defect zero at every rank, not merely convergent to zero. -/
theorem normalizedMarkedPayerDefect_eq_zero
    (endpoint : CanonicalPairEndpointConcentratedPacket packet)
    (rank : ℕ) :
    endpoint.normalizedMarkedPayerDefect rank = 0 := by
  rw [normalizedMarkedPayerDefect,
    endpoint.concentrated_subseq_eq_subsequence,
    endpoint.concentrated_mark_eq_subsequence]
  exact packet.rayPaidTargetProfile_normalizedMarkedPayerDefect_eq_zero
    (endpoint.subsequence rank) packet.canonicalEndpointScale

/-- Expanded form of the exact concentrated resolution `D_* / D_0` squared. -/
theorem concentrated_resolution_eq_minimumDebt_div_sourceDebt_sq
    (endpoint : CanonicalPairEndpointConcentratedPacket packet) :
    endpoint.concentrated.resolution =
      (quittingTerminalSemanticDebtSum source.point.1 /
        quittingTerminalSemanticDebtSum packet.raySource) ^ 2 := by
  rw [endpoint.concentrated_resolution_eq_rayResolution_sq]
  simp only [rayResolution]

end CanonicalPairEndpointConcentratedPacket

/-- The endpoint concentrated packet can be frozen on a further subsequence of
any supplied strict base subsequence.  The returned equality records the
refinement literally, so compactification consumers need not reselect an
unrelated endpoint sequence. -/
theorem exists_canonicalPairEndpointConcentratedPacket_refining
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (base : ℕ → ℕ) (hbase : StrictMono base) :
    ∃ endpoint : CanonicalPairEndpointConcentratedPacket packet,
      ∃ refinement : ℕ → ℕ, StrictMono refinement ∧
        endpoint.subsequence = base ∘ refinement := by
  obtain ⟨fixed, selected, hselected, haction⟩ :=
    exists_fixed_bool_strictMono_subsequence fun index ↦
      (packet.rayPaidAdapter (base index)).action
  let subsequence := base ∘ selected
  have hsubsequence : StrictMono subsequence := hbase.comp hselected
  let terminal := (packet.rayPaidAdapter (subsequence 0)).routedTerminal
  have hterminal : ∀ rank,
      (packet.rayPaidAdapter (subsequence rank)).routedTerminal = terminal := by
    intro rank
    change (packet.rayPaidAdapter (subsequence rank)).routedTerminal =
      (packet.rayPaidAdapter (subsequence 0)).routedTerminal
    apply Subtype.ext
    change (packet.rayPaidAdapter (subsequence rank)).routedCoalition =
      (packet.rayPaidAdapter (subsequence 0)).routedCoalition
    unfold QuittingStageAtomConcentratedPacketAdapter.routedCoalition
    change quittingPureEndpointRoutedCoalition packet.rayTerminal.val
        packet.payer (packet.rayPaidAdapter (base (selected rank))).action =
      quittingPureEndpointRoutedCoalition packet.rayTerminal.val packet.payer
        (packet.rayPaidAdapter (base (selected 0))).action
    rw [haction rank, haction 0]
  have hstageMass : ∀ rank, packet.rayResolution ^ 2 ≤
      quittingStageCoalitionMass reward
        (packet.rayPaidTargetProfile (subsequence rank)) (subsequence rank)
          terminal := by
    intro rank
    let index := subsequence rank
    rw [← hterminal rank]
    change packet.rayResolution ^ 2 ≤ quittingStageCoalitionMass reward
      (quittingMaximalCapSemanticPrefixProfile reward packet.raySource
        (packet.rayPaidAdapter index).targetProfile index) index
      (packet.rayPaidAdapter index).routedTerminal
    have hmass :=
      quittingStageCoalitionMass_maximalCapSemanticPrefixProfile_add reward
        packet.raySource (packet.rayPaidAdapter index).targetProfile index 0
          (packet.rayPaidAdapter index).routedTerminal
    simp only [Nat.add_zero] at hmass
    rw [hmass]
    have hsurvival :=
      minimumDebt_div_sourceDebt_le_maximalCapSemanticPrefixSurvival reward
        source.point.1 packet.raySource source.minimum source.minimumDebt_pos
          packet.raySource_mem index
    have hbase := (packet.rayPaidAdapter index).resolution_le_targetStageMass
    have hsurvival' : packet.rayResolution ≤
        quittingMaximalCapSemanticPrefixSurvival reward packet.raySource index :=
      hsurvival
    simpa only [pow_two] using
      (mul_le_mul hsurvival' hbase packet.rayResolution_pos.le
        (quittingMaximalCapSemanticPrefixSurvival_nonneg reward
          packet.raySource index))
  let concentrated : QuittingReprojectionConcentratedPacket reward
      packet.rayPaidTargetProfile packet.payer terminal
        packet.canonicalEndpointCutoff packet.canonicalEndpointScale := {
    resolution := packet.rayResolution ^ 2
    resolution_pos := sq_pos_of_pos packet.rayResolution_pos
    subseq := subsequence
    subseq_strictMono := hsubsequence
    mark := subsequence
    mark_lt := by
      intro rank
      simp [canonicalEndpointCutoff]
    stageMass := hstageMass
    semanticPrefix := by
      intro rank
      exact positive_stageCoalitionMass_has_semanticPrefixIncidence reward
        (packet.rayPaidTargetProfile (subsequence rank)) (subsequence rank)
          terminal ((sq_pos_of_pos packet.rayResolution_pos).trans_le
            (hstageMass rank))
    defect_tendsto := by
      have hzero : (fun rank ↦
          (quittingLiveMass reward
              (packet.rayPaidTargetProfile (subsequence rank))
                (subsequence rank) *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward
                  (packet.rayPaidTargetProfile (subsequence rank))
                  (subsequence rank + 1))).1
              (quittingProfileLiveRoot reward
                (packet.rayPaidTargetProfile (subsequence rank))
                (subsequence rank)) packet.payer) /
            packet.canonicalEndpointScale (subsequence rank)) = fun _ ↦ 0 := by
        funext rank
        exact packet.rayPaidTargetProfile_normalizedMarkedPayerDefect_eq_zero
          (subsequence rank) packet.canonicalEndpointScale
      rw [hzero]
      exact tendsto_const_nhds
  }
  exact ⟨{
    action := fixed
    terminal := terminal
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    action_eq := haction
    terminal_eq := hterminal
    concentrated := concentrated
    concentrated_subseq_eq_subsequence := rfl
    concentrated_mark_eq_subsequence := rfl
    concentrated_resolution_eq_rayResolution_sq := rfl
  }, selected, hselected, rfl⟩

/-- The endpoint concentrated packet is produced from the source ray itself;
no recurrence or leaf certificate is supplied. -/
theorem nonempty_canonicalPairEndpointConcentratedPacket
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (CanonicalPairEndpointConcentratedPacket packet) := by
  obtain ⟨endpoint, _⟩ :=
    packet.exists_canonicalPairEndpointConcentratedPacket_refining id
      strictMono_id
  exact ⟨endpoint⟩

/-- Source-attached result of the endpoint-minimum arm.  The entire incoming
ray packet is retained, while the generic handoff records the fresh half
parent and its re-extracted endpoint family. -/
structure CanonicalPairMinimumEndpointSupportRankHandoff
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  rayReturn : MaximalPrefixRayMinimumReturn packet
  endpointPacket : CanonicalPairEndpointConcentratedPacket packet
  supportHandoff : QuittingMinimumEndpointSupportRankHandoff reward
    source.point.1 packet.rayFamily.rayProfiles packet.rayPaidTargetProfile
      packet.payer
  endpointRefinement : ℕ → ℕ
  endpointRefinement_strictMono : StrictMono endpointRefinement
  endpointPacket_subsequence_eq : endpointPacket.subsequence =
    supportHandoff.subsequence ∘ endpointRefinement

/-- Source-attached off-minimum endpoint alternative. -/
structure CanonicalPairMinimumEndpointDebtAscent
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) where
  rayReturn : MaximalPrefixRayMinimumReturn packet
  endpointPacket : CanonicalPairEndpointConcentratedPacket packet
  debtAscent : QuittingMinimumEndpointDebtAscent reward source.point.1
    packet.rayFamily.rayProfiles packet.rayPaidTargetProfile packet.payer
  endpointRefinement : ℕ → ℕ
  endpointRefinement_strictMono : StrictMono endpointRefinement
  endpointPacket_subsequence_eq : endpointPacket.subsequence =
    debtAscent.subsequence ∘ endpointRefinement

namespace CanonicalPairMinimumEndpointSupportRankHandoff

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The stored concentrated endpoints converge to the very same endpoint
cluster used by the one-time support handoff. -/
theorem endpointPacket_endpoint_tendsto
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (packet.rayPaidTargetProfile
        (handoff.endpointPacket.subsequence rank))) atTop
      (nhds handoff.supportHandoff.endpointCluster) := by
  rw [handoff.endpointPacket_subsequence_eq]
  simpa only [Function.comp_def] using
    handoff.supportHandoff.endpoint_tendsto.comp
      handoff.endpointRefinement_strictMono.tendsto_atTop

/-- The source side of the joint compactification remains convergent along
the endpoint packet's refined subsequence. -/
theorem endpointPacket_source_tendsto
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (packet.rayFamily.rayProfiles
        (handoff.endpointPacket.subsequence rank))) atTop
      (nhds handoff.supportHandoff.sourceCluster) := by
  rw [handoff.endpointPacket_subsequence_eq]
  simpa only [Function.comp_def] using
    handoff.supportHandoff.source_tendsto.comp
      handoff.endpointRefinement_strictMono.tendsto_atTop

/-- The literal half-mixture sequence used by the support-rank argument is
also retained on the endpoint packet's refined subsequence. -/
theorem endpointPacket_half_tendsto
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (quittingHalfStoppingLawProfile reward
        (packet.rayFamily.rayProfiles
          (handoff.endpointPacket.subsequence rank))
        (packet.rayPaidTargetProfile
          (handoff.endpointPacket.subsequence rank)) packet.payer)) atTop
      (nhds handoff.supportHandoff.halfCluster) := by
  rw [handoff.endpointPacket_subsequence_eq]
  simpa only [Function.comp_def] using
    handoff.supportHandoff.half_tendsto.comp
      handoff.endpointRefinement_strictMono.tendsto_atTop

/-- Endpoint total debt converges to the same global minimum on the stored
concentrated-packet ranks. -/
theorem endpointPacket_endpointDebtSum_tendsto
    (handoff : CanonicalPairMinimumEndpointSupportRankHandoff packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (packet.rayPaidTargetProfile
          (handoff.endpointPacket.subsequence rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
  have hcontinuous :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      handoff.endpointPacket_endpoint_tendsto
  rw [handoff.supportHandoff.endpoint_debtSum_eq_minimum] at hcontinuous
  exact hcontinuous

end CanonicalPairMinimumEndpointSupportRankHandoff

namespace CanonicalPairMinimumEndpointDebtAscent

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

/-- The stored concentrated endpoints converge to the very same strict
endpoint cluster used by the debt-ascent alternative. -/
theorem endpointPacket_endpoint_tendsto
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (packet.rayPaidTargetProfile
        (ascent.endpointPacket.subsequence rank))) atTop
      (nhds ascent.debtAscent.endpointCluster) := by
  rw [ascent.endpointPacket_subsequence_eq]
  simpa only [Function.comp_def] using
    ascent.debtAscent.endpoint_tendsto.comp
      ascent.endpointRefinement_strictMono.tendsto_atTop

/-- The source side of the joint compactification remains convergent along
the endpoint packet's refined subsequence. -/
theorem endpointPacket_source_tendsto
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticPair reward
      (packet.rayFamily.rayProfiles
        (ascent.endpointPacket.subsequence rank))) atTop
      (nhds ascent.debtAscent.sourceCluster) := by
  rw [ascent.endpointPacket_subsequence_eq]
  simpa only [Function.comp_def] using
    ascent.debtAscent.source_tendsto.comp
      ascent.endpointRefinement_strictMono.tendsto_atTop

/-- Endpoint total debt converges to the literal strict endpoint-cluster
value on the stored concentrated-packet ranks. -/
theorem endpointPacket_endpointDebtSum_tendsto
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    Tendsto (fun rank ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (packet.rayPaidTargetProfile
          (ascent.endpointPacket.subsequence rank)))) atTop
      (nhds (quittingTerminalSemanticDebtSum
        ascent.debtAscent.endpointCluster)) :=
  continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
    ascent.endpointPacket_endpoint_tendsto

/-- The limit in the preceding theorem is strictly above the minimum debt. -/
theorem endpointCluster_debtSum_gt_minimum
    (ascent : CanonicalPairMinimumEndpointDebtAscent packet) :
    quittingTerminalSemanticDebtSum source.point.1 <
      quittingTerminalSemanticDebtSum ascent.debtAscent.endpointCluster :=
  ascent.debtAscent.endpoint_debtSum_gt_minimum

end CanonicalPairMinimumEndpointDebtAscent

/-- In the scalar minimum-return arm, the endpoint compactification either
lands on the same minimum fiber and performs the fresh support-rank handoff,
or remains strictly above that fiber. -/
theorem nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_of_return
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (rayReturn : MaximalPrefixRayMinimumReturn packet) :
    Nonempty (CanonicalPairMinimumEndpointSupportRankHandoff packet) ∨
      Nonempty (CanonicalPairMinimumEndpointDebtAscent packet) := by
  have hsourceDebtSum : Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (packet.rayFamily.rayProfiles index))) atTop
      (nhds (quittingTerminalSemanticDebtSum source.point.1)) := by
    simpa only [rayReturn.limit_eq] using packet.rayProfiles_wholeDebt_tendsto
  have hsurvival : Tendsto
      (quittingMaximalCapSemanticPrefixSurvival reward packet.raySource) atTop
      (nhds packet.rayResolution) := by
    have hlimit :=
      quittingMaximalCapSemanticPrefixSurvival_tendsto_limit_div reward
        source.point.1 packet.raySource source.minimum source.minimumDebt_pos
          packet.raySource_mem
    change Tendsto
      (quittingMaximalCapSemanticPrefixSurvival reward packet.raySource) atTop
        (nhds (packet.rayLimit /
          quittingTerminalSemanticDebtSum packet.raySource)) at hlimit
    rw [rayReturn.limit_eq] at hlimit
    exact hlimit
  let sourceMoverLimit := packet.rayResolution *
    quittingTerminalSemanticDebt packet.raySource packet.payer
  have hsourceMoverLimit : 0 < sourceMoverLimit :=
    mul_pos packet.rayResolution_pos packet.raySource_payerDebt_pos
  have hsourceMover : Tendsto (fun index ↦ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (packet.rayFamily.rayProfiles index)) packet.payer) atTop
      (nhds sourceMoverLimit) := by
    have heq : (fun index ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles index)) packet.payer) =
        fun index ↦ quittingMaximalCapSemanticPrefixSurvival reward
          packet.raySource index *
            quittingTerminalSemanticDebt packet.raySource packet.payer := by
      funext index
      rw [packet.rayFamily.rayProfiles_semantic_eq,
        quittingTerminalSemanticDebt_maximalCapSemanticPrefixOrbit_eq]
    rw [heq]
    exact hsurvival.mul_const _
  have hgeneric := exists_minimumEndpointSupportRankHandoff_or_debtAscent
    reward source.point.1 packet.rayFamily.rayProfiles
      packet.rayPaidTargetProfile packet.payer
      (fun index other hother ↦
        packet.rayPaidTargetProfile_opponent_eq index other hother)
      source.minimum source.minimumDebt_pos hsourceDebtSum sourceMoverLimit
      hsourceMoverLimit hsourceMover
      packet.rayPaidTargetProfile_payerDebt_eq_zero
  rcases hgeneric with hhandoff | hascent
  · obtain ⟨supportHandoff⟩ := hhandoff
    obtain ⟨endpointPacket, endpointRefinement, hrefinement,
        hsubsequence⟩ :=
      packet.exists_canonicalPairEndpointConcentratedPacket_refining
        supportHandoff.subsequence supportHandoff.subsequence_strictMono
    exact Or.inl ⟨{
      rayReturn := rayReturn
      endpointPacket := endpointPacket
      supportHandoff := supportHandoff
      endpointRefinement := endpointRefinement
      endpointRefinement_strictMono := hrefinement
      endpointPacket_subsequence_eq := hsubsequence
    }⟩
  · obtain ⟨debtAscent⟩ := hascent
    obtain ⟨endpointPacket, endpointRefinement, hrefinement,
        hsubsequence⟩ :=
      packet.exists_canonicalPairEndpointConcentratedPacket_refining
        debtAscent.subsequence debtAscent.subsequence_strictMono
    exact Or.inr ⟨{
      rayReturn := rayReturn
      endpointPacket := endpointPacket
      debtAscent := debtAscent
      endpointRefinement := endpointRefinement
      endpointRefinement_strictMono := hrefinement
      endpointPacket_subsequence_eq := hsubsequence
    }⟩

/-- Certificate-free source-facing exhaustion.  The canonical source itself
produces the scalar-ray branch; only its minimum-return arm is refined into
the endpoint support handoff versus strict endpoint ascent. -/
theorem nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_or_rayStall
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    Nonempty (CanonicalPairMinimumEndpointSupportRankHandoff packet) ∨
      Nonempty (CanonicalPairMinimumEndpointDebtAscent packet) ∨
        Nonempty (MaximalPrefixRayStall packet) := by
  rcases packet.nonempty_maximalPrefixRayMinimumReturn_or_stall with
    hreturn | hstall
  · obtain ⟨rayReturn⟩ := hreturn
    rcases
        nonempty_canonicalPairMinimumEndpointSupportRankHandoff_or_debtAscent_of_return
          packet rayReturn with handoff | ascent
    · exact Or.inl handoff
    · exact Or.inr (Or.inl ascent)
  · exact Or.inr (Or.inr hstall)

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
