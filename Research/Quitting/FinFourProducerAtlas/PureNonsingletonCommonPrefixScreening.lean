/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ExactPrefixAtomTransport
import Research.Quitting.FinFourProducerAtlas.MaximalPrefixRayDichotomy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer
import UniformEquilibrium.Quitting.Paths.PureNonsingletonCommonPrefixScreening

/-!
# Screening tail-only repairs behind the Fin4 maximal-prefix pair

The maximal-prefix construction retains one actual finite outer word and one
pure pair at its marked date.  Replacing only the behavioral tail strictly
behind that pair leaves the word and pair unchanged.  Pure nonsingleton
screening therefore makes the replacement profile's complete terminal
semantics and outcome law identical to those of the actual ray profile.

This is an architecture no-go for tail-only repair.  It does not eliminate
the strict maximal ray, change a marked root, compare two outer words, or
screen an edge inserted before the pure pair.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open QuittingSureSetOwnerRepair

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
  {bound : ℝ}
  {source : FinFourMinimumAtomProducer reward bound}
  {returnSource :
    FinFourOwnerCompressedMinimumReturnForcedPairSource source}
  {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

/-- The retained maximal-cap word at one actual ray index. -/
def rayScreeningWord
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) : List (Fin 4 → PMF Bool) :=
  quittingMaximalCapSemanticPrefixRootStack reward packet.raySource index

/-- A replacement tail placed strictly behind the unchanged pure pair. -/
def rayTailReplacementBaseProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingRootThenContinuationProfile reward
    (quittingPureSetRoot packet.rayTerminal.val) replacementTail

/-- The same actual outer word applied to a tail-only replacement behind the
retained pure pair. -/
def rayTailReplacementProfile
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward (packet.rayScreeningWord index)
    (packet.rayTailReplacementBaseProfile replacementTail)

/-- The screening word has exactly the retained ray depth. -/
theorem rayScreeningWord_length
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    (packet.rayScreeningWord index).length = index :=
  quittingMaximalCapSemanticPrefixRootStack_length reward packet.raySource
    index

/-- The replacement profile literally uses the retained word, pair, index,
and supplied post-pair tail. -/
theorem rayTailReplacementProfile_eq_literalRootStack
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    packet.rayTailReplacementProfile index replacementTail =
      quittingLiteralRootStackProfile reward
        (quittingMaximalCapSemanticPrefixRootStack reward packet.raySource
          index)
        (quittingRootThenContinuationProfile reward
          (quittingPureSetRoot packet.rayTerminal.val) replacementTail) := rfl

/-- The actual ray profile has the same literal word and pure pair; its tail
is the source-selected reference profile at the retained subsequence index. -/
theorem rayProfiles_eq_literalRootStack_purePair
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    packet.rayFamily.rayProfiles index =
      quittingLiteralRootStackProfile reward
        (packet.rayScreeningWord index)
        (quittingRootThenContinuationProfile reward
          (quittingPureSetRoot packet.rayTerminal.val)
          (packet.rayTail index)) := rfl

/-- The retained screening coalition is literally the source packet's moving
pair and has cardinality two. -/
theorem rayScreeningTerminal_card
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) :
    packet.rayTerminal.val.card = 2 := by
  rw [rayTerminal, packet.movingTerminal_card]

/-- Any tail-only replacement behind the fixed pure pair and common word has
the exact complete terminal semantic pair of the actual ray profile. -/
theorem rayTailReplacementProfile_semantic_eq_actual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (packet.rayTailReplacementProfile index replacementTail) =
      quittingTerminalSemanticPair reward
        (packet.rayFamily.rayProfiles index) := by
  rw [packet.rayTailReplacementProfile_eq_literalRootStack,
    packet.rayProfiles_eq_literalRootStack_purePair]
  exact
    (quittingTerminalSemanticPair_literalRootStack_pureSet_screen
      (packet.rayScreeningWord index) packet.rayTerminal.val
        (by rw [packet.rayScreeningTerminal_card])
        replacementTail (packet.rayTail index))

/-- Source provenance: the replacement realizes the same indexed semantic
orbit built from the packet's fixed `raySource`. -/
theorem rayTailReplacementProfile_semantic_eq_orbit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticPair reward
        (packet.rayTailReplacementProfile index replacementTail) =
      quittingMaximalCapSemanticPrefixOrbit reward packet.raySource index :=
  (packet.rayTailReplacementProfile_semantic_eq_actual index
      replacementTail).trans
    (packet.rayFamily.rayProfiles_semantic_eq index)

/-- Every coordinate debt is exactly the actual indexed ray debt. -/
theorem rayTailReplacementProfile_debt_eq_actual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) (who : Fin 4) :
    quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayTailReplacementProfile index replacementTail)) who =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles index)) who := by
  rw [packet.rayTailReplacementProfile_semantic_eq_actual]

/-- The named semantic debt change from the actual ray profile to the
tail-only replacement is zero in every coordinate. -/
theorem rayTailReplacementProfile_debtChange_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) (who : Fin 4) :
    quittingTerminalSemanticDebtChange
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles index))
        (quittingTerminalSemanticPair reward
          (packet.rayTailReplacementProfile index replacementTail)) who = 0 := by
  unfold quittingTerminalSemanticDebtChange
  rw [packet.rayTailReplacementProfile_debt_eq_actual, sub_self]

/-- Total semantic debt is exactly the actual indexed ray debt. -/
theorem rayTailReplacementProfile_wholeDebt_eq_actual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (packet.rayTailReplacementProfile index replacementTail)) =
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (packet.rayFamily.rayProfiles index)) := by
  rw [packet.rayTailReplacementProfile_semantic_eq_actual]

/-- The total semantic-debt change from the actual ray profile to the
tail-only replacement is literally zero. -/
theorem rayTailReplacementProfile_wholeDebtChange_eq_zero
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (packet.rayTailReplacementProfile index replacementTail)) -
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (packet.rayFamily.rayProfiles index)) = 0 := by
  rw [packet.rayTailReplacementProfile_wholeDebt_eq_actual, sub_self]

/-- Every varying family of post-pair replacement tails has the same scalar
debt limit as the actual maximal-prefix ray. -/
theorem rayTailReplacementProfile_wholeDebt_tendsto_rayLimit
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (replacementTail : ℕ → (quittingGame reward).BehaviorProfile) :
    Tendsto (fun index ↦ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward
        (packet.rayTailReplacementProfile index (replacementTail index))))
      atTop (nhds packet.rayLimit) := by
  convert packet.rayProfiles_wholeDebt_tendsto using 1
  funext index
  exact packet.rayTailReplacementProfile_wholeDebt_eq_actual index
    (replacementTail index)

/-- Before the outer word is applied, every replacement base has the same
Dirac terminal law as the actual pure-pair base. -/
theorem rayTailReplacementBaseProfile_outcomeMass_eq_pointMass
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward
        (packet.rayTailReplacementBaseProfile replacementTail) =
      fun outcome ↦
        ((PMF.pure (some packet.rayTerminal)) outcome).toReal := by
  calc
    quittingTerminalOutcomeMass reward
        (packet.rayTailReplacementBaseProfile replacementTail) =
        quittingTerminalOutcomeMass reward (packet.rayBaseProfile 0) := by
      funext outcome
      rw [rayTailReplacementBaseProfile, rayBaseProfile,
        quittingTerminalOutcomeMass_rootThenContinuation,
        quittingTerminalOutcomeMass_rootThenContinuation]
      rw [stationaryContinueMass_pureSetRoot_of_nonempty
        packet.rayTerminal.property]
      cases outcome <;> simp
    _ = _ := packet.rayBaseProfile_outcomeMass_eq_pointMass 0

/-- After applying the unchanged outer word, the complete outcome law of the
replacement remains exactly the law of the actual ray profile.  The common
word may itself absorb, so this law is not asserted to remain Dirac. -/
theorem rayTailReplacementProfile_outcomeMass_eq_actual
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ)
    (replacementTail : (quittingGame reward).BehaviorProfile) :
    quittingTerminalOutcomeMass reward
        (packet.rayTailReplacementProfile index replacementTail) =
      quittingTerminalOutcomeMass reward
        (packet.rayFamily.rayProfiles index) := by
  funext outcome
  rw [packet.rayTailReplacementProfile_eq_literalRootStack,
    packet.rayProfiles_eq_literalRootStack_purePair]
  have htransport := quittingTerminalOutcomeMass_literalRootStack_sub_eq
    reward (packet.rayScreeningWord index)
      (packet.rayTailReplacementBaseProfile replacementTail)
      (packet.rayBaseProfile index) outcome
  have hbase : quittingTerminalOutcomeMass reward
      (packet.rayTailReplacementBaseProfile replacementTail) outcome =
      quittingTerminalOutcomeMass reward (packet.rayBaseProfile index)
        outcome := by
    rw [packet.rayTailReplacementBaseProfile_outcomeMass_eq_pointMass,
      packet.rayBaseProfile_outcomeMass_eq_pointMass]
  rw [hbase, sub_self, mul_zero] at htransport
  exact sub_eq_zero.mp htransport

/-- No positive coordinate-debt repair can be created solely by replacing a
tail behind the unchanged pair and word. -/
theorem not_exists_positiveDebtChange_rayTailReplacement
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    ¬ ∃ replacementTail : (quittingGame reward).BehaviorProfile,
        ∃ who : Fin 4, 0 < quittingTerminalSemanticDebtChange
          (quittingTerminalSemanticPair reward
            (packet.rayFamily.rayProfiles index))
          (quittingTerminalSemanticPair reward
            (packet.rayTailReplacementProfile index replacementTail)) who := by
  rintro ⟨replacementTail, who, hpositive⟩
  rw [packet.rayTailReplacementProfile_debtChange_eq_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- No positive total-debt repair can be created solely by replacing a tail
behind the unchanged pair and word. -/
theorem not_exists_positiveWholeDebtChange_rayTailReplacement
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    ¬ ∃ replacementTail : (quittingGame reward).BehaviorProfile,
        0 < quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (packet.rayTailReplacementProfile index replacementTail)) -
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward
                (packet.rayFamily.rayProfiles index)) := by
  rintro ⟨replacementTail, hpositive⟩
  rw [packet.rayTailReplacementProfile_wholeDebtChange_eq_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- Nor can a tail-only replacement produce a positive prescribed-payoff
change at the whole source profile. -/
theorem not_exists_positivePayoffChange_rayTailReplacement
    (packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
      returnSource lambda) (index : ℕ) :
    ¬ ∃ replacementTail : (quittingGame reward).BehaviorProfile,
        ∃ who : Fin 4,
          0 < quittingTerminalPayoff reward
                (packet.rayTailReplacementProfile index replacementTail) who -
              quittingTerminalPayoff reward
                (packet.rayFamily.rayProfiles index) who := by
  rintro ⟨replacementTail, who, hpositive⟩
  have hsemantic :=
    packet.rayTailReplacementProfile_semantic_eq_actual index replacementTail
  have hpayoff := congrArg
    (fun pair : QuittingTerminalSemanticPair (Fin 4) ↦ pair.1 who) hsemantic
  change quittingTerminalPayoff reward
      (packet.rayTailReplacementProfile index replacementTail) who =
    quittingTerminalPayoff reward (packet.rayFamily.rayProfiles index) who
    at hpayoff
  rw [hpayoff, sub_self] at hpositive
  exact (lt_irrefl 0) hpositive

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
