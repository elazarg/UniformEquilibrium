/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Quitting.Root.SelfTailClosure

/-!
# Decorated arbitrary-prefix orbits

This file builds the source-independent topological object used by normalized
passport minimization.  The supplied family consists of actual profiles with
fixed labels.  Its orbit allows every finite word of product roots, with no
Nash condition.  The closure is therefore larger than the cluster set of the
supplied family.

The two scalar coordinates are an unconditional marked coalition mass and an
actual payoff difference between two profiles.  Both scale by the same joint
Continue product under a common literal prefix.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A whole joint semantic/law point, a post-mark joint semantic/law point,
an unconditional marked mass, and an actual payoff gain. -/
abbrev QuittingMarkedPairDecoration (ι : Type) [Fintype ι] :=
  (QuittingTerminalSemanticLawPoint ι ×
    QuittingTerminalSemanticLawPoint ι) × (ℝ × ℝ)

namespace QuittingMarkedPairDecoration

@[simp] def whole (point : QuittingMarkedPairDecoration ι) :
    QuittingTerminalSemanticLawPoint ι := point.1.1

@[simp] def tail (point : QuittingMarkedPairDecoration ι) :
    QuittingTerminalSemanticLawPoint ι := point.1.2

@[simp] def markedMass (point : QuittingMarkedPairDecoration ι) : ℝ := point.2.1

@[simp] def actualGain (point : QuittingMarkedPairDecoration ι) : ℝ := point.2.2

end QuittingMarkedPairDecoration

/-- Actual fixed-label data before adjoining arbitrary prefixes.  The two
profiles in each row are retained so that `actualGain` is a literal terminal
payoff difference, not an external scalar certificate. -/
structure QuittingMarkedPairDecoratedFamily
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  sourceProfile : ℕ → (quittingGame reward).BehaviorProfile
  profile : ℕ → (quittingGame reward).BehaviorProfile
  mark : ℕ → ℕ
  terminal : {S : Finset ι // S.Nonempty}
  markedOwner : ι
  gainMover : ι
  markedMass_pos : ∀ rank, 0 <
    quittingStageCoalitionMass reward (profile rank) (mark rank) terminal
  actualGain_pos : ∀ rank, 0 <
    quittingTerminalPayoff reward (profile rank) gainMover -
      quittingTerminalPayoff reward (sourceProfile rank) gainMover
  markedOwnerDefect_eq_zero : ∀ rank,
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (profile rank) (mark rank + 1))).1
      (quittingProfileLiveRoot reward (profile rank) (mark rank)) markedOwner = 0

namespace QuittingMarkedPairDecoratedFamily

variable (family : QuittingMarkedPairDecoratedFamily reward)

/-- Common arbitrary literal prefix of the endpoint profile. -/
def descendantProfile (rank : ℕ) (roots : List (ι → PMF Bool)) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward roots (family.profile rank)

/-- The same literal prefix on the comparison profile. -/
def descendantSourceProfile (rank : ℕ) (roots : List (ι → PMF Bool)) :
    (quittingGame reward).BehaviorProfile :=
  quittingLiteralRootStackProfile reward roots (family.sourceProfile rank)

/-- The original marked date shifted past the arbitrary prefix word. -/
def descendantMark (rank : ℕ) (roots : List (ι → PMF Bool)) : ℕ :=
  roots.length + family.mark rank

/-- Joint survival of an arbitrary finite root word. -/
def prefixSurvival (_family : QuittingMarkedPairDecoratedFamily reward)
    (roots : List (ι → PMF Bool)) : ℝ :=
  quittingCapNashStackContinueProduct roots

/-- The actual decorated base row, before any new roots are prefixed. -/
def baseDecoration (rank : ℕ) : QuittingMarkedPairDecoration ι :=
  (((quittingTerminalSemanticPair reward (family.profile rank),
      quittingTerminalOutcomeMass reward (family.profile rank)),
    (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward (family.profile rank)
          (family.mark rank + 1)),
      quittingTerminalOutcomeMass reward
        (quittingAllContinueProfileSpine reward (family.profile rank)
          (family.mark rank + 1)))),
    (quittingStageCoalitionMass reward (family.profile rank)
      (family.mark rank) family.terminal,
    quittingTerminalPayoff reward (family.profile rank) family.gainMover -
      quittingTerminalPayoff reward (family.sourceProfile rank) family.gainMover))

/-- One-root affine action on all four decoration coordinates. -/
def prefixMap (_family : QuittingMarkedPairDecoratedFamily reward)
    (root : ι → PMF Bool) (point : QuittingMarkedPairDecoration ι) :
    QuittingMarkedPairDecoration ι :=
  (((quittingTerminalSemanticPrefix reward root point.whole.1,
      quittingTerminalOutcomeLawPrefix root point.whole.2), point.tail),
    (quittingStationaryContinueMass root * point.markedMass,
      quittingStationaryContinueMass root * point.actualGain))

/-- Literal decoration of a finite arbitrary-prefix descendant.  The scalar
coordinates use their exact common-survival formulas; accessors below identify
them with the actual descendant mass and payoff difference. -/
def rawDecoration (family : QuittingMarkedPairDecoratedFamily reward)
    (rank : ℕ) : List (ι → PMF Bool) →
    QuittingMarkedPairDecoration ι
  | [] => family.baseDecoration rank
  | root :: roots => family.prefixMap root (rawDecoration family rank roots)

@[simp] theorem rawDecoration_nil (rank : ℕ) :
    family.rawDecoration rank [] = family.baseDecoration rank := by
  rfl

@[simp] theorem rawDecoration_cons (root : ι → PMF Bool) (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    family.rawDecoration rank (root :: roots) =
      family.prefixMap root (family.rawDecoration rank roots) := by
  rfl

/-- Exact joint-survival scaling of the marked-mass coordinate along an
arbitrary prefix word. -/
theorem rawDecoration_markedMass_eq_prefixSurvival_mul (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).markedMass =
      family.prefixSurvival roots *
        (family.baseDecoration rank).markedMass := by
  induction roots with
  | nil => simp [prefixSurvival]
  | cons root roots ih =>
      rw [rawDecoration_cons]
      change quittingStationaryContinueMass root *
          (family.rawDecoration rank roots).markedMass = _
      rw [ih]
      simp [prefixSurvival, mul_assoc]

/-- Exact joint-survival scaling of the actual payoff-gain coordinate along
the same arbitrary prefix word. -/
theorem rawDecoration_actualGain_eq_prefixSurvival_mul (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).actualGain =
      family.prefixSurvival roots *
        (family.baseDecoration rank).actualGain := by
  induction roots with
  | nil => simp [prefixSurvival]
  | cons root roots ih =>
      rw [rawDecoration_cons]
      change quittingStationaryContinueMass root *
          (family.rawDecoration rank roots).actualGain = _
      rw [ih]
      simp [prefixSurvival, mul_assoc]

omit [DecidableEq ι] in
/-- Iterating all-Continue spines adds their offsets. -/
theorem quittingAllContinueProfileSpine_add
    (profile : (quittingGame reward).BehaviorProfile) (first second : ℕ) :
    quittingAllContinueProfileSpine reward profile (first + second) =
      quittingAllContinueProfileSpine reward
        (quittingAllContinueProfileSpine reward profile first) second := by
  induction first generalizing profile with
  | zero => simp [quittingAllContinueProfileSpine]
  | succ first ih =>
      simpa only [Nat.succ_add, quittingAllContinueProfileSpine_succ_eq] using
        ih (quittingProfileAllContinueContinuation reward profile)

/-- The complete post-mark behavioral spine of a descendant is literally the
post-mark spine of its originating supplied row. -/
theorem descendant_postMarkSpine_eq (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    quittingAllContinueProfileSpine reward
        (family.descendantProfile rank roots)
        (family.descendantMark rank roots + 1) =
      quittingAllContinueProfileSpine reward (family.profile rank)
        (family.mark rank + 1) := by
  rw [descendantMark, show roots.length + family.mark rank + 1 =
      roots.length + (family.mark rank + 1) by omega,
    quittingAllContinueProfileSpine_add]
  rw [show quittingAllContinueProfileSpine reward
      (family.descendantProfile rank roots) roots.length =
      family.profile rank by
    exact quittingAllContinueProfileSpine_literalRootStackProfile_length
      reward roots (family.profile rank)]

/-- The marked live root of a descendant is literally the supplied row's
marked live root. -/
theorem descendant_markedRoot_eq (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    quittingProfileLiveRoot reward (family.descendantProfile rank roots)
        (family.descendantMark rank roots) =
      quittingProfileLiveRoot reward (family.profile rank) (family.mark rank) := by
  rw [← congrFun (quittingProfileSpineRoot_eq_profileLiveRoot reward
      (family.descendantProfile rank roots))
      (family.descendantMark rank roots)]
  rw [← congrFun (quittingProfileSpineRoot_eq_profileLiveRoot reward
      (family.profile rank)) (family.mark rank)]
  unfold quittingProfileSpineRoot
  rw [descendantMark, quittingAllContinueProfileSpine_add]
  rw [show quittingAllContinueProfileSpine reward
      (family.descendantProfile rank roots) roots.length =
      family.profile rank by
    exact quittingAllContinueProfileSpine_literalRootStackProfile_length
      reward roots (family.profile rank)]

/-- The fixed marked owner's zero local defect survives every arbitrary
prefix, at the correspondingly shifted actual date. -/
theorem descendant_markedOwnerDefect_eq_zero (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    quittingRootCoordinateNashDefect reward
      (quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward
          (family.descendantProfile rank roots)
          (family.descendantMark rank roots + 1))).1
      (quittingProfileLiveRoot reward (family.descendantProfile rank roots)
        (family.descendantMark rank roots)) family.markedOwner = 0 := by
  rw [family.descendant_postMarkSpine_eq,
    family.descendant_markedRoot_eq]
  exact family.markedOwnerDefect_eq_zero rank

/-- The scalar marked-mass coordinate is the actual unconditional atom mass
at the shifted descendant date. -/
theorem rawDecoration_markedMass_eq (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).markedMass =
      quittingStageCoalitionMass reward (family.descendantProfile rank roots)
        (family.descendantMark rank roots) family.terminal := by
  induction roots with
  | nil => simp [rawDecoration, baseDecoration, descendantProfile,
      descendantMark]
  | cons root roots ih =>
      calc
        (family.rawDecoration rank (root :: roots)).markedMass =
            quittingStationaryContinueMass root *
              (family.rawDecoration rank roots).markedMass := by
                rfl
        _ = quittingStationaryContinueMass root *
              quittingStageCoalitionMass reward
                (family.descendantProfile rank roots)
                (family.descendantMark rank roots) family.terminal := by
              rw [ih]
        _ = quittingStageCoalitionMass reward
              (family.descendantProfile rank (root :: roots))
              (family.descendantMark rank (root :: roots)) family.terminal := by
              simp only [descendantProfile, descendantMark, List.length_cons,
                quittingLiteralRootStackProfile_cons]
              rw [show roots.length + 1 + family.mark rank =
                  (roots.length + family.mark rank) + 1 by omega,
                quittingStageCoalitionMass_rootThenContinuation_succ]

omit [DecidableEq ι] in
/-- A common literal root prefix scales an actual payoff difference by its
joint Continue mass. -/
theorem terminalPayoff_sub_rootThenContinuation
    (root : ι → PMF Bool)
    (first second : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root first) who -
        quittingTerminalPayoff reward
          (quittingRootThenContinuationProfile reward root second) who =
      quittingStationaryContinueMass root *
        (quittingTerminalPayoff reward first who -
          quittingTerminalPayoff reward second who) := by
  rw [quittingTerminalPayoff_rootThenContinuation_eq,
    quittingTerminalPayoff_rootThenContinuation_eq,
    quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

/-- The scalar gain coordinate is the actual payoff difference between the
two commonly prefixed behavioral profiles. -/
theorem rawDecoration_actualGain_eq (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).actualGain =
      quittingTerminalPayoff reward (family.descendantProfile rank roots)
          family.gainMover -
        quittingTerminalPayoff reward
          (family.descendantSourceProfile rank roots) family.gainMover := by
  induction roots with
  | nil => simp [rawDecoration, baseDecoration, descendantProfile,
      descendantSourceProfile]
  | cons root roots ih =>
      calc
        (family.rawDecoration rank (root :: roots)).actualGain =
            quittingStationaryContinueMass root *
              (family.rawDecoration rank roots).actualGain := by
                rfl
        _ = quittingStationaryContinueMass root *
              (quittingTerminalPayoff reward
                  (family.descendantProfile rank roots) family.gainMover -
                quittingTerminalPayoff reward
                  (family.descendantSourceProfile rank roots)
                    family.gainMover) := by rw [ih]
        _ = quittingTerminalPayoff reward
                (family.descendantProfile rank (root :: roots))
                family.gainMover -
              quittingTerminalPayoff reward
                (family.descendantSourceProfile rank (root :: roots))
                family.gainMover := by
              simp only [descendantProfile, descendantSourceProfile,
                quittingLiteralRootStackProfile_cons]
              exact (terminalPayoff_sub_rootThenContinuation root _ _ _).symm

/-- The whole joint coordinate is literally the semantic/law point of the
actual prefixed endpoint profile. -/
theorem rawDecoration_whole_eq (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).whole =
      (quittingTerminalSemanticPair reward (family.descendantProfile rank roots),
        quittingTerminalOutcomeMass reward (family.descendantProfile rank roots)) := by
  induction roots with
  | nil => simp [rawDecoration, baseDecoration, descendantProfile]
  | cons root roots ih =>
      rw [rawDecoration_cons]
      change
        (quittingTerminalSemanticPrefix reward root
            (family.rawDecoration rank roots).whole.1,
          quittingTerminalOutcomeLawPrefix root
            (family.rawDecoration rank roots).whole.2) = _
      rw [ih]
      apply Prod.ext
      · exact (quittingTerminalSemanticPair_rootThenContinuation reward root
          (family.descendantProfile rank roots)).symm
      · exact quittingTerminalOutcomeLawPrefix_outcomeMass reward root
          (family.descendantProfile rank roots)

/-- The tail joint coordinate is never prefixed; it remains the actual
post-mark joint point of the originating supplied row. -/
theorem rawDecoration_tail_eq (rank : ℕ) (roots : List (ι → PMF Bool)) :
    (family.rawDecoration rank roots).tail =
      (quittingTerminalSemanticPair reward
          (quittingAllContinueProfileSpine reward (family.profile rank)
            (family.mark rank + 1)),
        quittingTerminalOutcomeMass reward
          (quittingAllContinueProfileSpine reward (family.profile rank)
            (family.mark rank + 1))) := by
  induction roots with
  | nil => simp [rawDecoration, baseDecoration]
  | cons root roots ih => simpa [rawDecoration_cons, prefixMap] using ih

/-- The decorated prefix map is continuous. -/
theorem continuous_prefixMap (root : ι → PMF Bool) :
    Continuous (family.prefixMap root) := by
  exact ((((continuous_quittingTerminalSemanticPrefix reward root).comp
      (continuous_fst.comp (continuous_fst.comp continuous_fst))).prodMk
        ((continuous_quittingTerminalOutcomeLawPrefix root).comp
          (continuous_snd.comp (continuous_fst.comp continuous_fst)))).prodMk
      (continuous_snd.comp continuous_fst)).prodMk
    ((continuous_const.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_const.mul (continuous_snd.comp continuous_snd)))

/-- Adding a root to the front of a raw word is exactly the affine decorated
prefix map. -/
theorem prefixMap_rawDecoration (root : ι → PMF Bool) (rank : ℕ)
    (roots : List (ι → PMF Bool)) :
    family.prefixMap root (family.rawDecoration rank roots) =
      family.rawDecoration rank (root :: roots) := rfl

/-- Raw orbit over every supplied rank and every finite arbitrary root word. -/
def rawPrefixOrbit : Set (QuittingMarkedPairDecoration ι) :=
  {point | ∃ rank roots, family.rawDecoration rank roots = point}

/-- Closed decorated arbitrary-prefix carrier. -/
def prefixOrbitCarrier : Set (QuittingMarkedPairDecoration ι) :=
  closure family.rawPrefixOrbit

/-- Every fixed root preserves the closed arbitrary-prefix carrier. -/
theorem prefixMap_mem_carrier (root : ι → PMF Bool)
    {point : QuittingMarkedPairDecoration ι}
    (hpoint : point ∈ family.prefixOrbitCarrier) :
    family.prefixMap root point ∈ family.prefixOrbitCarrier := by
  unfold prefixOrbitCarrier at hpoint ⊢
  apply map_mem_closure (family.continuous_prefixMap root) hpoint
  rintro candidate ⟨rank, roots, rfl⟩
  exact ⟨rank, root :: roots, rfl⟩

end QuittingMarkedPairDecoratedFamily

end GameTheory
