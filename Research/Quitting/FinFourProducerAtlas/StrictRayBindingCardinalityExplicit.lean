/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Research.Quitting.BindingCollisionGainPositivity
import Research.Quitting.FinFourProducerAtlas.StrictRayBindingCardinality
import Research.Topology.BoxComplementarityFaceLocalCountTwo
import Research.Topology.BoxComplementaritySpernerEventualLocalParity
import UniformEquilibrium.Quitting.Root.EndpointOpponentStability
import UniformEquilibrium.Quitting.Root.PlayerReindex

/-!
# Certificate-free binding cardinality for a strict Fin4 maximal ray

This module replaces the supplied abstract parity certificate by the concrete
same-resolution cubical-Sperner count at one actual late finite cap.
-/

noncomputable section

namespace GameTheory

open Filter Math Math.Probability Math.PMFProduct Set

variable {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
variable {bound : ℝ}
variable {source : FinFourMinimumAtomProducer reward bound}
variable {returnSource : FinFourOwnerCompressedMinimumReturnForcedPairSource source}
variable {lambda : ℝ}

namespace FinFourOwnerCompressedMinimumReturnForcedPairPacket

variable {packet : FinFourOwnerCompressedMinimumReturnForcedPairPacket
  returnSource lambda}

private theorem root_eq_allContinue_of_absorption_eq_zero
    (root : Fin 4 → PMF Bool)
    (hzero : quittingRootAbsorptionMass root = 0) :
    root = (quittingAllContinueRoot : Fin 4 → PMF Bool) := by
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at hzero
    linarith
  funext who
  simpa [quittingAllContinueRoot] using
    eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-- The limiting cap of every actual positive-hazard forward tail admits the
all-Continue exact root. -/
theorem FinFourStrictRayForwardExactCapTail.allContinue_exactNash_capLimit
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    IsεQuittingRootNash reward flow.forward.capLimit 0
      (quittingAllContinueRoot : Fin 4 → PMF Bool) :=
  (isZeroQuittingRootNash_allContinue_iff_singleton_le
    reward flow.forward.capLimit).2 flow.forward.singleton_le_capLimit

/-- If the limiting cap has no positive-absorption exact root, all Continue
is literally its unique exact root. -/
theorem FinFourStrictRayForwardExactCapTail.uniqueAllContinue_of_noPositiveRoot
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hnoPositive : ¬ ∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward flow.forward.capLimit 0 root ∧
        0 < quittingRootAbsorptionMass root) :
    HasUniqueAllContinueAtCapLimit flow := by
  intro root hnash
  have hnotPositive : ¬ 0 < quittingRootAbsorptionMass root := fun hpositive =>
    hnoPositive ⟨root, hnash, hpositive⟩
  have hzero : quittingRootAbsorptionMass root = 0 :=
    le_antisymm (not_lt.1 hnotPositive)
      (quittingRootAbsorptionMass_nonneg root)
  exact root_eq_allContinue_of_absorption_eq_zero root hzero

/-! ## A canonical coordinate normalization for one ordered binding pair -/

/-- Relabel `first` as coordinate two and `second` as coordinate three. -/
private def bindingPairEquiv (first second : Fin 4) : Fin 4 ≃ Fin 4 :=
  (Equiv.swap first 2).trans
    (Equiv.swap ((Equiv.swap first 2) second) 3)

private theorem bindingPairEquiv_first
    {first second : Fin 4} (hne : first ≠ second) :
    bindingPairEquiv first second first = 2 := by
  rw [bindingPairEquiv, Equiv.trans_apply, Equiv.swap_apply_left]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro heq
    apply hne
    have hmap : (Equiv.swap first 2) second =
        (Equiv.swap first 2) first := by
      rw [Equiv.swap_apply_left]
      exact heq.symm
    exact ((Equiv.swap first 2).injective hmap).symm
  · decide

private theorem bindingPairEquiv_second
    {first second : Fin 4} :
    bindingPairEquiv first second second = 3 := by
  rw [bindingPairEquiv, Equiv.trans_apply, Equiv.swap_apply_left]

private theorem quittingSingletonCapDefect_reindex
    (e : Fin 4 ≃ Fin 4)
    (originalReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (originalCap : Payoff (Fin 4)) (who : Fin 4) :
    quittingSingletonCapDefect (quittingRewardReindex e originalReward)
        (quittingPayoffReindex e originalCap) (e who) =
      quittingSingletonCapDefect originalReward originalCap who := by
  simp [quittingSingletonCapDefect, quittingSingletonTerminal,
    quittingCoalitionEquiv]

private theorem quittingSingletonCollisionGain_reindex
    (e : Fin 4 ≃ Fin 4)
    (originalReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (owner other : Fin 4) :
    quittingSingletonCollisionGain (quittingRewardReindex e originalReward)
        (e owner) (e other) =
      quittingSingletonCollisionGain originalReward owner other := by
  simp [quittingSingletonCollisionGain, quittingSingletonCollisionReward,
    quittingSoloReward, quittingCoalitionEquiv]

/-! ## Exact affine gains on the normalized binding face -/

private theorem quittingRootEndpointDifference_update_ownMarginal_local
    (normalizedReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (normalizedCap : Payoff (Fin 4)) (root : Fin 4 → PMF Bool)
    (who : Fin 4) (marginal : PMF Bool) :
    quittingRootEndpointDifference normalizedReward normalizedCap
        (Function.update root who marginal) who =
      quittingRootEndpointDifference normalizedReward normalizedCap root who := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff
  simp

private theorem quittingRootEndpointDifference_twoActiveFace
    (normalizedReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (normalizedCap : Payoff (Fin 4)) (root : Fin 4 → PMF Bool)
    (hzero : root 0 = PMF.pure false) (hone : root 1 = PMF.pure false) :
    quittingRootEndpointDifference normalizedReward normalizedCap root 2 =
        (root 3 true).toReal *
            quittingSingletonCollisionGain normalizedReward 3 2 -
          (root 3 false).toReal *
            quittingSingletonCapDefect normalizedReward normalizedCap 2 ∧
      quittingRootEndpointDifference normalizedReward normalizedCap root 3 =
        (root 2 true).toReal *
            quittingSingletonCollisionGain normalizedReward 2 3 -
          (root 2 false).toReal *
            quittingSingletonCapDefect normalizedReward normalizedCap 3 := by
  have htwo : Function.update root 2 (PMF.pure false) =
      quittingSoloStationaryRoot 3 (root 3) := by
    funext who
    fin_cases who <;>
      simp [quittingSoloStationaryRoot, hzero, hone]
  have hthree : Function.update root 3 (PMF.pure false) =
      quittingSoloStationaryRoot 2 (root 2) := by
    funext who
    fin_cases who <;>
      simp [quittingSoloStationaryRoot, hzero, hone]
  constructor
  · rw [← quittingRootEndpointDifference_update_ownMarginal_local
      normalizedReward normalizedCap root 2 (PMF.pure false), htwo]
    exact quittingRootEndpointDifference_soloStationaryRoot_other_cap_pmf
      normalizedReward normalizedCap (by decide : (2 : Fin 4) ≠ 3) (root 3)
  · rw [← quittingRootEndpointDifference_update_ownMarginal_local
      normalizedReward normalizedCap root 3 (PMF.pure false), hthree]
    exact quittingRootEndpointDifference_soloStationaryRoot_other_cap_pmf
      normalizedReward normalizedCap (by decide : (3 : Fin 4) ≠ 2) (root 2)

private theorem canonicalBridge_hasAffineBindingFaceGain
    (normalizedReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (normalizedCap : Payoff (Fin 4))
    (region : Set (UnitCube (Fin 4))) :
    (quittingEndpointNashBoxBridge normalizedReward normalizedCap).problem.HasAffineFaceGain
      region
      (quittingSingletonCapDefect normalizedReward normalizedCap 2)
      (quittingSingletonCollisionGain normalizedReward 3 2)
      (quittingSingletonCapDefect normalizedReward normalizedCap 3)
      (quittingSingletonCollisionGain normalizedReward 2 3) := by
  intro point _ hzero hone
  let bridge := quittingEndpointNashBoxBridge normalizedReward normalizedCap
  let root := bridge.rootEquiv point
  have hpureZero : root 0 = PMF.pure false := by
    apply eq_pure_false_of_true_toReal_eq_zero
    rw [bridge.quitProbability_eq, hzero]
  have hpureOne : root 1 = PMF.pure false := by
    apply eq_pure_false_of_true_toReal_eq_zero
    rw [bridge.quitProbability_eq, hone]
  have haffine := quittingRootEndpointDifference_twoActiveFace
    normalizedReward normalizedCap root hpureZero hpureOne
  constructor
  · rw [bridge.gain_eq]
    rw [haffine.1, bridge.quitProbability_eq, bridge.continueProbability_eq]
    ring
  · rw [bridge.gain_eq]
    rw [haffine.2, bridge.quitProbability_eq, bridge.continueProbability_eq]
    ring

/-! ## The same-resolution localization consumer -/

private def unitCubeOrigin : UnitCube (Fin 4) :=
  fun _ => ⟨0, by constructor <;> norm_num⟩

private theorem finFour_cases (who : Fin 4) :
    who = 0 ∨ who = 1 ∨ who = 2 ∨ who = 3 := by
  omega

private theorem dist_unitCubeOrigin_lt_iff
    (point : UnitCube (Fin 4)) {radius : ℝ} (hradius : 0 < radius) :
    dist point unitCubeOrigin < radius ↔ ∀ who, (point who : ℝ) < radius := by
  rw [dist_pi_lt_iff hradius]
  constructor
  · intro h who
    have hwho := h who
    change dist ((point who : Set.Icc (0 : ℝ) 1) : ℝ) 0 < radius at hwho
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (point who).property.1] at hwho
  · intro h who
    change dist ((point who : Set.Icc (0 : ℝ) 1) : ℝ) 0 < radius
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (point who).property.1]
    exact h who

private theorem boxComplementarityFaceThreshold_eq_of_gain_eq_zero
    {defect cross value : ℝ}
    (hdefect : 0 < defect) (hcross : 0 < cross)
    (hgain : -(1 - value) * defect + value * cross = 0) :
    boxComplementarityFaceThreshold defect cross = value := by
  rw [boxComplementarityFaceThreshold]
  field_simp [ne_of_gt (by linarith : 0 < defect + cross)]
  nlinarith

private theorem ceil_mul_div_lt_add_one
    (p : ℕ) (hp : 0 < p) {value : ℝ} (hvalue : 0 ≤ value) :
    (⌈(p : ℝ) * value⌉₊ : ℝ) / p < value + 1 / p := by
  have hceil : (⌈(p : ℝ) * value⌉₊ : ℝ) < (p : ℝ) * value + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg p) hvalue)
  calc
    (⌈(p : ℝ) * value⌉₊ : ℝ) / p <
        ((p : ℝ) * value + 1) / p :=
      (div_lt_div_iff_of_pos_right (Nat.cast_pos.mpr hp)).2 hceil
    _ = value + 1 / p := by
      field_simp

private theorem false_of_localized_binding_pair
    (problem : BoxComplementarityProblem (Fin 4))
    (selected : UnitCube (Fin 4)) (scale : ℝ)
    (hscale : 0 < scale) (hsmall : 3 * scale < 1)
    (hselectedSolution : problem.IsSolution selected)
    (hsolutions : ∀ point, problem.IsSolution point →
      ∀ who, (point who : ℝ) ≤ scale)
    (hselectedZero : (selected 0 : ℝ) = 0)
    (hselectedOne : (selected 1 : ℝ) = 0)
    (hselectedActive : 0 < (selected 2 : ℝ) + (selected 3 : ℝ))
    (defectTwo crossTwo defectThree crossThree : ℝ)
    (hcrossTwo : 0 < crossTwo) (hcrossThree : 0 < crossThree)
    (hregion : problem.IsLeadingNegativeRegion
      (Metric.ball unitCubeOrigin (3 * scale)))
    (haffine : problem.HasAffineFaceGain
      (Metric.ball unitCubeOrigin (3 * scale))
      defectTwo crossTwo defectThree crossThree) : False := by
  let target : Set (UnitCube (Fin 4)) :=
    Metric.ball unitCubeOrigin (2 * scale)
  let region : Set (UnitCube (Fin 4)) :=
    Metric.ball unitCubeOrigin (3 * scale)
  have htargetOpen : IsOpen target := Metric.isOpen_ball
  have hsolutionsTarget : problem.solutionSet ⊆ target := by
    intro point hpoint
    change dist point unitCubeOrigin < 2 * scale
    rw [dist_unitCubeOrigin_lt_iff point (by linarith)]
    intro who
    exact lt_of_le_of_lt (hsolutions point hpoint who) (by linarith)
  have hselectedRegion : selected ∈ region := by
    change dist selected unitCubeOrigin < 3 * scale
    rw [dist_unitCubeOrigin_lt_iff selected (by linarith)]
    intro who
    exact lt_of_le_of_lt (hsolutions selected hselectedSolution who) (by linarith)
  have hselectedTwoLt : (selected 2 : ℝ) < 1 :=
    lt_of_le_of_lt (hsolutions selected hselectedSolution 2) (by linarith)
  have hselectedThreeLt : (selected 3 : ℝ) < 1 :=
    lt_of_le_of_lt (hsolutions selected hselectedSolution 3) (by linarith)
  have hselectedTwoNonneg : 0 ≤ (selected 2 : ℝ) := (selected 2).property.1
  have hselectedThreeNonneg : 0 ≤ (selected 3 : ℝ) :=
    (selected 3).property.1
  have hmeshThicken : ∀ (p : ℕ) (hp : 0 < p), 1 / (p : ℝ) < scale →
      ∀ chain : Fin (4 + 1) →
          (boxComplementaritySpernerCube problem p hp).G,
        simplex (boxComplementaritySpernerCube problem p hp) 4 chain →
        (∃ index, boxComplementarityGridPoint p (chain index) ∈ target) →
        ∀ index, boxComplementarityGridPoint p (chain index) ∈ region := by
    intro p hp hmesh chain hsimplex htarget index
    obtain ⟨anchor, hanchor⟩ := htarget
    change dist (boxComplementarityGridPoint p (chain index))
      unitCubeOrigin < 3 * scale
    change dist (boxComplementarityGridPoint p (chain anchor))
      unitCubeOrigin < 2 * scale at hanchor
    calc
      dist (boxComplementarityGridPoint p (chain index)) unitCubeOrigin ≤
          dist (boxComplementarityGridPoint p (chain index))
              (boxComplementarityGridPoint p (chain anchor)) +
            dist (boxComplementarityGridPoint p (chain anchor))
              unitCubeOrigin := dist_triangle _ _ _
      _ < 1 / (p : ℝ) + 2 * scale := add_lt_add_of_le_of_lt
        (dist_boxComplementarityGridPoint_le_one_div_of_simplex
          problem p hp chain hsimplex index anchor) hanchor
      _ < 3 * scale := by linarith
  have hanchorOrigin : ∀ p (hp : 0 < p),
      boxComplementarityGridPoint p
        (boxComplementarityOriginChain p hp 0) ∈ target := by
    intro p hp
    change dist (boxComplementarityGridPoint p
      (boxComplementarityOriginChain p hp 0)) unitCubeOrigin < 2 * scale
    rw [dist_unitCubeOrigin_lt_iff _ (by linarith)]
    intro who
    rcases finFour_cases who with rfl | rfl | rfl | rfl
    all_goals
      simp [boxComplementarityGridPoint_val,
        boxComplementarityOriginChainValue]
      linarith
  by_cases htwo : 0 < (selected 2 : ℝ)
  · have hgainTwo : problem.gain selected 2 = 0 :=
      (hselectedSolution 2).2.2 htwo hselectedTwoLt
    by_cases hthree : 0 < (selected 3 : ℝ)
    · have hgainThree : problem.gain selected 3 = 0 :=
        (hselectedSolution 3).2.2 hthree hselectedThreeLt
      have hface := haffine selected hselectedRegion hselectedZero hselectedOne
      have hdefectTwo : 0 < defectTwo := by
        nlinarith [hface.1, hgainTwo]
      have hdefectThree : 0 < defectThree := by
        nlinarith [hface.2, hgainThree]
      have hthresholdTwo :
          boxComplementarityFaceThreshold defectTwo crossTwo =
            (selected 3 : ℝ) :=
        boxComplementarityFaceThreshold_eq_of_gain_eq_zero
          hdefectTwo hcrossTwo (hface.1.symm.trans hgainTwo)
      have hthresholdThree :
          boxComplementarityFaceThreshold defectThree crossThree =
            (selected 2 : ℝ) :=
        boxComplementarityFaceThreshold_eq_of_gain_eq_zero
          hdefectThree hcrossThree (hface.2.symm.trans hgainThree)
      have hsharp : problem.IsSharpBindingPairFace region
          defectTwo crossTwo defectThree crossThree := {
        defectTwo_pos := hdefectTwo
        crossTwo_pos := hcrossTwo
        defectThree_pos := hdefectThree
        crossThree_pos := hcrossThree
        affine := haffine
      }
      apply problem.not_eventually_localCompleteSimplexParity_eq_zero
        target htargetOpen hsolutionsTarget
      obtain ⟨threshold, hthreshold⟩ : ∃ threshold : ℕ,
          max (max (1 / scale) (1 / (selected 2 : ℝ)))
              (1 / (selected 3 : ℝ)) < threshold :=
        exists_nat_gt _
      refine ⟨threshold, ?_⟩
      intro p hpFine hp
      have hpReal : (0 : ℝ) < p := Nat.cast_pos.mpr hp
      have hthresholdP : (threshold : ℝ) ≤ p := by exact_mod_cast hpFine
      have hmeshScale : 1 / (p : ℝ) < scale := by
        have hinv : 1 / scale < (p : ℝ) := by
          linarith [le_max_left (1 / scale) (1 / (selected 2 : ℝ)),
            le_max_left
              (max (1 / scale) (1 / (selected 2 : ℝ)))
              (1 / (selected 3 : ℝ))]
        rw [div_lt_iff₀ hpReal]
        exact (div_lt_iff₀ hscale).1 hinv |>.trans_eq (mul_comm _ _)
      have hmeshTwo : 1 / (p : ℝ) < (selected 2 : ℝ) := by
        have hinv : 1 / (selected 2 : ℝ) < (p : ℝ) := by
          linarith [le_max_right (1 / scale) (1 / (selected 2 : ℝ)),
            le_max_left
              (max (1 / scale) (1 / (selected 2 : ℝ)))
              (1 / (selected 3 : ℝ))]
        rw [div_lt_iff₀ hpReal]
        exact (div_lt_iff₀ htwo).1 hinv |>.trans_eq (mul_comm _ _)
      have hmeshThree : 1 / (p : ℝ) < (selected 3 : ℝ) := by
        have hinv : 1 / (selected 3 : ℝ) < (p : ℝ) := by
          linarith [le_max_right
            (max (1 / scale) (1 / (selected 2 : ℝ)))
            (1 / (selected 3 : ℝ))]
        rw [div_lt_iff₀ hpReal]
        exact (div_lt_iff₀ hthree).1 hinv |>.trans_eq (mul_comm _ _)
      have hboundTwo : 2 ≤
          boxComplementarityFaceGridBound p defectTwo crossTwo := by
        have hone : 1 <
            boxComplementarityFaceGridBound p defectTwo crossTwo := by
          rw [lt_boxComplementarityFaceGridBound_iff p hp,
            hthresholdTwo]
          simpa using hmeshThree
        omega
      have hboundThree : 2 ≤
          boxComplementarityFaceGridBound p defectThree crossThree := by
        have hone : 1 <
            boxComplementarityFaceGridBound p defectThree crossThree := by
          rw [lt_boxComplementarityFaceGridBound_iff p hp,
            hthresholdThree]
          simpa using hmeshTwo
        omega
      apply boxComplementarityLocalCompleteSimplexParity_eq_zero_of_sharpFace
        problem p hp region hregion defectTwo crossTwo defectThree crossThree
        hsharp hboundTwo hboundThree target
        (hmeshThicken p hp hmeshScale) (hanchorOrigin p hp)
      change dist (boxComplementarityGridPoint p
        (boxComplementarityCornerChain p
          (boxComplementarityFaceGridBound p defectTwo crossTwo)
          (boxComplementarityFaceGridBound p defectThree crossThree) 2))
          unitCubeOrigin < 2 * scale
      rw [dist_unitCubeOrigin_lt_iff _ (by linarith)]
      have hTwoLe := boxComplementarityFaceGridBound_le p hdefectTwo hcrossTwo
      have hThreeLe :=
        boxComplementarityFaceGridBound_le p hdefectThree hcrossThree
      have hcornerTwo :
          ((boxComplementarityGridPoint p
            (boxComplementarityCornerChain p
              (boxComplementarityFaceGridBound p defectTwo crossTwo)
              (boxComplementarityFaceGridBound p defectThree crossThree) 2)
              2 : Set.Icc (0 : ℝ) 1) : ℝ) =
            (boxComplementarityFaceGridBound p defectThree crossThree : ℝ) /
              p := by
        rw [boxComplementarityGridPoint_val,
          boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
          boxComplementarityCornerChainValue_third]
        norm_num
      have hcornerThree :
          ((boxComplementarityGridPoint p
            (boxComplementarityCornerChain p
              (boxComplementarityFaceGridBound p defectTwo crossTwo)
              (boxComplementarityFaceGridBound p defectThree crossThree) 2)
              3 : Set.Icc (0 : ℝ) 1) : ℝ) =
            (boxComplementarityFaceGridBound p defectTwo crossTwo : ℝ) /
              p := by
        rw [boxComplementarityGridPoint_val,
          boxComplementarityCornerChain_val p hp hTwoLe hThreeLe,
          boxComplementarityCornerChainValue_fourth]
        norm_num
      have hselectedTwoLe := hsolutions selected hselectedSolution 2
      have hselectedThreeLe := hsolutions selected hselectedSolution 3
      intro who
      rcases finFour_cases who with rfl | rfl | rfl | rfl
      · simp [boxComplementarityCornerChain,
          boxComplementarityCornerChainValue]
        linarith
      · simp [boxComplementarityCornerChain,
          boxComplementarityCornerChainValue]
        linarith
      · rw [hcornerTwo, boxComplementarityFaceGridBound, hthresholdThree]
        exact (ceil_mul_div_lt_add_one p hp hselectedTwoNonneg).trans
          (by linarith)
      · rw [hcornerThree, boxComplementarityFaceGridBound, hthresholdTwo]
        exact (ceil_mul_div_lt_add_one p hp hselectedThreeNonneg).trans
          (by linarith)
    · have hthreeZero : (selected 3 : ℝ) = 0 :=
        le_antisymm (not_lt.1 hthree) hselectedThreeNonneg
      have hface := haffine selected hselectedRegion hselectedZero hselectedOne
      have hgainTwo : problem.gain selected 2 = 0 :=
        (hselectedSolution 2).2.2 htwo hselectedTwoLt
      have hdefectTwo : defectTwo = 0 := by
        rw [hgainTwo, hthreeZero] at hface
        simpa using hface.1.symm
      apply problem.not_eventually_localCompleteSimplexParity_eq_zero
        target htargetOpen hsolutionsTarget
      obtain ⟨threshold, hthreshold⟩ : ∃ threshold : ℕ,
          1 / scale < threshold := exists_nat_gt _
      refine ⟨threshold, ?_⟩
      intro p hpFine hp
      have hpReal : (0 : ℝ) < p := Nat.cast_pos.mpr hp
      have hthresholdP : (threshold : ℝ) ≤ p := by exact_mod_cast hpFine
      have hmesh : 1 / (p : ℝ) < scale := by
        have hinv : 1 / scale < (p : ℝ) := by linarith
        rw [div_lt_iff₀ hpReal]
        exact (div_lt_iff₀ hscale).1 hinv |>.trans_eq (mul_comm _ _)
      subst defectTwo
      exact boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloTwo
        problem p hp region hregion crossTwo defectThree crossThree haffine
        hcrossTwo.le target (fun vertices hcomplete hanchor ↦
          hmeshThicken p hp hmesh vertices hcomplete.1
            ⟨boxComplementarityCompleteSimplexAnchorIndex
              problem p hp vertices hcomplete, hanchor⟩)
  · have htwoZero : (selected 2 : ℝ) = 0 :=
      le_antisymm (not_lt.1 htwo) hselectedTwoNonneg
    have hthree : 0 < (selected 3 : ℝ) := by linarith
    have hgainThree : problem.gain selected 3 = 0 :=
      (hselectedSolution 3).2.2 hthree hselectedThreeLt
    have hface := haffine selected hselectedRegion hselectedZero hselectedOne
    have hdefectThree : defectThree = 0 := by
      rw [hgainThree, htwoZero] at hface
      simpa using hface.2.symm
    apply problem.not_eventually_localCompleteSimplexParity_eq_zero
      target htargetOpen hsolutionsTarget
    obtain ⟨threshold, hthreshold⟩ : ∃ threshold : ℕ,
        1 / scale < threshold := exists_nat_gt _
    refine ⟨threshold, ?_⟩
    intro p hpFine hp
    have hpReal : (0 : ℝ) < p := Nat.cast_pos.mpr hp
    have hthresholdP : (threshold : ℝ) ≤ p := by exact_mod_cast hpFine
    have hmesh : 1 / (p : ℝ) < scale := by
      have hinv : 1 / scale < (p : ℝ) := by linarith
      rw [div_lt_iff₀ hpReal]
      exact (div_lt_iff₀ hscale).1 hinv |>.trans_eq (mul_comm _ _)
    subst defectThree
    exact boxComplementarityLocalCompleteSimplexParity_eq_zero_of_soloThree
      problem p hp region hregion defectTwo crossTwo crossThree haffine
      hcrossThree.le target (fun vertices hcomplete hanchor ↦
        hmeshThicken p hp hmesh vertices hcomplete.1
          ⟨boxComplementarityCompleteSimplexAnchorIndex
            problem p hp vertices hcomplete, hanchor⟩)

/-! ## The strict-ray source adapter -/

/-- A two-coordinate limiting binding face is impossible on the actual
strict maximal ray once all Continue is the unique limiting exact root. -/
theorem FinFourStrictRayForwardExactCapTail.bindingFinset_card_ne_two
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hunique : HasUniqueAllContinueAtCapLimit flow) :
    flow.forward.bindingFinset.card ≠ 2 := by
  intro hcard
  obtain ⟨first, second, hne, hbinding⟩ := Finset.card_eq_two.mp hcard
  let e := bindingPairEquiv first second
  let normalizedReward := quittingRewardReindex e reward
  let normalizedLimit := quittingPayoffReindex e flow.forward.capLimit
  let outsideZero := e.symm 0
  let outsideOne := e.symm 1
  have heFirst : e first = 2 := bindingPairEquiv_first hne
  have heSecond : e second = 3 := bindingPairEquiv_second
  have hfirstMem : first ∈ flow.forward.bindingFinset := by
    rw [hbinding]
    simp
  have hsecondMem : second ∈ flow.forward.bindingFinset := by
    rw [hbinding]
    simp
  have houtsideZeroNeFirst : outsideZero ≠ first := by
    intro heq
    have := congrArg e heq
    rw [show e outsideZero = 0 from e.apply_symm_apply 0, heFirst] at this
    have := congrArg Fin.val this
    norm_num at this
  have houtsideZeroNeSecond : outsideZero ≠ second := by
    intro heq
    have := congrArg e heq
    rw [show e outsideZero = 0 from e.apply_symm_apply 0, heSecond] at this
    have := congrArg Fin.val this
    norm_num at this
  have houtsideOneNeFirst : outsideOne ≠ first := by
    intro heq
    have := congrArg e heq
    rw [show e outsideOne = 1 from e.apply_symm_apply 1, heFirst] at this
    have := congrArg Fin.val this
    norm_num at this
  have houtsideOneNeSecond : outsideOne ≠ second := by
    intro heq
    have := congrArg e heq
    rw [show e outsideOne = 1 from e.apply_symm_apply 1, heSecond] at this
    have := congrArg Fin.val this
    norm_num at this
  have houtsideZeroNotMem : outsideZero ∉ flow.forward.bindingFinset := by
    rw [hbinding]
    simp [houtsideZeroNeFirst, houtsideZeroNeSecond]
  have houtsideOneNotMem : outsideOne ∉ flow.forward.bindingFinset := by
    rw [hbinding]
    simp [houtsideOneNeFirst, houtsideOneNeSecond]
  have hdefectZero : 0 < quittingSingletonCapDefect normalizedReward
      normalizedLimit 0 := by
    rw [show (0 : Fin 4) = e outsideZero from (e.apply_symm_apply 0).symm]
    rw [quittingSingletonCapDefect_reindex]
    have hnonneg : 0 ≤ quittingSingletonCapDefect reward
        flow.forward.capLimit outsideZero := by
      exact sub_nonneg.mpr (flow.forward.singleton_le_capLimit outsideZero)
    exact lt_of_le_of_ne hnonneg fun hzero ↦
      houtsideZeroNotMem ((flow.forward.mem_bindingFinset_iff_capDefect_eq_zero
        outsideZero).2 hzero.symm)
  have hdefectOne : 0 < quittingSingletonCapDefect normalizedReward
      normalizedLimit 1 := by
    rw [show (1 : Fin 4) = e outsideOne from (e.apply_symm_apply 1).symm]
    rw [quittingSingletonCapDefect_reindex]
    have hnonneg : 0 ≤ quittingSingletonCapDefect reward
        flow.forward.capLimit outsideOne := by
      exact sub_nonneg.mpr (flow.forward.singleton_le_capLimit outsideOne)
    exact lt_of_le_of_ne hnonneg fun hzero ↦
      houtsideOneNotMem ((flow.forward.mem_bindingFinset_iff_capDefect_eq_zero
        outsideOne).2 hzero.symm)
  have hcrossTwoOriginal :
      0 < quittingSingletonCollisionGain reward second first :=
    flow.forward.quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two
      hunique hcard hsecondMem hfirstMem hne
  have hcrossThreeOriginal :
      0 < quittingSingletonCollisionGain reward first second :=
    flow.forward.quittingSingletonCollisionGain_pos_of_bindingFinset_card_eq_two
      hunique hcard hfirstMem hsecondMem hne.symm
  have hcrossTwo : 0 < quittingSingletonCollisionGain normalizedReward 3 2 := by
    rw [show (3 : Fin 4) = e second from heSecond.symm,
      show (2 : Fin 4) = e first from heFirst.symm,
      quittingSingletonCollisionGain_reindex]
    exact hcrossTwoOriginal
  have hcrossThree : 0 <
      quittingSingletonCollisionGain normalizedReward 2 3 := by
    rw [show (2 : Fin 4) = e first from heFirst.symm,
      show (3 : Fin 4) = e second from heSecond.symm,
      quittingSingletonCollisionGain_reindex]
    exact hcrossThreeOriginal
  let gap := min
    (quittingSingletonCapDefect normalizedReward normalizedLimit 0)
    (quittingSingletonCapDefect normalizedReward normalizedLimit 1)
  have hgap : 0 < gap := lt_min hdefectZero hdefectOne
  let normalizedCap : ℕ → Payoff (Fin 4) := fun time ↦
    quittingPayoffReindex e (flow.forward.pair time).2
  have hdefectZeroTendsto : Tendsto (fun time ↦
      quittingSingletonCapDefect normalizedReward (normalizedCap time) 0)
      atTop (nhds (quittingSingletonCapDefect normalizedReward
        normalizedLimit 0)) := by
    have hcap : Tendsto (fun time ↦ normalizedCap time 0) atTop
        (nhds (normalizedLimit 0)) := by
      simpa [normalizedCap, normalizedLimit, outsideZero] using
        flow.forward.cap_tendsto outsideZero
    simpa [quittingSingletonCapDefect] using hcap.sub_const
      (normalizedReward (quittingSingletonTerminal 0) 0)
  have hdefectOneTendsto : Tendsto (fun time ↦
      quittingSingletonCapDefect normalizedReward (normalizedCap time) 1)
      atTop (nhds (quittingSingletonCapDefect normalizedReward
        normalizedLimit 1)) := by
    have hcap : Tendsto (fun time ↦ normalizedCap time 1) atTop
        (nhds (normalizedLimit 1)) := by
      simpa [normalizedCap, normalizedLimit, outsideOne] using
        flow.forward.cap_tendsto outsideOne
    simpa [quittingSingletonCapDefect] using hcap.sub_const
      (normalizedReward (quittingSingletonTerminal 1) 1)
  have habsorptionTendsto : Tendsto (fun time ↦
      quittingRootAbsorptionMass (flow.forward.root time)) atTop (nhds 0) :=
    flow.forward.absorption_summable.tendsto_atTop_zero
  have heventuallySmall : ∀ᶠ time in atTop,
      quittingRootAbsorptionMass (flow.forward.root time) < 1 / 3 :=
    (tendsto_order.1 habsorptionTendsto).2 (1 / 3) (by norm_num)
  have heventuallyScaled : ∀ᶠ time in atTop,
      36 * quittingRewardBound reward *
          quittingRootAbsorptionMass (flow.forward.root time) < gap / 2 := by
    have hscaled := habsorptionTendsto.const_mul
      (36 * quittingRewardBound reward)
    exact (tendsto_order.1 hscaled).2 (gap / 2) (by linarith)
  have heventuallyDefectZero : ∀ᶠ time in atTop,
      3 * gap / 4 <
        quittingSingletonCapDefect normalizedReward (normalizedCap time) 0 := by
    apply (tendsto_order.1 hdefectZeroTendsto).1
    have hle : gap ≤ quittingSingletonCapDefect normalizedReward
        normalizedLimit 0 := min_le_left _ _
    linarith
  have heventuallyDefectOne : ∀ᶠ time in atTop,
      3 * gap / 4 <
        quittingSingletonCapDefect normalizedReward (normalizedCap time) 1 := by
    apply (tendsto_order.1 hdefectOneTendsto).1
    have hle : gap ≤ quittingSingletonCapDefect normalizedReward
        normalizedLimit 1 := min_le_right _ _
    linarith
  have heventually : ∀ᶠ time in atTop,
      (∀ who, 0 < flow.forward.currentHazard time who →
        who ∈ flow.forward.bindingFinset) ∧
      quittingRootAbsorptionMass (flow.forward.root time) < 1 / 3 ∧
      36 * quittingRewardBound reward *
          quittingRootAbsorptionMass (flow.forward.root time) < gap / 2 ∧
      3 * gap / 4 < quittingSingletonCapDefect normalizedReward
          (normalizedCap time) 0 ∧
      3 * gap / 4 < quittingSingletonCapDefect normalizedReward
          (normalizedCap time) 1 := by
    filter_upwards [flow.eventually_currentHazard_supported_binding,
      heventuallySmall, heventuallyScaled, heventuallyDefectZero,
      heventuallyDefectOne] with time hsupported hsmall hscaled hzero hone
    exact ⟨hsupported, hsmall, hscaled, hzero, hone⟩
  obtain ⟨time, hsupported, hsmallAbsorption, hscaledAbsorption,
      hfiniteDefectZero, hfiniteDefectOne⟩ := heventually.exists
  let selectedRoot := quittingRootReindex e (flow.forward.root time)
  let bridge := quittingEndpointNashBoxBridge normalizedReward (normalizedCap time)
  let selected : UnitCube (Fin 4) := bridge.rootEquiv.symm selectedRoot
  let scale := quittingRootAbsorptionMass (flow.forward.root time)
  have hscale : 0 < scale := by
    have htotal := flow.forward.totalHazard_pos time
    have hzero := quitProbability_le_quittingRootAbsorptionMass
      (flow.forward.root time) (0 : Fin 4)
    have hone := quitProbability_le_quittingRootAbsorptionMass
      (flow.forward.root time) (1 : Fin 4)
    have htwo := quitProbability_le_quittingRootAbsorptionMass
      (flow.forward.root time) (2 : Fin 4)
    have hthree := quitProbability_le_quittingRootAbsorptionMass
      (flow.forward.root time) (3 : Fin 4)
    rw [Fin.sum_univ_four] at htotal
    change quittingRootQuitRates (flow.forward.root time) 0 ≤
      quittingRootAbsorptionMass (flow.forward.root time) at hzero
    change quittingRootQuitRates (flow.forward.root time) 1 ≤
      quittingRootAbsorptionMass (flow.forward.root time) at hone
    change quittingRootQuitRates (flow.forward.root time) 2 ≤
      quittingRootAbsorptionMass (flow.forward.root time) at htwo
    change quittingRootQuitRates (flow.forward.root time) 3 ≤
      quittingRootAbsorptionMass (flow.forward.root time) at hthree
    exact lt_of_not_ge fun hnonpos ↦ by
      dsimp only [scale] at hnonpos
      linarith
  have hsmall : 3 * scale < 1 := by
    dsimp only [scale]
    linarith
  have hbridgeSelected : bridge.rootEquiv selected = selectedRoot :=
    bridge.rootEquiv.apply_symm_apply selectedRoot
  have hselectedCoordinate (who : Fin 4) :
      (selected who : ℝ) = quittingRootQuitRates selectedRoot who := by
    rw [← bridge.quitProbability_eq selected who, hbridgeSelected]
    rfl
  have hcurrentOutsideZero :
      flow.forward.currentHazard time outsideZero = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      exact houtsideZeroNotMem (hsupported outsideZero hpositive)
    · exact flow.forward.currentHazard_nonneg time outsideZero
  have hcurrentOutsideOne :
      flow.forward.currentHazard time outsideOne = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hpositive
      exact houtsideOneNotMem (hsupported outsideOne hpositive)
    · exact flow.forward.currentHazard_nonneg time outsideOne
  have hrateOutsideZero :
      quittingRootQuitRates (flow.forward.root time) outsideZero = 0 := by
    rw [flow.forward.quitRate_eq_totalHazard_mul_currentHazard,
      hcurrentOutsideZero, mul_zero]
  have hrateOutsideOne :
      quittingRootQuitRates (flow.forward.root time) outsideOne = 0 := by
    rw [flow.forward.quitRate_eq_totalHazard_mul_currentHazard,
      hcurrentOutsideOne, mul_zero]
  have hselectedZero : (selected 0 : ℝ) = 0 := by
    rw [hselectedCoordinate]
    dsimp only [selectedRoot, quittingRootQuitRates, quittingRootReindex]
    simpa [outsideZero, quittingRootQuitRates] using hrateOutsideZero
  have hselectedOne : (selected 1 : ℝ) = 0 := by
    rw [hselectedCoordinate]
    dsimp only [selectedRoot, quittingRootQuitRates, quittingRootReindex]
    simpa [outsideOne, quittingRootQuitRates] using hrateOutsideOne
  have hselectedActive : 0 < (selected 2 : ℝ) + (selected 3 : ℝ) := by
    have hsum : (∑ who, quittingRootQuitRates selectedRoot who) =
        flow.forward.totalHazard time := by
      unfold selectedRoot quittingRootReindex
      rw [QuittingForwardExactCapTail.totalHazard]
      exact Equiv.sum_comp e.symm
        (quittingRootQuitRates (flow.forward.root time))
    have htotal : 0 < flow.forward.totalHazard time :=
      flow.forward.totalHazard_pos time
    rw [← hsum, Fin.sum_univ_four] at htotal
    have hzeroRate : quittingRootQuitRates selectedRoot 0 = 0 := by
      rw [← hselectedCoordinate]
      exact hselectedZero
    have honeRate : quittingRootQuitRates selectedRoot 1 = 0 := by
      rw [← hselectedCoordinate]
      exact hselectedOne
    rw [hselectedCoordinate, hselectedCoordinate]
    linarith
  have hselectedSolution : bridge.problem.IsSolution selected := by
    rw [bridge.isSolution_iff_isZeroQuittingRootNash]
    rw [hbridgeSelected]
    exact (isZeroQuittingRootNash_reindex_iff e reward
      (flow.forward.pair time).2 (flow.forward.root time)).2
        (flow.forward.exactNash time)
  have hsolutions : ∀ point, bridge.problem.IsSolution point →
      ∀ who, (point who : ℝ) ≤ scale := by
    intro point hpoint who
    let candidate : Fin 4 → PMF Bool := fun player ↦
      bridge.rootEquiv point (e player)
    have hreindex : quittingRootReindex e candidate = bridge.rootEquiv point := by
      funext player
      simp [candidate]
    have hnashNormalized : IsεQuittingRootNash normalizedReward
        (normalizedCap time) 0 (bridge.rootEquiv point) :=
      (bridge.isSolution_iff_isZeroQuittingRootNash point).1 hpoint
    have hnashOriginal : IsεQuittingRootNash reward
        (flow.forward.pair time).2 0 candidate := by
      apply (isZeroQuittingRootNash_reindex_iff e reward
        (flow.forward.pair time).2 candidate).1
      simpa [normalizedReward, normalizedCap, hreindex] using hnashNormalized
    have hmax := FinFourStrictRayForwardExactCapTail.root_maximal
      packet flow time candidate hnashOriginal
    have hcoordinate := quitProbability_le_quittingRootAbsorptionMass
      candidate (e.symm who)
    rw [← bridge.quitProbability_eq point who]
    change quittingRootQuitRates (bridge.rootEquiv point) who ≤ scale
    have hcandidateCoordinate :
        quittingRootQuitRates candidate (e.symm who) =
          quittingRootQuitRates (bridge.rootEquiv point) who := by
      simp [candidate, quittingRootQuitRates]
    rw [← hcandidateCoordinate]
    exact hcoordinate.trans (hmax.trans_eq rfl)
  have hnormalizedRewardBound : ∀ terminal player,
      |normalizedReward terminal player| ≤ quittingRewardBound reward := by
    intro terminal player
    exact abs_reward_le_quittingRewardBound reward
      ((quittingCoalitionEquiv e).symm terminal) (e.symm player)
  have horiginalCapBox := quittingTerminalSemanticCarrier_mem_box reward
    (flow.forward.pair time) (abs_reward_le_quittingRewardBound reward)
    (flow.forward.pair_mem time)
  have hnormalizedCapBound : ∀ player,
      |normalizedCap time player| ≤ quittingRewardBound reward := by
    intro player
    rw [abs_le]
    exact ⟨horiginalCapBox.2.1 (e.symm player),
      horiginalCapBox.2.2 (e.symm player)⟩
  have hleadingRegion : bridge.problem.IsLeadingNegativeRegion
      (Metric.ball unitCubeOrigin (3 * scale)) := by
    constructor
    · intro point hpoint player
      have hcoordinate := (dist_unitCubeOrigin_lt_iff point
        (by linarith : 0 < 3 * scale)).1 hpoint player
      linarith
    · intro point hpoint player hplayer
      have hcoordinates := (dist_unitCubeOrigin_lt_iff point
        (by linarith : 0 < 3 * scale)).1 hpoint
      let pointRoot := bridge.rootEquiv point
      have htv : quittingRootOpponentTVSum pointRoot
          (quittingAllContinueRoot : Fin 4 → PMF Bool) player < 9 * scale := by
        rcases finFour_cases player with rfl | rfl | rfl | rfl
        · simp [quittingRootOpponentTVSum,
            Math.Probability.pmfTV_bool_eq_abs_apply_true,
            quittingAllContinueRoot, pointRoot, bridge.quitProbability_eq]
          rw [Fin.sum_univ_four]
          repeat' rw [abs_of_nonneg (point _).property.1]
          linarith [hcoordinates 1, hcoordinates 2, hcoordinates 3]
        · simp [quittingRootOpponentTVSum,
            Math.Probability.pmfTV_bool_eq_abs_apply_true,
            quittingAllContinueRoot, pointRoot, bridge.quitProbability_eq]
          rw [Fin.sum_univ_four]
          repeat' rw [abs_of_nonneg (point _).property.1]
          linarith [hcoordinates 0, hcoordinates 2, hcoordinates 3]
        · omega
        · omega
      have hstability :=
        abs_quittingRootEndpointDifference_sub_le_opponentTVSum
          normalizedReward (normalizedCap time) pointRoot
            (quittingAllContinueRoot : Fin 4 → PMF Bool) player
              hnormalizedRewardBound hnormalizedCapBound
      have hboundNonneg := quittingRewardBound_nonneg reward
      have hperturb :
          |quittingRootEndpointDifference normalizedReward (normalizedCap time)
                pointRoot player -
              quittingRootEndpointDifference normalizedReward (normalizedCap time)
                (quittingAllContinueRoot : Fin 4 → PMF Bool) player| ≤
            36 * quittingRewardBound reward * scale := by
        refine hstability.trans ?_
        have hmul := mul_le_mul_of_nonneg_left htv.le (by positivity :
          0 ≤ 4 * quittingRewardBound reward)
        convert hmul using 1
        ring
      rw [bridge.gain_eq]
      have hbase : quittingRootEndpointDifference normalizedReward
          (normalizedCap time)
          (quittingAllContinueRoot : Fin 4 → PMF Bool) player =
          -quittingSingletonCapDefect normalizedReward
            (normalizedCap time) player := by
        rw [quittingRootEndpointDifference_allContinueRoot]
        unfold quittingSingletonCapDefect
        ring
      have hscaled : 36 * quittingRewardBound reward * scale < gap / 2 := by
        exact hscaledAbsorption
      rcases finFour_cases player with rfl | rfl | rfl | rfl
      · rw [hbase] at hperturb
        have hupper := (abs_le.mp hperturb).2
        linarith
      · rw [hbase] at hperturb
        have hupper := (abs_le.mp hperturb).2
        linarith
      · omega
      · omega
  exact false_of_localized_binding_pair bridge.problem selected scale hscale
    hsmall hselectedSolution hsolutions hselectedZero hselectedOne
    hselectedActive
    (quittingSingletonCapDefect normalizedReward (normalizedCap time) 2)
    (quittingSingletonCollisionGain normalizedReward 3 2)
    (quittingSingletonCapDefect normalizedReward (normalizedCap time) 3)
    (quittingSingletonCollisionGain normalizedReward 2 3)
    hcrossTwo hcrossThree hleadingRegion
    (canonicalBridge_hasAffineBindingFaceGain normalizedReward
      (normalizedCap time) (Metric.ball unitCubeOrigin (3 * scale)))

/-- Under limiting all-Continue uniqueness, the actual strict ray has either
full binding support or exactly three binding coordinates. -/
theorem FinFourStrictRayForwardExactCapTail.bindingFinset_eq_univ_or_card_eq_three
    (flow : FinFourStrictRayForwardExactCapTail packet)
    (hunique : HasUniqueAllContinueAtCapLimit flow) :
    flow.forward.bindingFinset = Finset.univ ∨
      flow.forward.bindingFinset.card = 3 := by
  by_cases huniv : flow.forward.bindingFinset = Finset.univ
  · exact Or.inl huniv
  right
  have hstrict : flow.forward.bindingFinset ⊂ (Finset.univ : Finset (Fin 4)) :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, huniv⟩
  have hcardLt : flow.forward.bindingFinset.card < 4 := by
    simpa using Finset.card_lt_card hstrict
  have hcardPos : 0 < flow.forward.bindingFinset.card :=
    Finset.card_pos.mpr
      (FinFourBindingPairParityCertificate.bindingFinset_nonempty flow)
  have hcardNeOne :=
    flow.forward.bindingFinset_card_ne_one_of_unique_allContinue hunique
  have hcardNeTwo := flow.bindingFinset_card_ne_two hunique
  omega

namespace FinFourStrictRayForwardExactCapTail

/-- Certificate-free source-facing trichotomy for one actual strict maximal
ray.  Failure of limiting uniqueness is returned as a literal positive exact
root at the same limiting cap. -/
theorem positiveAbsorptionExactRoot_at_capLimit_or_bindingFinset_eq_univ_or_card_eq_three
    (flow : FinFourStrictRayForwardExactCapTail packet) :
    (∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward flow.forward.capLimit 0 root ∧
        0 < quittingRootAbsorptionMass root) ∨
      flow.forward.bindingFinset = Finset.univ ∨
        flow.forward.bindingFinset.card = 3 := by
  by_cases hnoPositive : ¬ ∃ root : Fin 4 → PMF Bool,
      IsεQuittingRootNash reward flow.forward.capLimit 0 root ∧
        0 < quittingRootAbsorptionMass root
  · right
    exact flow.bindingFinset_eq_univ_or_card_eq_three
      (flow.uniqueAllContinue_of_noPositiveRoot hnoPositive)
  · left
    exact not_not.mp hnoPositive

end FinFourStrictRayForwardExactCapTail

end FinFourOwnerCompressedMinimumReturnForcedPairPacket

end GameTheory
