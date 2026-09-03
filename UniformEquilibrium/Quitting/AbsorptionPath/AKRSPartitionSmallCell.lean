/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.PMFProduct.SmallCellProductization
import UniformEquilibrium.Quitting.AbsorptionPath.AKRSPartition
import UniformEquilibrium.Quitting.Classification.Existence.WellSupportedAbsorbingSequence
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Product rows for the canonical AKRS partition

Large jumps are copied literally.  Every selected small cell is converted to
an exact-absorption independent row with the same singleton support and an
explicit coordinate error.  The small-cell parameter is exactly
`1 / (resolution - 1)`, the absorption odds associated with the partition's
`1 / resolution` threshold.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace SmallCellProductization

/-- Convert the real Bernoulli parameters produced by the game-independent
small-cell theorem into literal quitting roots. -/
def quittingRoot {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) : ι → PMF Bool :=
  fun player => quittingHazardCoin (packet.root player)
    (packet.root_nonneg player) (packet.root_lt_one player).le

omit [Nonempty ι] in
@[simp] theorem quittingRoot_true_toReal
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) (player : ι) :
    (packet.quittingRoot player true).toReal = packet.root player := by
  simp [quittingRoot]

omit [Nonempty ι] in
@[simp] theorem quittingRoot_false_toReal
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) (player : ι) :
    (packet.quittingRoot player false).toReal = 1 - packet.root player := by
  simp [quittingRoot]

omit [Nonempty ι] in
theorem quittingRootCoalitionMass
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law)
    (coalition : Finset ι) :
    GameTheory.quittingRootCoalitionMass packet.quittingRoot coalition =
      Math.PMFProduct.coalitionMass packet.root coalition := by
  unfold GameTheory.quittingRootCoalitionMass quittingRootQuitRates
  congr 1
  funext player
  exact packet.quittingRoot_true_toReal player

omit [Nonempty ι] in
/-- The converted row uses Quit exactly on the singleton support of the
source cell. -/
theorem quittingRoot_true_pos_iff_singletonMass_pos
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) (player : ι) :
    0 < (packet.quittingRoot player true).toReal ↔ 0 < law {player} := by
  rw [packet.quittingRoot_true_toReal]
  exact packet.quit_pos_iff_singletonMass_pos player

omit [Nonempty ι] in
/-- Continue remains in support at every small-cell row. -/
theorem quittingRoot_false_toReal_pos
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) (player : ι) :
    0 < (packet.quittingRoot player false).toReal := by
  rw [packet.quittingRoot_false_toReal]
  exact sub_pos.mpr (packet.root_lt_one player)

omit [Nonempty ι] in
theorem quittingRoot_absorption_exact
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law) :
    quittingRootAbsorptionMass packet.quittingRoot = 1 - law ∅ := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simpa only [packet.quittingRoot_false_toReal,
    Math.PMFProduct.continueMass] using packet.absorption_exact

omit [Nonempty ι] in
theorem quittingRoot_coalition_coordinate_error
    {ε : ℝ} {law : Finset ι → ℝ}
    (packet : SmallCellProductization ε law)
    (coalition : Finset ι) (hcoalition : coalition.Nonempty) :
    |GameTheory.quittingRootCoalitionMass packet.quittingRoot coalition -
        law coalition| ≤
      akrsSmallCellCoordinateConstant ι * ε * (1 - law ∅) := by
  rw [packet.quittingRootCoalitionMass coalition]
  exact packet.coalition_coordinate_error coalition hcoalition

end SmallCellProductization

omit [Nonempty ι] in
/-- A small independent Bernoulli row has the incident-collision estimate
used at every discrete jump in the AKRS partition.  The proof keeps one
distinguished additional quitter and bounds all remaining odds by one. -/
theorem quittingRootCoalitionMass_le_absorptionOdds_mul_singleton
    (root : ι → PMF Bool) {δ : ℝ}
    (hδnonneg : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (habsorption : quittingRootAbsorptionMass root ≤ δ)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    quittingRootCoalitionMass root coalition ≤
      (δ / (1 - δ)) * quittingRootCoalitionMass root {player} := by
  let x : ι → ℝ := fun who ↦ (root who true).toReal
  let others := coalition.erase player
  have hothersNonempty : others.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsubset : coalition ⊆ {player} := by
      intro who hwho
      by_contra hne
      have hnePlayer : who ≠ player := by
        simpa only [Finset.mem_singleton] using hne
      have hwhoOthers : who ∈ others := by
        exact Finset.mem_erase.mpr ⟨hnePlayer, hwho⟩
      rw [hempty] at hwhoOthers
      simp at hwhoOthers
    have hcardLe : coalition.card ≤ 1 := by
      exact (Finset.card_le_card hsubset).trans_eq (Finset.card_singleton player)
    omega
  obtain ⟨other, hother⟩ := hothersNonempty
  have hδltOne : δ < 1 := hδhalf.trans_lt (by norm_num)
  have hdenominatorPos : 0 < 1 - δ := sub_pos.mpr hδltOne
  have hxnonneg (who : ι) : 0 ≤ x who := ENNReal.toReal_nonneg
  have hxleδ (who : ι) : x who ≤ δ := by
    exact (quittingQuitProbability_le_absorptionMass root who).trans
      habsorption
  have hxleone (who : ι) : x who ≤ 1 :=
    (hxleδ who).trans (hδhalf.trans (by norm_num))
  have hxlecontinue (who : ι) : x who ≤ 1 - x who := by
    linarith [hxleδ who, hδhalf]
  have hotherOdds : x other ≤ (δ / (1 - δ)) * (1 - x other) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hdenominatorPos).2
    have hxother := hxleδ other
    nlinarith [hxnonneg other]
  have hrestNonneg :
      0 ≤ ∏ who ∈ others.erase other, x who :=
    Finset.prod_nonneg fun who _ ↦ hxnonneg who
  have hrestComparison :
      (∏ who ∈ others.erase other, x who) ≤
        ∏ who ∈ others.erase other, (1 - x who) := by
    exact Finset.prod_le_prod
      (fun who _ ↦ hxnonneg who)
      (fun who _ ↦ hxlecontinue who)
  have hcontinueRestNonneg :
      0 ≤ ∏ who ∈ others.erase other, (1 - x who) :=
    Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hxleone who)
  have hoddsNonneg : 0 ≤ δ / (1 - δ) :=
    div_nonneg hδnonneg hdenominatorPos.le
  have hothersProduct :
      (∏ who ∈ others, x who) ≤
        (δ / (1 - δ)) * ∏ who ∈ others, (1 - x who) := by
    rw [show (∏ who ∈ others, x who) =
        x other * ∏ who ∈ others.erase other, x who by
      simpa [mul_comm] using (Finset.prod_erase_mul others x hother).symm]
    rw [show (∏ who ∈ others, (1 - x who)) =
        (1 - x other) * ∏ who ∈ others.erase other, (1 - x who) by
      simpa [mul_comm] using
        (Finset.prod_erase_mul others (fun who ↦ 1 - x who) hother).symm]
    calc
      x other * ∏ who ∈ others.erase other, x who ≤
          x other * ∏ who ∈ others.erase other, (1 - x who) :=
        mul_le_mul_of_nonneg_left hrestComparison (hxnonneg other)
      _ ≤ ((δ / (1 - δ)) * (1 - x other)) *
          ∏ who ∈ others.erase other, (1 - x who) :=
        mul_le_mul_of_nonneg_right hotherOdds hcontinueRestNonneg
      _ = (δ / (1 - δ)) *
          ((1 - x other) *
            ∏ who ∈ others.erase other, (1 - x who)) := by ring
  have hinside :
      (∏ who ∈ coalition, x who) =
        x player * ∏ who ∈ others, x who := by
    simpa [others, mul_comm] using
      (Finset.prod_erase_mul coalition x hplayer).symm
  have hsingletonComplement :
      ({player} : Finset ι)ᶜ = others ∪ coalitionᶜ := by
    ext who
    simp only [Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_union, Finset.mem_erase, others]
    constructor
    · intro hne
      by_cases hwho : who ∈ coalition
      · exact Or.inl ⟨hne, hwho⟩
      · exact Or.inr hwho
    · rintro (⟨hne, _⟩ | hnot)
      · exact hne
      · exact fun heq ↦ hnot (heq ▸ hplayer)
  have hdisjoint : Disjoint others coalitionᶜ := by
    refine Finset.disjoint_left.mpr ?_
    intro who hwho hcomplement
    have hnotCoalition : who ∉ coalition := by
      simpa only [Finset.mem_compl] using hcomplement
    exact hnotCoalition (Finset.mem_erase.mp hwho).2
  have hsingletonOutside :
      (∏ who ∈ ({player} : Finset ι)ᶜ, (1 - x who)) =
        (∏ who ∈ others, (1 - x who)) *
          ∏ who ∈ coalitionᶜ, (1 - x who) := by
    rw [hsingletonComplement, Finset.prod_union hdisjoint]
  have hcommonNonneg :
      0 ≤ x player * ∏ who ∈ coalitionᶜ, (1 - x who) :=
    mul_nonneg (hxnonneg player) <|
      Finset.prod_nonneg fun who _ ↦ sub_nonneg.mpr (hxleone who)
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  change
    ((∏ who ∈ coalition, x who) *
      ∏ who ∈ coalitionᶜ, (1 - x who)) ≤
      (δ / (1 - δ)) *
        ((∏ who ∈ ({player} : Finset ι), x who) *
          ∏ who ∈ ({player} : Finset ι)ᶜ, (1 - x who))
  rw [hinside, hsingletonOutside]
  simp only [Finset.prod_singleton]
  calc
    (x player * ∏ who ∈ others, x who) *
          ∏ who ∈ coalitionᶜ, (1 - x who) =
        (x player * ∏ who ∈ coalitionᶜ, (1 - x who)) *
          ∏ who ∈ others, x who := by ring
    _ ≤ (x player * ∏ who ∈ coalitionᶜ, (1 - x who)) *
          ((δ / (1 - δ)) *
            ∏ who ∈ others, (1 - x who)) :=
      mul_le_mul_of_nonneg_left hothersProduct hcommonNonneg
    _ = (δ / (1 - δ)) *
        (x player * ((∏ who ∈ others, (1 - x who)) *
          ∏ who ∈ coalitionᶜ, (1 - x who))) := by ring

namespace QuittingAbsorptionPath

omit [Nonempty ι] in
/-- A jump row is copied literally from the path's uniquely determined
product root.  Under the no-terminal-jump hypothesis, exact path sequential
perfection makes this copied row support-optimal at zero error against the
path continuation immediately after the jump. -/
theorem copiedJumpRoot_supportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (path : AbsorptionPath (ι := ι))
    (hperfect : IsSequentiallyPerfectAbsorptionPath reward path 0)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    {time : ℝ} (htime : time ∈ pathJumps path.1) :
    IsQuittingRootSupportApproxNash reward
      (absorptionPathPayoff reward path time) 0
      (absorptionPathJumpRoot path time) := by
  have hrow : QuittingRowεPerfect reward
      (absorptionPathPayoff reward path time)
      (absorptionPathJumpRoot path time) 0 := by
    intro who
    exact (hperfect who).1 time htime (hnoTerminalJump time htime)
  simpa using supportApproxNash_of_quittingRowεPerfect hrow

omit [Nonempty ι] in
/-- The copied large-jump row has exactly the normalized path-jump law; no
metric approximation or support enlargement is used on this arm. -/
theorem copiedJumpRoot_coalitionMass
    (path : AbsorptionPath (ι := ι))
    {time : ℝ} (htime : time ∈ pathJumps path.1)
    (coalition : {S : Finset ι // S.Nonempty}) :
    quittingRootCoalitionMass (absorptionPathJumpRoot path time) coalition.1 =
      pathJump path.1 time coalition / (1 - time) := by
  exact (absorptionPathJumpRoot_relation path htime coalition).symm

omit [Nonempty ι] in
/-- One-stage absorption is the sum of all nonempty exact coalition masses. -/
theorem quittingRootAbsorptionMass_eq_sum_coalitionMass
    (root : ι → PMF Bool) :
    quittingRootAbsorptionMass root =
      ∑ coalition : {S : Finset ι // S.Nonempty},
        quittingRootCoalitionMass root coalition.1 := by
  rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset ι))]
  · rw [quittingRootAbsorptionMass,
      quittingRootCoalitionMass_sum_nonempty]
  · intro coalition
    simp [Finset.nonempty_iff_ne_empty]

/-- One small cell in the published AKRS partition.  The collision field is
the exact hypothesis established by the partition: a multi-quitter cell mass
is at most `ε` times every incident singleton mass. -/
structure SmallPathCell (path : CadlagPath (ι := ι)) (ε : ℝ) where
  start : ℝ
  stop : ℝ
  start_mem : start ∈ Set.Icc (0 : ℝ) 1
  stop_mem : stop ∈ Set.Icc (0 : ℝ) 1
  start_lt_stop : start < stop
  start_lt_one : start < 1
  start_le_leftTotal : start ≤ pathLeftTotal path start
  leftTotal_stop_le_one : pathLeftTotal path stop ≤ 1
  absorption_le : pathCellAbsorption path start stop ≤ ε
  collision_le_singleton : ∀ coalition player,
    2 ≤ coalition.card → player ∈ coalition →
      pathCellLaw path start stop coalition ≤
        ε * pathCellLaw path start stop {player}

namespace SmallPathCell

omit [DecidableEq ι] [Nonempty ι] in
theorem law_nonneg {path : CadlagPath (ι := ι)} {ε : ℝ}
    (cell : SmallPathCell path ε) (coalition : Finset ι) :
    0 ≤ pathCellLaw path cell.start cell.stop coalition :=
  pathCellLaw_nonneg path cell.start_mem cell.stop_mem
    cell.start_lt_stop.le cell.start_lt_one cell.start_le_leftTotal
    cell.leftTotal_stop_le_one coalition

omit [DecidableEq ι] [Nonempty ι] in
theorem law_absorption {path : CadlagPath (ι := ι)} {ε : ℝ}
    (cell : SmallPathCell path ε) :
    1 - pathCellLaw path cell.start cell.stop ∅ =
      pathCellAbsorption path cell.start cell.stop := by
  rw [pathCellLaw_empty]
  ring

/-- The checked small-cell theorem selects an exact-absorption,
support-preserving product row for every valid small path cell. -/
theorem nonempty_productization
    {path : CadlagPath (ι := ι)} {ε : ℝ}
    (cell : SmallPathCell path ε) (hεpos : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    Nonempty (SmallCellProductization ε
      (pathCellLaw path cell.start cell.stop)) := by
  apply exists_akrsSmallCellProductization hεpos hεhalf
  · exact cell.law_nonneg
  · exact sum_pathCellLaw path cell.start cell.stop
  · rw [cell.law_absorption]
    exact cell.absorption_le
  · exact cell.collision_le_singleton

end SmallPathCell

/-- Conservative cell parameter for the published product-jump estimate.
A non-large jump has absorption at most `1 / resolution`, hence every
incident collision/singleton odds ratio is at most
`1 / (resolution - 1)`. -/
def partitionSmallCellError (resolution : ℕ) : ℝ :=
  1 / ((resolution : ℝ) - 1)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The partition error is exactly the odds corresponding to conditional
absorption `1 / resolution`. -/
theorem partitionSmallCellError_eq_resolutionAbsorptionOdds
    (resolution : ℕ) (hresolution : 1 < resolution) :
    partitionSmallCellError resolution =
      (1 / (resolution : ℝ)) / (1 - 1 / (resolution : ℝ)) := by
  unfold partitionSmallCellError
  have hresolutionReal : (1 : ℝ) < resolution := by
    exact_mod_cast hresolution
  field_simp [ne_of_gt hresolutionReal, ne_of_gt (by linarith : (0 : ℝ) < resolution)]

/-- Apart from the collision-domination field supplied by the product-root
jump and singleton-derivative measure argument, the non-large branch is
already a valid small path cell with error `1 / resolution`. -/
def smallPathCellOfPartition
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hsmall : pathTotal path.1 start ≤
      partitionProbe resolution start)
    (hcollision : ∀ coalition player,
      2 ≤ coalition.card → player ∈ coalition →
        pathCellLaw path.1 start
            (nextPartitionCut path resolution start) coalition ≤
          partitionSmallCellError resolution *
            pathCellLaw path.1 start
              (nextPartitionCut path resolution start) {player}) :
    SmallPathCell path.1 (partitionSmallCellError resolution) := by
  let stop := nextPartitionCut path resolution start
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartMem : start ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hstart.1, hstart.2.le⟩
  have hstopFromStart := nextPartitionCut_mem_Icc path hpathTotal
    resolution hresolutionOne hstartMem
  have hstopMem : stop ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hstart.1.trans hstopFromStart.1, hstopFromStart.2⟩
  have hstopBoundary : stop ∈ partitionBoundaryTimes path :=
    nextPartitionCut_mem_partitionBoundaryTimes path hpathTotal
      resolution hresolutionOne hstartMem
  have hstopProbe : stop ≤ partitionProbe resolution start :=
    nextPartitionCut_le_probe_of_pathTotal_le path resolution start hsmall
  have hresolutionPos : (0 : ℝ) < resolution := by positivity
  have hresolutionSubPos : (0 : ℝ) < (resolution : ℝ) - 1 := by
    have hresolutionReal : (3 : ℝ) ≤ resolution := by
      exact_mod_cast hresolution
    linarith
  have hdenominatorPos : 0 < 1 - start := sub_pos.mpr hstart.2
  refine {
    start := start
    stop := stop
    start_mem := hstartMem
    stop_mem := hstopMem
    start_lt_stop := lt_nextPartitionCut path hpathTotal resolution
      hresolutionTwo hstart hstartBoundary
    start_lt_one := hstart.2
    start_le_leftTotal := ?_
    leftTotal_stop_le_one := ?_
    absorption_le := ?_
    collision_le_singleton := hcollision
  }
  · rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
      hstartBoundary]
  · rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
      hstopBoundary]
    exact hstopMem.2
  · unfold pathCellAbsorption
    rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path
        hstopBoundary,
      pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstartBoundary]
    have hdifference : stop - start ≤
        (1 - start) / (resolution : ℝ) := by
      unfold partitionProbe at hstopProbe
      linarith
    calc
      (stop - start) / (1 - start) ≤
          ((1 - start) / (resolution : ℝ)) / (1 - start) :=
        (div_le_div_iff_of_pos_right hdenominatorPos).2 hdifference
      _ = 1 / (resolution : ℝ) := by
        field_simp [ne_of_gt hdenominatorPos, ne_of_gt hresolutionPos]
      _ ≤ partitionSmallCellError resolution := by
        unfold partitionSmallCellError
        apply (div_le_div_iff₀ hresolutionPos hresolutionSubPos).2
        linarith

omit [Nonempty ι] in
/-- The exact published per-stage dichotomy, with the collision field kept
literal on the small-cell branch. -/
theorem copiedJump_or_smallPathCellOfPartition
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hcollision : ∀ coalition player,
      2 ≤ coalition.card → player ∈ coalition →
        pathCellLaw path.1 start
            (nextPartitionCut path resolution start) coalition ≤
          partitionSmallCellError resolution *
            pathCellLaw path.1 start
              (nextPartitionCut path resolution start) {player}) :
    (start ∈ pathJumps path.1 ∧
      nextPartitionCut path resolution start = pathTotal path.1 start) ∨
      Nonempty (SmallPathCell path.1 (partitionSmallCellError resolution)) := by
  by_cases hlarge : partitionProbe resolution start < pathTotal path.1 start
  · exact Or.inl ⟨
      mem_pathJumps_of_probe_lt_pathTotal_of_boundary path resolution
        hstartBoundary hlarge,
      nextPartitionCut_eq_pathTotal_of_probe_lt path resolution start hlarge⟩
  · exact Or.inr ⟨smallPathCellOfPartition path hpathTotal resolution
      hresolution hstart hstartBoundary (not_lt.mp hlarge) hcollision⟩

omit [Nonempty ι] in
/-- A copied jump row has exactly the conditional absorption of its partition
cell. -/
theorem copiedJumpRoot_absorption_eq_pathCellAbsorption
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    {start : ℝ} (hstart : start ∈ pathJumps path.1)
    {stop : ℝ} (hstop : stop = pathTotal path.1 start) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path start) =
      pathCellAbsorption path.1 start stop := by
  rw [quittingRootAbsorptionMass_eq_sum_coalitionMass]
  simp_rw [copiedJumpRoot_coalitionMass path hstart]
  rw [← Finset.sum_div]
  unfold pathCellAbsorption
  have hstopBoundary : stop ∈ partitionBoundaryTimes path := by
    rw [hstop]
    exact pathTotal_mem_partitionBoundaryTimes path hpathTotal hstart.1
  rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
    pathLeftTotal_eq_of_mem_pathJumps path hstart]
  congr 1
  rw [hstop, ← pathTotal_sub_pathLeftTotal_eq_sum_pathJump,
    pathLeftTotal_eq_of_mem_pathJumps path hstart]

omit [Nonempty ι] in
/-- A jump lying below the resolution probe has conditional absorption at
most `1 / resolution`. This is the quantitative product-root jump input
before applying the product-row odds estimate. -/
theorem absorptionPathJumpRoot_absorption_le_inv_resolution_of_probe
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {time : ℝ} (htime : time ∈ pathJumps path.1)
    (hprobe : pathTotal path.1 time ≤ partitionProbe resolution time) :
    quittingRootAbsorptionMass (absorptionPathJumpRoot path time) ≤
      1 / (resolution : ℝ) := by
  have htimeLtOne : time < 1 :=
    (lt_pathTotal_of_mem_pathJumps path htime).trans_le
      (hpathTotal time htime.1)
  have hresolutionPos : (0 : ℝ) < resolution := by
    exact_mod_cast (Nat.zero_lt_of_lt hresolution)
  rw [copiedJumpRoot_absorption_eq_pathCellAbsorption path hpathTotal
    htime rfl]
  unfold pathCellAbsorption
  have htotalBoundary : pathTotal path.1 time ∈
      partitionBoundaryTimes path :=
    pathTotal_mem_partitionBoundaryTimes path hpathTotal htime.1
  rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path htotalBoundary,
    pathLeftTotal_eq_of_mem_pathJumps path htime]
  apply (div_le_iff₀ (sub_pos.mpr htimeLtOne)).2
  unfold partitionProbe at hprobe
  have hscaled :
      pathTotal path.1 time - time ≤
        (1 - time) / (resolution : ℝ) := by
    linarith
  calc
    pathTotal path.1 time - time ≤
        (1 - time) / (resolution : ℝ) := hscaled
    _ = (1 / (resolution : ℝ)) * (1 - time) := by
      field_simp [ne_of_gt hresolutionPos]

omit [Nonempty ι] in
/-- At every non-large path jump, product-root realization gives the exact
incident-collision bound used by the small-cell measure argument. -/
theorem pathJump_le_partitionSmallCellError_mul_singleton_of_probe
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {time : ℝ} (htime : time ∈ pathJumps path.1)
    (hprobe : pathTotal path.1 time ≤ partitionProbe resolution time)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    pathJump path.1 time ⟨coalition,
        Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
      partitionSmallCellError resolution *
        pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionGtOne : 1 < resolution := by omega
  have hresolutionReal : (3 : ℝ) ≤ resolution := by
    exact_mod_cast hresolution
  let δ : ℝ := 1 / (resolution : ℝ)
  have hδnonneg : 0 ≤ δ := by positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp only [δ]
    have hresolutionPos : (0 : ℝ) < resolution := by positivity
    apply (div_le_div_iff₀ hresolutionPos (by norm_num : (0 : ℝ) < 2)).2
    linarith
  have habsorption :
      quittingRootAbsorptionMass (absorptionPathJumpRoot path time) ≤ δ :=
    absorptionPathJumpRoot_absorption_le_inv_resolution_of_probe path
      hpathTotal resolution hresolutionOne htime hprobe
  have hroot :=
    quittingRootCoalitionMass_le_absorptionOdds_mul_singleton
      (absorptionPathJumpRoot path time) hδnonneg hδhalf habsorption
      coalition player hcard hplayer
  have hcoalitionNonempty : coalition.Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)
  have hrelationCoalition := absorptionPathJumpRoot_relation path htime
    ⟨coalition, hcoalitionNonempty⟩
  have hrelationSingleton := absorptionPathJumpRoot_relation path htime
    ⟨{player}, Finset.singleton_nonempty player⟩
  have htimeLtOne : time < 1 :=
    (lt_pathTotal_of_mem_pathJumps path htime).trans_le
      (hpathTotal time htime.1)
  have hdiv :
      pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ / (1 - time) ≤
        partitionSmallCellError resolution *
          (pathJump path.1 time
            ⟨{player}, Finset.singleton_nonempty player⟩ / (1 - time)) := by
    rw [hrelationCoalition, hrelationSingleton]
    rw [partitionSmallCellError_eq_resolutionAbsorptionOdds resolution
      hresolutionGtOne]
    exact hroot
  calc
    pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ =
        (pathJump path.1 time ⟨coalition, hcoalitionNonempty⟩ /
          (1 - time)) * (1 - time) := by
      field_simp [ne_of_gt (sub_pos.mpr htimeLtOne)]
    _ ≤ (partitionSmallCellError resolution *
          (pathJump path.1 time
            ⟨{player}, Finset.singleton_nonempty player⟩ / (1 - time))) *
        (1 - time) :=
      mul_le_mul_of_nonneg_right hdiv (sub_pos.mpr htimeLtOne).le
    _ = partitionSmallCellError resolution *
        pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ := by
      field_simp [ne_of_gt (sub_pos.mpr htimeLtOne)]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The affine resolution probe is monotone in its base point. -/
theorem partitionProbe_mono
    (resolution : ℕ) (hresolution : 1 ≤ resolution)
    {earlier later : ℝ} (hearlerLater : earlier ≤ later) :
    partitionProbe resolution earlier ≤ partitionProbe resolution later := by
  have hresolutionPos : (0 : ℝ) < resolution := by
    exact_mod_cast (Nat.zero_lt_of_lt hresolution)
  have hcoefficient : 0 ≤ 1 - 1 / (resolution : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hresolutionPos).2 <| by
      have hresolutionReal : (1 : ℝ) ≤ resolution := by
        exact_mod_cast hresolution
      simpa only [one_mul] using hresolutionReal
  unfold partitionProbe
  calc
    earlier + (1 - earlier) / (resolution : ℝ) =
        (1 - 1 / (resolution : ℝ)) * earlier +
          1 / (resolution : ℝ) := by ring
    _ ≤ (1 - 1 / (resolution : ℝ)) * later +
          1 / (resolution : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hearlerLater hcoefficient
      linarith
    _ = later + (1 - later) / (resolution : ℝ) := by ring

omit [Nonempty ι] in
/-- Every literal jump inside a selected non-large partition cell satisfies
the conservative incident-collision estimate. -/
theorem pathJump_le_partitionSmallCellError_mul_singleton_of_mem_small_cell
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {start stop time : ℝ}
    (hstop : stop ∈ partitionBoundaryTimes path)
    (hstopProbe : stop ≤ partitionProbe resolution start)
    (htime : time ∈ Set.Ico start stop)
    (htimeJump : time ∈ pathJumps path.1)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    pathJump path.1 time ⟨coalition,
        Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩ ≤
      partitionSmallCellError resolution *
        pathJump path.1 time
          ⟨{player}, Finset.singleton_nonempty player⟩ := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have htotalStop : pathTotal path.1 time ≤ stop :=
    pathTotal_le_of_boundary_lt_boundary path (Or.inl htimeJump) hstop
      htime.2
  have hprobeMono : partitionProbe resolution start ≤
      partitionProbe resolution time :=
    partitionProbe_mono resolution hresolutionOne htime.1
  apply pathJump_le_partitionSmallCellError_mul_singleton_of_probe path
    hpathTotal resolution hresolution htimeJump
  · exact htotalStop.trans (hstopProbe.trans hprobeMono)
  · exact hcard
  · exact hplayer

omit [Nonempty ι] in
/-- The product-root jump estimate and gap-component/singleton-derivative
fencing lemma give collision domination on every selected non-large cell. -/
theorem pathCellLaw_le_partitionSmallCellError_mul_singleton_of_small_partition_cell
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    {start : ℝ} (hstart : start ∈ Set.Ico (0 : ℝ) 1)
    (hstartBoundary : start ∈ partitionBoundaryTimes path)
    (hsmall : pathTotal path.1 start ≤ partitionProbe resolution start)
    (coalition : Finset ι) (player : ι)
    (hcard : 2 ≤ coalition.card) (hplayer : player ∈ coalition) :
    pathCellLaw path.1 start (nextPartitionCut path resolution start)
        coalition ≤
      partitionSmallCellError resolution *
        pathCellLaw path.1 start (nextPartitionCut path resolution start)
          {player} := by
  let stop := nextPartitionCut path resolution start
  let terminal : {S : Finset ι // S.Nonempty} :=
    ⟨coalition, Finset.card_pos.mp
      (lt_of_lt_of_le Nat.zero_lt_two hcard)⟩
  let singleton : {S : Finset ι // S.Nonempty} :=
    ⟨{player}, Finset.singleton_nonempty player⟩
  have hresolutionOne : 1 ≤ resolution := by omega
  have hstartIcc : start ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hstart.1, hstart.2.le⟩
  have hstopFromStart := nextPartitionCut_mem_Icc path hpathTotal
    resolution hresolutionOne hstartIcc
  have hstopIcc : stop ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hstart.1.trans hstopFromStart.1, hstopFromStart.2⟩
  have hstopBoundary : stop ∈ partitionBoundaryTimes path :=
    nextPartitionCut_mem_partitionBoundaryTimes path hpathTotal
      resolution hresolutionOne hstartIcc
  have hstopProbe : stop ≤ partitionProbe resolution start :=
    nextPartitionCut_le_probe_of_pathTotal_le path resolution start hsmall
  have hstartStop : start < stop :=
    lt_nextPartitionCut path hpathTotal resolution (by omega) hstart
      hstartBoundary
  have herrorNonneg : 0 ≤ partitionSmallCellError resolution := by
    unfold partitionSmallCellError
    apply one_div_nonneg.mpr
    have hresolutionReal : (1 : ℝ) ≤ resolution := by
      exact_mod_cast hresolutionOne
    linarith
  have hjumpBound : ∀ time ∈ Set.Ico start stop,
      pathJump path.1 time terminal ≤
        partitionSmallCellError resolution * pathJump path.1 time singleton := by
    intro time htime
    by_cases htimeJump : time ∈ pathJumps path.1
    · simpa only [terminal, singleton] using
        pathJump_le_partitionSmallCellError_mul_singleton_of_mem_small_cell
          path hpathTotal resolution hresolution hstopBoundary hstopProbe
          htime htimeJump coalition player hcard hplayer
    · have htimeIcc : time ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨hstart.1.trans htime.1,
          htime.2.le.trans hstopIcc.2⟩
      have hcoalitionZero : pathJump path.1 time terminal = 0 := by
        by_contra hne
        exact htimeJump ⟨htimeIcc, terminal, hne⟩
      rw [hcoalitionZero]
      exact mul_nonneg herrorNonneg
        (pathJump_nonneg path.1 htimeIcc singleton)
  have hincrement :=
    leftValue_incidentCoalitionIncrement_le_of_pathJump_bounds path
      hpathTotal herrorNonneg hstartIcc hstopIcc hstartStop coalition player hcard
      hjumpBound
  rw [pathCellLaw_nonempty path.1 start stop terminal,
    pathCellLaw_nonempty path.1 start stop singleton]
  calc
    (path.1.leftValue stop terminal - path.1.leftValue start terminal) /
          (1 - start) ≤
        (partitionSmallCellError resolution *
          (path.1.leftValue stop singleton -
            path.1.leftValue start singleton)) / (1 - start) :=
      (div_le_div_iff_of_pos_right (sub_pos.mpr hstart.2)).2 <| by
        simpa only [terminal, singleton] using hincrement
    _ = partitionSmallCellError resolution *
        ((path.1.leftValue stop singleton -
          path.1.leftValue start singleton) / (1 - start)) := by ring

/-- Exact product-root and singleton-derivative analytic input for the
published small-cell branch. Collision domination is needed only when the
selected cell is non-large; copied large jumps are decoded directly and do
not satisfy a resolution-smallness claim. -/
def HasPartitionSmallCellCollisionDomination
    (path : AbsorptionPath (ι := ι)) (resolution : ℕ) : Prop :=
  ∀ stage,
    pathTotal path.1 (partitionCut path resolution stage) ≤
      partitionProbe resolution (partitionCut path resolution stage) →
    ∀ coalition player,
    2 ≤ coalition.card → player ∈ coalition →
      pathCellLaw path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) coalition ≤
        partitionSmallCellError resolution *
          pathCellLaw path.1 (partitionCut path resolution stage)
            (partitionCut path resolution (stage + 1)) {player}

omit [Nonempty ι] in
/-- Every resolution at least three has the exact collision-domination data
needed by the selected-cell decoder. -/
theorem hasPartitionSmallCellCollisionDomination
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    HasPartitionSmallCellCollisionDomination path resolution := by
  intro stage hsmall coalition player hcard hplayer
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartIcc := partitionCut_mem_Icc path hpathTotal resolution
    hresolutionOne stage
  have hstartIco : partitionCut path resolution stage ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨hstartIcc.1,
      partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
        hresolutionTwo stage⟩
  have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
    hpathTotal resolution hresolutionOne stage
  rw [partitionCut_succ]
  exact
    pathCellLaw_le_partitionSmallCellError_mul_singleton_of_small_partition_cell
      path hpathTotal resolution hresolution hstartIco hstartBoundary hsmall
      coalition player hcard hplayer

omit [Nonempty ι] in
theorem partitionSmallCellError_pos
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    0 < partitionSmallCellError resolution := by
  unfold partitionSmallCellError
  have hresolutionReal : (3 : ℝ) ≤ resolution := by
    exact_mod_cast hresolution
  exact one_div_pos.mpr (by linarith)

omit [Nonempty ι] in
theorem partitionSmallCellError_le_half
    (resolution : ℕ) (hresolution : 3 ≤ resolution) :
    partitionSmallCellError resolution ≤ 1 / 2 := by
  unfold partitionSmallCellError
  have hresolutionReal : (3 : ℝ) ≤ resolution := by
    exact_mod_cast hresolution
  have hdenominator : (0 : ℝ) < (resolution : ℝ) - 1 := by linarith
  apply (div_le_div_iff₀ hdenominator (by norm_num : (0 : ℝ) < 2)).2
  linarith

/-- One literal output row of the published partition decoder.  The source
field records whether the row is a copied path jump or the checked
productization of the corresponding small cell; downstream arguments can
therefore recover the exact support information of either arm. -/
structure PartitionCellRowData
    (path : AbsorptionPath (ι := ι)) (resolution stage : ℕ) where
  root : ι → PMF Bool
  absorption_exact :
    quittingRootAbsorptionMass root =
      pathCellAbsorption path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1))
  source :
    (∃ (_hjump : partitionCut path resolution stage ∈ pathJumps path.1),
      partitionCut path resolution (stage + 1) =
          pathTotal path.1 (partitionCut path resolution stage) ∧
        root = absorptionPathJumpRoot path
          (partitionCut path resolution stage)) ∨
    (∃ (cell : SmallPathCell path.1
          (partitionSmallCellError resolution))
        (packet : SmallCellProductization
          (partitionSmallCellError resolution)
          (pathCellLaw path.1 cell.start cell.stop)),
      cell.start = partitionCut path resolution stage ∧
        cell.stop = partitionCut path resolution (stage + 1) ∧
        root = packet.quittingRoot)

/-- Every recursive partition cell has a literal decoder row once the
published collision domination has been supplied. -/
theorem nonempty_partitionCellRowData
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) :
    Nonempty (PartitionCellRowData path resolution stage) := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  let start := partitionCut path resolution stage
  let stop := partitionCut path resolution (stage + 1)
  have hstartMem : start ∈ Set.Ico (0 : ℝ) 1 := ⟨
    (partitionCut_mem_Icc path hpathTotal resolution hresolutionOne stage).1,
    partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
      hresolutionTwo stage⟩
  have hstartBoundary : start ∈ partitionBoundaryTimes path :=
    partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
      hresolutionOne stage
  by_cases hlarge : partitionProbe resolution start < pathTotal path.1 start
  · have hjump : start ∈ pathJumps path.1 :=
      mem_pathJumps_of_probe_lt_pathTotal_of_boundary path resolution
        hstartBoundary hlarge
    have hstop : stop = pathTotal path.1 start := by
      simpa only [stop, start, partitionCut_succ] using
        nextPartitionCut_eq_pathTotal_of_probe_lt path resolution start hlarge
    refine ⟨{
      root := absorptionPathJumpRoot path start
      absorption_exact := ?_
      source := Or.inl ⟨hjump, ?_, rfl⟩
    }⟩
    · exact copiedJumpRoot_absorption_eq_pathCellAbsorption path
        hpathTotal hjump hstop
    · exact hstop
  · have hsmall : pathTotal path.1 start ≤ partitionProbe resolution start :=
      not_lt.mp hlarge
    have hcellCollision : ∀ coalition player,
        2 ≤ coalition.card → player ∈ coalition →
          pathCellLaw path.1 start
              (nextPartitionCut path resolution start) coalition ≤
            partitionSmallCellError resolution *
              pathCellLaw path.1 start
                (nextPartitionCut path resolution start) {player} := by
      simpa only [start, stop, partitionCut_succ] using
        hcollision stage (by simpa only [start] using hsmall)
    let cell := smallPathCellOfPartition path hpathTotal resolution
      hresolution hstartMem hstartBoundary hsmall hcellCollision
    let packet := Classical.choice <|
      cell.nonempty_productization
        (partitionSmallCellError_pos resolution hresolution)
        (partitionSmallCellError_le_half resolution hresolution)
    refine ⟨{
      root := packet.quittingRoot
      absorption_exact := ?_
      source := Or.inr ⟨cell, packet, rfl, rfl, rfl⟩
    }⟩
    change quittingRootAbsorptionMass packet.quittingRoot =
      pathCellAbsorption path.1 start stop
    rw [packet.quittingRoot_absorption_exact, cell.law_absorption]
    have hcellStart : cell.start = start := rfl
    have hcellStop : cell.stop = stop := rfl
    rw [hcellStart, hcellStop]

/-- A canonical decoded row, chosen from the literal copied-jump/small-cell
packet above. -/
def partitionCellRoot
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) : ι → PMF Bool :=
  (Classical.choice <| nonempty_partitionCellRowData path hpathTotal
    hnoTerminalJump resolution hresolution hcollision stage).root

/-- The canonical decoded row has exactly the conditional absorption of its
partition cell. -/
theorem partitionCellRoot_absorption_exact
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) :
    quittingRootAbsorptionMass
        (partitionCellRoot path hpathTotal hnoTerminalJump resolution
          hresolution hcollision stage) =
      pathCellAbsorption path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1)) := by
  exact (Classical.choice <| nonempty_partitionCellRowData path hpathTotal
    hnoTerminalJump resolution hresolution hcollision stage).absorption_exact

/-- The canonical array of decoded partition rows at one resolution. -/
def partitionCellRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution) :
    ℕ → ι → PMF Bool :=
  partitionCellRoot path hpathTotal hnoTerminalJump resolution hresolution
    hcollision

omit [Nonempty ι] in
/-- Between two admissible clock boundaries, one minus the conditional cell
absorption is the ratio of the two live masses. -/
theorem one_sub_pathCellAbsorption_of_boundaries
    (path : AbsorptionPath (ι := ι))
    {start stop : ℝ}
    (hstart : start ∈ partitionBoundaryTimes path)
    (hstop : stop ∈ partitionBoundaryTimes path)
    (hstartOne : start < 1) :
    1 - pathCellAbsorption path.1 start stop =
      (1 - stop) / (1 - start) := by
  unfold pathCellAbsorption
  rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstart,
    pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstop]
  field_simp [ne_of_gt (sub_pos.mpr hstartOne)]
  ring

/-- The survival through the first `cutoff` decoded rows is literally the
live clock mass at the corresponding recursive cut. -/
theorem quittingSurvivalPrefix_partitionCellRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (cutoff : ℕ) :
    quittingSurvivalPrefix
        (partitionCellRoots path hpathTotal hnoTerminalJump resolution
          hresolution hcollision) cutoff =
      1 - partitionCut path resolution cutoff := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  induction cutoff with
  | zero => simp
  | succ cutoff ih =>
      rw [quittingSurvivalPrefix_succ, ih]
      change (1 - partitionCut path resolution cutoff) *
        quittingStationaryContinueMass
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision cutoff) = _
      have habsorption := partitionCellRoot_absorption_exact path hpathTotal
        hnoTerminalJump resolution hresolution hcollision cutoff
      have hcontinue : quittingStationaryContinueMass
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision cutoff) =
          1 - pathCellAbsorption path.1
            (partitionCut path resolution cutoff)
            (partitionCut path resolution (cutoff + 1)) := by
        unfold quittingRootAbsorptionMass at habsorption
        linarith
      rw [hcontinue, one_sub_pathCellAbsorption_of_boundaries path
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
          hresolutionOne cutoff)
        (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
          hresolutionOne (cutoff + 1))
        (partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
          hresolutionTwo cutoff)]
      field_simp [ne_of_gt (sub_pos.mpr <|
        partitionCut_lt_one path hpathTotal hnoTerminalJump resolution
          hresolutionTwo cutoff)]

/-- The decoded partition rows absorb completely because their exact
survival prefix is `1 - partitionCut`, and the recursive cuts converge to
one. -/
theorem isCompletelyAbsorbing_partitionCellRoots
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution) :
    IsCompletelyAbsorbing
      (partitionCellRoots path hpathTotal hnoTerminalJump resolution
        hresolution hcollision) := by
  have hcuts := tendsto_partitionCut_one path hpathTotal resolution
    (by omega : 1 ≤ resolution)
  have hlive : Tendsto (fun cutoff ↦
      1 - partitionCut path resolution cutoff) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hcuts using 1
    all_goals norm_num
  exact hlive.congr' <| Filter.Eventually.of_forall fun cutoff ↦
    (quittingSurvivalPrefix_partitionCellRoots path hpathTotal
      hnoTerminalJump resolution hresolution hcollision cutoff).symm

/-- The canonical row retains the literal copied-jump/small-cell provenance
of the packet from which it was chosen. -/
theorem partitionCellRoot_source
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) :
    (∃ (_hjump : partitionCut path resolution stage ∈ pathJumps path.1),
      partitionCut path resolution (stage + 1) =
          pathTotal path.1 (partitionCut path resolution stage) ∧
        partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage =
          absorptionPathJumpRoot path (partitionCut path resolution stage)) ∨
    (∃ (cell : SmallPathCell path.1
          (partitionSmallCellError resolution))
        (packet : SmallCellProductization
          (partitionSmallCellError resolution)
          (pathCellLaw path.1 cell.start cell.stop)),
      cell.start = partitionCut path resolution stage ∧
        cell.stop = partitionCut path resolution (stage + 1) ∧
        partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage = packet.quittingRoot) := by
  exact (Classical.choice <| nonempty_partitionCellRowData path hpathTotal
    hnoTerminalJump resolution hresolution hcollision stage).source

omit [DecidableEq ι] [Nonempty ι] in
/-- Positive all-Continue mass forces every marginal Continue probability to
be positive. -/
theorem quittingRoot_false_toReal_pos_of_continueMass_pos
    (root : ι → PMF Bool)
    (hcontinue : 0 < quittingStationaryContinueMass root) (player : ι) :
    0 < (root player false).toReal := by
  have hproduct : 0 < ∏ who, (root who false).toReal := by
    simpa [quittingStationaryContinueMass_eq_prod_continueProbability]
      using hcontinue
  by_contra hnot
  have hzero : (root player false).toReal = 0 :=
    le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
  have hproductZero : (∏ who, (root who false).toReal) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ player) hzero
  rw [hproductZero] at hproduct
  exact (lt_irrefl 0) hproduct

omit [Nonempty ι] in
/-- With positive all-Continue mass, a positive marginal Quit probability has
positive singleton-coalition mass. -/
theorem quittingRootCoalitionMass_singleton_pos_of_continueMass_pos_local
    (root : ι → PMF Bool) (player : ι)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hquit : 0 < (root player true).toReal) :
    0 < quittingRootCoalitionMass root {player} := by
  have houtside : 0 <
      ∏ other ∈ ({player}ᶜ : Finset ι),
        (1 - (root other true).toReal) := by
    apply Finset.prod_pos
    intro other _
    rw [← Math.PMFProduct.pmfBool_false_toReal]
    exact quittingRoot_false_toReal_pos_of_continueMass_pos root hcontinue other
  unfold quittingRootCoalitionMass quittingRootQuitRates
    Math.PMFProduct.coalitionMass
  simp only [Finset.prod_singleton]
  exact mul_pos hquit houtside

/-- A selected partition row has strictly positive all-Continue mass. -/
theorem partitionCellRoot_continueMass_pos
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) :
    0 < quittingStationaryContinueMass
      (partitionCellRoot path hpathTotal hnoTerminalJump resolution
        hresolution hcollision stage) := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hstartOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo stage
  have hstopOne := partitionCut_lt_one path hpathTotal hnoTerminalJump
    resolution hresolutionTwo (stage + 1)
  have hsurvival := one_sub_pathCellAbsorption_of_boundaries path
    (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
      hresolutionOne stage)
    (partitionCut_mem_partitionBoundaryTimes path hpathTotal resolution
      hresolutionOne (stage + 1)) hstartOne
  have hratio : 0 <
      (1 - partitionCut path resolution (stage + 1)) /
        (1 - partitionCut path resolution stage) :=
    div_pos (sub_pos.mpr hstopOne) (sub_pos.mpr hstartOne)
  rw [← hsurvival] at hratio
  have habsorption := partitionCellRoot_absorption_exact path hpathTotal
    hnoTerminalJump resolution hresolution hcollision stage
  unfold quittingRootAbsorptionMass at habsorption
  linarith

/-- Continue is literally in support at every selected partition row. -/
theorem partitionCellRoot_false_toReal_pos
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι) :
    0 < ((partitionCellRoot path hpathTotal hnoTerminalJump resolution
      hresolution hcollision stage) player false).toReal :=
  quittingRoot_false_toReal_pos_of_continueMass_pos _
    (partitionCellRoot_continueMass_pos path hpathTotal hnoTerminalJump
      resolution hresolution hcollision stage) player

omit [DecidableEq ι] [Nonempty ι] in
/-- If the total mass is unchanged between a value and a strictly later left
limit, coordinatewise monotonicity makes every coordinate unchanged. -/
theorem CadlagPath.value_eq_leftValue_of_lt_of_total_eq
    (path : CadlagPath (ι := ι))
    {start stop : ℝ}
    (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1)
    (hstartStop : start < stop)
    (htotal : pathLeftTotal path stop = pathTotal path start)
    (coalition : {S : Finset ι // S.Nonempty}) :
    path.value start coalition = path.leftValue stop coalition := by
  have hcoordinate_nonneg (other : {S : Finset ι // S.Nonempty}) :
      0 ≤ path.leftValue stop other - path.value start other :=
    sub_nonneg.mpr <|
      path.value_le_leftValue_of_lt other hstart hstop hstartStop
  have hsum : (∑ other,
      (path.leftValue stop other - path.value start other)) = 0 := by
    rw [Finset.sum_sub_distrib]
    change pathLeftTotal path stop - pathTotal path start = 0
    rw [htotal, sub_self]
  have hall := (Fintype.sum_eq_zero_iff_of_nonneg hcoordinate_nonneg).mp hsum
  have hzero : path.leftValue stop coalition - path.value start coalition = 0 := by
    simpa using congrFun hall coalition
  linarith

omit [Nonempty ι] in
/-- A copied jump cell has exactly its normalized path-jump coalition law,
coordinate by coordinate. -/
theorem pathCellLaw_eq_pathJump_div_of_copiedJump
    (path : AbsorptionPath (ι := ι))
    {start stop : ℝ}
    (hstart : start ∈ Set.Icc (0 : ℝ) 1)
    (hstop : stop ∈ Set.Icc (0 : ℝ) 1)
    (hstartStop : start < stop)
    (htotal : pathLeftTotal path.1 stop = pathTotal path.1 start)
    (coalition : {S : Finset ι // S.Nonempty}) :
    pathCellLaw path.1 start stop coalition.1 =
      pathJump path.1 start coalition / (1 - start) := by
  rw [pathCellLaw_nonempty]
  have hcoordinate := CadlagPath.value_eq_leftValue_of_lt_of_total_eq
    path.1 hstart hstop hstartStop htotal coalition
  unfold pathJump
  rw [← hcoordinate]

/-- A selected decoder row never introduces a new supported Quit action:
positive Quit probability for a player comes from positive singleton mass in
the literal source cell. -/
theorem partitionCellRoot_quitProbability_pos_imp_pathCellLaw_singleton_pos
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (player : ι)
    (hquit : 0 < ((partitionCellRoot path hpathTotal hnoTerminalJump
      resolution hresolution hcollision stage) player true).toReal) :
    0 < pathCellLaw path.1 (partitionCut path resolution stage)
      (partitionCut path resolution (stage + 1)) {player} := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hcontinue := partitionCellRoot_continueMass_pos path hpathTotal
    hnoTerminalJump resolution hresolution hcollision stage
  have hsource := partitionCellRoot_source path hpathTotal hnoTerminalJump
    resolution hresolution hcollision stage
  rcases hsource with hcopied | hsmall
  · obtain ⟨hjump, hstopTotal, hroot⟩ := hcopied
    let start := partitionCut path resolution stage
    let stop := partitionCut path resolution (stage + 1)
    have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne stage
    have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne (stage + 1)
    have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne stage
    have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne (stage + 1)
    have hstartIco : start ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨hstartMem.1, partitionCut_lt_one path hpathTotal hnoTerminalJump
        resolution hresolutionTwo stage⟩
    have hstartStop : start < stop := by
      rw [show stop = partitionCut path resolution (stage + 1) by rfl,
        show start = partitionCut path resolution stage by rfl,
        partitionCut_succ]
      exact lt_nextPartitionCut path hpathTotal resolution hresolutionTwo
        hstartIco hstartBoundary
    have htotal : pathLeftTotal path.1 stop = pathTotal path.1 start := by
      rw [show stop = partitionCut path resolution (stage + 1) by rfl,
        pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
        hstopTotal]
    have hquitCopied :
        0 < ((absorptionPathJumpRoot path start) player true).toReal := by
      simpa only [start, hroot] using hquit
    have hcontinueCopied :
        0 < quittingStationaryContinueMass
          (absorptionPathJumpRoot path start) := by
      simpa only [start, hroot] using hcontinue
    have hmassPos :=
      quittingRootCoalitionMass_singleton_pos_of_continueMass_pos_local
        (absorptionPathJumpRoot path start) player hcontinueCopied hquitCopied
    have hmass := copiedJumpRoot_coalitionMass path (by
      simpa only [start] using hjump)
      ⟨{player}, Finset.singleton_nonempty player⟩
    have hlaw := pathCellLaw_eq_pathJump_div_of_copiedJump path
      (by simpa only [start] using hstartMem)
      (by simpa only [stop] using hstopMem) hstartStop htotal
      ⟨{player}, Finset.singleton_nonempty player⟩
    have heq : quittingRootCoalitionMass
        (absorptionPathJumpRoot path start) {player} =
        pathCellLaw path.1 start stop {player} := by
      calc
        quittingRootCoalitionMass (absorptionPathJumpRoot path start) {player} =
            pathJump path.1 start
              ⟨{player}, Finset.singleton_nonempty player⟩ / (1 - start) := by
          simpa only [start] using hmass
        _ = pathCellLaw path.1 start stop {player} := by
          simpa only [start, stop] using hlaw.symm
    rw [heq] at hmassPos
    simpa only [start, stop] using hmassPos
  · obtain ⟨cell, packet, hcellStart, hcellStop, hroot⟩ := hsmall
    have hquitPacket : 0 < (packet.quittingRoot player true).toReal := by
      simpa only [hroot] using hquit
    have hsourcePositive :=
      (packet.quittingRoot_true_pos_iff_singletonMass_pos player).1 hquitPacket
    simpa only [hcellStart, hcellStop] using hsourcePositive

/-- Every selected row approximates its literal cell coalition law with the
published dimension constant.  Copied jumps have zero error; small cells use
the checked productization estimate. -/
theorem partitionCellRoot_coalition_coordinate_error
    (path : AbsorptionPath (ι := ι))
    (hpathTotal : ∀ time ∈ Set.Icc (0 : ℝ) 1,
      pathTotal path.1 time ≤ 1)
    (hnoTerminalJump : HasNoTerminalTotalJump path)
    (resolution : ℕ) (hresolution : 3 ≤ resolution)
    (hcollision : HasPartitionSmallCellCollisionDomination path resolution)
    (stage : ℕ) (coalition : Finset ι) (hcoalition : coalition.Nonempty) :
    |quittingRootCoalitionMass
          (partitionCellRoot path hpathTotal hnoTerminalJump resolution
            hresolution hcollision stage) coalition -
        pathCellLaw path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) coalition| ≤
      akrsSmallCellCoordinateConstant ι *
        partitionSmallCellError resolution *
        pathCellAbsorption path.1 (partitionCut path resolution stage)
          (partitionCut path resolution (stage + 1)) := by
  have hresolutionOne : 1 ≤ resolution := by omega
  have hresolutionTwo : 2 ≤ resolution := by omega
  have hdataSource :=
    partitionCellRoot_source path hpathTotal hnoTerminalJump resolution
      hresolution hcollision stage
  have habsorption_nonneg : 0 ≤ pathCellAbsorption path.1
      (partitionCut path resolution stage)
      (partitionCut path resolution (stage + 1)) := by
    rw [← partitionCellRoot_absorption_exact path hpathTotal
      hnoTerminalJump resolution hresolution hcollision stage]
    exact quittingRootAbsorptionMass_nonneg _
  rcases hdataSource with hcopied | hsmall
  · obtain ⟨hjump, hstopTotal, hroot⟩ := hcopied
    have hstartMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne stage
    have hstopMem := partitionCut_mem_Icc path hpathTotal resolution
      hresolutionOne (stage + 1)
    have hstartBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne stage
    have hstopBoundary := partitionCut_mem_partitionBoundaryTimes path
      hpathTotal resolution hresolutionOne (stage + 1)
    have hstartIco : partitionCut path resolution stage ∈ Set.Ico (0 : ℝ) 1 :=
      ⟨hstartMem.1, partitionCut_lt_one path hpathTotal hnoTerminalJump
        resolution hresolutionTwo stage⟩
    have hstartStop : partitionCut path resolution stage <
        partitionCut path resolution (stage + 1) := by
      rw [partitionCut_succ]
      exact lt_nextPartitionCut path hpathTotal resolution hresolutionTwo
        hstartIco hstartBoundary
    have htotal : pathLeftTotal path.1
        (partitionCut path resolution (stage + 1)) =
          pathTotal path.1 (partitionCut path resolution stage) := by
      rw [pathLeftTotal_eq_of_mem_partitionBoundaryTimes path hstopBoundary,
        hstopTotal]
    have hlaw := pathCellLaw_eq_pathJump_div_of_copiedJump path hstartMem
      hstopMem hstartStop htotal ⟨coalition, hcoalition⟩
    have hmass := copiedJumpRoot_coalitionMass path hjump
      ⟨coalition, hcoalition⟩
    have hmass' : quittingRootCoalitionMass
        (absorptionPathJumpRoot path (partitionCut path resolution stage))
          coalition =
        pathJump path.1 (partitionCut path resolution stage)
          ⟨coalition, hcoalition⟩ /
            (1 - partitionCut path resolution stage) := by
      simpa using hmass
    have hlaw' : pathCellLaw path.1 (partitionCut path resolution stage)
        (partitionCut path resolution (stage + 1)) coalition =
        pathJump path.1 (partitionCut path resolution stage)
          ⟨coalition, hcoalition⟩ /
            (1 - partitionCut path resolution stage) := by
      simpa using hlaw
    rw [hroot, hmass', hlaw', sub_self, abs_zero]
    have hconstant : 0 ≤ akrsSmallCellCoordinateConstant ι := by
      unfold akrsSmallCellCoordinateConstant
      exact_mod_cast Nat.zero_le (2 ^ Fintype.card ι)
    exact mul_nonneg
      (mul_nonneg hconstant
        (partitionSmallCellError_pos resolution hresolution).le)
      habsorption_nonneg
  · obtain ⟨cell, packet, hcellStart, hcellStop, hroot⟩ := hsmall
    have hpacket := packet.quittingRoot_coalition_coordinate_error
      coalition hcoalition
    rw [cell.law_absorption] at hpacket
    simpa only [hroot, hcellStart, hcellStop] using hpacket


end QuittingAbsorptionPath
end GameTheory
