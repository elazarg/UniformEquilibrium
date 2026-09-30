import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockSampledLPDual
import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables

/-!
# Literal guarded-crossed child-LP infeasibility

All rows are evaluated on the canonical restriction of the actual source
reward table to a child and one outsider. The half table excludes every
proper-child universal raw criterion, including its permitted positive-singleton
Never relaxation. The unit table has four strict three-player-child duals.
These conclusions do not exclude extending a particular child equilibrium.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open scoped BigOperators

abbrev RawChild (child : Finset (Fin 4)) := QuittingChildPlayer (· ∉ child)

/-- The actual child-plus-one-outsider table, not a separately supplied fixture. -/
abbrev rawChildReward
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child}) :=
  quittingChildWithOutsiderReward reward (· ∉ child) outside

private def rawChildCoalition (child coalition : Finset (Fin 4)) : Finset (RawChild child) :=
  Finset.univ.filter (fun who => who.1 ∈ coalition)

private theorem rawChildCoalition_original_map
    (child coalition : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (hsubset : coalition ⊆ child) :
    (cappedClockChildCoalition (rawChildCoalition child coalition)).map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside) = coalition := by
  ext player
  simp only [cappedClockChildCoalition, Finset.mem_map, rawChildCoalition,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨who, hwho, rfl⟩, heq⟩
    have hvalue : who.1 = player := by
      change who.1 = player at heq
      exact heq
    simpa only [hvalue] using hwho
  · intro hplayer
    let who : RawChild child := ⟨player, not_not.mpr (hsubset hplayer)⟩
    exact ⟨some who, ⟨who, hplayer, rfl⟩, rfl⟩

private theorem rawChildReward_eq_original_weight
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (terminal : {A : Finset (Option (RawChild child)) // A.Nonempty})
    (original : Finset (Fin 4))
    (hmap : terminal.1.map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside) = original)
    (who : Option (RawChild child)) :
    rawChildReward reward child outside terminal who =
      weightOfReward reward original
        (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside who) := by
  have hnonempty : original.Nonempty := hmap ▸ Finset.map_nonempty.mpr terminal.2
  rw [rawChildReward, quittingChildWithOutsiderReward_apply_original]
  simp only [weightOfReward, dite_eq_left hnonempty]
  congr 1
  exact Subtype.ext hmap

private theorem rawChild_future_delta
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child coalition : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty)
    (who : RawChild child) :
    cappedClockExactLPDelta (rawChildReward reward child outside)
      (.future ⟨rawChildCoalition child coalition, hcoalition⟩) who =
      weightOfReward reward {who.1} who.1 - weightOfReward reward coalition who.1 := by
  dsimp only [cappedClockExactLPDelta]
  rw [rawChildReward_eq_original_weight reward child outside _ {who.1} (by simp),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

private theorem rawChild_future_base
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child coalition : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty) :
    cappedClockExactLPBase (rawChildReward reward child outside)
      (.future ⟨rawChildCoalition child coalition, hcoalition⟩) =
      weightOfReward reward {outside.1} outside.1 - weightOfReward reward coalition outside.1 := by
  dsimp only [cappedClockExactLPBase]
  rw [rawChildReward_eq_original_weight reward child outside _ {outside.1} (by simp),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

private theorem rawChild_joining_delta
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child coalition : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty)
    (who : RawChild child) :
    cappedClockExactLPDelta (rawChildReward reward child outside)
      (.joining ⟨rawChildCoalition child coalition, hcoalition⟩) who =
      weightOfReward reward (insert who.1 coalition) who.1 -
        weightOfReward reward coalition who.1 := by
  dsimp only [cappedClockExactLPDelta]
  rw [rawChildReward_eq_original_weight reward child outside _ (insert who.1 coalition) (by
    simp only [cappedClockChildCoalition, Finset.map_insert]
    change insert who.1 ((cappedClockChildCoalition (rawChildCoalition child coalition)).map
      (quittingChildWithOutsiderOriginalEmbedding (· ∉ child) outside)) = insert who.1 coalition
    exact congrArg (insert who.1) (rawChildCoalition_original_map child coalition outside hsubset)),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

private theorem rawChild_joining_base
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (child coalition : Finset (Fin 4)) (outside : {who : Fin 4 // who ∉ child})
    (hsubset : coalition ⊆ child) (hcoalition : (rawChildCoalition child coalition).Nonempty) :
    cappedClockExactLPBase (rawChildReward reward child outside)
      (.joining ⟨rawChildCoalition child coalition, hcoalition⟩) =
      weightOfReward reward (insert outside.1 coalition) outside.1 -
        weightOfReward reward coalition outside.1 := by
  dsimp only [cappedClockExactLPBase]
  rw [rawChildReward_eq_original_weight reward child outside _ (insert outside.1 coalition) (by
    simp only [cappedClockJoinedCoalition, Finset.map_insert,
      quittingChildWithOutsiderOriginalEmbedding_none]
    exact congrArg (insert outside.1)
      (rawChildCoalition_original_map child coalition outside hsubset)),
    rawChildReward_eq_original_weight reward child outside _ coalition
      (rawChildCoalition_original_map child coalition outside hsubset)]
  simp

def halfDualChild : Fin 7 → Finset (Fin 4) :=
  ![{0}, {0, 1}, {0, 2}, {0, 1, 2}, {0, 3}, {0, 1, 3}, {0, 2, 3}]

def halfDualOutside : Fin 7 → Fin 4 := ![1, 2, 1, 3, 1, 2, 1]

theorem halfDualOutside_notMem (index : Fin 7) :
    halfDualOutside index ∉ halfDualChild index := by
  fin_cases index <;> decide

private def halfDualCoalition : Fin 7 → Fin 2 → Finset (Fin 4) :=
  ![![{0}, {0}], ![{0}, {0}], ![{0}, {0, 2}], ![{0, 2}, {0, 2}],
    ![{0}, {0}], ![{0, 1}, {0, 1}], ![{0}, {0, 2}]]

private def halfDualJoining : Fin 7 → Fin 2 → Bool :=
  ![![true, true], ![false, false], ![true, false], ![false, false],
    ![true, true], ![true, true], ![true, false]]

private theorem halfDualCoalition_nonempty (index : Fin 7) (row : Fin 2) :
    (rawChildCoalition (halfDualChild index) (halfDualCoalition index row)).Nonempty := by
  exact (by decide : ∀ index row,
    (rawChildCoalition (halfDualChild index) (halfDualCoalition index row)).Nonempty) index row

private theorem halfDualCoalition_subset (index : Fin 7) (row : Fin 2) :
    halfDualCoalition index row ⊆ halfDualChild index := by
  exact (by decide : ∀ index row,
    halfDualCoalition index row ⊆ halfDualChild index) index row

/-- The packet's seven displayed F/J row combinations, padded by a zero coefficient. -/
def halfDualSample (index : Fin 7) (row : Fin 2) :
    CappedClockExactLPRow (RawChild (halfDualChild index)) :=
  if halfDualJoining index row then
    .joining ⟨rawChildCoalition (halfDualChild index) (halfDualCoalition index row),
      halfDualCoalition_nonempty index row⟩
  else
    .future ⟨rawChildCoalition (halfDualChild index) (halfDualCoalition index row),
      halfDualCoalition_nonempty index row⟩

def halfDualCoefficient : Fin 7 → Fin 2 → ℝ :=
  ![![1, 0], ![1, 0], ![1, 2], ![1, 0], ![1, 0], ![1, 0], ![1, 2]]

def halfDualColumn : Fin 7 → Fin 4 → ℝ :=
  ![![0, 0, 0, 0], ![0, -3, 0, 0], ![-8 / 3, 0, -7, 0], ![-4 / 3, 0, -8, 0],
    ![0, 0, 0, -3], ![0, 0, 0, -2], ![-8 / 3, 0, -7, -1]]

def halfDualObjective : Fin 7 → ℝ := ![1, 1, 1, 1, 1, 3, 1]

private theorem halfDual_original_delta (index : Fin 7) (row : Fin 2)
    (who : RawChild (halfDualChild index)) :
    cappedClockExactLPDelta
      (rawChildReward halfCeilingReward (halfDualChild index)
        ⟨halfDualOutside index, halfDualOutside_notMem index⟩)
      (halfDualSample index row) who =
      if halfDualJoining index row then
        weightOfReward halfCeilingReward (insert who.1 (halfDualCoalition index row)) who.1 -
          weightOfReward halfCeilingReward (halfDualCoalition index row) who.1
      else
        weightOfReward halfCeilingReward {who.1} who.1 -
          weightOfReward halfCeilingReward (halfDualCoalition index row) who.1 := by
  unfold halfDualSample
  split_ifs
  · exact rawChild_joining_delta _ _ _ _ (halfDualCoalition_subset index row) _ who
  · exact rawChild_future_delta _ _ _ _ (halfDualCoalition_subset index row) _ who

private theorem halfDual_original_base (index : Fin 7) (row : Fin 2) :
    cappedClockExactLPBase
      (rawChildReward halfCeilingReward (halfDualChild index)
        ⟨halfDualOutside index, halfDualOutside_notMem index⟩)
      (halfDualSample index row) =
      if halfDualJoining index row then
        weightOfReward halfCeilingReward
          (insert (halfDualOutside index) (halfDualCoalition index row)) (halfDualOutside index) -
          weightOfReward halfCeilingReward (halfDualCoalition index row) (halfDualOutside index)
      else
        weightOfReward halfCeilingReward {halfDualOutside index} (halfDualOutside index) -
          weightOfReward halfCeilingReward (halfDualCoalition index row)
            (halfDualOutside index) := by
  unfold halfDualSample
  split_ifs
  · exact rawChild_joining_base _ _ _ _ (halfDualCoalition_subset index row) _
  · exact rawChild_future_base _ _ _ _ (halfDualCoalition_subset index row) _

theorem halfDual_column_eq (index : Fin 7) (who : RawChild (halfDualChild index)) :
    ∑ row, halfDualCoefficient index row *
      cappedClockExactLPDelta
        (rawChildReward halfCeilingReward (halfDualChild index)
          ⟨halfDualOutside index, halfDualOutside_notMem index⟩)
        (halfDualSample index row) who = halfDualColumn index who.1 := by
  simp_rw [halfDual_original_delta]
  fin_cases index
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [halfDualChild] at hwho
  all_goals norm_num +decide [halfDualCoefficient, halfDualColumn, halfDualJoining,
    halfDualCoalition, halfDualChild, halfDualOutside, weightOfReward, halfCeilingReward,
    coalitionCode, Fin.sum_univ_succ]

theorem halfDual_objective_eq (index : Fin 7) :
    ∑ row, halfDualCoefficient index row *
      cappedClockExactLPBase
        (rawChildReward halfCeilingReward (halfDualChild index)
          ⟨halfDualOutside index, halfDualOutside_notMem index⟩)
        (halfDualSample index row) = halfDualObjective index := by
  simp_rw [halfDual_original_base]
  fin_cases index
  all_goals norm_num +decide [halfDualCoefficient, halfDualObjective, halfDualJoining,
    halfDualCoalition, halfDualChild, halfDualOutside, weightOfReward, halfCeilingReward,
    coalitionCode, Fin.sum_univ_succ]

private theorem halfDual_nonnegative (index : Fin 7) (row : Fin 2) :
    0 ≤ halfDualCoefficient index row := by
  fin_cases index <;> fin_cases row <;> norm_num [halfDualCoefficient]

private theorem halfDual_column_nonpositive (index : Fin 7) (who : Fin 4) :
    halfDualColumn index who ≤ 0 := by
  fin_cases index <;> fin_cases who <;> norm_num [halfDualColumn]

private theorem halfDual_objective_positive (index : Fin 7) :
    0 < halfDualObjective index := by
  fin_cases index <;> norm_num [halfDualObjective]

private theorem halfDual_not_never (index : Fin 7) (row : Fin 2) :
    halfDualSample index row ≠ .never := by
  unfold halfDualSample
  split_ifs <;> simp

/-- The seven children containing zero fail even the relaxed F/J criterion. -/
theorem halfCeiling_child_containing_zero_no_certificates (index : Fin 7) :
    let reward := rawChildReward halfCeilingReward (halfDualChild index)
      ⟨halfDualOutside index, halfDualOutside_notMem index⟩
    ¬Nonempty (CappedClockParentRewardCertificate reward) ∧
      ¬Nonempty (CappedClockParentFutureJoinCertificate reward) := by
  have hcolumns (who : RawChild (halfDualChild index)) :=
    (halfDual_column_eq index who).le.trans (halfDual_column_nonpositive index who.1)
  have hobjective := (halfDual_objective_eq index).symm ▸ halfDual_objective_positive index
  exact ⟨not_nonempty_cappedClockParentRewardCertificate_of_sampledDual
    _ (halfDualSample index) (halfDualCoefficient index) (halfDual_nonnegative index)
    hcolumns hobjective,
    not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual
      _ (halfDualSample index) (halfDual_not_never index) (halfDualCoefficient index)
      (halfDual_nonnegative index) hcolumns hobjective⟩

theorem halfCeiling_ownSingleton_zero_of_ne_zero (who : Fin 4) (hne : who ≠ 0) :
    halfCeilingReward ⟨{who}, Finset.singleton_nonempty who⟩ who = 0 := by
  fin_cases who
  all_goals norm_num at hne
  all_goals norm_num [halfCeilingReward, coalitionCode]

/-- A child missing player zero has no positive own singleton to license dropping Never. -/
theorem halfCeiling_child_missing_zero_no_positive_singleton
    (child : Finset (Fin 4)) (hzero : 0 ∉ child) :
    ¬∃ who : RawChild child,
      0 < halfCeilingReward ⟨{who.1}, Finset.singleton_nonempty who.1⟩ who.1 := by
  rintro ⟨who, hpositive⟩
  have hne : who.1 ≠ 0 := by
    rintro heq
    exact who.2 (by simpa only [heq] using hzero)
  rw [halfCeiling_ownSingleton_zero_of_ne_zero who.1 hne] at hpositive
  exact lt_irrefl _ hpositive

/-- Its actual Never row has zero columns and outsider objective one. -/
theorem halfCeiling_child_missing_zero_no_rewardCertificate
    (child : Finset (Fin 4)) (hzero : 0 ∉ child) :
    ¬Nonempty (CappedClockParentRewardCertificate
      (rawChildReward halfCeilingReward child ⟨0, hzero⟩)) := by
  apply not_nonempty_cappedClockParentRewardCertificate_of_sampledDual
    _ (fun _ : Unit => .never) (fun _ => 1) (by intro _; norm_num)
  · intro who
    have hne : who.1 ≠ 0 := by
      rintro heq
      exact who.2 (by simpa only [heq] using hzero)
    simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, cappedClockExactLPDelta]
    rw [rawChildReward, quittingChildWithOutsiderReward_apply_original]
    simpa using (halfCeiling_ownSingleton_zero_of_ne_zero who.1 hne).le
  · norm_num [rawChildReward, cappedClockExactLPBase,
      quittingChildWithOutsiderReward_apply_original, halfCeilingReward, coalitionCode]

private theorem halfDualChild_complete (child : Finset (Fin 4))
    (hproper : child ≠ Finset.univ) (hzero : 0 ∈ child) :
    ∃ index : Fin 7, child = halfDualChild index := by
  exact (by decide : ∀ child : Finset (Fin 4), child ≠ Finset.univ → 0 ∈ child →
    ∃ index : Fin 7, child = halfDualChild index) child hproper hzero

/-- Every proper-child raw test fails on its actual one-outsider restriction,
including the positive-singleton condition required to omit the Never row. -/
theorem halfCeiling_every_proper_child_raw_test_fails
    (child : Finset (Fin 4)) (hproper : child ≠ Finset.univ) :
    ∃ outside : {who : Fin 4 // who ∉ child},
      ¬(Nonempty (CappedClockParentRewardCertificate
          (rawChildReward halfCeilingReward child outside)) ∨
        ((∃ who : RawChild child,
          0 < halfCeilingReward ⟨{who.1}, Finset.singleton_nonempty who.1⟩ who.1) ∧
          Nonempty (CappedClockParentFutureJoinCertificate
            (rawChildReward halfCeilingReward child outside)))) := by
  by_cases hzero : 0 ∈ child
  · obtain ⟨index, rfl⟩ := halfDualChild_complete child hproper hzero
    refine ⟨⟨halfDualOutside index, halfDualOutside_notMem index⟩, ?_⟩
    rcases halfCeiling_child_containing_zero_no_certificates index with ⟨hfull, hrelaxed⟩
    rintro (hcertificate | ⟨_, hcertificate⟩)
    · exact hfull hcertificate
    · exact hrelaxed hcertificate
  · refine ⟨⟨0, hzero⟩, ?_⟩
    rintro (hcertificate | ⟨hpositive, _⟩)
    · exact halfCeiling_child_missing_zero_no_rewardCertificate child hzero hcertificate
    · exact halfCeiling_child_missing_zero_no_positive_singleton child hzero hpositive

def unitDualChild (outside : Fin 4) : Finset (Fin 4) := Finset.univ.erase outside

private def unitDualCoalition : Fin 4 → Fin 4 → Finset (Fin 4) :=
  ![![{2}, {1, 2}, {3}, {1, 2, 3}], ![{2}, {0, 3}, {2}, {2}],
    ![{0}, {1}, {0, 1}, {0}], ![{1}, {0, 2}, {0, 1, 2}, {1}]]

private def unitDualJoining : Fin 4 → Fin 4 → Bool :=
  ![![false, true, false, false], ![true, false, true, true],
    ![true, true, true, true], ![true, false, false, true]]

private theorem unitDualCoalition_nonempty (outside row : Fin 4) :
    (rawChildCoalition (unitDualChild outside) (unitDualCoalition outside row)).Nonempty := by
  exact (by decide : ∀ outside row,
    (rawChildCoalition (unitDualChild outside) (unitDualCoalition outside row)).Nonempty)
      outside row

private theorem unitDualCoalition_subset (outside row : Fin 4) :
    unitDualCoalition outside row ⊆ unitDualChild outside := by
  exact (by decide : ∀ outside row,
    unitDualCoalition outside row ⊆ unitDualChild outside) outside row

/-- The four displayed unit-table combinations, using the actual child player type. -/
def unitDualSample (outside row : Fin 4) :
    CappedClockExactLPRow (RawChild (unitDualChild outside)) :=
  if unitDualJoining outside row then
    .joining ⟨rawChildCoalition (unitDualChild outside) (unitDualCoalition outside row),
      unitDualCoalition_nonempty outside row⟩
  else
    .future ⟨rawChildCoalition (unitDualChild outside) (unitDualCoalition outside row),
      unitDualCoalition_nonempty outside row⟩

def unitDualCoefficient : Fin 4 → Fin 4 → ℝ :=
  ![![2, 3, 4, 9], ![1, 1, 0, 0], ![86, 19, 22, 0], ![5, 7, 2, 0]]

def unitDualColumn : Fin 4 → Fin 4 → ℝ :=
  ![![0, -12, -12, -12], ![-1, 0, -1, -1], ![-133, -602, 0, -133], ![-25, -25, -28, 0]]

def unitDualObjective : Fin 4 → ℝ := ![12, 5, 133, 25]

def unitDualWeightSum : Fin 4 → ℝ := ![18, 2, 127, 14]

def unitDualErrorFactor : Fin 4 → ℝ := ![36, 4, 254, 28]

private theorem unitDual_original_delta (outside row : Fin 4)
    (who : RawChild (unitDualChild outside)) :
    cappedClockExactLPDelta
      (rawChildReward unitCeilingReward (unitDualChild outside)
        ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) who =
      if unitDualJoining outside row then
        weightOfReward unitCeilingReward (insert who.1 (unitDualCoalition outside row)) who.1 -
          weightOfReward unitCeilingReward (unitDualCoalition outside row) who.1
      else
        weightOfReward unitCeilingReward {who.1} who.1 -
          weightOfReward unitCeilingReward (unitDualCoalition outside row) who.1 := by
  unfold unitDualSample
  split_ifs
  · exact rawChild_joining_delta _ _ _ _ (unitDualCoalition_subset outside row) _ who
  · exact rawChild_future_delta _ _ _ _ (unitDualCoalition_subset outside row) _ who

private theorem unitDual_original_base (outside row : Fin 4) :
    cappedClockExactLPBase
      (rawChildReward unitCeilingReward (unitDualChild outside)
        ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) =
      if unitDualJoining outside row then
        weightOfReward unitCeilingReward (insert outside (unitDualCoalition outside row)) outside -
          weightOfReward unitCeilingReward (unitDualCoalition outside row) outside
      else
        weightOfReward unitCeilingReward {outside} outside -
          weightOfReward unitCeilingReward (unitDualCoalition outside row) outside := by
  unfold unitDualSample
  split_ifs
  · exact rawChild_joining_base _ _ _ _ (unitDualCoalition_subset outside row) _
  · exact rawChild_future_base _ _ _ _ (unitDualCoalition_subset outside row) _

theorem unitDual_column_eq (outside : Fin 4) (who : RawChild (unitDualChild outside)) :
    ∑ row, unitDualCoefficient outside row *
      cappedClockExactLPDelta
        (rawChildReward unitCeilingReward (unitDualChild outside)
          ⟨outside, by simp [unitDualChild]⟩)
        (unitDualSample outside row) who = unitDualColumn outside who.1 := by
  simp_rw [unitDual_original_delta]
  fin_cases outside
  all_goals rcases who with ⟨who, hwho⟩
  all_goals fin_cases who
  all_goals norm_num [unitDualChild] at hwho
  all_goals norm_num +decide [unitDualCoefficient, unitDualColumn, unitDualJoining,
    unitDualCoalition, unitDualChild, weightOfReward, unitCeilingReward,
    coalitionCode, Fin.sum_univ_succ]

theorem unitDual_objective_eq (outside : Fin 4) :
    ∑ row, unitDualCoefficient outside row *
      cappedClockExactLPBase
        (rawChildReward unitCeilingReward (unitDualChild outside)
          ⟨outside, by simp [unitDualChild]⟩)
        (unitDualSample outside row) = unitDualObjective outside := by
  simp_rw [unitDual_original_base]
  fin_cases outside
  all_goals norm_num +decide [unitDualCoefficient, unitDualObjective, unitDualJoining,
    unitDualCoalition, unitDualChild, weightOfReward, unitCeilingReward,
    coalitionCode, Fin.sum_univ_succ]

theorem unitDual_weightSum_eq (outside : Fin 4) :
    ∑ row, unitDualCoefficient outside row = unitDualWeightSum outside := by
  fin_cases outside <;> norm_num [unitDualCoefficient, unitDualWeightSum, Fin.sum_univ_succ]

private theorem unitDual_nonnegative (outside row : Fin 4) :
    0 ≤ unitDualCoefficient outside row := by
  fin_cases outside <;> fin_cases row <;> norm_num [unitDualCoefficient]

private theorem unitDual_not_never (outside row : Fin 4) :
    unitDualSample outside row ≠ .never := by
  unfold unitDualSample
  split_ifs <;> simp

/-- All four unit-table children fail even the relaxed F/J criterion. -/
theorem unitCeiling_three_player_child_no_certificates (outside : Fin 4) :
    let reward := rawChildReward unitCeilingReward (unitDualChild outside)
      ⟨outside, by simp [unitDualChild]⟩
    ¬Nonempty (CappedClockParentRewardCertificate reward) ∧
      ¬Nonempty (CappedClockParentFutureJoinCertificate reward) := by
  have hcolumns (who : RawChild (unitDualChild outside)) :
      ∑ row, unitDualCoefficient outside row *
        cappedClockExactLPDelta
          (rawChildReward unitCeilingReward (unitDualChild outside)
            ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) who ≤ 0 := by
    rw [unitDual_column_eq]
    fin_cases outside
    all_goals rcases who with ⟨who, hwho⟩
    all_goals fin_cases who
    all_goals norm_num [unitDualChild] at hwho
    all_goals norm_num [unitDualColumn]
  have hobjective : 0 < ∑ row, unitDualCoefficient outside row *
      cappedClockExactLPBase
        (rawChildReward unitCeilingReward (unitDualChild outside)
          ⟨outside, by simp [unitDualChild]⟩) (unitDualSample outside row) := by
    rw [unitDual_objective_eq]
    fin_cases outside <;> norm_num [unitDualObjective]
  exact ⟨not_nonempty_cappedClockParentRewardCertificate_of_sampledDual
    _ (unitDualSample outside) (unitDualCoefficient outside) (unitDual_nonnegative outside)
    hcolumns hobjective,
    not_nonempty_cappedClockParentFutureJoinCertificate_of_sampledDual
      _ (unitDualSample outside) (unitDual_not_never outside) (unitDualCoefficient outside)
      (unitDual_nonnegative outside) hcolumns hobjective⟩

end GameTheory.GuardedCrossedResponseExamples
