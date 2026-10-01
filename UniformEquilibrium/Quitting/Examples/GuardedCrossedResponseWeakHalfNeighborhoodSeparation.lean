import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseRawClassSeparation
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakBoundaryProducer
import UniformEquilibrium.Quitting.Stationary.RewardCoordinatePerturbation
import UniformEquilibrium.Quitting.Root.PlayerReindex

/-! # Every relabeled weak half-ceiling raw test fails in the literal unit reward ball

These are direct lower-ranking or positive half-face witnesses. No class
exclusion is inferred from a child-LP certificate failure.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open QuittingFinFourEndpointRows

private theorem weight_reindex_nonempty
    (e : Fin 4 ≃ Fin 4)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty) (who : Fin 4) :
    weightOfReward (quittingRewardReindex e reward) coalition who =
      weightOfReward reward (coalition.map e.symm.toEmbedding) (e.symm who) := by
  rw [weightOfReward, dite_eq_left hnonempty, weightOfReward,
    dite_eq_left (Finset.map_nonempty.mpr hnonempty)]
  rfl

private theorem weight_reindex_map_nonempty
    (e : Fin 4 ≃ Fin 4)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty) (who : Fin 4) :
    weightOfReward (quittingRewardReindex e reward) (coalition.map e.toEmbedding) (e who) =
      weightOfReward reward coalition who := by
  rw [weight_reindex_nonempty e reward _ (Finset.map_nonempty.mpr hnonempty)]
  have hcancel : (coalition.map e.toEmbedding).map e.symm.toEmbedding = coalition := by
    ext coordinate
    simp
  rw [hcancel, Equiv.symm_apply_apply]

private theorem weakLowerRanking_of_reindex
    (e : Fin 4 ≃ Fin 4)
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (who partner : Fin 4)
    (hraw : QuittingCrossedWeakLowerRanking (quittingRewardReindex e reward) who partner) :
    QuittingCrossedWeakLowerRanking reward (e.symm who) (e.symm partner) := by
  intro own other hown hother hnonempty
  have hcarrier :
      (quittingCrossedRawOutsiders (e.symm who) (e.symm partner)).map e.toEmbedding =
        quittingCrossedRawOutsiders who partner := by
    simp [quittingCrossedRawOutsiders, Finset.map_erase]
  have hown' : own.map e.toEmbedding ⊆
      (quittingCrossedRawOutsiders (e.symm who) (e.symm partner)).map e.toEmbedding :=
    Finset.map_subset_map.mpr hown
  have hother' : other.map e.toEmbedding ⊆
      (quittingCrossedRawOutsiders (e.symm who) (e.symm partner)).map e.toEmbedding :=
    Finset.map_subset_map.mpr hother
  rw [hcarrier] at hown' hother'
  have h := hraw (own.map e.toEmbedding) (other.map e.toEmbedding)
    hown' hother' (Finset.map_nonempty.mpr hnonempty)
  have hleft := weight_reindex_map_nonempty e reward other hnonempty (e.symm who)
  have hright := weight_reindex_map_nonempty e reward (insert (e.symm who) own)
    (Finset.insert_nonempty _ _) (e.symm who)
  simp only [Finset.map_insert, Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
    at hleft hright
  rw [hleft, hright] at h
  exact h

private theorem unit_lower_violation
    (first second : Fin 4) (hdistinct : first ≠ second)
    (hpair : ¬((first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0))) :
    (∃ coalition : Finset (Fin 4), coalition.Nonempty ∧
      coalition ⊆ quittingCrossedRawOutsiders first second ∧
      1 ≤ weightOfReward unitCeilingReward coalition first -
        weightOfReward unitCeilingReward {first} first) ∨
    (∃ coalition : Finset (Fin 4), coalition.Nonempty ∧
      coalition ⊆ quittingCrossedRawOutsiders second first ∧
      1 ≤ weightOfReward unitCeilingReward coalition second -
        weightOfReward unitCeilingReward {second} second) := by
  fin_cases first
  all_goals fin_cases second
  all_goals try exact (hdistinct rfl).elim
  all_goals try exact (hpair (Or.inl ⟨rfl, rfl⟩)).elim
  all_goals try exact (hpair (Or.inr ⟨rfl, rfl⟩)).elim
  all_goals
    solve
    | (left; refine ⟨{0}, by simp, by decide, ?_⟩
       norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode])
    | (left; refine ⟨{1}, by simp, by decide, ?_⟩
       norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode])
    | (left; refine ⟨{2}, by simp, by decide, ?_⟩
       norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode])
    | (left; refine ⟨{3}, by simp, by decide, ?_⟩
       norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode])
    | (left; refine ⟨{0, 1}, by simp, by decide, ?_⟩
       norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode])

private theorem not_weakLowerRanking_of_source_gap
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (who partner : Fin 4) (coalition : Finset (Fin 4)) (hnonempty : coalition.Nonempty)
    (hsubset : coalition ⊆ quittingCrossedRawOutsiders who partner)
    (hgap : 1 ≤ weightOfReward unitCeilingReward coalition who -
      weightOfReward unitCeilingReward {who} who) :
    ¬QuittingCrossedWeakLowerRanking other who partner := by
  intro hraw
  have h := hraw ∅ coalition (Finset.empty_subset _) hsubset hnonempty
  change weightOfReward other coalition who ≤ weightOfReward other {who} who at h
  have hchange := Maths.FiniteInequality.abs_sub_differences_le
    (weightOfReward unitCeilingReward coalition who) (weightOfReward unitCeilingReward {who} who)
    (weightOfReward other coalition who) (weightOfReward other {who} who) error
    (abs_weightOfReward_sub_le_of_coordinate_error unitCeilingReward other error hclose
      coalition hnonempty who)
    (abs_weightOfReward_sub_le_of_coordinate_error unitCeilingReward other error hclose
      {who} (by simp) who)
  have hlower := (abs_le.mp hchange).1
  linarith

private theorem halfFirstSureOutsidersResidual_eq_source_coordinates
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) :
    quittingHalfFirstResidual reward 1 1 =
      (weightOfReward reward {0, 2, 3} 0 + weightOfReward reward Finset.univ 0 -
        weightOfReward reward {2, 3} 0 - weightOfReward reward {1, 2, 3} 0) / 2 := by
  have hmass : continueMassExcl (halfFirstRow 1 1) 0 = 0 :=
    quittingCrossed_continueMassExcl_partner_one (halfFirstRow 1 1) 0 2
      (by decide) (by norm_num [halfFirstRow])
  rw [quittingHalfFirstResidual, quittingDiscountedDisplacement, hmass,
    sigmaValue_eq_pureQuitEndpointRowSum, excludedValue_eq_excludedEndpointRowSum]
  simp only [pureQuitEndpointRowSum, excludedEndpointRowSum, Fin.sum_univ_succ]
  simp +decide [opponentCoalitionMass, Math.Finset.finFourCoalitionOfRow, Fin.prod_univ_succ,
    halfFirstRow]
  rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  ring

private theorem unit_reindexed_halfFirst_corner_pos
    (e : Fin 4 ≃ Fin 4)
    (hpair : (e.symm 0 = 0 ∧ e.symm 1 = 1) ∨ (e.symm 0 = 1 ∧ e.symm 1 = 0)) :
    1 / 2 ≤ quittingHalfFirstResidual (quittingRewardReindex e unitCeilingReward) 1 1 := by
  have h23 : ({2, 3} : Finset (Fin 4)).map e.symm.toEmbedding =
      (Finset.univ.erase (e.symm 0)).erase (e.symm 1) := by
    rw [show ({2, 3} : Finset (Fin 4)) = (Finset.univ.erase 0).erase 1 by decide]
    simp [Finset.map_erase]
  have h023 : ({0, 2, 3} : Finset (Fin 4)).map e.symm.toEmbedding =
      Finset.univ.erase (e.symm 1) := by
    rw [show ({0, 2, 3} : Finset (Fin 4)) = Finset.univ.erase 1 by decide]
    simp [Finset.map_erase]
  have h123 : ({1, 2, 3} : Finset (Fin 4)).map e.symm.toEmbedding =
      Finset.univ.erase (e.symm 0) := by
    rw [show ({1, 2, 3} : Finset (Fin 4)) = Finset.univ.erase 0 by decide]
    simp [Finset.map_erase]
  rw [halfFirstSureOutsidersResidual_eq_source_coordinates]
  rw [weight_reindex_nonempty e _ {0, 2, 3} (by simp),
    weight_reindex_nonempty e _ Finset.univ (by simp),
    weight_reindex_nonempty e _ {2, 3} (by simp),
    weight_reindex_nonempty e _ {1, 2, 3} (by simp)]
  rw [h23, h023, h123]
  have huniv : (Finset.univ : Finset (Fin 4)).map e.symm.toEmbedding = Finset.univ := by
    simp
  rw [huniv]
  rcases hpair with ⟨hzero, hone⟩ | ⟨hzero, hone⟩
  all_goals rw [hzero, hone]
  all_goals norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

/-- Every relabeling fails the literal weak half test throughout the exact unit radius. -/
theorem unitCeiling_not_reindexed_weakHalfRawGuards_of_coordinate_error
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (error : ℝ)
    (herror : error < 1 / 1000)
    (hclose : ∀ terminal who, |other terminal who - unitCeilingReward terminal who| ≤ error)
    (e : Fin 4 ≃ Fin 4) :
    ¬QuittingHalfWeakRawGuards (quittingRewardReindex e other) := by
  intro hraw
  by_cases hpair : (e.symm 0 = 0 ∧ e.symm 1 = 1) ∨ (e.symm 0 = 1 ∧ e.symm 1 = 0)
  · have hnonpositive := hraw.upper.first 2 2
    change quittingHalfFirstResidual (quittingRewardReindex e other) 1 1 ≤ 0 at hnonpositive
    have hpositive := unit_reindexed_halfFirst_corner_pos e hpair
    have hmass : continueMassExcl (halfFirstRow 1 1) 0 = 0 :=
      quittingCrossed_continueMassExcl_partner_one (halfFirstRow 1 1) 0 2
        (by decide) (by norm_num [halfFirstRow])
    have hchange := abs_quittingDiscountedDisplacement_sub_le_of_coordinate_error
      (quittingRewardReindex e unitCeilingReward) (quittingRewardReindex e other) error
      (fun terminal who => hclose ((quittingCoalitionEquiv e).symm terminal) (e.symm who))
      (halfFirstRow 1 1) 0 (by
        intro coordinate _
        fin_cases coordinate <;> norm_num [halfFirstRow])
    rw [hmass] at hchange
    change |quittingHalfFirstResidual (quittingRewardReindex e other) 1 1 -
      quittingHalfFirstResidual (quittingRewardReindex e unitCeilingReward) 1 1| ≤
        2 * error * (1 - 0) at hchange
    have hlower := (abs_le.mp hchange).1
    linarith
  · have hdistinct : e.symm (0 : Fin 4) ≠ e.symm 1 :=
      fun h => (by norm_num : (0 : Fin 4) ≠ 1) (e.symm.injective h)
    rcases unit_lower_violation (e.symm 0) (e.symm 1) hdistinct hpair with
      ⟨coalition, hnonempty, hsubset, hgap⟩ | ⟨coalition, hnonempty, hsubset, hgap⟩
    · exact not_weakLowerRanking_of_source_gap other error herror hclose
        (e.symm 0) (e.symm 1) coalition hnonempty hsubset hgap
        (weakLowerRanking_of_reindex e other 0 1 hraw.lowerFirst)
    · exact not_weakLowerRanking_of_source_gap other error herror hclose
        (e.symm 1) (e.symm 0) coalition hnonempty hsubset hgap
        (weakLowerRanking_of_reindex e other 1 0 hraw.lowerSecond)

/-- Ordinary full-table distance retains all sixty independent source coordinates. -/
theorem unitCeiling_not_reindexed_weakHalfRawGuards_of_dist_lt
    (other : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hclose : dist other unitCeilingReward < 1 / 1000) (e : Fin 4 ≃ Fin 4) :
    ¬QuittingHalfWeakRawGuards (quittingRewardReindex e other) := by
  apply unitCeiling_not_reindexed_weakHalfRawGuards_of_coordinate_error
    other (dist other unitCeilingReward) hclose _ e
  intro terminal who
  simpa only [Real.dist_eq] using
    (dist_le_pi_dist (other terminal) (unitCeilingReward terminal) who).trans
      (dist_le_pi_dist other unitCeilingReward terminal)

end GameTheory.GuardedCrossedResponseExamples
