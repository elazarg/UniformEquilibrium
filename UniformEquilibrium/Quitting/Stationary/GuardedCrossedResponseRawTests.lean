import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawResidual
import MathUE.Finset.ProdLtOne

/-! # Finite strict reward-table tests for crossed source guards -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {n : ℕ}

/-- Packet (L), expanded as all finite comparisons behind its minimum and maximum. -/
def QuittingCrossedStrictLowerRanking
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n) : Prop :=
  ∀ own other : Finset (Fin n),
    own ⊆ quittingCrossedRawOutsiders recipient partner →
    other ⊆ quittingCrossedRawOutsiders recipient partner →
    other.Nonempty →
    weightOfReward reward other recipient <
      weightOfReward reward (insert recipient own) recipient

/-- Packet (U), the strict joining comparison for every outsider coalition. -/
def QuittingCrossedStrictUnitJoining
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n) : Prop :=
  ∀ outsider : Finset (Fin n),
    outsider ⊆ quittingCrossedRawOutsiders recipient partner →
    weightOfReward reward (insert recipient (insert partner outsider)) recipient <
      weightOfReward reward (insert partner outsider) recipient

private theorem rawBernoulliWeight_nonneg
    (hazard : Fin n → ℝ) (carrier subset : Finset (Fin n))
    (hsubset : subset ⊆ carrier)
    (hbox : ∀ coordinate ∈ carrier, 0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    0 ≤ bernoulliWeight hazard carrier subset := by
  unfold bernoulliWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg fun coordinate hcoordinate =>
      (hbox coordinate (hsubset hcoordinate)).1
  · exact Finset.prod_nonneg fun coordinate hcoordinate =>
      sub_nonneg.mpr (hbox coordinate (Finset.mem_sdiff.mp hcoordinate).1).2

private theorem exists_rawBernoulliWeight_pos
    (hazard : Fin n → ℝ) (carrier : Finset (Fin n))
    (hbox : ∀ coordinate ∈ carrier, 0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    ∃ subset ∈ carrier.powerset, 0 < bernoulliWeight hazard carrier subset := by
  by_contra hnone
  have hzero : ∀ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset = 0 := by
    intro subset hsubset
    exact le_antisymm
      (le_of_not_gt (fun hpositive => hnone ⟨subset, hsubset, hpositive⟩))
      (rawBernoulliWeight_nonneg hazard carrier subset
        (Finset.mem_powerset.mp hsubset) hbox)
  have hsum := sum_bernoulliWeight hazard carrier
  rw [Finset.sum_eq_zero hzero] at hsum
  norm_num at hsum

/-- Every strict joining comparison makes the literal sure-partner residual negative. -/
theorem quittingCrossed_displacement_partner_one_neg_of_unitJoining
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hone : hazard partner = 1)
    (hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1)
    (hjoining : QuittingCrossedStrictUnitJoining reward recipient partner) :
    quittingDiscountedDisplacement reward 0 hazard recipient < 0 := by
  rw [quittingCrossed_displacement_partner_one_eq_sum_joining
    reward hazard recipient partner hne hone]
  let carrier := quittingCrossedRawOutsiders recipient partner
  have hpositive : 0 < ∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset *
        (weightOfReward reward (insert partner subset) recipient -
          weightOfReward reward (insert recipient (insert partner subset)) recipient) := by
    obtain ⟨subset, hsubset, hmass⟩ :=
      exists_rawBernoulliWeight_pos hazard carrier hbox
    apply Finset.sum_pos'
    · intro other hother
      exact mul_nonneg
        (rawBernoulliWeight_nonneg hazard carrier other
          (Finset.mem_powerset.mp hother) hbox)
        (sub_nonneg.mpr (hjoining other (Finset.mem_powerset.mp hother)).le)
    · exact ⟨subset, hsubset, mul_pos hmass
        (sub_pos.mpr (hjoining subset (Finset.mem_powerset.mp hsubset)))⟩
  have hneg :
      (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset *
          (weightOfReward reward (insert recipient (insert partner subset)) recipient -
            weightOfReward reward (insert partner subset) recipient)) =
        -(∑ subset ∈ carrier.powerset,
          bernoulliWeight hazard carrier subset *
            (weightOfReward reward (insert partner subset) recipient -
              weightOfReward reward (insert recipient (insert partner subset)) recipient)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro subset _
    ring
  change (∑ subset ∈ carrier.powerset,
    bernoulliWeight hazard carrier subset *
      (weightOfReward reward (insert recipient (insert partner subset)) recipient -
        weightOfReward reward (insert partner subset) recipient)) < 0
  rw [hneg]
  linarith

/-- A positive outsider hazard makes the outsiders' all-Continue mass strictly
less than one. -/
private theorem rawOutsiderSurvival_lt_one
    (hazard : Fin n → ℝ) (carrier : Finset (Fin n))
    (hbox : ∀ coordinate ∈ carrier, 0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1)
    (hactive : ∃ coordinate ∈ carrier, 0 < hazard coordinate) :
    (∏ coordinate ∈ carrier, (1 - hazard coordinate)) < 1 := by
  obtain ⟨witness, hwitness, hpositive⟩ := hactive
  apply Math.Finset.prod_lt_one_of_mem carrier (fun coordinate => 1 - hazard coordinate)
    witness hwitness
  · intro coordinate hcoordinate _
    exact sub_nonneg.mpr (hbox coordinate hcoordinate).2
  · intro coordinate hcoordinate _
    linarith [(hbox coordinate hcoordinate).1]
  · linarith

/-- Packet (L) makes the partner-zero source residual positive as soon as
some outsider has positive hazard. -/
theorem quittingCrossed_displacement_partner_zero_pos_of_lowerRanking
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (hazard : Fin n → ℝ) (recipient partner : Fin n)
    (hne : partner ≠ recipient) (hzero : hazard partner = 0)
    (hbox : ∀ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1)
    (hactive : ∃ coordinate ∈ quittingCrossedRawOutsiders recipient partner,
      0 < hazard coordinate)
    (hranking : QuittingCrossedStrictLowerRanking reward recipient partner) :
    0 < quittingDiscountedDisplacement reward 0 hazard recipient := by
  let carrier := quittingCrossedRawOutsiders recipient partner
  obtain ⟨active, hactiveCarrier, hactivePos⟩ := hactive
  have hnonempty : (carrier.powerset.erase (∅ : Finset (Fin n))).Nonempty := by
    refine ⟨{active}, ?_⟩
    apply Finset.mem_erase.mpr
    constructor
    · simp
    · apply Finset.mem_powerset.mpr
      exact Finset.singleton_subset_iff.mpr hactiveCarrier
  let baseline := (carrier.powerset.erase (∅ : Finset (Fin n))).sup' hnonempty
    (fun subset => weightOfReward reward subset recipient)
  have hpassive (subset : Finset (Fin n))
      (hsubset : subset ∈ carrier.powerset.erase (∅ : Finset (Fin n))) :
      weightOfReward reward subset recipient ≤ baseline :=
    Finset.le_sup' (fun subset => weightOfReward reward subset recipient) hsubset
  have hown (subset : Finset (Fin n)) (hsubset : subset ∈ carrier.powerset) :
      baseline < weightOfReward reward (insert recipient subset) recipient := by
    apply (Finset.sup'_lt_iff hnonempty).2
    intro other hother
    have hotherSubset := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hother)
    have hotherNonempty : other.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hother)
    exact hranking subset other (Finset.mem_powerset.mp hsubset)
      hotherSubset hotherNonempty
  have hmass := sum_bernoulliWeight hazard carrier
  have hQgt : baseline < ∑ subset ∈ carrier.powerset,
      bernoulliWeight hazard carrier subset *
        weightOfReward reward (insert recipient subset) recipient := by
    have hpositive : 0 < ∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset *
          (weightOfReward reward (insert recipient subset) recipient - baseline) := by
      obtain ⟨subset, hsubset, hweight⟩ :=
        exists_rawBernoulliWeight_pos hazard carrier hbox
      apply Finset.sum_pos'
      · intro other hother
        exact mul_nonneg
          (rawBernoulliWeight_nonneg hazard carrier other
            (Finset.mem_powerset.mp hother) hbox)
          (sub_nonneg.mpr (hown other hother).le)
      · exact ⟨subset, hsubset, mul_pos hweight (sub_pos.mpr (hown subset hsubset))⟩
    have hrewrite :
        (∑ subset ∈ carrier.powerset,
          bernoulliWeight hazard carrier subset *
            (weightOfReward reward (insert recipient subset) recipient - baseline)) =
          (∑ subset ∈ carrier.powerset,
            bernoulliWeight hazard carrier subset *
              weightOfReward reward (insert recipient subset) recipient) -
            (∑ subset ∈ carrier.powerset,
              bernoulliWeight hazard carrier subset) * baseline := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hrewrite, hmass, one_mul] at hpositive
    exact sub_pos.mp hpositive
  have hempty : (∅ : Finset (Fin n)) ∈ carrier.powerset :=
    Finset.empty_mem_powerset carrier
  have hsplit := Finset.sum_erase_add carrier.powerset
    (bernoulliWeight hazard carrier) hempty
  have hemptyWeight : bernoulliWeight hazard carrier ∅ =
      ∏ coordinate ∈ carrier, (1 - hazard coordinate) := by
    simp [bernoulliWeight]
  rw [hemptyWeight] at hsplit
  have hHle :
      (∑ subset ∈ carrier.powerset,
        bernoulliWeight hazard carrier subset *
          weightOfReward reward subset recipient) ≤
        (1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate)) * baseline := by
    have hzeroEmpty : bernoulliWeight hazard carrier ∅ *
        weightOfReward reward ∅ recipient = 0 := by
      simp [weightOfReward]
    have hsumEq :
        (∑ subset ∈ carrier.powerset,
          bernoulliWeight hazard carrier subset *
            weightOfReward reward subset recipient) =
          ∑ subset ∈ carrier.powerset.erase (∅ : Finset (Fin n)),
            bernoulliWeight hazard carrier subset *
              weightOfReward reward subset recipient := by
      have h := Finset.sum_erase_add carrier.powerset
        (fun subset => bernoulliWeight hazard carrier subset *
          weightOfReward reward subset recipient) hempty
      rw [hzeroEmpty, add_zero] at h
      exact h.symm
    rw [hsumEq]
    calc
      (∑ subset ∈ carrier.powerset.erase (∅ : Finset (Fin n)),
        bernoulliWeight hazard carrier subset *
          weightOfReward reward subset recipient) ≤
          ∑ subset ∈ carrier.powerset.erase (∅ : Finset (Fin n)),
            bernoulliWeight hazard carrier subset * baseline := by
              apply Finset.sum_le_sum
              intro subset hsubset
              exact mul_le_mul_of_nonneg_left (hpassive subset hsubset)
                (rawBernoulliWeight_nonneg hazard carrier subset
                  (Finset.mem_powerset.mp (Finset.mem_of_mem_erase hsubset)) hbox)
      _ = (1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate)) * baseline := by
        rw [← Finset.sum_mul]
        congr 1
        linarith
  have hfactor : 0 < 1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate) := by
    have hlt := rawOutsiderSurvival_lt_one hazard carrier hbox
      ⟨active, hactiveCarrier, hactivePos⟩
    linarith
  rw [quittingCrossed_displacement_partner_zero_eq_sums
    reward hazard recipient partner hne hzero]
  nlinarith [mul_lt_mul_of_pos_left hQgt hfactor]

end GameTheory
