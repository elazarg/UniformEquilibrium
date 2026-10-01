import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement
import MathUE.Finset.BernoulliBounds
import MathUE.DirectedTransport.FiniteInequality.Perturbation

/-! # Entrywise raw-reward errors in the actual coalition response sums -/

noncomputable section

namespace GameTheory

open Math.Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Only literal nonempty source coordinates are compared. -/
theorem abs_weightOfReward_sub_le_of_coordinate_error
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (coalition : Finset ι) (hnonempty : coalition.Nonempty) (who : ι) :
    |weightOfReward other coalition who - weightOfReward reward coalition who| ≤ error := by
  simpa only [weightOfReward, dite_eq_left hnonempty] using hclose ⟨coalition, hnonempty⟩ who

/-- Pure Quit is a probability-weighted sum of actual reward coordinates. -/
theorem abs_sigmaValue_sub_le_of_coordinate_error
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hazard : ι → ℝ) (who : ι)
    (hbox : ∀ coordinate ∈ Finset.univ.erase who,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    |sigmaValue (weightOfReward other) hazard who -
      sigmaValue (weightOfReward reward) hazard who| ≤ error := by
  classical
  let carrier := Finset.univ.erase who
  have h := Maths.FiniteInequality.abs_weightedSum_sub_le
    (fun subset : ↥carrier.powerset => bernoulliWeight hazard carrier subset.1)
    (fun subset => weightOfReward reward (insert who subset.1) who)
    (fun subset => weightOfReward other (insert who subset.1) who) error
    (fun subset => bernoulliWeight_nonneg_of_bounds hazard carrier subset.1
      (Finset.mem_powerset.mp subset.2) hbox)
    (fun subset => abs_weightOfReward_sub_le_of_coordinate_error reward other error hclose
      (insert who subset.1) (Finset.insert_nonempty who subset.1) who)
  have hsum (payoff : Finset ι → ℝ) :
      (∑ subset : ↥carrier.powerset,
        bernoulliWeight hazard carrier subset.1 * payoff subset.1) =
      ∑ subset ∈ carrier.powerset, bernoulliWeight hazard carrier subset * payoff subset :=
    Finset.sum_coe_sort carrier.powerset (fun subset =>
      bernoulliWeight hazard carrier subset * payoff subset)
  have htotal : (∑ subset : ↥carrier.powerset,
      bernoulliWeight hazard carrier subset.1) = 1 :=
    (Finset.sum_coe_sort carrier.powerset (bernoulliWeight hazard carrier)).trans
      (sum_bernoulliWeight hazard carrier)
  rw [hsum (fun subset => weightOfReward other (insert who subset) who),
    hsum (fun subset => weightOfReward reward (insert who subset) who), htotal, mul_one] at h
  simpa only [carrier, sigmaValue, bernoulliWeight] using h

/-- Pure Continue uses precisely the nonempty opponents' absorption mass. -/
theorem abs_excludedValue_sub_le_of_coordinate_error
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hazard : ι → ℝ) (who : ι)
    (hbox : ∀ coordinate ∈ Finset.univ.erase who,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    |excludedValue (weightOfReward other) hazard who -
      excludedValue (weightOfReward reward) hazard who| ≤
      error * (1 - continueMassExcl hazard who) := by
  classical
  let carrier := Finset.univ.erase who
  have h := Maths.FiniteInequality.abs_weightedSum_sub_le
    (fun subset : ↥(carrier.powerset.erase ∅) => bernoulliWeight hazard carrier subset.1)
    (fun subset => weightOfReward reward subset.1 who)
    (fun subset => weightOfReward other subset.1 who) error
    (fun subset => bernoulliWeight_nonneg_of_bounds hazard carrier subset.1
      (Finset.mem_powerset.mp (Finset.mem_of_mem_erase subset.2)) hbox)
    (fun subset => abs_weightOfReward_sub_le_of_coordinate_error reward other error hclose
      subset.1 (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp subset.2).1) who)
  have hsum (payoff : Finset ι → ℝ) :
      (∑ subset : ↥(carrier.powerset.erase ∅),
        bernoulliWeight hazard carrier subset.1 * payoff subset.1) =
      ∑ subset ∈ carrier.powerset.erase ∅,
        bernoulliWeight hazard carrier subset * payoff subset :=
    Finset.sum_coe_sort (carrier.powerset.erase ∅) (fun subset =>
      bernoulliWeight hazard carrier subset * payoff subset)
  have htotal : (∑ subset : ↥(carrier.powerset.erase ∅),
      bernoulliWeight hazard carrier subset.1) =
      1 - ∏ coordinate ∈ carrier, (1 - hazard coordinate) :=
    (Finset.sum_coe_sort (carrier.powerset.erase ∅)
      (bernoulliWeight hazard carrier)).trans (sum_bernoulliWeight_erase_empty hazard carrier)
  rw [hsum (fun subset => weightOfReward other subset who),
    hsum (fun subset => weightOfReward reward subset who), htotal] at h
  simpa only [carrier, excludedValue, bernoulliWeight, continueMassExcl] using h

/-- The actual undiscounted response changes by at most twice the absorbed
opponents' mass times the raw coordinate error. This retains boundary hazards. -/
theorem abs_quittingDiscountedDisplacement_sub_le_of_coordinate_error
    (reward other : {S : Finset ι // S.Nonempty} → Payoff ι) (error : ℝ)
    (hclose : ∀ terminal who, |other terminal who - reward terminal who| ≤ error)
    (hazard : ι → ℝ) (who : ι)
    (hbox : ∀ coordinate ∈ Finset.univ.erase who,
      0 ≤ hazard coordinate ∧ hazard coordinate ≤ 1) :
    |quittingDiscountedDisplacement other 0 hazard who -
      quittingDiscountedDisplacement reward 0 hazard who| ≤
      2 * error * (1 - continueMassExcl hazard who) := by
  have hmass : 0 ≤ 1 - continueMassExcl hazard who := by
    apply sub_nonneg.mpr
    exact Finset.prod_le_one₀ (fun coordinate hcoordinate =>
      sub_nonneg.mpr (hbox coordinate hcoordinate).2)
      (fun coordinate hcoordinate => sub_le_self _ (hbox coordinate hcoordinate).1)
  have hquit := abs_sigmaValue_sub_le_of_coordinate_error reward other error hclose
    hazard who hbox
  have hcont := abs_excludedValue_sub_le_of_coordinate_error reward other error hclose
    hazard who hbox
  calc
    _ = |(1 - continueMassExcl hazard who) *
        (sigmaValue (weightOfReward other) hazard who -
          sigmaValue (weightOfReward reward) hazard who) -
        (excludedValue (weightOfReward other) hazard who -
          excludedValue (weightOfReward reward) hazard who)| := by
      congr 1
      simp only [quittingDiscountedDisplacement, sub_zero, one_mul]
      ring
    _ ≤ |(1 - continueMassExcl hazard who) *
        (sigmaValue (weightOfReward other) hazard who -
          sigmaValue (weightOfReward reward) hazard who)| +
        |excludedValue (weightOfReward other) hazard who -
          excludedValue (weightOfReward reward) hazard who| := abs_sub _ _
    _ ≤ (1 - continueMassExcl hazard who) * error +
        error * (1 - continueMassExcl hazard who) := by
      rw [abs_mul, abs_of_nonneg hmass]
      exact add_le_add (mul_le_mul_of_nonneg_left hquit hmass) hcont
    _ = _ := by ring

end GameTheory
