import UniformEquilibrium.Quitting.Classification.ProductLowQuittingPremiumPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Hazard degree of singleton-relative quitting premiums

The polynomial is obtained by fixing the reward coordinates in the existing
joint reward-hazard polynomial. Degree at most one in each hazard is the
multiaffinity assertion; the total-degree bound counts hazards only.
-/

noncomputable section

namespace GameTheory

variable {n : Nat}

/-- Specialize the reward block of the existing joint polynomial to an actual
real reward table, leaving precisely the hazard variables free. -/
def quittingFixedRewardPremiumPolynomial
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.append (fun index => MvPolynomial.C (quittingRewardTableCoordinates reward index))
      MvPolynomial.X) (quittingProductLowPremiumPolynomial player)

/-- The specialization is the literal opponent-coalition premium polynomial. -/
theorem quittingFixedRewardPremiumPolynomial_eq_sum
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) :
    quittingFixedRewardPremiumPolynomial reward player =
      ∑ coalition ∈ (Finset.univ.erase player).powerset,
        ((∏ other ∈ coalition, MvPolynomial.X other) *
          ∏ other ∈ Finset.univ.erase player \ coalition,
            (1 - MvPolynomial.X other)) *
          MvPolynomial.C
            (reward ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player -
              reward (quittingSingletonTerminal player) player) := by
  simp only [quittingFixedRewardPremiumPolynomial, quittingProductLowPremiumPolynomial,
    map_sum, map_mul, map_prod, map_sub, map_one, MvPolynomial.eval₂Hom_X',
    quittingProductLowHazardCoordinate, quittingProductLowRewardCoordinate,
    Fin.append_left, Fin.append_right, quittingRewardTableCoordinates,
    Equiv.symm_apply_apply]

/-- Evaluation agrees with the actual fixed-table hazard premium for every real
hazard vector, without restricting the hazards to the unit cube. -/
theorem eval_quittingFixedRewardPremiumPolynomial
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) (hazard : Fin n → ℝ) :
    MvPolynomial.eval hazard (quittingFixedRewardPremiumPolynomial reward player) =
      quittingHazardQuitPremium reward hazard player := by
  rw [quittingFixedRewardPremiumPolynomial_eq_sum]
  simp only [quittingHazardQuitPremium, map_sum, map_mul, map_prod, map_sub,
    map_one, MvPolynomial.eval_X, MvPolynomial.eval_C]

private theorem degrees_hazardProduct_le (set : Finset (Fin n)) :
    (∏ other ∈ set, (MvPolynomial.X other : MvPolynomial (Fin n) ℝ)).degrees ≤ set.val := by
  calc
    _ ≤ ∑ other ∈ set, (MvPolynomial.X other : MvPolynomial (Fin n) ℝ).degrees :=
      MvPolynomial.degrees_prod_le
    _ = set.val := by simp [Finset.sum_multiset_singleton]

private theorem degrees_continueProduct_le (set : Finset (Fin n)) :
    (∏ other ∈ set, (1 - MvPolynomial.X other : MvPolynomial (Fin n) ℝ)).degrees ≤
      set.val := by
  calc
    _ ≤ ∑ other ∈ set,
        (1 - MvPolynomial.X other : MvPolynomial (Fin n) ℝ).degrees :=
      MvPolynomial.degrees_prod_le
    _ ≤ ∑ other ∈ set, ({other} : Multiset (Fin n)) := by
      apply Finset.sum_le_sum
      intro other _
      simpa using (MvPolynomial.degrees_sub_le
        (p := (1 : MvPolynomial (Fin n) ℝ)) (q := MvPolynomial.X other))
    _ = set.val := Finset.sum_multiset_singleton set

/-- Every variable occurs at most once, and the quitting player's own hazard
does not occur at all. This multiset bound also yields the total-degree bound. -/
theorem degrees_quittingFixedRewardPremiumPolynomial_le
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) :
    (quittingFixedRewardPremiumPolynomial reward player).degrees ≤
      (Finset.univ.erase player).val := by
  rw [quittingFixedRewardPremiumPolynomial_eq_sum]
  apply MvPolynomial.degrees_sum_le _ _ |>.trans
  apply Finset.sup_le
  intro coalition hcoalition
  have hsubset := Finset.mem_powerset.mp hcoalition
  calc
    _ ≤ (((∏ other ∈ coalition, (MvPolynomial.X other : MvPolynomial (Fin n) ℝ)) *
          ∏ other ∈ Finset.univ.erase player \ coalition,
            (1 - MvPolynomial.X other)).degrees + 0) := by
      simpa only [MvPolynomial.degrees_C] using
        (MvPolynomial.degrees_mul_le (p :=
          (∏ other ∈ coalition, (MvPolynomial.X other : MvPolynomial (Fin n) ℝ)) *
            ∏ other ∈ Finset.univ.erase player \ coalition,
              (1 - MvPolynomial.X other))
          (q := MvPolynomial.C
            (reward ⟨insert player coalition, Finset.insert_nonempty player coalition⟩ player -
              reward (quittingSingletonTerminal player) player)))
    _ ≤ coalition.val + (Finset.univ.erase player \ coalition).val := by
      rw [add_zero]
      exact MvPolynomial.degrees_mul_le.trans
        (add_le_add (degrees_hazardProduct_le coalition)
          (degrees_continueProduct_le _))
    _ = (Finset.univ.erase player).val := by
      rw [Finset.sdiff_val]
      exact add_tsub_cancel_of_le (Finset.val_le_iff.mpr hsubset)

/-- The fixed-reward premium is multiaffine: its degree in every individual
hazard variable is at most one. -/
theorem degreeOf_quittingFixedRewardPremiumPolynomial_le_one
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player other : Fin n) :
    (quittingFixedRewardPremiumPolynomial reward player).degreeOf other ≤ 1 := by
  rw [MvPolynomial.degreeOf_def]
  exact (Multiset.count_le_of_le other
    (degrees_quittingFixedRewardPremiumPolynomial_le reward player)).trans
      ((Multiset.nodup_iff_count_le_one.mp (Finset.univ.erase player).nodup) other)

/-- A player's pure-Quit premium has degree zero in that player's own hazard. -/
theorem degreeOf_quittingFixedRewardPremiumPolynomial_self
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) :
    (quittingFixedRewardPremiumPolynomial reward player).degreeOf player = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [MvPolynomial.degreeOf_def]
  simpa using Multiset.count_le_of_le player
    (degrees_quittingFixedRewardPremiumPolynomial_le reward player)

/-- With rewards fixed, the total hazard degree is at most the number of
opponents. No degree restriction is imposed on the joint reward coordinates. -/
theorem totalDegree_quittingFixedRewardPremiumPolynomial_le
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (player : Fin n) :
    (quittingFixedRewardPremiumPolynomial reward player).totalDegree ≤ n - 1 := by
  calc
    _ ≤ (quittingFixedRewardPremiumPolynomial reward player).degrees.card :=
      MvPolynomial.totalDegree_le_degrees_card _
    _ ≤ (Finset.univ.erase player).val.card :=
      Multiset.card_le_card (degrees_quittingFixedRewardPremiumPolynomial_le reward player)
    _ = n - 1 := by simp

end GameTheory
