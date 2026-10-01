import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCeilingCoefficients
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import MathUE.Polynomial.TensorBernsteinQuadraticCoefficients
import MathUE.Polynomial.TensorBernsteinQuadraticPerturbation

/-! # Exact reward-coordinate norms of the actual half-face coefficient functionals

The fifteen coordinates are all nonempty terminal coalitions, in the
canonical binary-mask equivalence. Each basis table has one actual recipient
reward equal to one and every other terminal coordinate zero. Its coefficient
is evaluated in the actual reward-generated residual, not a surrogate bound.
-/

noncomputable section

namespace GameTheory

open QuittingFinFourEndpointRows

/-- One literal coordinate basis vector of the full nonempty terminal reward table. -/
def quittingRecipientRewardBasis
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (recipient : Fin 4) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun outcome who => if outcome = terminal ∧ who = recipient then 1 else 0

/-- The exact half-face residual of a single terminal coordinate. -/
def quittingHalfBasisPolynomial (recipient : Fin 4) (row : Fin 15) (x y : ℝ) : ℝ :=
  (1 / 2) * (if 2 ∈ Math.Finset.finFourCoalitionOfRow row then x else 1 - x) *
    (if 3 ∈ Math.Finset.finFourCoalitionOfRow row then y else 1 - y) *
    (if recipient ∈ Math.Finset.finFourCoalitionOfRow row then
      1 - (1 / 2) * (1 - x) * (1 - y) else -1)

private theorem half_displacement_eq_reward_coordinate_sum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hazard : Fin 4 → ℝ) (recipient : Fin 4) (x y : ℝ)
    (hsurvival : continueMassExcl hazard recipient = (1 / 2) * (1 - x) * (1 - y))
    (hmass : ∀ row : Fin 15,
      opponentCoalitionMass hazard recipient (Math.Finset.finFourCoalitionOfRow row) =
        (1 / 2) * (if 2 ∈ Math.Finset.finFourCoalitionOfRow row then x else 1 - x) *
          (if 3 ∈ Math.Finset.finFourCoalitionOfRow row then y else 1 - y)) :
    quittingDiscountedDisplacement reward 0 hazard recipient =
      ∑ row : Fin 15, quittingHalfBasisPolynomial recipient row x y *
        reward (Math.Finset.finFourCoalitionRowEquiv row) recipient := by
  have hweight (row : Fin 15) :
      weightOfReward reward (Math.Finset.finFourCoalitionOfRow row) recipient =
        reward (Math.Finset.finFourCoalitionRowEquiv row) recipient := by
    simp only [weightOfReward, dite_eq_left (Math.Finset.finFourCoalitionOfRow_nonempty row)]
    rfl
  rw [quittingDiscountedDisplacement, sigmaValue_eq_pureQuitEndpointRowSum,
    excludedValue_eq_excludedEndpointRowSum, hsurvival]
  simp only [sub_zero, one_mul, pureQuitEndpointRowSum, excludedEndpointRowSum, hweight]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row _
  by_cases hmem : recipient ∈ Math.Finset.finFourCoalitionOfRow row
  · simp only [hmem, not_true_eq_false, ite_true, ite_false, sub_zero,
      quittingHalfBasisPolynomial, hmass]
    ring
  · simp only [hmem, not_false_eq_true, ite_true, ite_false,
      quittingHalfBasisPolynomial, hmass]
    ring

/-- The actual first residual is linear in the fifteen recipient-zero rewards. -/
theorem quittingHalfFirstResidual_eq_reward_coordinate_sum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingHalfFirstResidual reward x y =
      ∑ row : Fin 15, quittingHalfBasisPolynomial 0 row x y *
        reward (Math.Finset.finFourCoalitionRowEquiv row) 0 := by
  apply half_displacement_eq_reward_coordinate_sum reward (halfFirstRow x y) 0 x y
  · rw [continueMassExcl,
      show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    simp [halfFirstRow]
    ring
  · intro row
    fin_cases row <;>
      simp [opponentCoalitionMass, Fin.prod_univ_succ, halfFirstRow,
        Math.Finset.finFourCoalitionOfRow] <;> ring

/-- The actual second residual is linear in the fifteen recipient-one rewards. -/
theorem quittingHalfSecondResidual_eq_reward_coordinate_sum
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (x y : ℝ) :
    quittingHalfSecondResidual reward x y =
      ∑ row : Fin 15, quittingHalfBasisPolynomial 1 row x y *
        reward (Math.Finset.finFourCoalitionRowEquiv row) 1 := by
  apply half_displacement_eq_reward_coordinate_sum reward (halfSecondRow x y) 1 x y
  · rw [continueMassExcl,
      show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    simp [halfSecondRow]
    ring
  · intro row
    fin_cases row <;>
      simp [opponentCoalitionMass, Fin.prod_univ_succ, halfSecondRow,
        Math.Finset.finFourCoalitionOfRow] <;> ring

/-- All fifteen first-recipient basis tables are evaluated in the actual source residual. -/
theorem quittingHalfFirstResidual_rewardBasis (row : Fin 15) :
    quittingHalfFirstResidual
        (quittingRecipientRewardBasis (Math.Finset.finFourCoalitionRowEquiv row) 0) =
      quittingHalfBasisPolynomial 0 row := by
  funext x y
  rw [quittingHalfFirstResidual_eq_reward_coordinate_sum]
  simp [quittingRecipientRewardBasis]

/-- All fifteen second-recipient basis tables are evaluated in the actual source residual. -/
theorem quittingHalfSecondResidual_rewardBasis (row : Fin 15) :
    quittingHalfSecondResidual
        (quittingRecipientRewardBasis (Math.Finset.finFourCoalitionRowEquiv row) 1) =
      quittingHalfBasisPolynomial 1 row := by
  funext x y
  rw [quittingHalfSecondResidual_eq_reward_coordinate_sum]
  simp [quittingRecipientRewardBasis]

/-- The literal coefficient functional is the dot product with its fifteen
actual basis-table coefficients, not merely bounded by such a vector. -/
theorem quittingHalfFirstCoefficient_eq_sum_basis
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual reward) first second =
      ∑ row : Fin 15,
        Math.quadraticTensorBernsteinCoefficient
            (quittingHalfFirstResidual
              (quittingRecipientRewardBasis (Math.Finset.finFourCoalitionRowEquiv row) 0))
            first second * reward (Math.Finset.finFourCoalitionRowEquiv row) 0 := by
  have hfunction : quittingHalfFirstResidual reward = fun x y =>
      ∑ row : Fin 15, quittingHalfBasisPolynomial 0 row x y *
        reward (Math.Finset.finFourCoalitionRowEquiv row) 0 := by
    funext x y
    exact quittingHalfFirstResidual_eq_reward_coordinate_sum reward x y
  rw [hfunction, Math.quadraticTensorBernsteinCoefficient_sum]
  simp_rw [Math.quadraticTensorBernsteinCoefficient_mul_const,
    quittingHalfFirstResidual_rewardBasis]

theorem quittingHalfSecondCoefficient_eq_sum_basis
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (first second : Fin 3) :
    Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual reward) first second =
      ∑ row : Fin 15,
        Math.quadraticTensorBernsteinCoefficient
            (quittingHalfSecondResidual
              (quittingRecipientRewardBasis (Math.Finset.finFourCoalitionRowEquiv row) 1))
            first second * reward (Math.Finset.finFourCoalitionRowEquiv row) 1 := by
  have hfunction : quittingHalfSecondResidual reward = fun x y =>
      ∑ row : Fin 15, quittingHalfBasisPolynomial 1 row x y *
        reward (Math.Finset.finFourCoalitionRowEquiv row) 1 := by
    funext x y
    exact quittingHalfSecondResidual_eq_reward_coordinate_sum reward x y
  rw [hfunction, Math.quadraticTensorBernsteinCoefficient_sum]
  simp_rw [Math.quadraticTensorBernsteinCoefficient_mul_const,
    quittingHalfSecondResidual_rewardBasis]

private theorem sum_abs_halfBasisCoefficient_recipientZero_firstZero
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 0 row) 0 second|) =
        Math.halfSurvivalBernsteinErrorFactor 0 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient_recipientZero_firstOne
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 0 row) 1 second|) =
        Math.halfSurvivalBernsteinErrorFactor 1 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient_recipientZero_firstTwo
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 0 row) 2 second|) =
        Math.halfSurvivalBernsteinErrorFactor 2 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient_recipientOne_firstZero
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 1 row) 0 second|) =
        Math.halfSurvivalBernsteinErrorFactor 0 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient_recipientOne_firstOne
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 1 row) 1 second|) =
        Math.halfSurvivalBernsteinErrorFactor 1 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient_recipientOne_firstTwo
    (second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial 1 row) 2 second|) =
        Math.halfSurvivalBernsteinErrorFactor 2 second := by
  fin_cases second
  all_goals norm_num +decide [Fin.sum_univ_succ, quittingHalfBasisPolynomial,
    Math.Finset.finFourCoalitionOfRow, Math.quadraticTensorBernsteinCoefficient,
    Math.quadraticBernsteinCoefficient, Math.halfSurvivalBernsteinErrorFactor]

private theorem sum_abs_halfBasisCoefficient (recipient : Fin 4)
    (hrecipient : recipient = 0 ∨ recipient = 1) (first second : Fin 3) :
    (∑ row : Fin 15, |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial recipient row) first second|) =
        Math.halfSurvivalBernsteinErrorFactor first second := by
  rcases hrecipient with rfl | rfl
  · fin_cases first
    · exact sum_abs_halfBasisCoefficient_recipientZero_firstZero second
    · exact sum_abs_halfBasisCoefficient_recipientZero_firstOne second
    · exact sum_abs_halfBasisCoefficient_recipientZero_firstTwo second
  · fin_cases first
    · exact sum_abs_halfBasisCoefficient_recipientOne_firstZero second
    · exact sum_abs_halfBasisCoefficient_recipientOne_firstOne second
    · exact sum_abs_halfBasisCoefficient_recipientOne_firstTwo second

/-- Packet (7.5) is the exact reward-coordinate l1 norm of the first
functional: [1,3/2,2;3/2,7/4,2;2,2,2], not only an upper bound. -/
theorem quittingHalfFirstCoefficient_reward_l1_norm (first second : Fin 3) :
    (∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
      |Math.quadraticTensorBernsteinCoefficient
        (quittingHalfFirstResidual (quittingRecipientRewardBasis terminal 0)) first second|) =
      Math.halfSurvivalBernsteinErrorFactor first second := by
  rw [← Equiv.sum_comp Math.Finset.finFourCoalitionRowEquiv
    (fun terminal => |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfFirstResidual (quittingRecipientRewardBasis terminal 0)) first second|)]
  simp_rw [quittingHalfFirstResidual_rewardBasis]
  exact sum_abs_halfBasisCoefficient 0 (Or.inl rfl) first second

/-- The same exact coordinate norm array holds for the second recipient. -/
theorem quittingHalfSecondCoefficient_reward_l1_norm (first second : Fin 3) :
    (∑ terminal : {S : Finset (Fin 4) // S.Nonempty},
      |Math.quadraticTensorBernsteinCoefficient
        (quittingHalfSecondResidual (quittingRecipientRewardBasis terminal 1)) first second|) =
      Math.halfSurvivalBernsteinErrorFactor first second := by
  rw [← Equiv.sum_comp Math.Finset.finFourCoalitionRowEquiv
    (fun terminal => |Math.quadraticTensorBernsteinCoefficient
      (quittingHalfSecondResidual (quittingRecipientRewardBasis terminal 1)) first second|)]
  simp_rw [quittingHalfSecondResidual_rewardBasis]
  exact sum_abs_halfBasisCoefficient 1 (Or.inr rfl) first second

/-- The displayed tensor expansion of the actual first residual is unique. -/
theorem quittingHalfFirstCoefficient_unique
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coefficients : Fin 3 → Fin 3 → ℝ)
    (hexpansion : ∀ x y, quittingHalfFirstResidual reward x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        coefficients first second * Math.quadraticBernsteinBasis first x *
          Math.quadraticBernsteinBasis second y) :
    coefficients = Math.quadraticTensorBernsteinCoefficient (quittingHalfFirstResidual reward) := by
  funext first second
  exact Math.eq_quadraticTensorBernsteinCoefficient_of_reconstruction
    _ coefficients hexpansion first second

/-- The displayed tensor expansion of the actual second residual is unique. -/
theorem quittingHalfSecondCoefficient_unique
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (coefficients : Fin 3 → Fin 3 → ℝ)
    (hexpansion : ∀ x y, quittingHalfSecondResidual reward x y =
      ∑ first : Fin 3, ∑ second : Fin 3,
        coefficients first second * Math.quadraticBernsteinBasis first x *
          Math.quadraticBernsteinBasis second y) :
    coefficients =
      Math.quadraticTensorBernsteinCoefficient (quittingHalfSecondResidual reward) := by
  funext first second
  exact Math.eq_quadraticTensorBernsteinCoefficient_of_reconstruction
    _ coefficients hexpansion first second

end GameTheory
