import UniformEquilibrium.Quitting.Stationary.RewardRowTranslation
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakBoundaryProducer

/-! # Actual crossed guards are invariant under terminal recipient-row translations

These are identities of the source matrix, residual polynomials, and raw
tests. They are not strategic equivalence for arbitrary profiles with Never.
-/

noncomputable section

namespace GameTheory

variable {n : ℕ}

/-- Lower-ranking tests inspect only the selected recipient's terminal row. -/
theorem quittingCrossedStrictLowerRanking_congr_recipient
    (reward other : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (recipient partner : Fin n) (hrow : ∀ terminal, other terminal recipient =
      reward terminal recipient) :
    QuittingCrossedStrictLowerRanking other recipient partner ↔
      QuittingCrossedStrictLowerRanking reward recipient partner := by
  unfold QuittingCrossedStrictLowerRanking
  simp_rw [weightOfReward_congr_recipient reward other recipient hrow]

theorem quittingCrossedSourceGuards_playerwiseTranslation_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (shift : Payoff (Fin n)) (first second : Fin n) (height : ℝ) :
    QuittingCrossedSourceGuards (quittingPlayerwiseAffineReward reward 1 shift)
        first second height ↔ QuittingCrossedSourceGuards reward first second height := by
  constructor <;> intro h <;> exact
    ⟨by simpa only [quittingDiscountedDisplacement_zero_playerwiseTranslation] using h.lowerFirst,
      by simpa only [quittingDiscountedDisplacement_zero_playerwiseTranslation] using h.lowerSecond,
      by simpa only [quittingDiscountedDisplacement_zero_playerwiseTranslation] using h.upperFirst,
      by simpa only [quittingDiscountedDisplacement_zero_playerwiseTranslation] using h.upperSecond⟩

theorem quittingCrossedStrictLowerRanking_playerwiseTranslation_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (shift : Payoff (Fin n)) (recipient partner : Fin n) :
    QuittingCrossedStrictLowerRanking (quittingPlayerwiseAffineReward reward 1 shift)
        recipient partner ↔ QuittingCrossedStrictLowerRanking reward recipient partner := by
  have hcomparison (own other : Finset (Fin n)) (hnonempty : other.Nonempty) :
      weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) other recipient <
          weightOfReward (quittingPlayerwiseAffineReward reward 1 shift)
            (insert recipient own) recipient ↔
        weightOfReward reward other recipient <
          weightOfReward reward (insert recipient own) recipient := by
    rw [weightOfReward_playerwiseTranslation _ _ _ hnonempty,
      weightOfReward_playerwiseTranslation _ _ _ (Finset.insert_nonempty _ _)]
    exact add_lt_add_iff_right _
  constructor
  · intro h own other hown hother hnonempty
    exact (hcomparison own other hnonempty).mp (h own other hown hother hnonempty)
  · intro h own other hown hother hnonempty
    exact (hcomparison own other hnonempty).mpr (h own other hown hother hnonempty)

theorem quittingCrossedStrictUnitJoining_playerwiseTranslation_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (shift : Payoff (Fin n)) (recipient partner : Fin n) :
    QuittingCrossedStrictUnitJoining (quittingPlayerwiseAffineReward reward 1 shift)
        recipient partner ↔ QuittingCrossedStrictUnitJoining reward recipient partner := by
  unfold QuittingCrossedStrictUnitJoining
  simp only [weightOfReward_playerwiseTranslation _ _ _ (Finset.insert_nonempty _ _),
    add_lt_add_iff_right]

theorem quittingCrossedStrictRawUnitGuards_playerwiseTranslation_iff
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (shift : Payoff (Fin n)) (first second : Fin n) :
    QuittingCrossedStrictRawUnitGuards (quittingPlayerwiseAffineReward reward 1 shift)
        first second ↔ QuittingCrossedStrictRawUnitGuards reward first second := by
  constructor
  · intro h
    exact ⟨(quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerFirst,
      (quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerSecond,
      (quittingCrossedStrictUnitJoining_playerwiseTranslation_iff _ _ _ _).mp h.upperFirst,
      (quittingCrossedStrictUnitJoining_playerwiseTranslation_iff _ _ _ _).mp h.upperSecond⟩
  · intro h
    exact ⟨(quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerFirst,
      (quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerSecond,
      (quittingCrossedStrictUnitJoining_playerwiseTranslation_iff _ _ _ _).mpr h.upperFirst,
      (quittingCrossedStrictUnitJoining_playerwiseTranslation_iff _ _ _ _).mpr h.upperSecond⟩

theorem quittingHalfFirstResidual_playerwiseTranslation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    quittingHalfFirstResidual (quittingPlayerwiseAffineReward reward 1 shift) =
      quittingHalfFirstResidual reward := by
  funext x y
  exact quittingDiscountedDisplacement_zero_playerwiseTranslation reward shift (halfFirstRow x y) 0

theorem quittingHalfSecondResidual_playerwiseTranslation
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    quittingHalfSecondResidual (quittingPlayerwiseAffineReward reward 1 shift) =
      quittingHalfSecondResidual reward := by
  funext x y
  exact quittingDiscountedDisplacement_zero_playerwiseTranslation reward shift (halfSecondRow x y) 1

theorem quittingHalfStrictBernsteinUpper_playerwiseTranslation_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    QuittingHalfStrictBernsteinUpper (quittingPlayerwiseAffineReward reward 1 shift) ↔
      QuittingHalfStrictBernsteinUpper reward := by
  constructor <;> intro h <;> exact
    ⟨by simpa only [quittingHalfFirstResidual_playerwiseTranslation] using h.first,
      by simpa only [quittingHalfSecondResidual_playerwiseTranslation] using h.second⟩

theorem quittingHalfStrictRawGuards_playerwiseTranslation_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    QuittingHalfStrictRawGuards (quittingPlayerwiseAffineReward reward 1 shift) ↔
      QuittingHalfStrictRawGuards reward := by
  constructor
  · intro h
    exact ⟨(quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerFirst,
      (quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerSecond,
      (quittingHalfStrictBernsteinUpper_playerwiseTranslation_iff _ _).mp h.upper⟩
  · intro h
    exact ⟨(quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerFirst,
      (quittingCrossedStrictLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerSecond,
      (quittingHalfStrictBernsteinUpper_playerwiseTranslation_iff _ _).mpr h.upper⟩

theorem quittingCrossedWeakLowerRanking_playerwiseTranslation_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (shift : Payoff (Fin 4)) (recipient partner : Fin 4) :
    QuittingCrossedWeakLowerRanking (quittingPlayerwiseAffineReward reward 1 shift)
        recipient partner ↔ QuittingCrossedWeakLowerRanking reward recipient partner := by
  have hcomparison (own other : Finset (Fin 4)) (hnonempty : other.Nonempty) :
      weightOfReward (quittingPlayerwiseAffineReward reward 1 shift) other recipient ≤
          weightOfReward (quittingPlayerwiseAffineReward reward 1 shift)
            (insert recipient own) recipient ↔
        weightOfReward reward other recipient ≤
          weightOfReward reward (insert recipient own) recipient := by
    rw [weightOfReward_playerwiseTranslation _ _ _ hnonempty,
      weightOfReward_playerwiseTranslation _ _ _ (Finset.insert_nonempty _ _)]
    exact add_le_add_iff_right _
  constructor
  · intro h own other hown hother hnonempty
    exact (hcomparison own other hnonempty).mp (h own other hown hother hnonempty)
  · intro h own other hown hother hnonempty
    exact (hcomparison own other hnonempty).mpr (h own other hown hother hnonempty)

theorem quittingHalfWeakBernsteinUpper_playerwiseTranslation_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    QuittingHalfWeakBernsteinUpper (quittingPlayerwiseAffineReward reward 1 shift) ↔
      QuittingHalfWeakBernsteinUpper reward := by
  constructor <;> intro h <;> exact
    ⟨by simpa only [quittingHalfFirstResidual_playerwiseTranslation] using h.first,
      by simpa only [quittingHalfSecondResidual_playerwiseTranslation] using h.second⟩

theorem quittingHalfWeakRawGuards_playerwiseTranslation_iff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)) (shift : Payoff (Fin 4)) :
    QuittingHalfWeakRawGuards (quittingPlayerwiseAffineReward reward 1 shift) ↔
      QuittingHalfWeakRawGuards reward := by
  constructor
  · intro h
    exact ⟨(quittingCrossedWeakLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerFirst,
      (quittingCrossedWeakLowerRanking_playerwiseTranslation_iff _ _ _ _).mp h.lowerSecond,
      (quittingHalfWeakBernsteinUpper_playerwiseTranslation_iff _ _).mp h.upper⟩
  · intro h
    exact ⟨(quittingCrossedWeakLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerFirst,
      (quittingCrossedWeakLowerRanking_playerwiseTranslation_iff _ _ _ _).mpr h.lowerSecond,
      (quittingHalfWeakBernsteinUpper_playerwiseTranslation_iff _ _).mpr h.upper⟩

end GameTheory
