import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculation
import UniformEquilibrium.Quitting.Stationary.DiscountedDisplacement

/-! # Actual stationary response on a singleton hazard axis -/

noncomputable section

namespace GameTheory

variable {n : ℕ}

/-- Exact two-coalition expansion with one active opponent. -/
theorem quittingDiscountedDisplacement_singletonRow_of_ne
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    {owner recipient : Fin n} (hne : recipient ≠ owner) (rate : ℝ) :
    quittingDiscountedDisplacement reward 0 (singletonRow rate owner) recipient =
      rate * ((1 - rate) * (weightOfReward reward) {recipient} recipient +
        rate * (weightOfReward reward) {recipient, owner} recipient -
        (weightOfReward reward) {owner} recipient) := by
  unfold quittingDiscountedDisplacement
  rw [sigmaValue_singletonRow_of_ne (weightOfReward reward) rate hne,
    excludedValue_singletonRow_of_ne (weightOfReward reward) rate hne]
  unfold continueMassExcl
  rw [prod_one_sub_singletonRow]
  have howner : owner ∈ Finset.univ.erase recipient :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ owner⟩
  simp only [howner, ite_true]
  ring

end GameTheory
