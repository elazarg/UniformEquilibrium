import MathUE.Finset.FinFourNonemptyCoalitions
import UniformEquilibrium.Quitting.Bellman.Finite.HazardRowBridge
import Mathlib.Tactic.FinCases

/-! # Finite row expansions of four-player pure endpoint payoffs -/

noncomputable section

namespace GameTheory.QuittingFinFourEndpointRows

open Math.Finset

/-- Product mass of one prescribed opponent coalition when the selected
player's own action is fixed separately. -/
def opponentCoalitionMass
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) (coalition : Finset (Fin 4)) : ℝ :=
  ∏ other,
    if other = who then 1
    else if other ∈ coalition then hazard other else 1 - hazard other

/-- The opponent mass is unchanged by inserting the selected player into the
coalition whose opponents are prescribed. -/
@[simp] theorem opponentCoalitionMass_insert_self
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) (coalition : Finset (Fin 4)) :
    opponentCoalitionMass hazard who (insert who coalition) =
      opponentCoalitionMass hazard who coalition := by
  unfold opponentCoalitionMass
  apply Finset.prod_congr rfl
  intro player _
  by_cases heq : player = who <;> simp [heq]

@[simp] theorem opponentCoalitionMass_singleton_self
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) :
    opponentCoalitionMass hazard who {who} =
      opponentCoalitionMass hazard who ∅ := by
  change opponentCoalitionMass hazard who (insert who ∅) =
    opponentCoalitionMass hazard who ∅
  exact opponentCoalitionMass_insert_self hazard who ∅

/-- Product-factor form of an opponent coalition mass when the selected
player is absent from the prescribed coalition. -/
theorem opponentCoalitionMass_eq_products_of_not_mem
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) (coalition : Finset (Fin 4))
    (hnot : who ∉ coalition) :
    opponentCoalitionMass hazard who coalition =
      (∏ player ∈ coalition, hazard player) *
        ∏ player ∈ Finset.univ.erase who \ coalition, (1 - hazard player) := by
  have hsub : coalition ⊆ Finset.univ.erase who := by
    intro player hplayer
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    exact hnot (heq ▸ hplayer)
  unfold opponentCoalitionMass
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ who)]
  simp
  calc
    (∏ player ∈ Finset.univ.erase who,
        if player = who then 1
        else if player ∈ coalition then hazard player else 1 - hazard player) =
        ∏ player ∈ Finset.univ.erase who,
          if player ∈ coalition then hazard player else 1 - hazard player := by
      apply Finset.prod_congr rfl
      intro player hplayer
      have hne : player ≠ who := Finset.ne_of_mem_erase hplayer
      simp [hne]
    _ = ∏ player ∈ coalition ∪ (Finset.univ.erase who \ coalition),
          if player ∈ coalition then hazard player else 1 - hazard player := by
      rw [Finset.union_sdiff_of_subset hsub]
    _ = (∏ player ∈ coalition,
          if player ∈ coalition then hazard player else 1 - hazard player) *
        ∏ player ∈ Finset.univ.erase who \ coalition,
          if player ∈ coalition then hazard player else 1 - hazard player := by
      rw [Finset.prod_union Finset.disjoint_sdiff]
    _ = _ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro player hplayer
        simp [hplayer]
      · apply Finset.prod_congr rfl
        intro player hplayer
        have hnotMember : player ∉ coalition :=
          (Finset.mem_sdiff.mp hplayer).2
        simp [hnotMember]

/-- Full row-coordinate expansion of a player's sure-Quit endpoint value. -/
def pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) : ℝ :=
  ∑ row : (Fin 15),
    if who ∈ finFourCoalitionOfRow row then
      opponentCoalitionMass hazard who (finFourCoalitionOfRow row) *
        weightOfReward reward (finFourCoalitionOfRow row) who
    else 0

private theorem sigmaValue_zero_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    sigmaValue (weightOfReward reward) hazard 0 =
      pureQuitEndpointRowSum reward hazard 0 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (0 : (Fin 4))).powerset =
      ({∅, {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3}} :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 0 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2, 3} (by decide)]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_one_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    sigmaValue (weightOfReward reward) hazard 1 =
      pureQuitEndpointRowSum reward hazard 1 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (1 : (Fin 4))).powerset =
      ({∅, {0}, {2}, {0, 2}, {3}, {0, 3}, {2, 3}, {0, 2, 3}} :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 1 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2, 3} (by decide)]
  rw [show ({1, 0} : Finset (Fin 4)) = {0, 1} by decide,
    show ({1, 0, 2} : Finset (Fin 4)) = {0, 1, 2} by decide,
    show ({1, 0, 3} : Finset (Fin 4)) = {0, 1, 3} by decide,
    show ({1, 0, 2, 3} : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_two_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    sigmaValue (weightOfReward reward) hazard 2 =
      pureQuitEndpointRowSum reward hazard 2 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (2 : (Fin 4))).powerset =
      ({∅, {0}, {1}, {0, 1}, {3}, {0, 3}, {1, 3}, {0, 1, 3}} :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 2 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1, 3} (by decide)]
  rw [show ({2, 0} : Finset (Fin 4)) = {0, 2} by decide,
    show ({2, 1} : Finset (Fin 4)) = {1, 2} by decide,
    show ({2, 0, 1} : Finset (Fin 4)) = {0, 1, 2} by decide,
    show ({2, 0, 3} : Finset (Fin 4)) = {0, 2, 3} by decide,
    show ({2, 1, 3} : Finset (Fin 4)) = {1, 2, 3} by decide,
    show ({2, 0, 1, 3} : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

private theorem sigmaValue_three_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    sigmaValue (weightOfReward reward) hazard 3 =
      pureQuitEndpointRowSum reward hazard 3 := by
  rw [sigmaValue]
  rw [show (Finset.univ.erase (3 : (Fin 4))).powerset =
      ({∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}} :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 3 ∅ (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1, 2} (by decide)]
  rw [show ({3, 0} : Finset (Fin 4)) = {0, 3} by decide,
    show ({3, 1} : Finset (Fin 4)) = {1, 3} by decide,
    show ({3, 0, 1} : Finset (Fin 4)) = {0, 1, 3} by decide,
    show ({3, 2} : Finset (Fin 4)) = {2, 3} by decide,
    show ({3, 0, 2} : Finset (Fin 4)) = {0, 2, 3} by decide,
    show ({3, 1, 2} : Finset (Fin 4)) = {1, 2, 3} by decide,
    show ({3, 0, 1, 2} : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
  simp [pureQuitEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow,
    opponentCoalitionMass, Fin.prod_univ_succ]

theorem sigmaValue_eq_pureQuitEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) :
    sigmaValue (weightOfReward reward) hazard who =
      pureQuitEndpointRowSum reward hazard who := by
  fin_cases who
  · exact sigmaValue_zero_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_one_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_two_eq_pureQuitEndpointRowSum reward hazard
  · exact sigmaValue_three_eq_pureQuitEndpointRowSum reward hazard

/-- Full row-coordinate expansion of the nonempty-opponent Quit contribution
to the selected player's pure-Continue endpoint. -/
def excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) : ℝ :=
  ∑ row : (Fin 15),
    if who ∉ finFourCoalitionOfRow row then
      opponentCoalitionMass hazard who (finFourCoalitionOfRow row) *
        weightOfReward reward (finFourCoalitionOfRow row) who
    else 0

private theorem excludedValue_zero_eq_excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    excludedValue (weightOfReward reward) hazard 0 =
      excludedEndpointRowSum reward hazard 0 := by
  rw [excludedValue,
    show (Finset.univ.erase (0 : (Fin 4))).powerset.erase ∅ =
      ({ {1}, {2}, {1, 2}, {3}, {1, 3}, {2, 3}, {1, 2, 3} } :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 0 {1, 2, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow]

private theorem excludedValue_one_eq_excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    excludedValue (weightOfReward reward) hazard 1 =
      excludedEndpointRowSum reward hazard 1 := by
  rw [excludedValue,
    show (Finset.univ.erase (1 : (Fin 4))).powerset.erase ∅ =
      ({ {0}, {2}, {0, 2}, {3}, {0, 3}, {2, 3}, {0, 2, 3} } :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {2, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 1 {0, 2, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow]

private theorem excludedValue_two_eq_excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    excludedValue (weightOfReward reward) hazard 2 =
      excludedEndpointRowSum reward hazard 2 := by
  rw [excludedValue,
    show (Finset.univ.erase (2 : (Fin 4))).powerset.erase ∅ =
      ({ {0}, {1}, {0, 1}, {3}, {0, 3}, {1, 3}, {0, 1, 3} } :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {1, 3} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 2 {0, 1, 3} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow]

private theorem excludedValue_three_eq_excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) :
    excludedValue (weightOfReward reward) hazard 3 =
      excludedEndpointRowSum reward hazard 3 := by
  rw [excludedValue,
    show (Finset.univ.erase (3 : (Fin 4))).powerset.erase ∅ =
      ({ {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2} } :
        Finset (Finset (Fin 4))) by decide]
  repeat' rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {1, 2} (by decide),
    ← opponentCoalitionMass_eq_products_of_not_mem hazard 3 {0, 1, 2} (by decide)]
  simp [excludedEndpointRowSum, Fin.sum_univ_succ, finFourCoalitionOfRow]

theorem excludedValue_eq_excludedEndpointRowSum
    (reward : {coalition : Finset (Fin 4) // coalition.Nonempty} → Payoff (Fin 4))
    (hazard : (Fin 4) → ℝ) (who : (Fin 4)) :
    excludedValue (weightOfReward reward) hazard who =
      excludedEndpointRowSum reward hazard who := by
  fin_cases who
  · exact excludedValue_zero_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_one_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_two_eq_excludedEndpointRowSum reward hazard
  · exact excludedValue_three_eq_excludedEndpointRowSum reward hazard

end GameTheory.QuittingFinFourEndpointRows
