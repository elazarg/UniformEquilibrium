import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseTables
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseRawAdapter
import UniformEquilibrium.Quitting.Stationary.OneSidedWeakUnitProducer

/-! # Exact finite raw guard coverage of the literal crossed-response tables -/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

private theorem subset_pair_cases (coalition : Finset (Fin 4))
    (hsubset : coalition ⊆ {2, 3}) :
    coalition = ∅ ∨ coalition = {2} ∨ coalition = {3} ∨ coalition = {2, 3} := by
  have hpowerset : ({2, 3} : Finset (Fin 4)).powerset = {∅, {2}, {3}, {2, 3}} := by
    decide
  have hmem := Finset.mem_powerset.mpr hsubset
  rw [hpowerset] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem

private theorem nonempty_subset_pair_cases (coalition : Finset (Fin 4))
    (hsubset : coalition ⊆ {2, 3}) (hnonempty : coalition.Nonempty) :
    coalition = {2} ∨ coalition = {3} ∨ coalition = {2, 3} := by
  rcases subset_pair_cases coalition hsubset with hempty | htwo | hthree | hboth
  · simp [hempty] at hnonempty
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hthree)
  · exact Or.inr (Or.inr hboth)

theorem halfCeiling_lowerFirst : QuittingCrossedStrictLowerRanking halfCeilingReward 0 1 := by
  intro own other hown hother hnonempty
  have hcarrier : quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} := by decide
  rw [hcarrier] at hown hother
  rcases subset_pair_cases own hown with h | h | h | h <;>
    rcases nonempty_subset_pair_cases other hother hnonempty with h' | h' | h' <;>
    subst own <;> subst other <;>
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

theorem halfCeiling_lowerSecond : QuittingCrossedStrictLowerRanking halfCeilingReward 1 0 := by
  intro own other hown hother hnonempty
  have hcarrier : quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} := by decide
  rw [hcarrier] at hown hother
  rcases subset_pair_cases own hown with h | h | h | h <;>
    rcases nonempty_subset_pair_cases other hother hnonempty with h' | h' | h' <;>
    subst own <;> subst other <;>
    norm_num +decide [weightOfReward, halfCeilingReward, coalitionCode]

theorem unitCeiling_lowerFirst : QuittingCrossedStrictLowerRanking unitCeilingReward 0 1 := by
  intro own other hown hother hnonempty
  have hcarrier : quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} := by decide
  rw [hcarrier] at hown hother
  rcases subset_pair_cases own hown with h | h | h | h <;>
    rcases nonempty_subset_pair_cases other hother hnonempty with h' | h' | h' <;>
    subst own <;> subst other <;>
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem unitCeiling_lowerSecond : QuittingCrossedStrictLowerRanking unitCeilingReward 1 0 := by
  intro own other hown hother hnonempty
  have hcarrier : quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} := by decide
  rw [hcarrier] at hown hother
  rcases subset_pair_cases own hown with h | h | h | h <;>
    rcases nonempty_subset_pair_cases other hother hnonempty with h' | h' | h' <;>
    subst own <;> subst other <;>
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem unitCeiling_upperFirst : QuittingCrossedStrictUnitJoining unitCeilingReward 0 1 := by
  intro outsider hsubset
  have hcarrier : quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} := by decide
  rw [hcarrier] at hsubset
  rcases subset_pair_cases outsider hsubset with h | h | h | h <;> subst outsider <;>
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem unitCeiling_upperSecond : QuittingCrossedStrictUnitJoining unitCeilingReward 1 0 := by
  intro outsider hsubset
  have hcarrier : quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} := by decide
  rw [hcarrier] at hsubset
  rcases subset_pair_cases outsider hsubset with h | h | h | h <;> subst outsider <;>
    norm_num +decide [weightOfReward, unitCeilingReward, coalitionCode]

theorem unitCeiling_strictRawGuards :
    QuittingCrossedStrictRawUnitGuards unitCeilingReward 0 1 :=
  ⟨unitCeiling_lowerFirst, unitCeiling_lowerSecond,
    unitCeiling_upperFirst, unitCeiling_upperSecond⟩

/-- The weaker sixteen-comparison one-sided criterion has a literal source instance. -/
theorem unitCeiling_oneSidedWeakRawGuards :
    QuittingOneSidedWeakUnitRawGuards unitCeilingReward 0 1 := by
  constructor
  · intro own other hown hother hnonempty
    exact (unitCeiling_lowerFirst own other hown hother hnonempty).le
  · intro outsider hsubset
    exact (unitCeiling_upperSecond outsider hsubset).le

end GameTheory.GuardedCrossedResponseExamples
