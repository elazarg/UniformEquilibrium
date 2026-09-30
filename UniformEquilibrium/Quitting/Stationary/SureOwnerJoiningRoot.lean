import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseStrategic
import FixedPointTheorems.brouwer

/-! # A literal outsider joining-game root with one sure owner and one passive player -/

noncomputable section

namespace GameTheory

open Set

variable {n : ℕ}

/-- Only outsider joining gains enter the auxiliary map. The two selected
players' hazards are fixed to one and zero, respectively. -/
def quittingSureOwnerJoiningClippedMap
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (owner passive : Fin n) (hazard : Fin n → ℝ) : Fin n → ℝ :=
  fun who => if who = owner then 1 else if who = passive then 0
    else quittingDiscountedClippedMap reward 0 hazard who

private theorem continuous_sureOwnerJoiningClippedMap
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (owner passive : Fin n) : Continuous (quittingSureOwnerJoiningClippedMap reward
      owner passive) := by
  apply continuous_pi
  intro who
  by_cases howner : who = owner
  · simpa only [quittingSureOwnerJoiningClippedMap, ite_eq_left howner] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (1 : ℝ)))
  by_cases hpassive : who = passive
  · simpa only [quittingSureOwnerJoiningClippedMap, ite_eq_right howner,
      ite_eq_left hpassive] using
      (continuous_const : Continuous (fun _ : Fin n → ℝ => (0 : ℝ)))
  simp only [quittingSureOwnerJoiningClippedMap, ite_eq_right howner, ite_eq_right hpassive]
  have hpair : Continuous (fun hazard : Fin n → ℝ => ((0 : ℝ), hazard)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using
    (continuous_apply who).comp ((continuous_quittingDiscountedClippedMap reward).comp
      hpair)

/-- Brouwer constructs the outsiders' finite joining-game Nash root from the
actual reward polynomials, while fixing the selected owner and passive hazards. -/
theorem exists_quittingSureOwnerJoiningRoot
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (owner passive : Fin n) (hdistinct : owner ≠ passive) :
    ∃ hazard : Fin n → ℝ,
      (∀ who, 0 ≤ hazard who) ∧ (∀ who, hazard who ≤ 1) ∧
      hazard owner = 1 ∧ hazard passive = 0 ∧
      ∀ who, who ≠ owner → who ≠ passive →
        (hazard who = 0 → quittingDiscountedDisplacement reward 0 hazard who ≤ 0) ∧
        (0 < hazard who → hazard who < 1 →
          quittingDiscountedDisplacement reward 0 hazard who = 0) ∧
        (hazard who = 1 → 0 ≤ quittingDiscountedDisplacement reward 0 hazard who) := by
  let cube : Set (Fin n → ℝ) := Icc (fun _ => 0) (fun _ => 1)
  have hmaps : ∀ hazard : Fin n → ℝ,
      quittingSureOwnerJoiningClippedMap reward owner passive hazard ∈ cube := by
    intro hazard
    constructor <;> intro who <;>
      simp only [quittingSureOwnerJoiningClippedMap, quittingDiscountedClippedMap] <;>
      split_ifs <;> try norm_num
  let selfMap : cube → cube := fun point =>
    ⟨quittingSureOwnerJoiningClippedMap reward owner passive point.1, hmaps point.1⟩
  have hcontinuous : Continuous selfMap :=
    continuous_induced_rng.2
      ((continuous_sureOwnerJoiningClippedMap reward owner passive).comp continuous_subtype_val)
  have hnonempty : cube.Nonempty :=
    ⟨(fun _ => 0), ⟨fun _ => le_rfl, fun _ => zero_le_one⟩⟩
  obtain ⟨point, hpoint⟩ := brouwer_fixed_point cube
    (convex_Icc _ _) isCompact_Icc hnonempty ⟨selfMap, hcontinuous⟩
  have hfixed : quittingSureOwnerJoiningClippedMap reward owner passive point.1 = point.1 :=
    congrArg Subtype.val hpoint
  have howner : point.1 owner = 1 := by
    have h := congrFun hfixed owner
    simpa [quittingSureOwnerJoiningClippedMap] using h.symm
  have hpassive : point.1 passive = 0 := by
    have h := congrFun hfixed passive
    simpa [quittingSureOwnerJoiningClippedMap, hdistinct.symm] using h.symm
  refine ⟨point.1, point.2.1, point.2.2, howner, hpassive, ?_⟩
  intro who hwhoOwner hwhoPassive
  apply (Math.UnitIntervalClip.clipped_unitInterval_add_eq_self_iff
    (point.2.1 who) (point.2.2 who)).mp
  have h := congrFun hfixed who
  simpa [quittingSureOwnerJoiningClippedMap, hwhoOwner, hwhoPassive,
    quittingDiscountedClippedMap] using h

end GameTheory
