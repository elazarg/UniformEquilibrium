import Mathlib.Topology.Instances.Real.Lemmas

noncomputable section

namespace Math.LinearProgramming

inductive PivotRepairTailCoordinate
  | late
  | never
  | firstAtom
  deriving DecidableEq

instance : Fintype PivotRepairTailCoordinate where
  elems := {.late, .never, .firstAtom}
  complete coordinate := by cases coordinate <;> simp

abbrev PivotRepairMass (deadline : ℕ) :=
  Fin deadline ⊕ PivotRepairTailCoordinate → ℝ

def pivotRepairHead {deadline : ℕ} (mass : PivotRepairMass deadline)
    (time : Fin deadline) : ℝ :=
  mass (Sum.inl time)

def pivotRepairLate {deadline : ℕ} (mass : PivotRepairMass deadline) : ℝ :=
  mass (Sum.inr .late)

def pivotRepairNever {deadline : ℕ} (mass : PivotRepairMass deadline) : ℝ :=
  mass (Sum.inr .never)

def pivotRepairFirstAtom {deadline : ℕ} (mass : PivotRepairMass deadline) : ℝ :=
  mass (Sum.inr .firstAtom)

/-- Literal LP mass constraints, with the boundary coordinate `firstAtom`
independent of the total late finite mass. -/
def IsPivotRepairMassFeasible {deadline : ℕ}
    (mass : PivotRepairMass deadline) : Prop :=
  (∀ time, 0 ≤ pivotRepairHead mass time) ∧
    0 ≤ pivotRepairLate mass ∧ 0 ≤ pivotRepairNever mass ∧
    (∑ time, pivotRepairHead mass time) + pivotRepairLate mass +
        pivotRepairNever mass = 1 ∧
    0 ≤ pivotRepairFirstAtom mass ∧
      pivotRepairFirstAtom mass ≤ pivotRepairLate mass

def pivotRepairMassFeasibleSet (deadline : ℕ) : Set (PivotRepairMass deadline) :=
  {mass | IsPivotRepairMassFeasible mass}

def pivotRepairAllLateMass (deadline : ℕ) : PivotRepairMass deadline
  | Sum.inl _ => 0
  | Sum.inr .late => 1
  | Sum.inr .never => 0
  | Sum.inr .firstAtom => 0

theorem pivotRepairAllLateMass_feasible (deadline : ℕ) :
    IsPivotRepairMassFeasible (pivotRepairAllLateMass deadline) := by
  simp [IsPivotRepairMassFeasible, pivotRepairHead, pivotRepairLate,
    pivotRepairNever, pivotRepairFirstAtom, pivotRepairAllLateMass]

theorem pivotRepairMassFeasibleSet_nonempty (deadline : ℕ) :
    (pivotRepairMassFeasibleSet deadline).Nonempty :=
  ⟨pivotRepairAllLateMass deadline, pivotRepairAllLateMass_feasible deadline⟩

theorem isClosed_pivotRepairMassFeasibleSet (deadline : ℕ) :
    IsClosed (pivotRepairMassFeasibleSet deadline) := by
  have hhead : IsClosed {mass : PivotRepairMass deadline |
      ∀ time, 0 ≤ pivotRepairHead mass time} := by
    rw [show {mass : PivotRepairMass deadline | ∀ time, 0 ≤ pivotRepairHead mass time} =
        ⋂ time, {mass | mass (Sum.inl time) ∈ Set.Ici (0 : ℝ)} by
      ext mass
      simp [pivotRepairHead]]
    exact isClosed_iInter fun time ↦ isClosed_Ici.preimage (continuous_apply _)
  have hlate : IsClosed {mass : PivotRepairMass deadline | 0 ≤ pivotRepairLate mass} :=
    isClosed_Ici.preimage (continuous_apply _)
  have hnever : IsClosed {mass : PivotRepairMass deadline | 0 ≤ pivotRepairNever mass} :=
    isClosed_Ici.preimage (continuous_apply _)
  have hsum : IsClosed {mass : PivotRepairMass deadline |
      (∑ time, pivotRepairHead mass time) + pivotRepairLate mass +
        pivotRepairNever mass = 1} := by
    apply isClosed_singleton.preimage
    exact ((continuous_finsetSum _ fun time _ ↦ continuous_apply (Sum.inl time)).add
      (continuous_apply _)).add (continuous_apply _)
  have halpha : IsClosed {mass : PivotRepairMass deadline |
      0 ≤ pivotRepairFirstAtom mass} :=
    isClosed_Ici.preimage (continuous_apply _)
  have halphaLate : IsClosed {mass : PivotRepairMass deadline |
      pivotRepairFirstAtom mass ≤ pivotRepairLate mass} :=
    isClosed_le (continuous_apply _) (continuous_apply _)
  exact hhead.inter (hlate.inter (hnever.inter (hsum.inter (halpha.inter halphaLate))))

theorem pivotRepairMassFeasible_mem_Icc {deadline : ℕ}
    {mass : PivotRepairMass deadline} (h : IsPivotRepairMassFeasible mass) :
    mass ∈ Set.Icc (0 : PivotRepairMass deadline) 1 := by
  rcases h with ⟨hhead, hlate, hnever, hsum, halpha, halphaLate⟩
  constructor
  · intro coordinate
    cases coordinate with
    | inl time => exact hhead time
    | inr coordinate => cases coordinate <;> assumption
  · intro coordinate
    cases coordinate with
    | inl time =>
        change pivotRepairHead mass time ≤ 1
        rw [← hsum]
        calc
          pivotRepairHead mass time ≤ ∑ t, pivotRepairHead mass t :=
            Finset.single_le_sum (fun t _ ↦ hhead t) (Finset.mem_univ time)
          _ ≤ (∑ t, pivotRepairHead mass t) + pivotRepairLate mass :=
            le_add_of_nonneg_right hlate
          _ ≤ (∑ t, pivotRepairHead mass t) + pivotRepairLate mass +
              pivotRepairNever mass := le_add_of_nonneg_right hnever
    | inr coordinate =>
        cases coordinate with
        | late =>
            change pivotRepairLate mass ≤ 1
            rw [← hsum]
            exact le_add_of_nonneg_left (Finset.sum_nonneg fun t _ ↦ hhead t) |>.trans
              (le_add_of_nonneg_right hnever)
        | never =>
            change pivotRepairNever mass ≤ 1
            rw [← hsum]
            exact le_add_of_nonneg_left
              (add_nonneg (Finset.sum_nonneg fun t _ ↦ hhead t) hlate)
        | firstAtom =>
            change pivotRepairFirstAtom mass ≤ 1
            exact halphaLate.trans (by
              rw [← hsum]
              exact le_add_of_nonneg_left (Finset.sum_nonneg fun t _ ↦ hhead t) |>.trans
                (le_add_of_nonneg_right hnever))

theorem isCompact_pivotRepairMassFeasibleSet (deadline : ℕ) :
    IsCompact (pivotRepairMassFeasibleSet deadline) := by
  apply (isCompact_Icc : IsCompact
    (Set.Icc (0 : PivotRepairMass deadline) 1)).of_isClosed_subset
      (isClosed_pivotRepairMassFeasibleSet deadline)
  exact fun _ h ↦ pivotRepairMassFeasible_mem_Icc h

end Math.LinearProgramming
