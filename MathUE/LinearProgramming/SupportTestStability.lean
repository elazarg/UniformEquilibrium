import MathUE.LinearProgramming.FiniteSupportDegree
import Mathlib.Topology.Instances.Matrix

/-!
# Stability of strict finite complementarity support tests

Inverse-principal candidates and their residuals vary continuously wherever
the selected principal is nonsingular. The finite strict inequalities in a
support inventory can therefore be preserved on one matrix neighborhood.
-/

noncomputable section

open Filter
open scoped Topology

namespace Math.LinearProgramming

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- Principal extraction is a fixed coordinate restriction. -/
theorem continuous_principalMatrix (support : Finset ι) :
    Continuous (fun matrix : Matrix ι ι ℝ =>
      matrix.toSquareBlockProp (fun who => who ∈ support)) :=
  continuous_id.matrix_submatrix Subtype.val Subtype.val

omit [Fintype ι] in
/-- Inverse-principal candidates depend continuously on the ambient matrix
at every nonsingular selected principal, including the empty principal. -/
theorem continuousAt_principalInverseCandidate
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (hdet : (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0) :
    ContinuousAt (fun other : Matrix ι ι ℝ =>
      principalInverseCandidate other anchor support) matrix := by
  have hinverse : ContinuousAt (fun other : Matrix ι ι ℝ =>
      (other.toSquareBlockProp (fun who => who ∈ support))⁻¹) matrix := by
    apply ContinuousAt.comp _ (continuous_principalMatrix support).continuousAt
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hmulVec : Continuous (fun inverse : Matrix support support ℝ =>
      inverse.mulVec (fun coordinate : support => anchor coordinate)) :=
    continuous_id.matrix_mulVec continuous_const
  have hvector : ContinuousAt (fun other : Matrix ι ι ℝ =>
      (other.toSquareBlockProp (fun who => who ∈ support))⁻¹.mulVec
        (fun coordinate : support => anchor coordinate)) matrix :=
    hmulVec.continuousAt.comp hinverse
  apply continuousAt_pi.mpr
  intro who
  by_cases hwho : who ∈ support
  · simp only [principalInverseCandidate, dite_eq_left hwho]
    exact (continuous_apply (⟨who, hwho⟩ : support)).continuousAt.comp hvector
  · simp only [principalInverseCandidate, dite_eq_right hwho]
    exact continuousAt_const

/-- The actual inactive residuals are continuous functions of the matrix. -/
theorem continuousAt_principalInverseCandidate_residual
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (hdet : (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (who : ι) :
    ContinuousAt (fun other : Matrix ι ι ℝ =>
      lcpResidual other (-anchor) (principalInverseCandidate other anchor support) who) matrix := by
  have hcandidate := continuousAt_principalInverseCandidate matrix anchor support hdet
  change ContinuousAt (fun other => -anchor who + ∑ coordinate,
    principalInverseCandidate other anchor support coordinate * other who coordinate) matrix
  apply continuousAt_const.add
  apply tendsto_finsetSum
  intro coordinate _hcoordinate
  exact ((continuous_apply coordinate).continuousAt.comp hcandidate).mul
    (continuous_apply_apply who coordinate).continuousAt

/-- Each large support is either strictly admissible or has a strict sign
witness rejecting it. Rejected supports need not have every entry nonzero. -/
def HasStrictLCPSupportInventory (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) : Prop :=
  ∀ support : Finset ι, 2 ≤ support.card →
    ((∀ who ∈ support, 0 < principalInverseCandidate matrix anchor support who) ∧
      ∀ who ∉ support,
        0 < lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who) ∨
    (∃ who ∈ support, principalInverseCandidate matrix anchor support who < 0) ∨
    ∃ who ∉ support,
      lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who < 0

private theorem not_mem_admissible_of_rejected
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ) (support : Finset ι)
    (hreject : (∃ who ∈ support, principalInverseCandidate matrix anchor support who < 0) ∨
      ∃ who ∉ support,
        lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who < 0) :
    support ∉ admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) := by
  intro hmem
  obtain ⟨_hlarge, hpositive, hinactive⟩ :=
    (mem_admissibleLCPSupports_iff _ _ _ _).mp hmem
  rcases hreject with ⟨who, hwho, hnegative⟩ | ⟨who, hwho, hnegative⟩
  · exact hnegative.not_ge (hpositive who hwho).le
  · exact hnegative.not_ge (hinactive who hwho)

/-- A strict inventory supplies exactly the strict-slack premise of the
canonical inverse-support degree computation. -/
theorem HasStrictLCPSupportInventory.strict_inactive
    {matrix : Matrix ι ι ℝ} {anchor : ι → ℝ}
    (hinventory : HasStrictLCPSupportInventory matrix anchor)
    (support : Finset ι)
    (hmem : support ∈ admissibleLCPSupports matrix anchor
      (principalInverseCandidate matrix anchor)) :
    ∀ who ∉ support,
      0 < lcpResidual matrix (-anchor) (principalInverseCandidate matrix anchor support) who := by
  have hlarge := ((mem_admissibleLCPSupports_iff _ _ _ _).mp hmem).1
  rcases hinventory support hlarge with hgood | hbad
  · exact hgood.2
  · exact (not_mem_admissible_of_rejected matrix anchor support hbad hmem).elim

/-- Strict acceptance or rejection persists simultaneously on every support;
in particular the exact admissible-support finset is locally constant. -/
theorem eventually_strictLCPSupportInventory_and_admissible_eq
    (matrix : Matrix ι ι ℝ) (anchor : ι → ℝ)
    (hprincipal : ∀ support : Finset ι, 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (hinventory : HasStrictLCPSupportInventory matrix anchor) :
    ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix,
      HasStrictLCPSupportInventory other anchor ∧
      admissibleLCPSupports other anchor (principalInverseCandidate other anchor) =
        admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) := by
  classical
  have hlocal (support : Finset ι) :
      ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix,
        (2 ≤ support.card →
          ((∀ who ∈ support, 0 < principalInverseCandidate other anchor support who) ∧
            ∀ who ∉ support, 0 < lcpResidual other (-anchor)
              (principalInverseCandidate other anchor support) who) ∨
          (∃ who ∈ support, principalInverseCandidate other anchor support who < 0) ∨
          ∃ who ∉ support, lcpResidual other (-anchor)
            (principalInverseCandidate other anchor support) who < 0) ∧
        (support ∈ admissibleLCPSupports other anchor (principalInverseCandidate other anchor) ↔
          support ∈ admissibleLCPSupports matrix anchor
            (principalInverseCandidate matrix anchor)) := by
    by_cases hlarge : 2 ≤ support.card
    · have hcandidate := continuousAt_principalInverseCandidate
        matrix anchor support (hprincipal support hlarge)
      have hresidual := continuousAt_principalInverseCandidate_residual
        matrix anchor support (hprincipal support hlarge)
      rcases hinventory support hlarge with hgood | hbad
      · have hpositive : ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix,
            ∀ who ∈ support, 0 < principalInverseCandidate other anchor support who := by
          apply eventually_all.mpr
          intro who
          by_cases hwho : who ∈ support
          · filter_upwards [((continuous_apply who).continuousAt.comp hcandidate).eventually
              (isOpen_Ioi.mem_nhds (hgood.1 who hwho))] with other hother
            exact fun _ => hother
          · exact Eventually.of_forall (fun _ hmem => (hwho hmem).elim)
        have hinactive : ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix,
            ∀ who ∉ support, 0 < lcpResidual other (-anchor)
              (principalInverseCandidate other anchor support) who := by
          apply eventually_all.mpr
          intro who
          by_cases hwho : who ∈ support
          · exact Eventually.of_forall (fun _ hnot => (hnot hwho).elim)
          · filter_upwards [(hresidual who).eventually
              (isOpen_Ioi.mem_nhds (hgood.2 who hwho))] with other hother
            exact fun _ => hother
        filter_upwards [hpositive, hinactive] with other hpositiveOther hinactiveOther
        have hmemOther := (mem_admissibleLCPSupports_iff other anchor
          (principalInverseCandidate other anchor) support).mpr
          ⟨hlarge, hpositiveOther, fun who hwho => (hinactiveOther who hwho).le⟩
        have hmem := (mem_admissibleLCPSupports_iff matrix anchor
          (principalInverseCandidate matrix anchor) support).mpr
          ⟨hlarge, hgood.1, fun who hwho => (hgood.2 who hwho).le⟩
        exact ⟨fun _ => Or.inl ⟨hpositiveOther, hinactiveOther⟩,
          ⟨fun _ => hmem, fun _ => hmemOther⟩⟩
      · have hnot := not_mem_admissible_of_rejected matrix anchor support hbad
        have hpersist : ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix,
            (∃ who ∈ support, principalInverseCandidate other anchor support who < 0) ∨
            ∃ who ∉ support, lcpResidual other (-anchor)
              (principalInverseCandidate other anchor support) who < 0 := by
          rcases hbad with ⟨who, hwho, hnegative⟩ | ⟨who, hwho, hnegative⟩
          · filter_upwards [((continuous_apply who).continuousAt.comp hcandidate).eventually
              (isOpen_Iio.mem_nhds hnegative)] with other hother
            exact Or.inl ⟨who, hwho, hother⟩
          · filter_upwards [(hresidual who).eventually
              (isOpen_Iio.mem_nhds hnegative)] with other hother
            exact Or.inr ⟨who, hwho, hother⟩
        filter_upwards [hpersist] with other hother
        have hnotOther := not_mem_admissible_of_rejected other anchor support hother
        exact ⟨fun _ => Or.inr hother,
          ⟨fun hmem => (hnotOther hmem).elim, fun hmem => (hnot hmem).elim⟩⟩
    · exact Eventually.of_forall (fun _ => ⟨fun h => (hlarge h).elim,
        ⟨fun h => (hlarge ((mem_admissibleLCPSupports_iff _ _ _ _).mp h).1).elim,
          fun h => (hlarge ((mem_admissibleLCPSupports_iff _ _ _ _).mp h).1).elim⟩⟩)
  filter_upwards [eventually_all.mpr hlocal] with other hother
  exact ⟨fun support hlarge => (hother support).1 hlarge,
    Finset.ext (fun support => (hother support).2)⟩

/-- Principal nonsingularity and determinant signs persist together on the
finite collection of large supports. -/
theorem eventually_principal_nonsingular_and_sign_eq
    (matrix : Matrix ι ι ℝ)
    (hprincipal : ∀ support : Finset ι, 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0) :
    ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix, ∀ support : Finset ι, 2 ≤ support.card →
      (other.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0 ∧
      SignType.sign (other.toSquareBlockProp (fun who => who ∈ support)).det =
        SignType.sign (matrix.toSquareBlockProp (fun who => who ∈ support)).det := by
  classical
  apply eventually_all.mpr
  intro support
  by_cases hlarge : 2 ≤ support.card
  · have hcontinuous : ContinuousAt (fun other : Matrix ι ι ℝ =>
        (other.toSquareBlockProp (fun who => who ∈ support)).det) matrix :=
      (continuous_principalMatrix support).matrix_det.continuousAt
    rcases lt_or_gt_of_ne (hprincipal support hlarge) with hnegative | hpositive
    · filter_upwards [hcontinuous.eventually (isOpen_Iio.mem_nhds hnegative)] with other hother
      exact fun _ => ⟨hother.ne, (sign_neg hother).trans (sign_neg hnegative).symm⟩
    · filter_upwards [hcontinuous.eventually (isOpen_Ioi.mem_nhds hpositive)] with other hother
      exact fun _ => ⟨hother.ne', (sign_pos hother).trans (sign_pos hpositive).symm⟩
  · exact Eventually.of_forall (fun _ h => (hlarge h).elim)

omit [DecidableEq ι] in
/-- One negative entry per column is a finite open condition. -/
theorem eventually_negative_columns (matrix : Matrix ι ι ℝ)
    (hnegative : ∀ column, ∃ row, matrix row column < 0) :
    ∀ᶠ other : Matrix ι ι ℝ in 𝓝 matrix, ∀ column, ∃ row, other row column < 0 := by
  apply eventually_all.mpr
  intro column
  obtain ⟨row, hrow⟩ := hnegative column
  filter_upwards [(continuous_apply_apply row column).continuousAt.eventually
    (isOpen_Iio.mem_nhds hrow)] with other hother
  exact ⟨row, hother⟩

/-- The finite raw tests give local constancy of canonical degree among
zero-diagonal matrices. The exact support inventory and full R0 are retained. -/
theorem eventually_r0Degree_eq_of_strict_support_inventory
    {n : ℕ} [Nonempty (Fin n)]
    (matrix : Matrix (Fin n) (Fin n) ℝ) (anchor : Fin n → ℝ)
    (hdiagonal : ∀ who, matrix who who = 0) (hanchor : ∀ who, 0 < anchor who)
    (hnegative : ∀ column, ∃ row, matrix row column < 0)
    (hprincipal : ∀ support : Finset (Fin n), 2 ≤ support.card →
      (matrix.toSquareBlockProp (fun who => who ∈ support)).det ≠ 0)
    (hinventory : HasStrictLCPSupportInventory matrix anchor) :
    ∀ᶠ other : Matrix (Fin n) (Fin n) ℝ in 𝓝 matrix,
      ∃ hR0 : IsR0Matrix other,
        admissibleLCPSupports other anchor (principalInverseCandidate other anchor) =
          admissibleLCPSupports matrix anchor (principalInverseCandidate matrix anchor) ∧
        ((∀ who, other who who = 0) → r0Degree other hR0 =
          r0Degree matrix (isR0Matrix_of_negative_columns_of_nonsingular_principals
            matrix hnegative hprincipal)) := by
  classical
  filter_upwards [eventually_negative_columns matrix hnegative,
    eventually_principal_nonsingular_and_sign_eq matrix hprincipal,
    eventually_strictLCPSupportInventory_and_admissible_eq matrix anchor hprincipal hinventory]
    with other hnegativeOther hprincipalOther htestOther
  have hprincipal' := fun support hlarge => (hprincipalOther support hlarge).1
  refine ⟨isR0Matrix_of_negative_columns_of_nonsingular_principals
    other hnegativeOther hprincipal', htestOther.2, ?_⟩
  intro hdiagonalOther
  rw [r0Degree_eq_sum_admissible_inverse_supports other anchor hdiagonalOther hanchor
    hnegativeOther hprincipal' htestOther.1.strict_inactive,
    r0Degree_eq_sum_admissible_inverse_supports matrix anchor hdiagonal hanchor
      hnegative hprincipal hinventory.strict_inactive, htestOther.2]
  apply Finset.sum_congr rfl
  intro support hmem
  have hlarge := ((mem_admissibleLCPSupports_iff _ _ _ _).mp hmem).1
  exact congrArg (fun value : SignType => (value : ℤ)) (hprincipalOther support hlarge).2

end Math.LinearProgramming
