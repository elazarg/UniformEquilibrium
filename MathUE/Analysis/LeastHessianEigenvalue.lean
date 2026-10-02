import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Order.Compact

/-! # The actual self-adjoint Hessian and its attained least eigenvalue

The least eigenvalue is the canonical infimum of the nonzero-vector
Rayleigh quotient. Its eigenvalue property is proved, not assumed. Joint
compact minimization on a set and the unit sphere produces its set minimum.
-/

noncomputable section

namespace Math

open Set Metric
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- Riesz representation of the actual second Fréchet derivative. -/
def realHessian (potential : E → ℝ) (point : E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ potential) point)

omit [Nontrivial E] in
theorem realHessian_inner (potential : E → ℝ) (point first second : E) :
    inner ℝ (realHessian potential point first) second =
      fderiv ℝ (fderiv ℝ potential) point first second :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ first second

omit [Nontrivial E] in
theorem realHessian_isSelfAdjoint
    (potential : E → ℝ) (point : E) (hsmooth : ContDiffAt ℝ 2 potential point) :
    IsSelfAdjoint (realHessian potential point) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  change inner ℝ (realHessian potential point first) second =
    inner ℝ first (realHessian potential point second)
  rw [realHessian_inner, real_inner_comm, realHessian_inner]
  exact hsmooth.isSymmSndFDerivAt (by simp) first second

/-- This number is an actual eigenvalue under C2 regularity. Zero vectors
are excluded, so positive-definite Hessians retain a positive least eigenvalue. -/
def leastHessianEigenvalue (potential : E → ℝ) (point : E) : ℝ :=
  ⨅ direction : {direction : E // direction ≠ 0},
    (realHessian potential point).rayleighQuotient direction

def minimumHessianEigenvalue (potential : E → ℝ) (box : Set E) : ℝ :=
  ⨅ point : box, leastHessianEigenvalue potential point

theorem leastHessianEigenvalue_hasEigenvalue
    (potential : E → ℝ) (point : E) (hsmooth : ContDiffAt ℝ 2 potential point) :
    Module.End.HasEigenvalue (realHessian potential point).toLinearMap
      (leastHessianEigenvalue potential point) := by
  have hsym := (realHessian_isSelfAdjoint potential point hsmooth).isSymmetric
  exact hsym.hasEigenvalue_iInf_of_finiteDimensional

omit [Nontrivial E] in
theorem leastHessianEigenvalue_le_rayleigh
    (potential : E → ℝ) (point direction : E) (hne : direction ≠ 0) :
    leastHessianEigenvalue potential point ≤
      (realHessian potential point).rayleighQuotient direction := by
  apply ciInf_le (f := fun vector : {vector : E // vector ≠ 0} =>
    (realHessian potential point).rayleighQuotient vector) _ ⟨direction, hne⟩
  refine ⟨-‖realHessian potential point‖, ?_⟩
  rintro value ⟨vector, rfl⟩
  exact neg_le_of_abs_le ((realHessian potential point).rayleighQuotient_le_norm vector)

omit [Nontrivial E] in
theorem leastHessianEigenvalue_le_of_hasEigenvalue
    (potential : E → ℝ) (point : E) (eigenvalue : ℝ)
    (heigenvalue : Module.End.HasEigenvalue (realHessian potential point).toLinearMap
      eigenvalue) :
    leastHessianEigenvalue potential point ≤ eigenvalue := by
  obtain ⟨direction, hvector⟩ := heigenvalue.exists_hasEigenvector
  have hnonzero : direction ≠ 0 := hvector.2
  have hquotient := leastHessianEigenvalue_le_rayleigh potential point direction hnonzero
  have happly : realHessian potential point direction = eigenvalue • direction :=
    hvector.apply_eq_smul
  have heq : (realHessian potential point).rayleighQuotient direction = eigenvalue := by
    rw [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, happly]
    simp only [inner_smul_left, RCLike.re_to_real, real_inner_self_eq_norm_sq,
      RCLike.conj_to_real]
    exact mul_div_cancel_right₀ eigenvalue (pow_ne_zero 2 (norm_ne_zero_iff.mpr hnonzero))
  rwa [heq] at hquotient

omit [Nontrivial E] in
/-- The same least eigenvalue bounds every actual directional second
derivative, including the zero vector, with the Euclidean norm squared. -/
theorem leastHessianEigenvalue_mul_norm_sq_le
    (potential : E → ℝ) (point direction : E) :
    leastHessianEigenvalue potential point * ‖direction‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ potential) point direction direction := by
  by_cases hzero : direction = 0
  · simp [hzero]
  have hquotient := leastHessianEigenvalue_le_rayleigh potential point direction hzero
  have hnorm : 0 < ‖direction‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hzero)
  simpa only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real, realHessian_inner] using
    (le_div_iff₀ hnorm).mp hquotient

/-- Produce the full-set spectral minimum from C2 on a neighborhood.
No supplied eigenvector, spectral minimum, or continuity of sorted eigenvalue
labels is needed: minimize the actual quadratic form jointly on box × sphere. -/
theorem exists_minimumHessianEigenvalue
    (potential : E → ℝ) (box domain : Set E)
    (hcompact : IsCompact box) (hnonempty : box.Nonempty)
    (hopen : IsOpen domain) (hbox : box ⊆ domain)
    (hsmooth : ContDiffOn ℝ 2 potential domain) :
    ∃ point ∈ box,
      IsMinOn (leastHessianEigenvalue potential) box point ∧
      minimumHessianEigenvalue potential box = leastHessianEigenvalue potential point ∧
      Module.End.HasEigenvalue (realHessian potential point).toLinearMap
        (leastHessianEigenvalue potential point) ∧
      ∀ other ∈ box, ∀ direction,
        leastHessianEigenvalue potential point * ‖direction‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ potential) other direction direction := by
  have : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  have hsphere : (sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hsecond : ContinuousOn (fderiv ℝ (fderiv ℝ potential)) domain :=
    (hsmooth.fderiv_of_isOpen hopen (by norm_num)).continuousOn_fderiv_of_isOpen hopen le_rfl
  have hquadratic : ContinuousOn
      (fun pair : E × E => fderiv ℝ (fderiv ℝ potential) pair.1 pair.2 pair.2)
      (box ×ˢ sphere 0 1) :=
    ((hsecond.comp continuous_fst.continuousOn
      (fun _ hpair => hbox hpair.1)).clm_apply continuous_snd.continuousOn).clm_apply
        continuous_snd.continuousOn
  obtain ⟨pair, hpair, hminimum⟩ :=
    (hcompact.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn
      (hnonempty.prod hsphere) hquadratic
  have hnorm : ‖pair.2‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hpair.2
  have hvalue : leastHessianEigenvalue potential pair.1 =
      fderiv ℝ (fderiv ℝ potential) pair.1 pair.2 pair.2 := by
    rw [leastHessianEigenvalue,
      (realHessian potential pair.1).iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one]
    have hminSphere : IsMinOn (realHessian potential pair.1).rayleighQuotient
        (sphere 0 1) pair.2 := by
      intro vector hvector
      change (realHessian potential pair.1).rayleighQuotient pair.2 ≤
        (realHessian potential pair.1).rayleighQuotient vector
      have hvectorNorm : ‖vector‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using hvector
      have hcompare := hminimum
        (show (pair.1, vector) ∈ box ×ˢ sphere (0 : E) 1 from ⟨hpair.1, hvector⟩)
      change fderiv ℝ (fderiv ℝ potential) pair.1 pair.2 pair.2 ≤
        fderiv ℝ (fderiv ℝ potential) pair.1 vector vector at hcompare
      simpa only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
        realHessian_inner, hnorm, hvectorNorm, one_pow, div_one] using
        hcompare
    rw [IsMinOn.iInf_eq hpair.2 hminSphere]
    simp only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      realHessian_inner, hnorm, one_pow, div_one]
  have hleast : IsMinOn (leastHessianEigenvalue potential) box pair.1 := by
    intro other hother
    change leastHessianEigenvalue potential pair.1 ≤
      ⨅ vector : {vector : E // vector ≠ 0},
        (realHessian potential other).rayleighQuotient vector
    rw [(realHessian potential other).iInf_rayleigh_eq_iInf_rayleigh_sphere zero_lt_one]
    let : Nonempty (sphere (0 : E) 1) := hsphere.to_subtype
    apply le_ciInf
    intro vector
    have hvectorNorm : ‖(vector : E)‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using vector.2
    have hcompare := hminimum
      (show (other, (vector : E)) ∈ box ×ˢ sphere (0 : E) 1 from ⟨hother, vector.2⟩)
    change fderiv ℝ (fderiv ℝ potential) pair.1 pair.2 pair.2 ≤
      fderiv ℝ (fderiv ℝ potential) other (vector : E) (vector : E) at hcompare
    rw [hvalue]
    simpa only [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
      realHessian_inner, hvectorNorm, one_pow, div_one] using
      hcompare
  refine ⟨pair.1, hpair.1, hleast, IsMinOn.iInf_eq hpair.1 hleast,
    leastHessianEigenvalue_hasEigenvalue potential pair.1
      (hsmooth.contDiffAt (hopen.mem_nhds (hbox hpair.1))), ?_⟩
  intro other hother direction
  exact (mul_le_mul_of_nonneg_right (hleast hother) (sq_nonneg _)).trans
    (leastHessianEigenvalue_mul_norm_sq_le potential other direction)

end Math
