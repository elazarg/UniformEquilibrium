import MathUE.LinearProgramming.ProjectiveNormalization
import MathUE.Analysis.QuasiconvexLowerBoxBoundary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-! # Standard-Q obstruction to quasiconvex lower-face drift

Actual standard LCP solutions are normalized by the existing canonical
projectivization. Only their normalized coefficients and boxed residuals enter
the compact limit. The cemetery coefficient may vanish in that limit.
-/

noncomputable section

namespace Math.LinearProgramming

open Set Filter Topology
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem derivative_weighted_balance
    (matrix : ι → ι → ℝ) (source point residual : ι → ℝ)
    (cemetery : ℝ) (singleton : ι → ℝ)
    (htotal : cemetery + ∑ i, singleton i = 1)
    (hbalance : ∀ who, residual who =
      cemetery * source who + ∑ owner, singleton owner * matrix who owner)
    (derivative : (ι → ℝ) →L[ℝ] ℝ) :
    derivative (residual - point) =
      cemetery * derivative (source - point) +
        ∑ owner, singleton owner * derivative ((fun who => matrix who owner) - point) := by
  have hvector : residual - point =
      cemetery • (source - point) +
        ∑ owner, singleton owner • ((fun who => matrix who owner) - point) := by
    ext who
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [hbalance who]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hmass := congrArg (fun mass : ℝ => mass * point who) htotal
    nlinarith
  rw [hvector, map_add, map_smul, map_sum]
  simp only [map_smul, smul_eq_mul]

omit [DecidableEq ι] in
private theorem derivative_toward_box_nonneg
    (width point target : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ Set.Icc 0 width) (htarget : target ∈ Set.Icc 0 width)
    (hmin : IsMinOn potential (Set.Icc 0 width) point)
    (hdiff : HasFDerivAt potential derivative point) :
    0 ≤ derivative (target - point) := by
  have hlocal : IsLocalMinOn potential (Set.Icc 0 width) point :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  exact hlocal.hasFDerivWithinAt_nonneg hdiff.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ι → ℝ) width).segment_subset hpoint htarget))

private def normalizedFaceResidual
    (matrix : ι → ι → ℝ) (source : ι → ℝ)
    (solution : ProjectiveLCPSolution matrix source) : ι → ℝ :=
  fun who => solution.cemetery * source who +
    ∑ owner, solution.singleton owner * matrix who owner

omit [DecidableEq ι] in
private theorem normalized_face_solution_box_and_outside
    (matrix : ι → ι → ℝ) (width point : ι → ℝ)
    (potential : (ι → ℝ) → ℝ) (derivative : (ι → ℝ) →L[ℝ] ℝ)
    (hpoint : point ∈ Set.Icc 0 width)
    (hmin : IsMinOn potential (Set.Icc 0 width) point)
    (hdiff : HasFDerivAt potential derivative point)
    (hupper : ∀ who owner, matrix who owner < width who)
    (hdrift : ∀ owner, point owner = 0 →
      0 < derivative (point - (fun who => matrix who owner)))
    (owner : ι) (howner : point owner = 0)
    (rate : ℝ) (hrate : 0 < rate) (hrateOne : rate < 1)
    (weight : ι → ℝ)
    (hstandard : IsStandardLCPSolution matrix
      (fun who => (1 - rate) * point who + rate * matrix who owner) weight) :
    let solution := projectivizeStandardLCPSolution hstandard
    solution.cemetery ≤ 1 ∧
      (∀ who, solution.singleton who ≤ 1) ∧
      normalizedFaceResidual matrix
          (fun who => (1 - rate) * point who + rate * matrix who owner) solution ∈
        Set.Icc 0 width ∧
      ∃ who, point who ≠ 0 ∧
        normalizedFaceResidual matrix
          (fun player => (1 - rate) * point player + rate * matrix player owner)
          solution who = 0 := by
  let source := fun who => (1 - rate) * point who + rate * matrix who owner
  let solution := projectivizeStandardLCPSolution hstandard
  let residual := normalizedFaceResidual matrix source solution
  have hcemetery : 0 < solution.cemetery :=
    projectivizeStandardLCPSolution_cemetery_pos hstandard
  have hsum : 0 ≤ ∑ who, solution.singleton who :=
    Finset.sum_nonneg fun who _ => solution.singleton_nonneg who
  have hcemeteryOne : solution.cemetery ≤ 1 := by
    linarith [solution.total]
  have hsingletonOne (who : ι) : solution.singleton who ≤ 1 := by
    have hterm : solution.singleton who ≤ ∑ player, solution.singleton player :=
      Finset.single_le_sum (fun player _ => solution.singleton_nonneg player)
        (Finset.mem_univ who)
    linarith [solution.total, solution.cemetery_nonneg]
  have hsourceUpper (who : ι) : source who ≤ width who := by
    calc
      source who ≤ (1 - rate) * width who + rate * width who :=
        add_le_add
          (mul_le_mul_of_nonneg_left (hpoint.2 who) (sub_nonneg.mpr hrateOne.le))
          (mul_le_mul_of_nonneg_left (hupper who owner).le hrate.le)
      _ = width who := by ring
  have hbox : residual ∈ Set.Icc 0 width := by
    constructor
    · exact solution.residual_nonneg
    · intro who
      calc
        residual who = solution.cemetery * source who +
            ∑ player, solution.singleton player * matrix who player := rfl
        _ ≤ solution.cemetery * width who +
            ∑ player, solution.singleton player * width who :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hsourceUpper who) solution.cemetery_nonneg)
            (Finset.sum_le_sum fun player _ =>
              mul_le_mul_of_nonneg_left (hupper who player).le
                (solution.singleton_nonneg player))
        _ = width who := by
          rw [← Finset.sum_mul, ← add_mul, solution.total, one_mul]
  have hnonneg : 0 ≤ derivative (residual - point) :=
    derivative_toward_box_nonneg width point residual potential derivative
      hpoint hbox hmin hdiff
  have houtside : ∃ who, point who ≠ 0 ∧ 0 < solution.singleton who := by
    by_contra hnone
    have hnegative (who : ι) (hwho : point who = 0) :
        derivative ((fun player => matrix player who) - point) < 0 := by
      have h := hdrift who hwho
      rw [map_sub] at h ⊢
      linarith
    have hsumNonpos :
        (∑ who, solution.singleton who *
          derivative ((fun player => matrix player who) - point)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro who _
      by_cases hzero : solution.singleton who = 0
      · simp [hzero]
      · have hpositive : 0 < solution.singleton who :=
          lt_of_le_of_ne (solution.singleton_nonneg who) (Ne.symm hzero)
        have hbind : point who = 0 := by
          by_contra hnot
          exact hnone ⟨who, hnot, hpositive⟩
        exact mul_nonpos_of_nonneg_of_nonpos (solution.singleton_nonneg who)
          (hnegative who hbind).le
    have hsource : source - point = rate • ((fun who => matrix who owner) - point) := by
      ext who
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, source]
      ring
    have hfirst : solution.cemetery * derivative (source - point) < 0 := by
      rw [hsource, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hcemetery
        (mul_neg_of_pos_of_neg hrate (hnegative owner howner))
    have hbalance := derivative_weighted_balance matrix source point residual
      solution.cemetery solution.singleton solution.total (fun _ => rfl) derivative
    linarith
  obtain ⟨who, hnot, hweight⟩ := houtside
  refine ⟨hcemeteryOne, hsingletonOne, hbox, who, hnot, ?_⟩
  exact (mul_eq_zero.mp (solution.complementary who)).resolve_left (ne_of_gt hweight)

private abbrev FaceLCPState (ι : Type) := ℝ × (ℝ × ((ι → ℝ) × (ι → ℝ)))

omit [DecidableEq ι] in
/-- Textbook standard Q excludes quasiconvex positive drift on every lower face.
The theorem constructs all LCP data and its normalized compact limit internally. -/
theorem not_quasiconvexOn_of_standardQ_positive_face_drift [Nonempty ι]
    (matrix : ι → ι → ℝ) (width : ι → ℝ) (potential : (ι → ℝ) → ℝ)
    (hQ : IsStandardQ matrix)
    (hdiagonal : ∀ who, matrix who who = 0)
    (hwidth : ∀ who, 0 < width who)
    (hupper : ∀ who owner, matrix who owner < width who)
    (hdiff : ∀ point ∈ Set.Icc (0 : ι → ℝ) width, DifferentiableAt ℝ potential point)
    (hdrift : ∀ point ∈ Set.Icc (0 : ι → ℝ) width, ∀ owner, point owner = 0 →
      0 < fderiv ℝ potential point (point - (fun who => matrix who owner))) :
    ¬QuasiconvexOn ℝ (Set.Icc (0 : ι → ℝ) width) potential := by
  classical
  intro hquasiconvex
  have hcontinuous : ContinuousOn potential (Set.Icc (0 : ι → ℝ) width) :=
    fun point hpoint => (hdiff point hpoint).continuousAt.continuousWithinAt
  obtain ⟨point, hboundary, hminBoundary⟩ :=
    (Math.isCompact_lowerBoxBoundary (0 : ι → ℝ) width).exists_isMinOn
      (Math.lowerBoxBoundary_nonempty (0 : ι → ℝ) width (fun who => (hwidth who).le))
      (hcontinuous.mono (fun _ hpoint => hpoint.1))
  have hmin : IsMinOn potential (Set.Icc (0 : ι → ℝ) width) point :=
    Math.lowerBoxBoundary_minimum_isMinOn_of_quasiconvex
      0 width point potential (fderiv ℝ potential point) (fun owner who => matrix who owner)
      hboundary hminBoundary (hdiff point hboundary.1).hasFDerivAt hwidth
      hdiagonal (fun owner who => (hupper who owner).le)
      (hdrift point hboundary.1) hquasiconvex
  obtain ⟨owner, howner⟩ := hboundary.2
  let rate := fun n : ℕ => (1 / ((n : ℝ) + 1)) / 2
  have hrate (n : ℕ) : 0 < rate n ∧ rate n < 1 := by
    constructor
    · dsimp only [rate]
      positivity
    · have hbound : 1 / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr (by
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)
      dsimp only [rate]
      linarith
  let source := fun n who => (1 - rate n) * point who + rate n * matrix who owner
  let weight := fun n => Classical.choose (hQ (source n))
  have hweight (n : ℕ) : IsStandardLCPSolution matrix (source n) (weight n) :=
    Classical.choose_spec (hQ (source n))
  let solution := fun n => projectivizeStandardLCPSolution (hweight n)
  let residual := fun n => normalizedFaceResidual matrix (source n) (solution n)
  let state : ℕ → FaceLCPState ι :=
    fun n => (rate n, (solution n).cemetery, (solution n).singleton, residual n)
  let good : Set (FaceLCPState ι) := {entry |
    entry.2.1 + ∑ who, entry.2.2.1 who = 1 ∧
      (∀ who, entry.2.2.2 who =
        entry.2.1 * ((1 - entry.1) * point who + entry.1 * matrix who owner) +
          ∑ player, entry.2.2.1 player * matrix who player) ∧
      (∀ who, entry.2.2.1 who * entry.2.2.2 who = 0) ∧
      ∃ who, point who ≠ 0 ∧ entry.2.2.2 who = 0}
  have hclosed : IsClosed good := by
    have htotal : IsClosed {entry : FaceLCPState ι |
        entry.2.1 + ∑ who, entry.2.2.1 who = 1} :=
      isClosed_eq (by fun_prop) continuous_const
    have hbalance : IsClosed {entry : FaceLCPState ι | ∀ who,
        entry.2.2.2 who =
          entry.2.1 * ((1 - entry.1) * point who + entry.1 * matrix who owner) +
            ∑ player, entry.2.2.1 player * matrix who player} := by
      simpa only [Set.iInter_ofPred] using
        isClosed_iInter (fun who => isClosed_eq
          (by fun_prop : Continuous (fun entry : FaceLCPState ι => entry.2.2.2 who))
          (by fun_prop : Continuous (fun entry : FaceLCPState ι =>
            entry.2.1 * ((1 - entry.1) * point who + entry.1 * matrix who owner) +
              ∑ player, entry.2.2.1 player * matrix who player)))
    have hcomplementary : IsClosed {entry : FaceLCPState ι | ∀ who,
        entry.2.2.1 who * entry.2.2.2 who = 0} := by
      simpa only [Set.iInter_ofPred] using
        isClosed_iInter (fun who => isClosed_eq
          (by fun_prop : Continuous (fun entry : FaceLCPState ι =>
            entry.2.2.1 who * entry.2.2.2 who)) continuous_const)
    have houtside : IsClosed {entry : FaceLCPState ι |
        ∃ who, point who ≠ 0 ∧ entry.2.2.2 who = 0} := by
      have h := isClosed_iUnion_of_finite (fun who : {who : ι // point who ≠ 0} =>
        isClosed_eq
          (by fun_prop : Continuous (fun entry : FaceLCPState ι => entry.2.2.2 who.1))
          (continuous_const (y := (0 : ℝ))))
      convert h using 1
      ext entry
      simp
    exact htotal.inter (hbalance.inter (hcomplementary.inter houtside))
  have hstate (n : ℕ) :
      state n ∈ Set.Icc (0 : FaceLCPState ι) (1, 1, 1, width) ∩ good := by
    obtain ⟨hcemeteryOne, hsingletonOne, hbox, houtside⟩ :=
      normalized_face_solution_box_and_outside matrix width point potential
        (fderiv ℝ potential point) hboundary.1 hmin (hdiff point hboundary.1).hasFDerivAt
        hupper (hdrift point hboundary.1) owner howner
        (rate n) (hrate n).1 (hrate n).2 (weight n) (hweight n)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ⟨(hrate n).1.le, (solution n).cemetery_nonneg,
        (solution n).singleton_nonneg, hbox.1⟩
    · exact ⟨(hrate n).2.le, hcemeteryOne, hsingletonOne, hbox.2⟩
    · exact ⟨(solution n).total, fun _ => rfl, (solution n).complementary, houtside⟩
  obtain ⟨limit, hlimit, subsequence, hmono, htendsto⟩ :=
    (isCompact_Icc.inter_right hclosed).tendsto_subseq hstate
  have hrateLimit : limit.1 = 0 := by
    have hzero : Tendsto rate atTop (𝓝 0) := by
      simpa only [rate, zero_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    exact tendsto_nhds_unique
      ((continuous_fst.tendsto limit).comp htendsto)
      (hzero.comp hmono.tendsto_atTop)
  obtain ⟨htotal, hbalance, hcomplementary, who, hnot, hzero⟩ := hlimit.2
  let cemetery := limit.2.1
  let singleton := limit.2.2.1
  let target := limit.2.2.2
  have hmass : cemetery + ∑ player, singleton player = 1 := htotal
  have htarget : target ∈ Set.Icc (0 : ι → ℝ) width :=
    ⟨hlimit.1.1.2.2.2, hlimit.1.2.2.2.2⟩
  have hcemetery : 0 ≤ cemetery := hlimit.1.1.2.1
  have hsingleton : ∀ player, 0 ≤ singleton player := hlimit.1.1.2.2.1
  have htargetBalance (player : ι) :
      target player = cemetery * point player +
        ∑ quitter, singleton quitter * matrix player quitter := by
    simpa only [hrateLimit, sub_zero, one_mul, zero_mul, add_zero]
      using hbalance player
  have hnonzero : ∃ quitter, 0 < singleton quitter := by
    by_contra hnone
    have hweights : singleton = 0 := by
      funext quitter
      exact le_antisymm (le_of_not_gt (fun hpos => hnone ⟨quitter, hpos⟩))
        (hsingleton quitter)
    have hcemeteryOne : cemetery = 1 := by
      simpa only [hweights, Pi.zero_apply, Finset.sum_const_zero, add_zero] using hmass
    have hequal := htargetBalance who
    rw [hcemeteryOne, hweights] at hequal
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, one_mul, add_zero] at hequal
    exact hnot (hequal.symm.trans hzero)
  have hminValue : potential point ≤ potential target := hmin htarget
  have hbackward : 0 ≤ fderiv ℝ potential target (target - point) := by
    have h := Math.quasiconvexOn_hasFDerivAt_sub_nonpos
      (Set.Icc (0 : ι → ℝ) width) potential target point (fderiv ℝ potential target)
      hquasiconvex htarget hboundary.1 hminValue (hdiff target htarget).hasFDerivAt
    rw [map_sub] at h ⊢
    linarith
  have hterms (quitter : ι) : 0 ≤ singleton quitter *
      fderiv ℝ potential target (target - (fun player => matrix player quitter)) := by
    by_cases hweight : singleton quitter = 0
    · simp [hweight]
    · have hbind : target quitter = 0 :=
        (mul_eq_zero.mp (hcomplementary quitter)).resolve_left hweight
      exact mul_nonneg (hsingleton quitter) (hdrift target htarget quitter hbind).le
  have hsum : 0 < ∑ quitter, singleton quitter *
      fderiv ℝ potential target (target - (fun player => matrix player quitter)) := by
    apply Finset.sum_pos'
    · exact fun quitter _ => hterms quitter
    · obtain ⟨quitter, hweight⟩ := hnonzero
      have hbind : target quitter = 0 :=
        (mul_eq_zero.mp (hcomplementary quitter)).resolve_left (ne_of_gt hweight)
      exact ⟨quitter, Finset.mem_univ quitter,
        mul_pos hweight (hdrift target htarget quitter hbind)⟩
  have hfinal := derivative_weighted_balance matrix point target target
    cemetery singleton hmass htargetBalance (fderiv ℝ potential target)
  have hforward : fderiv ℝ potential target (point - target) ≤ 0 := by
    rw [map_sub] at hbackward ⊢
    linarith
  have hfirst : cemetery * fderiv ℝ potential target (point - target) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcemetery hforward
  have hsign :
      (∑ quitter, singleton quitter *
        fderiv ℝ potential target ((fun player => matrix player quitter) - target)) =
      -(∑ quitter, singleton quitter *
        fderiv ℝ potential target (target - (fun player => matrix player quitter))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro quitter _
    rw [map_sub, map_sub]
    ring
  rw [sub_self, map_zero, hsign] at hfinal
  linarith only [hfinal, hfirst, hsum]

end Math.LinearProgramming
