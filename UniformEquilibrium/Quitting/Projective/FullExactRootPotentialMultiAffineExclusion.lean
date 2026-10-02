import MathUE.Analysis.CoordinateAffineBoxMinimum
import MathUE.Polynomial.MvPolynomialCoordinateAffine
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialMinimum

/-! # Full exact-root exclusion of every multi-affine polynomial

The proof uses an internally produced minimizing vertex and two-coordinate
interpolation. It imposes no total-degree restriction: triple and full-order
square-free terms are retained.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

omit [Fintype ι] [Nontrivial ι] in
private theorem update_mem_three_box (point : Payoff ι)
    (hpoint : point ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3))
    (coordinate : ι) (value : ℝ) (hvalue : value ∈ Set.Icc (-3 : ℝ) 3) :
    Function.update point coordinate value ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) := by
  constructor <;> intro other
  · by_cases heq : other = coordinate
    · subst other
      simpa using hvalue.1
    · simpa [heq] using hpoint.1 other
  · by_cases heq : other = coordinate
    · subst other
      simpa using hvalue.2
    · simpa [heq] using hpoint.2 other

/-- Coordinate-affine smooth potentials themselves are excluded, independently
of any polynomial syntax or total-degree hypothesis. -/
theorem not_isQuittingFullExactRootPotential_coordinateAffine
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (potential : Payoff ι → ℝ) (haffine : Math.IsCoordinateAffine potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3), DifferentiableAt ℝ potential point) :
    ¬ IsQuittingFullExactRootPotential reward 3 potential := by
  intro hpotential
  obtain ⟨minimum, hminimum, hmin, _⟩ :=
    hpotential.exists_minimum_above_singleton hreward (by norm_num : (1 : ℝ) < 3)
      hcontinuous hdiff
  have hminimumMem : minimum ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) :=
    ⟨fun who => (abs_le.mp (hminimum who)).1, fun who => (abs_le.mp (hminimum who)).2⟩
  obtain ⟨vertex, hvertex, hvertexEndpoints, hvertexMin⟩ :=
    haffine.exists_vertex_minimum (fun _ => (-3 : ℝ)) (fun _ => 3)
      minimum hminimumMem hmin
  have hvertexBox : ∀ who, |vertex who| ≤ 3 :=
    fun who => abs_le.mpr ⟨hvertex.1 who, hvertex.2 who⟩
  have hvertexAbove := hpotential.minimum_above_singleton_of_differentiable hreward
    (by norm_num : (1 : ℝ) < 3) hdiff vertex hvertexBox hvertexMin
  let top : Payoff ι := fun _ => 3
  have hvertexTop : vertex = top := by
    funext who
    rcases hvertexEndpoints who with hbottom | htop
    · have hnonneg := hsingleton who
      have habove := hvertexAbove who
      rw [hbottom] at habove
      linarith
    · exact htop
  have htopMin : IsMinOn potential (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) top := by
    simpa only [hvertexTop] using hvertexMin
  have htopMem : top ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3) := by
    constructor <;> intro who <;> norm_num [top]
  have hstrict : ∀ point ∈ Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3),
      (∃ who, point who = -3) → potential top < potential point := by
    intro point hpoint hnegative
    apply lt_of_le_of_ne (htopMin hpoint)
    intro hequal
    have hpointMin : IsMinOn potential
        (Set.Icc (fun _ => (-3 : ℝ)) (fun _ => 3)) point := by
      intro target htarget
      rw [← hequal]
      exact htopMin htarget
    have habove := hpotential.minimum_above_singleton_of_differentiable hreward
      (by norm_num : (1 : ℝ) < 3) hdiff point
      (fun who => abs_le.mpr ⟨hpoint.1 who, hpoint.2 who⟩) hpointMin
    obtain ⟨who, hwho⟩ := hnegative
    have hown := habove who
    have hnonneg := hsingleton who
    rw [hwho] at hown
    linarith
  let gap : ι → ℝ := fun who => potential (Function.update top who (-3)) - potential top
  have hgap : ∀ who, 0 < gap who := by
    intro who
    exact sub_pos.mpr (hstrict (Function.update top who (-3))
      (update_mem_three_box top htopMem who (-3) (by norm_num)) ⟨who, by simp⟩)
  obtain ⟨owner, _, hsmallest⟩ := Set.exists_min_image Set.univ gap
    Set.finite_univ Set.univ_nonempty
  let own := quittingSoloReward reward owner owner
  let weight := (3 - own) / 6
  have hownNonneg : 0 ≤ own := hsingleton owner
  have hownUpper : own ≤ 1 :=
    (le_abs_self _).trans (hreward (quittingSingletonTerminal owner) owner)
  have hweightPos : 0 < weight := by dsimp [weight]; linarith
  have hweightUpper : weight ≤ 1 / 2 := by dsimp [weight]; linarith
  let point := Function.update top owner own
  have hpointC : point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => 3) := by
    constructor <;> intro who
    · by_cases heq : who = owner
      · subst who
        simp [point, own]
      · have hsolo := (le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)
        change quittingSoloReward reward who who ≤ 1 at hsolo
        have hpointWho : point who = 3 := by simp [point, top, heq]
        change quittingSoloReward reward who who ≤ point who
        rw [hpointWho]
        exact hsolo.trans (by norm_num : (1 : ℝ) ≤ 3)
    · by_cases heq : who = owner
      · subst who
        simpa [point] using hownUpper.trans (by norm_num : (1 : ℝ) ≤ 3)
      · simp [point, top, heq]
  have hpointDiff := (hdiff point hpointC).hasFDerivAt
  let derivative := fderiv ℝ potential point
  have hcoordinate : (1 - weight) * 3 + weight * (-3) = own := by
    dsimp [weight]
    ring
  have htopUpdate : Function.update top owner 3 = top := by
    funext who
    simp [top]
  have hpointValue : potential point - potential top = weight * gap owner := by
    have hinterpolate := haffine.update_interpolate top owner (-3) 3 weight
    rw [hcoordinate, htopUpdate] at hinterpolate
    dsimp [gap, point]
    linarith
  have hpartial : ∀ who, who ≠ owner → derivative (Pi.single who 1) < 0 := by
    intro who hne
    let double := Function.update (Function.update top who (-3)) owner (-3)
    have hdoubleBox := update_mem_three_box (Function.update top who (-3))
      (update_mem_three_box top htopMem who (-3) (by norm_num)) owner (-3) (by norm_num)
    have hdoubleGap : 0 < potential double - potential top :=
      sub_pos.mpr (hstrict double hdoubleBox ⟨owner, by simp [double]⟩)
    have hbaseOwner : (Function.update top who (-3)) owner = 3 := by
      simp [top, Ne.symm hne]
    have hbaseUpdate : Function.update (Function.update top who (-3)) owner 3 =
        Function.update top who (-3) := by
      simpa only [Function.update_eq_self] using
        (congrArg (Function.update (Function.update top who (-3)) owner) hbaseOwner).symm
    have hcomm : Function.update (Function.update top who (-3)) owner own =
        Function.update point who (-3) := by
      rw [Function.update_comm hne]
    have hinterpolate := haffine.update_interpolate (Function.update top who (-3))
      owner (-3) 3 weight
    rw [hcoordinate, hbaseUpdate, hcomm] at hinterpolate
    have hfiniteDifference := haffine.update_sub_eq_derivative point derivative
      hpointDiff who (-3)
    have hpointWho : point who = 3 := by simp [point, top, hne]
    rw [hpointWho] at hfiniteDifference
    have hsmall := hsmallest who (Set.mem_univ _)
    have hsmallWeighted := mul_le_mul_of_nonneg_left hsmall hweightPos.le
    have hdoubleWeighted := mul_pos hweightPos hdoubleGap
    have hweightSign : 0 ≤ 1 - 2 * weight := by linarith
    have hsingleWeighted := mul_nonneg hweightSign (hgap who).le
    change gap owner ≤ gap who at hsmall
    dsimp [gap, double] at hsmallWeighted hpointValue hdoubleWeighted hsingleWeighted
    change derivative (Pi.single who 1) < 0
    nlinarith
  have hunit := hpotential.singletonFace_drift hreward (by norm_num : (1 : ℝ) < 3)
    point owner (fun who => ⟨hpointC.1 who, hpointC.2 who⟩)
    (by simp [point, own]) derivative hpointDiff
  have hnonpos : derivative (point - quittingSoloReward reward owner) ≤ 0 := by
    conv_lhs => rw [pi_eq_sum_univ' (point - quittingSoloReward reward owner)]
    rw [map_sum]
    apply Finset.sum_nonpos
    intro who _
    rw [map_smul]
    change (point who - quittingSoloReward reward owner who) *
      derivative (Pi.single who 1) ≤ 0
    by_cases heq : who = owner
    · subst who
      simp [point, own]
    · have hcoefficient : 0 ≤ point who - quittingSoloReward reward owner who := by
        have hsolo := (le_abs_self _).trans (hreward (quittingSingletonTerminal owner) who)
        change quittingSoloReward reward owner who ≤ 1 at hsolo
        have hpointWho : point who = 3 := by simp [point, top, heq]
        rw [hpointWho]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos hcoefficient (hpartial who heq).le
  linarith

variable {dimension : ℕ}

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- Every square-free polynomial is excluded, including all sixteen monomials
in dimension four and all interaction orders in arbitrary finite dimension. -/
theorem not_isQuittingFullExactRootPotential_multiAffine
    [Nontrivial (Fin dimension)]
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (polynomial : MvPolynomial (Fin dimension) ℝ)
    (haffine : Math.IsMultiAffineMvPolynomial polynomial) :
    ¬ IsQuittingFullExactRootPotential reward 3
      (fun point => MvPolynomial.eval point polynomial) := by
  have hsmooth := Math.contDiff_eval_mvPolynomial polynomial 1
  exact not_isQuittingFullExactRootPotential_coordinateAffine hreward hsingleton _
    (Math.isCoordinateAffine_eval_mvPolynomial polynomial haffine)
    hsmooth.continuous.continuousOn (fun point _ => hsmooth.differentiable_one point)

omit [Fintype ι] [DecidableEq ι] [Nontrivial ι] in
/-- The repository's rational expression facade measures individual degrees
on its normalized polynomial, allowing arbitrary syntactic cancellation. -/
theorem not_isQuittingFullExactRootPotential_rational_multiAffine
    [Nontrivial (Fin dimension)]
    {reward : {S : Finset (Fin dimension) // S.Nonempty} → Payoff (Fin dimension)}
    (hreward : ∀ terminal who, |reward terminal who| ≤ 1)
    (hsingleton : ∀ who, 0 ≤ quittingSoloReward reward who who)
    (expression : Math.Interval.RationalPolynomial dimension)
    (haffine : ∀ coordinate, expression.toMvPolynomial.degreeOf coordinate ≤ 1) :
    ¬ IsQuittingFullExactRootPotential reward 3
      (fun point => Math.Interval.RationalPolynomial.evalReal point expression) := by
  let polynomial := MvPolynomial.map (Rat.castHom ℝ) expression.toMvPolynomial
  have hreal : Math.IsMultiAffineMvPolynomial polynomial := by
    intro coordinate
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro exponent hexponent
    exact (MvPolynomial.degreeOf_le_iff.mp (haffine coordinate)) exponent
      (MvPolynomial.support_map_subset (Rat.castHom ℝ) expression.toMvPolynomial hexponent)
  have hevaluation : (fun point => Math.Interval.RationalPolynomial.evalReal point expression) =
      (fun point => MvPolynomial.eval point polynomial) := by
    funext point
    rw [Math.Interval.RationalPolynomial.evalReal_eq_eval₂_toMvPolynomial,
      MvPolynomial.eval₂_eq_eval_map]
  rw [hevaluation]
  exact not_isQuittingFullExactRootPotential_multiAffine hreward hsingleton polynomial hreal

end GameTheory
