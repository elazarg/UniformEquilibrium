import UniformEquilibrium.Quitting.Examples.GuardedCrossedResponseCoordinateFreedom
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseHalfCoefficientNorms
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The literal selected twenty-two-coordinate open polyhedral slice

For each four-vector of signed own-singleton levels, the printed singleton
matrix is fixed. The selected nonsingleton coordinates satisfy exactly
twenty-four strict lower comparisons and eighteen strict affine coefficient
inequalities. Their region is open, convex, and nonempty. The other twenty-two
nonsingleton coordinates are independently arbitrary actual reward values.
-/

noncomputable section

namespace GameTheory.GuardedCrossedResponseExamples

open Set QuittingLCPClassification

/-- The twenty-two selected-recipient nonsingleton coordinates. -/
abbrev HalfSelectedRewardCoordinate :=
  {coordinate : {S : Finset (Fin 4) // S.Nonempty} × Fin 4 //
    coordinate.1.1.card ≠ 1 ∧ (coordinate.2 = 0 ∨ coordinate.2 = 1)}

abbrev HalfSelectedRewardSpace := HalfSelectedRewardCoordinate → ℝ

theorem card_halfSelectedRewardCoordinate : Fintype.card HalfSelectedRewardCoordinate = 22 := by
  decide

/-- Every actual reward coordinate is an explicit affine function of the selected entries. -/
def halfSelectedRewardAffine (solo : Payoff (Fin 4))
    (terminal : {S : Finset (Fin 4) // S.Nonempty}) (who : Fin 4) :
    HalfSelectedRewardSpace →ᵃ[ℝ] ℝ :=
  if h : terminal.1.card ≠ 1 ∧ (who = 0 ∨ who = 1) then
    (LinearMap.proj ⟨(terminal, who), h⟩ : HalfSelectedRewardSpace →ₗ[ℝ] ℝ).toAffineMap
  else AffineMap.const ℝ HalfSelectedRewardSpace
    (halfCeilingRewardWithFreedom solo 0 terminal who)

/-- The baseline table for the affine constraints has zero outsider nonsingletons. -/
def halfSelectedReward (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  fun terminal who => halfSelectedRewardAffine solo terminal who selected

/-- Final actual table: both sets of twenty-two nonsingleton entries are independent. -/
def halfPolyhedralReward (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) :
    {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  quittingHalfOutsiderCompletion (halfSelectedReward solo selected) outside

theorem halfPolyhedralReward_selected
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) (coordinate : HalfSelectedRewardCoordinate) :
    halfPolyhedralReward solo selected outside coordinate.1.1 coordinate.1.2 =
      selected coordinate := by
  rw [halfPolyhedralReward, quittingHalfOutsiderCompletion_selected _ _ _ _ coordinate.property.2]
  simp [halfSelectedReward, halfSelectedRewardAffine, coordinate.property]

theorem halfPolyhedralReward_outside
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) (coordinate : HalfOutsiderRewardCoordinate) :
    halfPolyhedralReward solo selected outside coordinate.1.1 coordinate.1.2 = outside coordinate :=
  quittingHalfOutsiderCompletion_free _ outside coordinate

theorem halfPolyhedralReward_singleton
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) (owner who : Fin 4) :
    halfPolyhedralReward solo selected outside ⟨{owner}, Finset.singleton_nonempty owner⟩ who =
      halfCeilingRewardWithFreedom solo 0 ⟨{owner}, Finset.singleton_nonempty owner⟩ who := by
  rw [halfPolyhedralReward, quittingHalfOutsiderCompletion_singleton]
  simp [halfSelectedReward, halfSelectedRewardAffine]

theorem halfPolyhedralReward_ownSingleton
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) (who : Fin 4) :
    halfPolyhedralReward solo selected outside ⟨{who}, Finset.singleton_nonempty who⟩ who =
      solo who := by
  rw [halfPolyhedralReward_singleton, halfCeilingRewardWithFreedom_ownSingleton]

theorem halfPolyhedralReward_singletonMatrix
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) :
    quittingSingletonMatrix (halfPolyhedralReward solo selected outside) =
      sourceSingletonMatrix := by
  calc
    _ = quittingSingletonMatrix (halfCeilingRewardWithFreedom solo 0) := by
      ext who owner
      simp only [quittingSingletonMatrix, halfPolyhedralReward_singleton]
    _ = _ := (halfCeilingRewardWithFreedom_source solo 0).1

/-- The two nonsingleton coordinate blocks are independently identifiable
from the final actual table. -/
theorem halfPolyhedralReward_injective (solo : Payoff (Fin 4)) :
    Function.Injective (fun coordinates :
      HalfSelectedRewardSpace × (HalfOutsiderRewardCoordinate → ℝ) =>
        halfPolyhedralReward solo coordinates.1 coordinates.2) := by
  intro first second heq
  apply Prod.ext
  · funext coordinate
    have h := congrFun (congrFun heq coordinate.1.1) coordinate.1.2
    simpa only [halfPolyhedralReward_selected] using h
  · funext coordinate
    have h := congrFun (congrFun heq coordinate.1.1) coordinate.1.2
    simpa only [halfPolyhedralReward_outside] using h

/-- Every actual reward with the printed singleton matrix occurs in this
parameterization. Thus no additional reward equality is hidden in the slice. -/
theorem halfPolyhedralReward_covers_fixedSingletonMatrix
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = sourceSingletonMatrix) :
    halfPolyhedralReward
        (fun who => reward ⟨{who}, Finset.singleton_nonempty who⟩ who)
        (fun coordinate => reward coordinate.1.1 coordinate.1.2)
        (fun coordinate => reward coordinate.1.1 coordinate.1.2) = reward := by
  let solo : Payoff (Fin 4) := fun who =>
    reward ⟨{who}, Finset.singleton_nonempty who⟩ who
  funext terminal who
  by_cases hsingle : terminal.1.card = 1
  · obtain ⟨owner, hterminal⟩ := Finset.card_eq_one.mp hsingle
    have heq : terminal = ⟨{owner}, Finset.singleton_nonempty owner⟩ :=
      Subtype.ext hterminal
    rw [heq, halfPolyhedralReward_singleton]
    have hsame := congrFun (congrFun
      ((halfCeilingRewardWithFreedom_source solo 0).1.trans hmatrix.symm) who) owner
    change halfCeilingRewardWithFreedom solo 0 ⟨{owner}, Finset.singleton_nonempty owner⟩ who -
        halfCeilingRewardWithFreedom solo 0 ⟨{who}, Finset.singleton_nonempty who⟩ who =
      reward ⟨{owner}, Finset.singleton_nonempty owner⟩ who -
        reward ⟨{who}, Finset.singleton_nonempty who⟩ who at hsame
    rw [halfCeilingRewardWithFreedom_ownSingleton] at hsame
    dsimp [solo] at hsame
    linarith
  · fin_cases who
    · exact halfPolyhedralReward_selected _ _ _ ⟨(terminal, 0), hsingle, Or.inl rfl⟩
    · exact halfPolyhedralReward_selected _ _ _ ⟨(terminal, 1), hsingle, Or.inr rfl⟩
    · exact halfPolyhedralReward_outside _ _ _ ⟨(terminal, 2), hsingle, Or.inl rfl⟩
    · exact halfPolyhedralReward_outside _ _ _ ⟨(terminal, 3), hsingle, Or.inr rfl⟩

abbrev HalfOutsiderSubset := {coalition : Finset (Fin 4) // coalition ⊆ {2, 3}}
abbrev HalfNonemptyOutsiderSubset :=
  {coalition : Finset (Fin 4) // coalition ⊆ {2, 3} ∧ coalition.Nonempty}
abbrev HalfLowerAffineIndex := Fin 2 × HalfOutsiderSubset × HalfNonemptyOutsiderSubset
abbrev HalfUpperAffineIndex := Fin 2 × Fin 3 × Fin 3
abbrev HalfAffineConstraintIndex := HalfLowerAffineIndex ⊕ HalfUpperAffineIndex

theorem card_halfLowerAffineIndex : Fintype.card HalfLowerAffineIndex = 24 := by decide
theorem card_halfUpperAffineIndex : Fintype.card HalfUpperAffineIndex = 18 := by decide
theorem card_halfAffineConstraintIndex : Fintype.card HalfAffineConstraintIndex = 42 := by decide

private def halfRecipient (index : Fin 2) : Fin 4 := if index = 0 then 0 else 1

/-- Exact affine lower margin: an own-plus-outsiders coordinate minus an external coordinate. -/
def halfLowerAffineConstraint (solo : Payoff (Fin 4)) (index : HalfLowerAffineIndex) :
    HalfSelectedRewardSpace →ᵃ[ℝ] ℝ :=
  halfSelectedRewardAffine solo
      ⟨insert (halfRecipient index.1) index.2.1.1, Finset.insert_nonempty _ _⟩
      (halfRecipient index.1) -
    halfSelectedRewardAffine solo ⟨index.2.2.1, index.2.2.2.2⟩ (halfRecipient index.1)

/-- Exact affine upper margin, using the actual coefficient functional's
fifteen-coordinate expansion, with its sign reversed. -/
def halfUpperAffineConstraint (solo : Payoff (Fin 4)) (index : HalfUpperAffineIndex) :
    HalfSelectedRewardSpace →ᵃ[ℝ] ℝ :=
  -(∑ row : Fin 15,
    Math.quadraticTensorBernsteinCoefficient
      (quittingHalfBasisPolynomial (halfRecipient index.1) row) index.2.1 index.2.2 •
        halfSelectedRewardAffine solo (Math.Finset.finFourCoalitionRowEquiv row)
          (halfRecipient index.1))

def halfAffineConstraint (solo : Payoff (Fin 4)) (index : HalfAffineConstraintIndex) :
    HalfSelectedRewardSpace →ᵃ[ℝ] ℝ :=
  match index with
  | Sum.inl lower => halfLowerAffineConstraint solo lower
  | Sum.inr upper => halfUpperAffineConstraint solo upper

/-- A finite intersection of exactly forty-two strict affine half-spaces. -/
def halfSelectedPolyhedralRegion (solo : Payoff (Fin 4)) : Set HalfSelectedRewardSpace :=
  ⋂ index : HalfAffineConstraintIndex, (halfAffineConstraint solo index) ⁻¹' Ioi 0

theorem mem_halfSelectedPolyhedralRegion_iff
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace) :
    selected ∈ halfSelectedPolyhedralRegion solo ↔
      ∀ index, 0 < halfAffineConstraint solo index selected := by
  simp [halfSelectedPolyhedralRegion]

theorem isOpen_halfSelectedPolyhedralRegion (solo : Payoff (Fin 4)) :
    IsOpen (halfSelectedPolyhedralRegion solo) :=
  isOpen_iInter_of_finite fun index =>
    isOpen_Ioi.preimage (halfAffineConstraint solo index).continuous_of_finiteDimensional

theorem convex_halfSelectedPolyhedralRegion (solo : Payoff (Fin 4)) :
    Convex ℝ (halfSelectedPolyhedralRegion solo) :=
  convex_iInter fun index =>
    Convex.affine_preimage (halfAffineConstraint solo index) (convex_Ioi 0)

private theorem halfLowerAffineConstraint_apply (solo : Payoff (Fin 4))
    (selected : HalfSelectedRewardSpace) (index : HalfLowerAffineIndex) :
    halfLowerAffineConstraint solo index selected =
      weightOfReward (halfSelectedReward solo selected)
          (insert (halfRecipient index.1) index.2.1.1) (halfRecipient index.1) -
        weightOfReward (halfSelectedReward solo selected) index.2.2.1 (halfRecipient index.1) := by
  simp [halfLowerAffineConstraint, weightOfReward, index.2.2.2.2, halfSelectedReward]

private theorem halfUpperAffineConstraint_first (solo : Payoff (Fin 4))
    (selected : HalfSelectedRewardSpace) (first second : Fin 3) :
    halfUpperAffineConstraint solo (0, first, second) selected =
      -Math.quadraticTensorBernsteinCoefficient
        (quittingHalfFirstResidual (halfSelectedReward solo selected)) first second := by
  rw [quittingHalfFirstCoefficient_eq_sum_basis]
  simp_rw [quittingHalfFirstResidual_rewardBasis]
  simp [halfUpperAffineConstraint, halfRecipient, Fin.sum_univ_succ, halfSelectedReward]

private theorem halfUpperAffineConstraint_second (solo : Payoff (Fin 4))
    (selected : HalfSelectedRewardSpace) (first second : Fin 3) :
    halfUpperAffineConstraint solo (1, first, second) selected =
      -Math.quadraticTensorBernsteinCoefficient
        (quittingHalfSecondResidual (halfSelectedReward solo selected)) first second := by
  rw [quittingHalfSecondCoefficient_eq_sum_basis]
  simp_rw [quittingHalfSecondResidual_rewardBasis]
  simp [halfUpperAffineConstraint, halfRecipient, Fin.sum_univ_succ, halfSelectedReward]

/-- These forty-two affine inequalities are exactly the literal raw guards,
not a sufficient subregion or a constraint on a supplied equilibrium. -/
theorem halfSelectedPolyhedralRegion_iff_strictRawGuards
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace) :
    selected ∈ halfSelectedPolyhedralRegion solo ↔
      QuittingHalfStrictRawGuards (halfSelectedReward solo selected) := by
  rw [mem_halfSelectedPolyhedralRegion_iff]
  have houtsidersFirst : quittingCrossedRawOutsiders (0 : Fin 4) 1 = {2, 3} := by decide
  have houtsidersSecond : quittingCrossedRawOutsiders (1 : Fin 4) 0 = {2, 3} := by decide
  constructor
  · intro h
    refine ⟨?_, ?_, ⟨?_, ?_⟩⟩
    · intro own other hown hother hnonempty
      rw [houtsidersFirst] at hown hother
      have hmargin := h (Sum.inl (0, ⟨own, hown⟩, ⟨other, hother, hnonempty⟩))
      change 0 < halfLowerAffineConstraint solo _ selected at hmargin
      rw [halfLowerAffineConstraint_apply] at hmargin
      simpa [halfRecipient] using sub_pos.mp hmargin
    · intro own other hown hother hnonempty
      rw [houtsidersSecond] at hown hother
      have hmargin := h (Sum.inl (1, ⟨own, hown⟩, ⟨other, hother, hnonempty⟩))
      change 0 < halfLowerAffineConstraint solo _ selected at hmargin
      rw [halfLowerAffineConstraint_apply] at hmargin
      simpa [halfRecipient] using sub_pos.mp hmargin
    · intro first second
      have hmargin := h (Sum.inr (0, first, second))
      change 0 < halfUpperAffineConstraint solo _ selected at hmargin
      rw [halfUpperAffineConstraint_first] at hmargin
      linarith
    · intro first second
      have hmargin := h (Sum.inr (1, first, second))
      change 0 < halfUpperAffineConstraint solo _ selected at hmargin
      rw [halfUpperAffineConstraint_second] at hmargin
      linarith
  · intro h index
    rcases index with ⟨recipient, own, other⟩ | ⟨recipient, first, second⟩
    · change 0 < halfLowerAffineConstraint solo _ selected
      rw [halfLowerAffineConstraint_apply]
      fin_cases recipient
      · simpa [halfRecipient] using sub_pos.mpr
          (h.lowerFirst own.1 other.1 (by simpa [houtsidersFirst] using own.2)
            (by simpa [houtsidersFirst] using other.2.1) other.2.2)
      · simpa [halfRecipient] using sub_pos.mpr
          (h.lowerSecond own.1 other.1 (by simpa [houtsidersSecond] using own.2)
            (by simpa [houtsidersSecond] using other.2.1) other.2.2)
    · change 0 < halfUpperAffineConstraint solo _ selected
      fin_cases recipient
      · change 0 < halfUpperAffineConstraint solo (0, first, second) selected
        rw [halfUpperAffineConstraint_first]
        exact neg_pos.mpr (h.upper.first first second)
      · change 0 < halfUpperAffineConstraint solo (1, first, second) selected
        rw [halfUpperAffineConstraint_second]
        exact neg_pos.mpr (h.upper.second first second)

/-- Outsider nonsingleton values place no additional restriction on the selected region. -/
theorem halfPolyhedralReward_strictRawGuards_iff
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (outside : HalfOutsiderRewardCoordinate → ℝ) :
    QuittingHalfStrictRawGuards (halfPolyhedralReward solo selected outside) ↔
      selected ∈ halfSelectedPolyhedralRegion solo :=
  (quittingHalfOutsiderCompletion_strictRawGuards_iff _ outside).trans
    (halfSelectedPolyhedralRegion_iff_strictRawGuards solo selected).symm

/-- An explicit member is obtained by translating the printed center's selected rows. -/
theorem nonempty_halfSelectedPolyhedralRegion (solo : Payoff (Fin 4)) :
    (halfSelectedPolyhedralRegion solo).Nonempty := by
  let selected : HalfSelectedRewardSpace := fun coordinate =>
    halfCeilingRewardWithFreedom solo 0 coordinate.1.1 coordinate.1.2
  have heq : halfSelectedReward solo selected = halfCeilingRewardWithFreedom solo 0 := by
    funext terminal who
    dsimp [halfSelectedReward, halfSelectedRewardAffine]
    split_ifs <;> rfl
  refine ⟨selected, (halfSelectedPolyhedralRegion_iff_strictRawGuards solo selected).mpr ?_⟩
  rw [heq]
  exact (halfCeilingRewardWithFreedom_source solo 0).2

/-- Every point of the open selected polyhedron and every independent outsider
completion produces its own actual contracting stationary equilibrium and UE target. -/
theorem halfPolyhedralReward_stationaryTerminalNash_uniformPayoff
    (solo : Payoff (Fin 4)) (selected : HalfSelectedRewardSpace)
    (hselected : selected ∈ halfSelectedPolyhedralRegion solo)
    (outside : HalfOutsiderRewardCoordinate → ℝ) :
    ∃ root : Fin 4 → PMF Bool, ∃ value : Payoff (Fin 4),
      0 < hazardOfRoot root 0 ∧ hazardOfRoot root 0 < 1 / 2 ∧
      0 < hazardOfRoot root 1 ∧ hazardOfRoot root 1 < 1 / 2 ∧
      (∃ outsider, outsider ≠ 0 ∧ outsider ≠ 1 ∧ 0 < hazardOfRoot root outsider) ∧
      value = quittingTerminalPayoff (halfPolyhedralReward solo selected outside)
        (quittingStationaryProfile (halfPolyhedralReward solo selected outside) root) ∧
      (∀ who, quittingStationaryFixedOpponentsContinueMass root who < 1) ∧
      (quittingGame (halfPolyhedralReward solo selected outside)).IsεAsymptoticNash
        (quittingTerminalPayoff (halfPolyhedralReward solo selected outside)) 0
        (quittingStationaryProfile (halfPolyhedralReward solo selected outside) root) ∧
      (quittingGame (halfPolyhedralReward solo selected outside)).IsUniformEquilibriumPayoff
        none value := by
  have hraw := (halfPolyhedralReward_strictRawGuards_iff solo selected outside).mpr hselected
  have hmatrix := halfPolyhedralReward_singletonMatrix solo selected outside
  apply exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_halfStrictRaw _ _ _ hraw
  · rw [hmatrix, sourceSingletonMatrix_det]
    norm_num
  · rw [hmatrix]
    exact sourceSingletonMatrix_inverse_pos

end GameTheory.GuardedCrossedResponseExamples
