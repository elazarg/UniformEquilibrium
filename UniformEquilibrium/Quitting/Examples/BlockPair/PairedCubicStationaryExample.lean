import MathUE.CubicAnchorRoot
import MathUE.Polynomial.AlgebraicRoot
import UniformEquilibrium.Quitting.Root.FinFourEndpointRowSum
import UniformEquilibrium.Quitting.Root.RationalReward
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientSameProfile
import UniformEquilibrium.Quitting.Stationary.CompleteBehavioralCap
import UniformEquilibrium.Quitting.Stationary.RewardRowTranslation
import UniformEquilibrium.Quitting.Examples.BlockPair.FourPlayerPairedSingleton
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # A paired rational table with an exact cubic stationary equilibrium

The two hazards are uniquely selected in rational open intervals. Every row
sum, residual, payoff and complete cap refers to the literal original table.
The same stationary profile works at every accuracy. Positive playerwise
affine variants are compiled anew through their contracting opponent clocks;
no strategic-equivalence assertion about Never is used.
-/

noncomputable section

namespace GameTheory.PairedCubicStationaryExample

open QuittingFinFourEndpointRows Math.Finset QuittingLCPClassification Math.PMFProduct
open scoped BigOperators

/-- All fifteen nonempty terminal rows, including asymmetric joint rewards. -/
def rationalReward : RationalQuittingReward 4 := fun terminal =>
  match decide (0 ∈ terminal.val), decide (1 ∈ terminal.val),
      decide (2 ∈ terminal.val), decide (3 ∈ terminal.val) with
  | true, false, false, false => ![1, 4, 0, 0]
  | false, true, false, false => ![4, 1, 0, 0]
  | true, true, false, false => ![2, 2, 3, 2]
  | false, false, true, false => ![0, 0, 1, 4]
  | true, false, true, false => ![1, 1, -1, 1]
  | false, true, true, false => ![1, 1, -1, 1]
  | true, true, true, false => ![-2, -2, 0, 1]
  | false, false, false, true => ![0, 0, 4, 1]
  | true, false, false, true => ![1, 0, -1, 3]
  | false, true, false, true => ![0, 1, -1, 3]
  | true, true, false, true => ![-2, -2, 2, 1]
  | false, false, true, true => ![3, 3, 4, -1]
  | true, false, true, true => ![-1, 2, 2, -1]
  | false, true, true, true => ![2, -1, 2, -1]
  | true, true, true, true => ![1, 1, 4, 4]
  | false, false, false, false => 0

def reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  rationalQuittingRewardToReal rationalReward

theorem singletonMatrix :
    quittingSingletonMatrix reward = FourPlayerPairedSingleton.pairedSingletonMatrix := by
  ext owner who
  fin_cases owner <;> fin_cases who <;>
    norm_num +decide [quittingSingletonMatrix, reward, rationalQuittingRewardToReal,
      rationalReward, FourPlayerPairedSingleton.pairedSingletonMatrix]

def firstPolynomial (x : ℝ) : ℝ := 3 * x ^ 3 - 10 * x ^ 2 + 12 * x - 2

def secondPolynomial (x y : ℝ) : ℝ :=
  4 * x ^ 2 * y ^ 2 - 5 * x ^ 2 * y + x ^ 2 -
    4 * x * y ^ 2 + 3 * x * y - 3 * x + y

private theorem firstPolynomial_strictMono :
    StrictMonoOn firstPolynomial (Set.Ioo (197 / 1000 : ℝ) (1 / 5)) := by
  intro a ha b hb hab
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hfactor : 0 < 3 * (b ^ 2 + a * b + a ^ 2) - 10 * (a + b) + 12 := by
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg ha0 hb0, ha.2, hb.2]
  have hpositive := mul_pos (sub_pos.mpr hab) hfactor
  have hidentity : firstPolynomial b - firstPolynomial a =
      (b - a) * (3 * (b ^ 2 + a * b + a ^ 2) - 10 * (a + b) + 12) := by
    unfold firstPolynomial
    ring
  rw [← hidentity] at hpositive
  linarith

theorem exists_unique_firstRoot :
    ∃! x : ℝ, x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5) ∧ firstPolynomial x = 0 := by
  have hanchor (z : ℝ) :
      Math.cubicAnchor (-2) 12 (-10) 3 z = firstPolynomial z := by
    unfold Math.cubicAnchor firstPolynomial
    ring
  obtain ⟨x, hx, hzero⟩ :=
    Math.exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos
      (a := -2) (b := 12) (c := -10) (d := 3)
      (lo := 197 / 1000) (hi := 1 / 5) (by norm_num)
      (by norm_num [Math.cubicAnchor]) (by norm_num [Math.cubicAnchor])
  have hzero' : firstPolynomial x = 0 := by rwa [hanchor] at hzero
  refine ⟨x, ⟨hx, hzero'⟩, ?_⟩
  intro z hz
  apply firstPolynomial_strictMono.injOn hz.1 hx
  exact hz.2.trans hzero'.symm

private theorem secondPolynomial_strictMono {x : ℝ}
    (hx : x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5)) :
    StrictMonoOn (secondPolynomial x) (Set.Ioo (1 / 2 : ℝ) (3 / 5)) := by
  intro a ha b hb hab
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hx1 : x ≤ 1 := by linarith [hx.2]
  have hxsq : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith [hx.2])
      (show 0 ≤ 1 / 5 + x by linarith)]
  have hproduct : x * (1 - x) ≤ (4 / 25 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith [hx.2])
      (show 0 ≤ 4 / 5 - x by linarith [hx.2])]
  have hbound : x * (1 - x) * (a + b) ≤ (4 / 25 : ℝ) * (6 / 5) :=
    mul_le_mul hproduct (by linarith [ha.2, hb.2])
      (by linarith [ha.1, hb.1]) (by norm_num)
  have hfactor :
      0 < 4 * x ^ 2 * (a + b) - 5 * x ^ 2 - 4 * x * (a + b) + 3 * x + 1 := by
    nlinarith [hx.1]
  have hidentity : secondPolynomial x b - secondPolynomial x a =
      (b - a) *
        (4 * x ^ 2 * (a + b) - 5 * x ^ 2 - 4 * x * (a + b) + 3 * x + 1) := by
    unfold secondPolynomial
    ring
  have hpositive := mul_pos (sub_pos.mpr hab) hfactor
  rw [← hidentity] at hpositive
  linarith

theorem exists_unique_secondRoot {x : ℝ}
    (hx : x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5)) :
    ∃! y : ℝ, y ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5) ∧ secondPolynomial x y = 0 := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxsqLower : (197 / 1000 : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ x - 197 / 1000 by linarith [hx.1])
      (show 0 ≤ x + 197 / 1000 by linarith)]
  have hxsqUpper : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith [hx.2])
      (show 0 ≤ 1 / 5 + x by linarith)]
  have hleft : secondPolynomial x (1 / 2) < 0 := by
    unfold secondPolynomial
    nlinarith [hx.1]
  have hright : 0 < secondPolynomial x (3 / 5) := by
    unfold secondPolynomial
    nlinarith [hx.2]
  have hanchor (z : ℝ) :
      Math.cubicAnchor (x ^ 2 - 3 * x) (-5 * x ^ 2 + 3 * x + 1)
        (4 * x ^ 2 - 4 * x) 0 z = secondPolynomial x z := by
    unfold Math.cubicAnchor secondPolynomial
    ring
  obtain ⟨y, hy, hzero⟩ :=
    Math.exists_cubicAnchor_root_mem_Ioo_of_neg_of_pos
      (a := x ^ 2 - 3 * x) (b := -5 * x ^ 2 + 3 * x + 1)
      (c := 4 * x ^ 2 - 4 * x) (d := 0)
      (lo := 1 / 2) (hi := 3 / 5) (by norm_num)
      (by rwa [hanchor]) (by rwa [hanchor])
  have hzero' : secondPolynomial x y = 0 := by rwa [hanchor] at hzero
  refine ⟨y, ⟨hy, hzero'⟩, ?_⟩
  intro z hz
  apply (secondPolynomial_strictMono hx).injOn hz.1 hy
  exact hz.2.trans hzero'.symm

def firstRoot : ℝ := Classical.choose exists_unique_firstRoot

theorem firstRoot_spec :
    firstRoot ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5) ∧ firstPolynomial firstRoot = 0 :=
  (Classical.choose_spec exists_unique_firstRoot).1

def secondRoot : ℝ :=
  Classical.choose (exists_unique_secondRoot firstRoot_spec.1)

theorem secondRoot_spec :
    secondRoot ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5) ∧
      secondPolynomial firstRoot secondRoot = 0 :=
  (Classical.choose_spec (exists_unique_secondRoot firstRoot_spec.1)).1

theorem firstRoot_isAlgebraic : IsAlgebraic ℚ firstRoot := by
  let polynomial : Polynomial ℚ :=
    3 * Polynomial.X ^ 3 - 10 * Polynomial.X ^ 2 + 12 * Polynomial.X - 2
  refine ⟨polynomial, ?_, ?_⟩
  · intro hzero
    have hcoefficient := congrArg (fun p : Polynomial ℚ => p.coeff 3) hzero
    norm_num [polynomial, Polynomial.coeff_X] at hcoefficient
  · simpa only [polynomial, map_sub, map_add, map_mul, map_pow,
      Polynomial.aeval_X, map_ofNat, firstPolynomial] using firstRoot_spec.2

theorem secondRoot_isAlgebraic : IsAlgebraic ℚ secondRoot := by
  let x := firstRoot
  let polynomial : Polynomial ℝ :=
    Polynomial.C (4 * x ^ 2 - 4 * x) * Polynomial.X ^ 2 +
      Polynomial.C (-5 * x ^ 2 + 3 * x + 1) * Polynomial.X ^ 1 +
      Polynomial.C (x ^ 2 - 3 * x) * Polynomial.X ^ 0
  have hx : IsAlgebraic ℚ x := firstRoot_isAlgebraic
  have hn (n : ℕ) : IsAlgebraic ℚ (n : ℝ) := isAlgebraic_natCast n
  have hquadratic : IsAlgebraic ℚ (4 * x ^ 2 - 4 * x) := by
    simpa using
      ((hn 4).mul (hx.pow 2)).sub ((hn 4).mul hx)
  have hlinear : IsAlgebraic ℚ (-5 * x ^ 2 + 3 * x + 1) := by
    simpa using
      (((hn 5).neg.mul (hx.pow 2)).add ((hn 3).mul hx)).add (hn 1)
  have hconstant : IsAlgebraic ℚ (x ^ 2 - 3 * x) := by
    simpa using (hx.pow 2).sub ((hn 3).mul hx)
  have hcoefficients : ∀ degree, IsAlgebraic ℚ (polynomial.coeff degree) := by
    intro degree
    have hq : IsAlgebraic ℚ
        ((Polynomial.C (4 * x ^ 2 - 4 * x) * Polynomial.X ^ 2).coeff degree) := by
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · exact hquadratic
      · exact isAlgebraic_zero
    have hl : IsAlgebraic ℚ
        ((Polynomial.C (-5 * x ^ 2 + 3 * x + 1) * Polynomial.X ^ 1).coeff degree) := by
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · exact hlinear
      · exact isAlgebraic_zero
    have hc : IsAlgebraic ℚ
        ((Polynomial.C (x ^ 2 - 3 * x) * Polynomial.X ^ 0).coeff degree) := by
      rw [Polynomial.coeff_C_mul_X_pow]
      split_ifs
      · exact hconstant
      · exact isAlgebraic_zero
    simpa only [polynomial, Polynomial.coeff_add] using (hq.add hl).add hc
  have hnonzero : polynomial ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 1) hzero
    simp only [polynomial, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
    have hxsq : x ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
      have hbounds := firstRoot_spec.1
      change 197 / 1000 < x ∧ x < 1 / 5 at hbounds
      nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - x by linarith [hbounds.2])
        (show 0 ≤ 1 / 5 + x by linarith [hbounds.1])]
    have hlower : 197 / 1000 < x := firstRoot_spec.1.1
    nlinarith
  apply Polynomial.isAlgebraic_of_eval_eq_zero_of_coeff_isAlgebraic
    polynomial hnonzero hcoefficients
  have hidentity : polynomial.eval secondRoot = secondPolynomial x secondRoot := by
    simp only [polynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    unfold secondPolynomial
    ring
  rw [hidentity]
  exact secondRoot_spec.2

def hazard (x y : ℝ) : Fin 4 → ℝ := ![x, x, y, 0]

def inactiveResidual (x y : ℝ) : ℝ :=
  9 * x ^ 4 * y ^ 2 - 13 * x ^ 4 * y + 4 * x ^ 4 -
    22 * x ^ 3 * y ^ 2 + 34 * x ^ 3 * y - 12 * x ^ 3 +
    15 * x ^ 2 * y ^ 2 - 18 * x ^ 2 * y + 5 * x ^ 2 +
    4 * x * y + 2 * x - 2 * y ^ 2 - 3 * y

theorem sigmaValue_eq (x y : ℝ) (who : Fin 4) :
    sigmaValue (weightOfReward reward) (hazard x y) who =
      ![1 + x - 4 * x * y, 1 + x - 4 * x * y, 1 - 4 * x + 3 * x ^ 2,
        1 + 4 * x - 4 * x ^ 2 - 2 * y - 4 * x * y + 9 * x ^ 2 * y] who := by
  rw [sigmaValue_eq_pureQuitEndpointRowSum]
  fin_cases who
  all_goals
    simp only [pureQuitEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
    norm_num +decide [weightOfReward, reward, rationalQuittingRewardToReal, rationalReward]
  all_goals ring

theorem excludedValue_eq (x y : ℝ) (who : Fin 4) :
    excludedValue (weightOfReward reward) (hazard x y) who =
      ![4 * x - 3 * x * y, 4 * x - 3 * x * y, 3 * x ^ 2,
        4 * y - 6 * x * y + x ^ 2 * y + 2 * x ^ 2] who := by
  rw [excludedValue_eq_excludedEndpointRowSum]
  fin_cases who
  all_goals
    simp only [excludedEndpointRowSum, Fin.sum_univ_succ]
    simp +decide [opponentCoalitionMass, finFourCoalitionOfRow, Fin.prod_univ_succ, hazard]
    norm_num +decide [weightOfReward, reward, rationalQuittingRewardToReal, rationalReward]
  all_goals ring

theorem continueMassExcl_eq (x y : ℝ) (who : Fin 4) :
    continueMassExcl (hazard x y) who =
      ![(1 - x) * (1 - y), (1 - x) * (1 - y),
        (1 - x) ^ 2, (1 - x) ^ 2 * (1 - y)] who := by
  fin_cases who
  · change continueMassExcl (hazard x y) (0 : Fin 4) = _
    rw [continueMassExcl, show Finset.univ.erase (0 : Fin 4) = {1, 2, 3} by decide]
    simp [hazard, Finset.prod_insert]
  · change continueMassExcl (hazard x y) (1 : Fin 4) = _
    rw [continueMassExcl, show Finset.univ.erase (1 : Fin 4) = {0, 2, 3} by decide]
    simp [hazard, Finset.prod_insert]
  · change continueMassExcl (hazard x y) (2 : Fin 4) = _
    rw [continueMassExcl, show Finset.univ.erase (2 : Fin 4) = {0, 1, 3} by decide]
    simp [hazard, Finset.prod_insert, pow_two]
  · change continueMassExcl (hazard x y) (3 : Fin 4) = _
    rw [continueMassExcl, show Finset.univ.erase (3 : Fin 4) = {0, 1, 2} by decide]
    simp [hazard, Finset.prod_insert, pow_two, mul_assoc]

/-- The whole four-player residual vector, before imposing either root equation. -/
theorem displacement_eq (x y : ℝ) (who : Fin 4) :
    quittingDiscountedDisplacement reward 0 (hazard x y) who =
      ![secondPolynomial x y, secondPolynomial x y,
        -x * firstPolynomial x, inactiveResidual x y] who := by
  rw [quittingDiscountedDisplacement, sigmaValue_eq, excludedValue_eq, continueMassExcl_eq]
  fin_cases who
  all_goals norm_num [firstPolynomial, secondPolynomial, inactiveResidual]
  all_goals ring

theorem inactiveResidual_le {x y : ℝ}
    (hx : x ∈ Set.Ioo (197 / 1000 : ℝ) (1 / 5))
    (hy : y ∈ Set.Ioo (1 / 2 : ℝ) (3 / 5)) :
    inactiveResidual x y ≤ -(8269 / 15625 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hy0 : 0 ≤ y := by linarith [hy.1]
  have hxUpper : x ≤ 1 / 5 := hx.2.le
  have hyUpper : y ≤ 3 / 5 := hy.2.le
  have hpositive :
      9 * x ^ 4 * y ^ 2 + 4 * x ^ 4 + 34 * x ^ 3 * y +
        15 * x ^ 2 * y ^ 2 + 5 * x ^ 2 + 4 * x * y + 2 * x ≤
          (22981 / 15625 : ℝ) := by
    calc
      _ ≤ 9 * (1 / 5 : ℝ) ^ 4 * (3 / 5) ^ 2 + 4 * (1 / 5 : ℝ) ^ 4 +
          34 * (1 / 5 : ℝ) ^ 3 * (3 / 5) +
          15 * (1 / 5 : ℝ) ^ 2 * (3 / 5) ^ 2 + 5 * (1 / 5 : ℝ) ^ 2 +
          4 * (1 / 5 : ℝ) * (3 / 5) + 2 * (1 / 5 : ℝ) := by
        gcongr
      _ = _ := by norm_num
  have hnegative :
      0 ≤ 13 * x ^ 4 * y + 22 * x ^ 3 * y ^ 2 + 12 * x ^ 3 + 18 * x ^ 2 * y := by
    positivity
  have hyLower : 1 / 2 ≤ y := hy.1.le
  have hySquare : (1 / 2 : ℝ) ^ 2 ≤ y ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ y - 1 / 2 by linarith)
      (show 0 ≤ y + 1 / 2 by linarith)]
  unfold inactiveResidual
  nlinarith

def equilibriumHazard : Fin 4 → ℝ := hazard firstRoot secondRoot

theorem equilibriumHazard_bounds (who : Fin 4) :
    0 ≤ equilibriumHazard who ∧ equilibriumHazard who ≤ 1 := by
  have hx0 : 0 ≤ firstRoot := by linarith [firstRoot_spec.1.1]
  have hx1 : firstRoot ≤ 1 := by linarith [firstRoot_spec.1.2]
  have hy0 : 0 ≤ secondRoot := by linarith [secondRoot_spec.1.1]
  have hy1 : secondRoot ≤ 1 := by linarith [secondRoot_spec.1.2]
  fin_cases who
  · exact ⟨hx0, hx1⟩
  · exact ⟨hx0, hx1⟩
  · exact ⟨hy0, hy1⟩
  · exact ⟨le_rfl, zero_le_one⟩

def root : Fin 4 → PMF Bool :=
  rootOfHazard equilibriumHazard
    (fun who => (equilibriumHazard_bounds who).1)
    (fun who => (equilibriumHazard_bounds who).2)

theorem root_hazard : hazardOfRoot root = equilibriumHazard :=
  hazardOfRoot_rootOfHazard _ _ _

theorem root_absorption : 0 < quittingRootAbsorptionMass root := by
  apply (quittingRootAbsorptionMass_pos_iff_exists_quitProbability_pos root).mpr
  refine ⟨0, ?_⟩
  have hrate := congrFun root_hazard 0
  change (root 0 true).toReal = firstRoot at hrate
  rw [hrate]
  linarith [firstRoot_spec.1.1]

theorem root_absorbs : quittingStationaryContinueMass root < 1 := by
  have h := root_absorption
  unfold quittingRootAbsorptionMass at h
  linarith

theorem root_contracts (who : Fin 4) :
    quittingStationaryFixedOpponentsContinueMass root who < 1 := by
  by_cases hwho : who = 0
  · subst who
    apply quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit root
      (show (1 : Fin 4) ≠ 0 by decide)
    have hrate := congrFun root_hazard 1
    change (root 1 true).toReal = firstRoot at hrate
    rw [hrate]
    linarith [firstRoot_spec.1.1]
  · apply quittingStationaryFixedOpponentsContinueMass_lt_one_of_opponent_quit root (Ne.symm hwho)
    have hrate := congrFun root_hazard 0
    change (root 0 true).toReal = firstRoot at hrate
    rw [hrate]
    linarith [firstRoot_spec.1.1]

theorem root_jointSurvival :
    quittingStationaryContinueMass root =
      (1 - firstRoot) ^ 2 * (1 - secondRoot) := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp_rw [pmfBool_false_toReal]
  change (∏ who, (1 - hazardOfRoot root who)) = _
  rw [root_hazard]
  simp [equilibriumHazard, hazard, Fin.prod_univ_succ, pow_two, mul_assoc]

def value : Payoff (Fin 4) :=
  ![1 + firstRoot - 4 * firstRoot * secondRoot,
    1 + firstRoot - 4 * firstRoot * secondRoot,
    (firstRoot - 1) * (3 * firstRoot - 1),
    (4 * secondRoot - 6 * firstRoot * secondRoot +
      firstRoot ^ 2 * secondRoot + 2 * firstRoot ^ 2) /
      (1 - (1 - firstRoot) ^ 2 * (1 - secondRoot))]

theorem value_isAlgebraic (who : Fin 4) : IsAlgebraic ℚ (value who) := by
  have hx := firstRoot_isAlgebraic
  have hy := secondRoot_isAlgebraic
  have hn (n : ℕ) : IsAlgebraic ℚ (n : ℝ) := isAlgebraic_natCast n
  have hfirst : IsAlgebraic ℚ (1 + firstRoot - 4 * firstRoot * secondRoot) := by
    simpa using ((hn 1).add hx).sub (((hn 4).mul hx).mul hy)
  have hsecond : IsAlgebraic ℚ ((firstRoot - 1) * (3 * firstRoot - 1)) := by
    simpa using
      (hx.sub (hn 1)).mul (((hn 3).mul hx).sub (hn 1))
  have hnumerator : IsAlgebraic ℚ
      (4 * secondRoot - 6 * firstRoot * secondRoot +
        firstRoot ^ 2 * secondRoot + 2 * firstRoot ^ 2) := by
    simpa using
      ((((hn 4).mul hy).sub (((hn 6).mul hx).mul hy)).add
        ((hx.pow 2).mul hy)).add ((hn 2).mul (hx.pow 2))
  have hdenominator : IsAlgebraic ℚ
      (1 - (1 - firstRoot) ^ 2 * (1 - secondRoot)) := by
    simpa using
      (hn 1).sub ((((hn 1).sub hx).pow 2).mul ((hn 1).sub hy))
  fin_cases who
  · exact hfirst
  · exact hfirst
  · exact hsecond
  · change IsAlgebraic ℚ
      ((4 * secondRoot - 6 * firstRoot * secondRoot +
        firstRoot ^ 2 * secondRoot + 2 * firstRoot ^ 2) /
        (1 - (1 - firstRoot) ^ 2 * (1 - secondRoot)))
    simpa only [div_eq_mul_inv] using hnumerator.mul hdenominator.inv

private theorem value_eq_sigma (who : Fin 4) (hwho : who ≠ 3) :
    value who = sigmaValue (weightOfReward reward) equilibriumHazard who := by
  rw [equilibriumHazard, sigmaValue_eq]
  fin_cases who
  all_goals simp [value] at *
  all_goals ring

private theorem active_residual_zero (who : Fin 4) (hwho : who ≠ 3) :
    quittingDiscountedDisplacement reward 0 equilibriumHazard who = 0 := by
  rw [equilibriumHazard, displacement_eq]
  fin_cases who
  all_goals simp [firstRoot_spec.2, secondRoot_spec.2] at *

theorem root_hazard_isAlgebraic (who : Fin 4) :
    IsAlgebraic ℚ (hazardOfRoot root who) := by
  rw [root_hazard]
  fin_cases who
  · exact firstRoot_isAlgebraic
  · exact firstRoot_isAlgebraic
  · exact secondRoot_isAlgebraic
  · exact isAlgebraic_zero

theorem root_bellman : value = quittingRootSuccessorPayoff reward value root := by
  have hdenom : 1 - (1 - firstRoot) ^ 2 * (1 - secondRoot) ≠ 0 := by
    rw [← root_jointSurvival]
    linarith [root_absorbs]
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue, pmfBool_false_toReal]
  change value who = hazardOfRoot root who * _ + (1 - hazardOfRoot root who) * _
  rw [root_hazard]
  by_cases hwho : who = 3
  · subst who
    rw [equilibriumHazard, sigmaValue_eq, gammaValue, excludedValue_eq, continueMassExcl_eq]
    norm_num [hazard, value]
    field_simp [hdenom]
    ring
  · have hresidual := active_residual_zero who hwho
    have hvalue := value_eq_sigma who hwho
    unfold quittingDiscountedDisplacement at hresidual
    rw [hvalue]
    unfold gammaValue
    have hexcluded :
        excludedValue (weightOfReward reward) equilibriumHazard who =
          (1 - continueMassExcl equilibriumHazard who) *
            sigmaValue (weightOfReward reward) equilibriumHazard who := by
      nlinarith
    rw [hexcluded]
    ring

theorem root_terminalPayoff :
    quittingTerminalPayoff reward (quittingStationaryProfile reward root) = value :=
  quittingTerminalPayoff_stationary_eq_of_fixedPoint
    reward root value root_absorbs root_bellman

theorem root_endpointNash : IsεQuittingRootEndpointNash reward value 0 root := by
  have hzero (who : Fin 4) (hwho : who ≠ 3) :
      quittingRootEndpointDifference reward value root who = 0 := by
    have hmass := quittingRootAbsorptionMass_mul_endpointDifference_stationary reward root who
    rw [root_terminalPayoff, root_hazard] at hmass
    have hresidual := active_residual_zero who hwho
    rw [hresidual] at hmass
    exact (mul_eq_zero.mp hmass).resolve_left (ne_of_gt root_absorption)
  have hnegative : quittingRootEndpointDifference reward value root 3 ≤ 0 := by
    have hmass := quittingRootAbsorptionMass_mul_endpointDifference_stationary reward root 3
    rw [root_terminalPayoff, root_hazard, equilibriumHazard, displacement_eq] at hmass
    have hbound := inactiveResidual_le firstRoot_spec.1 secondRoot_spec.1
    change quittingRootAbsorptionMass root *
      quittingRootEndpointDifference reward value root 3 =
        inactiveResidual firstRoot secondRoot at hmass
    nlinarith [root_absorption]
  intro who
  rw [pmfBool_false_toReal]
  change (1 - hazardOfRoot root who) * quittingRootEndpointDifference reward value root who ≤ 0 ∧
    -0 ≤ hazardOfRoot root who * quittingRootEndpointDifference reward value root who
  rw [root_hazard]
  by_cases hwho : who = 3
  · subst who
    simpa [equilibriumHazard, hazard] using And.intro hnegative (le_rfl : (0 : ℝ) ≤ 0)
  · rw [hzero who hwho]
    simp

theorem root_fullCap (who : Fin 4) :
    quittingStationaryFullRateUnilateralCap reward root who = value who :=
  quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
    reward root value root_absorbs root_bellman root_endpointNash
    (isQuittingStationaryBoundaryAdmissible_of_contracts reward root value root_contracts) who

/-- The cap is over all behavioral responses, including Never and later replies. -/
theorem root_completeBehavioralCap (who : Fin 4) :
    quittingContinuationBestResponseValue reward (quittingStationaryProfile reward root) who =
      value who := by
  rw [quittingContinuationBestResponseValue_stationary_eq_fullRateUnilateralCap]
  exact root_fullCap who

theorem root_terminalNash :
    (quittingGame reward).IsεAsymptoticNash (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward root) :=
  isZeroAsymptoticNash_stationary_of_fixedPoint_endpointNash_contracts
    reward root value root_absorbs root_bellman root_endpointNash root_contracts

theorem root_sameProfileUniform :
    ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
      ∀ horizon, threshold ≤ horizon →
        (quittingGame reward).IsεHorizonNash none horizon accuracy
          (quittingStationaryProfile reward root) ∧
        ∀ who, |(quittingGame reward).finiteAveragePayoff none horizon
          (quittingStationaryProfile reward root) who - value who| ≤ accuracy := by
  obtain ⟨_, hsame⟩ := terminalNash_and_sameProfileUniform_of_stationaryBoundary
    reward root value root_absorption root_bellman
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward value root).mp
      root_endpointNash)
    (isQuittingStationaryBoundaryAdmissible_of_contracts reward root value root_contracts)
  simpa only [root_terminalPayoff] using hsame

theorem value_isUniformEquilibriumPayoff :
    (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
    reward root value root_absorbs root_bellman root_endpointNash root_contracts

/-- Affine compilation reuses the SAME root and freshly checks the Never boundary. -/
theorem root_playerwiseAffine_semantics (scale shift : Payoff (Fin 4))
    (hscale : ∀ who, 0 < scale who) :
    let translated := quittingPlayerwiseAffineReward reward scale shift
    let target := quittingPlayerwiseAffinePayoff scale shift value
    quittingTerminalPayoff translated (quittingStationaryProfile translated root) = target ∧
      (∀ who, quittingStationaryFullRateUnilateralCap translated root who = target who) ∧
      (quittingGame translated).IsεAsymptoticNash (quittingTerminalPayoff translated) 0
        (quittingStationaryProfile translated root) ∧
      (quittingGame translated).IsUniformEquilibriumPayoff none target ∧
      ∀ accuracy : ℝ, 0 < accuracy → ∃ threshold : ℕ,
        ∀ horizon, threshold ≤ horizon →
          (quittingGame translated).IsεHorizonNash none horizon accuracy
            (quittingStationaryProfile translated root) ∧
          ∀ who, |(quittingGame translated).finiteAveragePayoff none horizon
            (quittingStationaryProfile translated root) who - target who| ≤ accuracy := by
  let translated := quittingPlayerwiseAffineReward reward scale shift
  let target := quittingPlayerwiseAffinePayoff scale shift value
  have hbellman : target = quittingRootSuccessorPayoff translated target root := by
    funext who
    rw [quittingRootSuccessorPayoff_playerwiseAffine]
    change scale who * value who + shift who =
      scale who * quittingRootSuccessorPayoff reward value root who + shift who
    rw [← root_bellman]
  have hnash : IsεQuittingRootNash translated target 0 root :=
    isZeroQuittingRootNash_playerwiseAffine reward scale shift value root hscale
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward value root).mp
        root_endpointNash)
  have hendpoint := (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    translated target root).mpr hnash
  have hpayoff := quittingTerminalPayoff_stationary_eq_of_fixedPoint
    translated root target root_absorbs hbellman
  obtain ⟨hterminal, hsame⟩ := terminalNash_and_sameProfileUniform_of_stationaryBoundary
    translated root target root_absorption hbellman hnash
    (isQuittingStationaryBoundaryAdmissible_of_contracts translated root target root_contracts)
  refine ⟨hpayoff, ?_, hterminal, ?_, ?_⟩
  · intro who
    exact quittingStationaryFullRateUnilateralCap_eq_of_fixedPoint_endpointNash
      translated root target root_absorbs hbellman hendpoint
      (isQuittingStationaryBoundaryAdmissible_of_contracts translated root target root_contracts)
      who
  · exact isUniformEquilibriumPayoff_of_stationaryEndpointCertificate_contracts
      translated root target root_absorbs hbellman hendpoint root_contracts
  · simpa only [hpayoff] using hsame

def canonicalShift : Payoff (Fin 4) := ![0, -1, -1, -1]

def canonicalReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  quittingPlayerwiseAffineReward reward 1 canonicalShift

def normalizedReward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4) :=
  quittingPlayerwiseAffineReward reward (fun _ => 1 / 4) (fun who => canonicalShift who / 4)

theorem normalizedReward_eq (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) :
    normalizedReward terminal who = canonicalReward terminal who / 4 := by
  unfold normalizedReward canonicalReward quittingPlayerwiseAffineReward
  simp only [Pi.one_apply, one_mul]
  ring

theorem canonicalReward_singleton (who : Fin 4) :
    canonicalReward (quittingSingletonTerminal who) who = ![1, 0, 0, 0] who := by
  fin_cases who <;>
    norm_num +decide [canonicalReward, quittingPlayerwiseAffineReward, canonicalShift,
      reward, rationalQuittingRewardToReal, rationalReward, quittingSingletonTerminal]

theorem canonicalReward_bound (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) : |canonicalReward terminal who| ≤ 4 := by
  obtain ⟨row, rfl⟩ := finFourCoalitionRowEquiv.surjective terminal
  fin_cases row <;> fin_cases who <;>
    norm_num +decide [canonicalReward, quittingPlayerwiseAffineReward, reward,
      rationalQuittingRewardToReal, rationalReward, canonicalShift, finFourCoalitionRowEquiv,
      finFourCoalitionOfRow]

theorem normalizedReward_bound (terminal : {S : Finset (Fin 4) // S.Nonempty})
    (who : Fin 4) : |normalizedReward terminal who| ≤ 1 := by
  rw [normalizedReward_eq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact (div_le_one (by norm_num : (0 : ℝ) < 4)).mpr (canonicalReward_bound terminal who)

theorem canonicalReward_displacement (q : Fin 4 → ℝ) (who : Fin 4) :
    quittingDiscountedDisplacement canonicalReward 0 q who =
      quittingDiscountedDisplacement reward 0 q who :=
  quittingDiscountedDisplacement_zero_playerwiseTranslation reward canonicalShift q who

/-- Both source normalizations retain the original algebraic hazards and actual caps. -/
theorem canonical_and_normalized_sameRoot :
    (quittingTerminalPayoff canonicalReward (quittingStationaryProfile canonicalReward root) =
        quittingPlayerwiseAffinePayoff 1 canonicalShift value) ∧
      (∀ who, quittingStationaryFullRateUnilateralCap canonicalReward root who =
        value who + canonicalShift who) ∧
      (quittingTerminalPayoff normalizedReward (quittingStationaryProfile normalizedReward root) =
        fun who => (value who + canonicalShift who) / 4) ∧
      (∀ who, quittingStationaryFullRateUnilateralCap normalizedReward root who =
        (value who + canonicalShift who) / 4) := by
  obtain ⟨hcanonical, hcanonicalCap, _, _, _⟩ := root_playerwiseAffine_semantics
    1 canonicalShift (by intro who; norm_num)
  obtain ⟨hnormalized, hnormalizedCap, _, _, _⟩ := root_playerwiseAffine_semantics
    (fun _ => 1 / 4) (fun who => canonicalShift who / 4) (by intro who; norm_num)
  refine ⟨hcanonical, ?_, ?_, ?_⟩
  · simpa [canonicalReward, quittingPlayerwiseAffinePayoff] using hcanonicalCap
  · have htarget :
        quittingPlayerwiseAffinePayoff (fun _ : Fin 4 => (1 / 4 : ℝ))
          (fun who => canonicalShift who / 4) value =
          fun who => (value who + canonicalShift who) / 4 := by
      funext who
      change (1 / 4 : ℝ) * value who + canonicalShift who / 4 =
        (value who + canonicalShift who) / 4
      ring
    have hnormalized' :
        quittingTerminalPayoff normalizedReward
          (quittingStationaryProfile normalizedReward root) =
          quittingPlayerwiseAffinePayoff (fun _ => 1 / 4)
            (fun who => canonicalShift who / 4) value := hnormalized
    exact hnormalized'.trans htarget
  · intro who
    calc
      quittingStationaryFullRateUnilateralCap normalizedReward root who =
          (1 / 4 : ℝ) * value who + canonicalShift who / 4 := hnormalizedCap who
      _ = (value who + canonicalShift who) / 4 := by ring

end GameTheory.PairedCubicStationaryExample
