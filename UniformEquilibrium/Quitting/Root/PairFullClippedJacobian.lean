import UniformEquilibrium.Quitting.Root.FullClippedEndpointDerivative
import UniformEquilibrium.Quitting.Root.PairInactiveGapNumerator
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases

/-! # The actual full ambient Jacobian at an interior pair root

Active partials are identified using literal paired PMF endpoints on interior
coordinate lines. Inactive rows are full identity rows, not face derivatives.
Joining comparisons may have either sign. Strict inactive gaps include every
player outside the actual pair, even an unused member of a larger core.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem pair_gap_update_second
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    quittingRealHazardEndpointGap reward tail
      (Function.update (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))
        second rate) first =
      reward (quittingSingletonTerminal first) first - tail first +
        quittingPairHazardDenominator reward tail first second * rate := by
  let law := quittingHazardCoin rate hzero hone
  have hpoint : hazardOfRoot (PairedCycle.root first second firstLaw law) =
      Function.update (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))
        second rate := by
    funext who
    by_cases hsecond : who = second
    · subst who
      simp [hazardOfRoot, law]
    · by_cases hfirst : who = first
      · subst who
        simp [hazardOfRoot, hne]
      · simp [hazardOfRoot, PairedCycle.root_outside hfirst hsecond, hsecond]
  rw [← hpoint, quittingRealHazardEndpointGap_hazardOfRoot]
  unfold quittingRootEndpointDifference
  rw [PairedCycle.rootQuit_first reward tail hne,
    PairedCycle.rootContinue_first reward tail hne]
  simp only [law, quittingHazardCoin_true_toReal]
  unfold Math.PairedAffine.activeValue quittingPairHazardDenominator quittingPairJoiningGap
  ring

theorem quittingRealHazardEndpointGap_pair_cross_partial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard first)
      (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)) (Pi.single second 1) =
        quittingPairHazardDenominator reward tail first second := by
  let point := hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)
  have hregular := contDiff_quittingRealHazardEndpointGap reward tail 1 first
  have hgap := (hregular.differentiable_one point).hasFDerivAt
  have hchain := hgap.comp_hasDerivAt_of_eq (point second)
    (hasDerivAt_update point second (point second)) (by simp)
  have hpoint : point second = (secondLaw true).toReal := by simp [point, hazardOfRoot]
  have hlinear := (hasDerivAt_const (point second)
      (reward (quittingSingletonTerminal first) first - tail first)).add
        ((hasDerivAt_id (point second)).const_mul
          (quittingPairHazardDenominator reward tail first second))
  simp only [mul_one, zero_add] at hlinear
  have hformula := hlinear.congr_of_eventuallyEq (f₁ := fun rate =>
    quittingRealHazardEndpointGap reward tail (Function.update point second rate) first) (by
    filter_upwards [isOpen_Ioo.mem_nhds (hpoint.symm ▸ hsecond)] with rate hrate
    exact pair_gap_update_second reward tail hne firstLaw secondLaw rate hrate.1.le hrate.2.le)
  exact hchain.unique hformula

omit [Fintype ι] in
private def pairCoordinateEquiv {first second : ι} (hne : first ≠ second) :
    Fin 2 ≃ {who // who ∈ ({first, second} : Finset ι)} where
  toFun index := if index = 0 then ⟨first, by simp⟩ else ⟨second, by simp⟩
  invFun who := if who.val = first then 0 else 1
  left_inv := by
    intro index
    fin_cases index <;> simp [hne.symm]
  right_inv := by
    rintro ⟨who, hwho⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwho
    rcases hwho with rfl | rfl <;> simp [hne.symm]

/-- The canonical full pair block has determinant -alpha_first*alpha_second.
The following theorem separately identifies it as an actual derivative. -/
theorem quittingFullClippedDisplacementDerivative_pair_det
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det =
      -(quittingPairHazardDenominator reward tail first second *
        quittingPairHazardDenominator reward tail second first) := by
  rw [quittingFullClippedDisplacementDerivative_det_eq_active_det]
  rw [← Matrix.det_submatrix_equiv_self (pairCoordinateEquiv hne)]
  rw [Matrix.det_fin_two]
  have hcrossFirst := quittingRealHazardEndpointGap_pair_cross_partial
    reward tail hne firstLaw secondLaw hsecond
  have hcrossSecond := quittingRealHazardEndpointGap_pair_cross_partial
    reward tail hne.symm secondLaw firstLaw hfirst
  rw [← PairedCycle.root_swap hne firstLaw secondLaw] at hcrossSecond
  have hcoordinateZero : (pairCoordinateEquiv hne (0 : Fin 2)).val = first := rfl
  have hcoordinateOne : (pairCoordinateEquiv hne (1 : Fin 2)).val = second := rfl
  have hfirstMem : first ∈ ({first, second} : Finset ι) := by simp
  have hsecondMem : second ∈ ({first, second} : Finset ι) := by simp
  simp only [Matrix.submatrix_apply, hcoordinateZero, hcoordinateOne,
    quittingFullClippedDisplacementDerivative_matrix_entry, hfirstMem, hsecondMem, ite_true,
    quittingRealHazardEndpointGap_own_partial_eq_zero, hcrossFirst, hcrossSecond]
  ring

private theorem pair_exact_first_gap_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw)) :
    quittingRootEndpointDifference reward tail
      (PairedCycle.root first second firstLaw secondLaw) first = 0 := by
  apply quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail _ first
    ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail _).mpr hnash)
  · rw [PairedCycle.root_first hne, Math.PMFProduct.pmfBool_false_toReal]
    exact sub_pos.mpr hfirst.2
  · simpa only [PairedCycle.root_first hne] using hfirst.1

/-- Proper pair Nash plus strictly negative inactive gaps supplies the actual
full ambient derivative. No active-face derivative or index is an input. -/
theorem hasFDerivAt_quittingFullClippedDisplacement_of_pairNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hnegative : ∀ who, who ≠ first → who ≠ second →
      quittingRootEndpointDifference reward tail
        (PairedCycle.root first second firstLaw secondLaw) who < 0) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)))
      (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)) := by
  have hgapFirst := pair_exact_first_gap_zero reward tail hne firstLaw secondLaw hfirst hnash
  have hnashSwap : IsεQuittingRootNash reward tail 0
      (PairedCycle.root second first secondLaw firstLaw) := by
    rwa [← PairedCycle.root_swap hne firstLaw secondLaw]
  have hgapSecond := pair_exact_first_gap_zero reward tail hne.symm
    secondLaw firstLaw hsecond hnashSwap
  rw [← PairedCycle.root_swap hne firstLaw secondLaw] at hgapSecond
  apply hasFDerivAt_quittingFullClippedDisplacement
  · intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with rfl | rfl
    · simpa only [quittingRealHazardEndpointGap_hazardOfRoot, hgapFirst, add_zero,
        hazardOfRoot, PairedCycle.root_first hne] using hfirst
    · simpa only [quittingRealHazardEndpointGap_hazardOfRoot, hgapSecond, add_zero,
        hazardOfRoot, PairedCycle.root_second] using hsecond
  · intro player hplayer
    have hfirstNe : player ≠ first := by
      intro heq
      exact hplayer (heq.symm ▸ Finset.mem_insert_self first {second})
    have hsecondNe : player ≠ second := by
      intro heq
      exact hplayer (heq.symm ▸ (by simp : second ∈ ({first, second} : Finset ι)))
    left
    simpa [quittingRealHazardEndpointGap_hazardOfRoot, hazardOfRoot,
      PairedCycle.root_outside hfirstNe hsecondNe] using hnegative player hfirstNe hsecondNe

theorem quittingPairJoiningGap_eq_survival_mul_denominator_of_pairNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw)) :
    quittingPairJoiningGap reward first second =
      (1 - (secondLaw true).toReal) *
        quittingPairHazardDenominator reward tail first second := by
  have hgap := pair_exact_first_gap_zero reward tail hne firstLaw secondLaw hfirst hnash
  unfold quittingRootEndpointDifference at hgap
  rw [PairedCycle.rootQuit_first reward tail hne,
    PairedCycle.rootContinue_first reward tail hne] at hgap
  unfold Math.PairedAffine.activeValue at hgap
  dsimp only [quittingPairJoiningGap, quittingPairHazardDenominator]
  nlinarith [hgap]

/-- Same-sign strict joining comparisons make the actual full determinant
negative. Inactive inequalities are needed for actual differentiability,
not for this canonical block's algebraic determinant identity. -/
theorem quittingFullClippedDisplacementDerivative_pair_det_neg_of_pairNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first) :
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det <
      0 := by
  have hbalanceFirst := quittingPairJoiningGap_eq_survival_mul_denominator_of_pairNash
    reward tail hne firstLaw secondLaw hfirst hnash
  have hnashSwap : IsεQuittingRootNash reward tail 0
      (PairedCycle.root second first secondLaw firstLaw) := by
    rwa [← PairedCycle.root_swap hne firstLaw secondLaw]
  have hbalanceSecond := quittingPairJoiningGap_eq_survival_mul_denominator_of_pairNash
    reward tail hne.symm secondLaw firstLaw hsecond hnashSwap
  have hproduct : 0 < ((1 - (secondLaw true).toReal) * (1 - (firstLaw true).toReal)) *
      (quittingPairHazardDenominator reward tail first second *
        quittingPairHazardDenominator reward tail second first) := by
    rw [hbalanceFirst, hbalanceSecond] at hjoining
    nlinarith only [hjoining]
  have hpositive := pos_of_mul_pos_right hproduct
    (mul_pos (sub_pos.mpr hsecond.2) (sub_pos.mpr hfirst.2)).le
  rw [quittingFullClippedDisplacementDerivative_pair_det reward tail hne
    firstLaw secondLaw hfirst hsecond]
  exact neg_neg_of_pos hpositive

/-- The combined actual-source certificate: full ambient differentiability
and a negative, hence nonsingular, actual derivative. Every inactive player
is tested, including any unused member of a larger premium core. -/
theorem pairNash_hasFDerivAt_and_negative_det_fullClippedDisplacement
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second) (firstLaw secondLaw : PMF Bool)
    (hfirst : (firstLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (secondLaw true).toReal ∈ Ioo (0 : ℝ) 1)
    (hnash : IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second firstLaw secondLaw))
    (hnegative : ∀ who, who ≠ first → who ≠ second →
      quittingRootEndpointDifference reward tail
        (PairedCycle.root first second firstLaw secondLaw) who < 0)
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first) :
    HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)))
      (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)) ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det < 0 ∧
    (LinearMap.toMatrix'
      (quittingFullClippedDisplacementDerivative reward tail {first, second}
        (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw))).toLinearMap).det ≠
      0 := by
  have hnegativeDet := quittingFullClippedDisplacementDerivative_pair_det_neg_of_pairNash
    reward tail hne firstLaw secondLaw hfirst hsecond hnash hjoining
  exact ⟨hasFDerivAt_quittingFullClippedDisplacement_of_pairNash reward tail hne
    firstLaw secondLaw hfirst hsecond hnash hnegative, hnegativeDet, ne_of_lt hnegativeDet⟩

end GameTheory
