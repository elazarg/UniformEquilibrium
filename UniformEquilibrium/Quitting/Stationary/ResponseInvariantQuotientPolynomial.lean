import Mathlib.Algebra.MvPolynomial.Funext
import UniformEquilibrium.Quitting.Stationary.ResponseInvariantQuotientAmbientIdentity

/-! # Finite linear coefficient tests for actual response invariance

The polynomial evaluates to the existing zero-discount displacement after actual
coordinate repetition. Its finite test indices depend only on the block map and
coalition bases. The displayed coefficients are linear in the actual reward rows.
This is an exact response-invariance test, not an equilibrium producer.
-/

noncomputable section

namespace GameTheory

open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- The actual opponents' coalition mass after coordinate repetition. -/
def quittingBlockCoalitionPolynomial (block : ι → Fin k) (who : ι)
    (coalition : Finset ι) : MvPolynomial (Fin k) ℝ :=
  (∏ player ∈ coalition, MvPolynomial.X (block player)) *
    ∏ player ∈ Finset.univ.erase who \ coalition, (1 - MvPolynomial.X (block player))

/-- The opponents' all-Continue polynomial in the same block coordinates. -/
def quittingBlockContinuePolynomial (block : ι → Fin k) (who : ι) :
    MvPolynomial (Fin k) ℝ :=
  ∏ player ∈ Finset.univ.erase who, (1 - MvPolynomial.X (block player))

/-- The reward-independent basis multiplying each pure-Quit reward entry. -/
def quittingBlockQuitBasisPolynomial (block : ι → Fin k) (who : ι)
    (coalition : Finset ι) : MvPolynomial (Fin k) ℝ :=
  (1 - quittingBlockContinuePolynomial block who) *
    quittingBlockCoalitionPolynomial block who coalition

/-- A polynomial encoding of the canonical displacement, not a second response map. -/
def quittingBlockResponsePolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) (who : ι) :
    MvPolynomial (Fin k) ℝ :=
  (∑ coalition ∈ (Finset.univ.erase who).powerset,
    MvPolynomial.C (weightOfReward reward (insert who coalition) who) *
      quittingBlockQuitBasisPolynomial block who coalition) -
  ∑ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
    MvPolynomial.C (weightOfReward reward coalition who) *
      quittingBlockCoalitionPolynomial block who coalition

private theorem eval_quittingBlockCoalitionPolynomial (block : ι → Fin k) (who : ι)
    (coalition : Finset ι) (point : Fin k → ℝ) :
    MvPolynomial.eval point (quittingBlockCoalitionPolynomial block who coalition) =
      (∏ player ∈ coalition, quittingBlockLift block point player) *
        ∏ player ∈ Finset.univ.erase who \ coalition,
          (1 - quittingBlockLift block point player) := by
  simp [quittingBlockCoalitionPolynomial, quittingBlockLift]

private theorem eval_quittingBlockContinuePolynomial (block : ι → Fin k) (who : ι)
    (point : Fin k → ℝ) :
    MvPolynomial.eval point (quittingBlockContinuePolynomial block who) =
      continueMassExcl (quittingBlockLift block point) who := by
  simp [quittingBlockContinuePolynomial, continueMassExcl,
    quittingBlockLift]

/-- Exact evaluation holds on the entire signed ambient space, including empty indices. -/
theorem eval_quittingBlockResponsePolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) (who : ι)
    (point : Fin k → ℝ) :
    MvPolynomial.eval point (quittingBlockResponsePolynomial reward block who) =
      quittingDiscountedDisplacement reward 0 (quittingBlockLift block point) who := by
  simp only [quittingBlockResponsePolynomial, map_sub, MvPolynomial.eval_sum,
    map_mul, MvPolynomial.eval_C, quittingBlockQuitBasisPolynomial, map_one,
    eval_quittingBlockContinuePolynomial, eval_quittingBlockCoalitionPolynomial]
  unfold quittingDiscountedDisplacement sigmaValue excludedValue
  simp only [sub_zero, one_mul]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro coalition _
    ring
  · apply Finset.sum_congr rfl
    intro coalition _
    ring

/-- Every coefficient is the displayed finite linear combination of actual reward entries. -/
theorem coeff_quittingBlockResponsePolynomial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) (who : ι)
    (exponent : Fin k →₀ ℕ) :
    (quittingBlockResponsePolynomial reward block who).coeff exponent =
      (∑ coalition ∈ (Finset.univ.erase who).powerset,
        weightOfReward reward (insert who coalition) who *
          (quittingBlockQuitBasisPolynomial block who coalition).coeff exponent) -
      ∑ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
        weightOfReward reward coalition who *
          (quittingBlockCoalitionPolynomial block who coalition).coeff exponent := by
  simp only [quittingBlockResponsePolynomial, MvPolynomial.coeff_sub, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul]

/-- A finite reward-independent set containing every potentially nonzero coefficient. -/
def quittingBlockResponseCoefficientIndices (block : ι → Fin k) (who : ι) :
    Finset (Fin k →₀ ℕ) :=
  (Finset.univ.erase who).powerset.biUnion fun coalition =>
    (quittingBlockQuitBasisPolynomial block who coalition).support ∪
      (quittingBlockCoalitionPolynomial block who coalition).support

/-- No reward entry can create a coefficient outside the finite basis supports. -/
theorem coeff_quittingBlockResponsePolynomial_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) (who : ι)
    (exponent : Fin k →₀ ℕ)
    (houtside : exponent ∉ quittingBlockResponseCoefficientIndices block who) :
    (quittingBlockResponsePolynomial reward block who).coeff exponent = 0 := by
  have hquit (coalition : Finset ι) (hcoalition : coalition ∈
      (Finset.univ.erase who).powerset) :
      (quittingBlockQuitBasisPolynomial block who coalition).coeff exponent = 0 := by
    apply MvPolynomial.notMem_support_iff.mp
    intro hmem
    exact houtside (Finset.mem_biUnion.mpr
      ⟨coalition, hcoalition, Finset.mem_union_left _ hmem⟩)
  have hmass (coalition : Finset ι) (hcoalition : coalition ∈
      (Finset.univ.erase who).powerset) :
      (quittingBlockCoalitionPolynomial block who coalition).coeff exponent = 0 := by
    apply MvPolynomial.notMem_support_iff.mp
    intro hmem
    exact houtside (Finset.mem_biUnion.mpr
      ⟨coalition, hcoalition, Finset.mem_union_right _ hmem⟩)
  rw [coeff_quittingBlockResponsePolynomial]
  have hfirst : (∑ coalition ∈ (Finset.univ.erase who).powerset,
      weightOfReward reward (insert who coalition) who *
        (quittingBlockQuitBasisPolynomial block who coalition).coeff exponent) = 0 := by
    apply Finset.sum_eq_zero
    intro coalition hcoalition
    rw [hquit coalition hcoalition, mul_zero]
  have hsecond : (∑ coalition ∈ (Finset.univ.erase who).powerset.erase ∅,
      weightOfReward reward coalition who *
        (quittingBlockCoalitionPolynomial block who coalition).coeff exponent) = 0 := by
    apply Finset.sum_eq_zero
    intro coalition hcoalition
    rw [hmass coalition (Finset.mem_of_mem_erase hcoalition), mul_zero]
  rw [hfirst, hsecond, sub_self]

/-- Literal cube response invariance is polynomial equality for each pair in one block. -/
theorem quittingResponseInvariantOnUnitCube_iff_responsePolynomial_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) :
    QuittingResponseInvariantOnUnitCube reward block ↔
      ∀ first second : ι, block first = block second →
        quittingBlockResponsePolynomial reward block first =
          quittingBlockResponsePolynomial reward block second := by
  rw [quittingResponseInvariantOnUnitCube_iff_forall_ambient]
  constructor
  · intro hresponse first second hblock
    apply MvPolynomial.funext
    intro point
    simpa only [eval_quittingBlockResponsePolynomial] using hresponse point first second hblock
  · intro hpolynomial point first second hblock
    have heval := congrArg (MvPolynomial.eval point) (hpolynomial first second hblock)
    simpa only [eval_quittingBlockResponsePolynomial] using heval

/-- The exact finite system has coefficients linear in the original reward table.
The monomial index sets depend only on the displayed block map, not on reward data. -/
theorem quittingResponseInvariantOnUnitCube_iff_finite_coefficients
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (block : ι → Fin k) :
    QuittingResponseInvariantOnUnitCube reward block ↔
      ∀ first second : ι, block first = block second →
        ∀ exponent ∈ quittingBlockResponseCoefficientIndices block first ∪
            quittingBlockResponseCoefficientIndices block second,
          (quittingBlockResponsePolynomial reward block first).coeff exponent =
            (quittingBlockResponsePolynomial reward block second).coeff exponent := by
  rw [quittingResponseInvariantOnUnitCube_iff_responsePolynomial_eq]
  constructor
  · intro hpolynomial first second hblock exponent _
    exact congrArg (fun polynomial => polynomial.coeff exponent)
      (hpolynomial first second hblock)
  · intro hcoefficients first second hblock
    apply MvPolynomial.ext
    intro exponent
    by_cases hmem : exponent ∈ quittingBlockResponseCoefficientIndices block first ∪
        quittingBlockResponseCoefficientIndices block second
    · exact hcoefficients first second hblock exponent hmem
    · have hfirst : exponent ∉ quittingBlockResponseCoefficientIndices block first :=
        fun h => hmem (Finset.mem_union_left _ h)
      have hsecond : exponent ∉ quittingBlockResponseCoefficientIndices block second :=
        fun h => hmem (Finset.mem_union_right _ h)
      rw [coeff_quittingBlockResponsePolynomial_eq_zero reward block first exponent hfirst,
        coeff_quittingBlockResponsePolynomial_eq_zero reward block second exponent hsecond]

end GameTheory
