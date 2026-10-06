import UniformEquilibrium.Quitting.Root.PairedProductRoot
import UniformEquilibrium.Quitting.Root.FullClippedEndpointMap
import MathUE.Topology.CoordinateAffineAvoidance
import Mathlib.Tactic.FunProp

/-! # Actual inactive endpoint numerators for a mixed pair

The numerator retains all three nonempty opponent coalitions, including
the simultaneous pair and its larger joining coalition. An inactive player
means any player outside this pair, not necessarily outside a premium core.
The identities do not assert Nash, selected return, or a degree value.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The joining comparison against the partner's solo outcome. -/
def quittingPairJoiningGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) : ℝ :=
  reward ⟨{first, second}, by simp⟩ first - reward (quittingSingletonTerminal second) first

def quittingPairHazardDenominator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (first second : ι) : ℝ :=
  tail first - reward (quittingSingletonTerminal first) first +
    quittingPairJoiningGap reward first second

/-- The cleared full endpoint gap at the unique possible interior pair hazards. -/
def quittingPairInactiveGapNumerator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second who : ι) (tail : Payoff ι) : ℝ :=
  let firstGap := quittingPairJoiningGap reward first second
  let secondGap := quittingPairJoiningGap reward second first
  let firstExcess := tail first - reward (quittingSingletonTerminal first) first
  let secondExcess := tail second - reward (quittingSingletonTerminal second) second
  firstGap * secondGap * (reward (quittingSingletonTerminal who) who - tail who) +
    firstGap * secondExcess *
      (reward ⟨{who, first}, by simp⟩ who - reward (quittingSingletonTerminal first) who) +
    secondGap * firstExcess *
      (reward ⟨{who, second}, by simp⟩ who - reward (quittingSingletonTerminal second) who) +
    firstExcess * secondExcess *
      (reward ⟨{who, first, second}, by simp⟩ who - reward ⟨{first, second}, by simp⟩ who)

omit [Fintype ι] in
theorem quittingPairHazardDenominator_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι)
    (tail : Payoff ι) (rate : ℝ) :
    quittingPairHazardDenominator reward
      (Function.update tail first (tail first + rate)) first second =
        quittingPairHazardDenominator reward tail first second + 1 * rate := by
  simp only [quittingPairHazardDenominator, Function.update_self]
  ring

omit [Fintype ι] in
theorem continuous_quittingPairHazardDenominator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    Continuous (fun tail => quittingPairHazardDenominator reward tail first second) := by
  unfold quittingPairHazardDenominator
  fun_prop

omit [Fintype ι] in
theorem dense_quittingPairHazardDenominator_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second : ι) :
    Dense {tail | quittingPairHazardDenominator reward tail first second ≠ 0} :=
  Math.Topology.dense_nonzero_of_coordinate_affine _ first 1 one_ne_zero
    (quittingPairHazardDenominator_update reward first second)

/-- Denominator clearing uses the existing literal four-atom PMF endpoints.
The laws may have zero or sure hazards; only the displayed denominators must
be nonzero. -/
theorem quittingPairInactiveGapNumerator_eq_mul_endpointDifference
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second who : ι} (hne : first ≠ second)
    (hfirst : who ≠ first) (hsecond : who ≠ second)
    (firstLaw secondLaw : PMF Bool)
    (hfirstDen : quittingPairHazardDenominator reward tail first second ≠ 0)
    (hsecondDen : quittingPairHazardDenominator reward tail second first ≠ 0)
    (hfirstLaw : (firstLaw true).toReal =
      (tail second - reward (quittingSingletonTerminal second) second) /
        quittingPairHazardDenominator reward tail second first)
    (hsecondLaw : (secondLaw true).toReal =
      (tail first - reward (quittingSingletonTerminal first) first) /
        quittingPairHazardDenominator reward tail first second) :
    quittingPairInactiveGapNumerator reward first second who tail =
      quittingPairHazardDenominator reward tail first second *
        quittingPairHazardDenominator reward tail second first *
        quittingRootEndpointDifference reward tail
          (PairedCycle.root first second firstLaw secondLaw) who := by
  unfold quittingRootEndpointDifference
  rw [PairedCycle.rootQuit_eq_bellman reward tail hne,
    PairedCycle.rootContinue_outside reward tail hne hfirst hsecond, hfirstLaw, hsecondLaw]
  dsimp only [quittingPairInactiveGapNumerator, quittingPairHazardDenominator,
    quittingPairJoiningGap, Math.PairedAffine.bellman, Math.PairedAffine.contribution] at *
  field_simp; ring

/-- The same identity addresses the full ambient endpoint polynomial, not
a restricted active-face derivative. -/
theorem quittingPairInactiveGapNumerator_eq_mul_realHazardEndpointGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second who : ι} (hne : first ≠ second)
    (hfirst : who ≠ first) (hsecond : who ≠ second)
    (firstLaw secondLaw : PMF Bool)
    (hfirstDen : quittingPairHazardDenominator reward tail first second ≠ 0)
    (hsecondDen : quittingPairHazardDenominator reward tail second first ≠ 0)
    (hfirstLaw : (firstLaw true).toReal =
      (tail second - reward (quittingSingletonTerminal second) second) /
        quittingPairHazardDenominator reward tail second first)
    (hsecondLaw : (secondLaw true).toReal =
      (tail first - reward (quittingSingletonTerminal first) first) /
        quittingPairHazardDenominator reward tail first second) :
    quittingPairInactiveGapNumerator reward first second who tail =
      quittingPairHazardDenominator reward tail first second *
        quittingPairHazardDenominator reward tail second first *
        quittingRealHazardEndpointGap reward tail
          (hazardOfRoot (PairedCycle.root first second firstLaw secondLaw)) who := by
  rw [quittingRealHazardEndpointGap_hazardOfRoot]
  exact quittingPairInactiveGapNumerator_eq_mul_endpointDifference reward tail hne
    hfirst hsecond firstLaw secondLaw hfirstDen hsecondDen hfirstLaw hsecondLaw

omit [Fintype ι] in
theorem quittingPairInactiveGapNumerator_update
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second who : ι} (hfirst : who ≠ first) (hsecond : who ≠ second)
    (tail : Payoff ι) (rate : ℝ) :
    quittingPairInactiveGapNumerator reward first second who
      (Function.update tail who (tail who + rate)) =
        quittingPairInactiveGapNumerator reward first second who tail +
          (-(quittingPairJoiningGap reward first second *
            quittingPairJoiningGap reward second first)) * rate := by
  simp only [quittingPairInactiveGapNumerator, Function.update_self,
    Function.update_of_ne hfirst.symm, Function.update_of_ne hsecond.symm]
  ring

omit [Fintype ι] in
theorem continuous_quittingPairInactiveGapNumerator
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second who : ι) :
    Continuous (quittingPairInactiveGapNumerator reward first second who) := by
  unfold quittingPairInactiveGapNumerator
  fun_prop

omit [Fintype ι] in
theorem isOpen_quittingPairInactiveGapNumerator_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second who : ι) :
    IsOpen {tail | quittingPairInactiveGapNumerator reward first second who tail ≠ 0} :=
  Math.Topology.isOpen_nonzero_of_continuous _
    (continuous_quittingPairInactiveGapNumerator reward first second who)

omit [Fintype ι] in
theorem dense_quittingPairInactiveGapNumerator_ne_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second who : ι} (hfirst : who ≠ first) (hsecond : who ≠ second)
    (hgap : quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first ≠ 0) :
    Dense {tail | quittingPairInactiveGapNumerator reward first second who tail ≠ 0} := by
  apply Math.Topology.dense_nonzero_of_coordinate_affine
    (quittingPairInactiveGapNumerator reward first second who) who
    (-(quittingPairJoiningGap reward first second * quittingPairJoiningGap reward second first))
  · exact neg_ne_zero.mpr hgap
  · exact quittingPairInactiveGapNumerator_update reward hfirst hsecond

omit [Fintype ι] in
/-- A finite list of actual inactive recipients can be made simultaneously
nontied by changing annotations alone. No reward perturbation is involved. -/
theorem dense_iInter_quittingPairInactiveGapNumerator_ne_zero
    {κ : Type*} [Finite κ]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second who : κ → ι)
    (hfirst : ∀ index, who index ≠ first index)
    (hsecond : ∀ index, who index ≠ second index)
    (hgap : ∀ index, quittingPairJoiningGap reward (first index) (second index) *
      quittingPairJoiningGap reward (second index) (first index) ≠ 0) :
    Dense (⋂ index,
      {tail | quittingPairInactiveGapNumerator reward (first index) (second index)
        (who index) tail ≠ 0}) := by
  apply Math.Topology.dense_iInter_nonzero_of_coordinate_affine
    (fun index => quittingPairInactiveGapNumerator reward (first index) (second index)
      (who index)) who
    (fun index => -(quittingPairJoiningGap reward (first index) (second index) *
      quittingPairJoiningGap reward (second index) (first index)))
  · intro index
    exact continuous_quittingPairInactiveGapNumerator reward _ _ _
  · intro index
    exact neg_ne_zero.mpr (hgap index)
  · intro index
    exact quittingPairInactiveGapNumerator_update reward (hfirst index) (hsecond index)

end GameTheory
