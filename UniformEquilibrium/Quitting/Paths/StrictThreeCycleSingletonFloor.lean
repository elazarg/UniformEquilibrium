import UniformEquilibrium.Quitting.Paths.NormalizedSingletonPath

/-!
# Actual singleton floors on strict three-cycle paths

The child path is constructed from actual terminal continuation values.
Absorption, child floors and active-owner ties force every normalized vertex
to be visited after every starting date. Consequently a parent coordinate
stays above its own singleton payoff on a whole tail exactly when its actual
inverse-row coefficients are nonnegative. The player need not be outside
the child. No periodicity, supplied vertex visits, or continuation law is
assumed.
-/

noncomputable section

namespace GameTheory

open Math.LinearProgramming Math.LinearProgramming.ThreeCycleInverseFormulas
open QuittingLCPClassification

variable {ι : Type} [Fintype ι]

/-- For an actual absorbing strict-cycle singleton path, the floor of any
parent player on any whole tail is equivalent to nonnegativity of the
corresponding row times the actual child singleton-matrix inverse. -/
theorem quittingRootSequence_singletonFloor_on_tail_iff_inverseRow_nonneg_of_strictThreeCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (child : Fin 3 ↪ ι) (owner : ℕ → Fin 3)
    (a b c d e f : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hgap : 0 < cycleGap a b c d e f)
    (hmatrix : (quittingSingletonMatrix reward).submatrix child child =
      directedCycleMatrix a b c d e f)
    (hsolo : ∀ time other, other ≠ child (owner time) →
      roots time other = PMF.pure false)
    (hquit : ∀ time, (roots time (child (owner time)) true).toReal < 1)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    (hfloor : ∀ time i, quittingSoloReward reward (child i) (child i) ≤
      quittingRootSequenceTerminalValue reward roots (child i) time)
    (htie : ∀ time, 0 < (roots time (child (owner time)) true).toReal →
      quittingRootSequenceTerminalValue reward roots (child (owner time)) time =
        quittingSoloReward reward (child (owner time)) (child (owner time)))
    (who : ι) (start : ℕ) :
    (∀ time, start ≤ time → quittingSoloReward reward who who ≤
      quittingRootSequenceTerminalValue reward roots who time) ↔
      ∀ j, 0 ≤ Matrix.vecMul
        (fun i => quittingSingletonMatrix reward who (child i))
        ((quittingSingletonMatrix reward).submatrix child child)⁻¹ j := by
  let weight := columnWeight a b c d e f
  have hweight : ∀ i, 0 < weight i :=
    columnWeight_pos ha hb hc hd he hf hgap
  have hbalance : Matrix.vecMul weight
      ((quittingSingletonMatrix reward).submatrix child child) = 1 := by
    rw [hmatrix]
    exact columnWeight_vecMul a b c d e f hgap.ne'
  have hdet : ((quittingSingletonMatrix reward).submatrix child child).det ≠ 0 := by
    rw [hmatrix, directedCycleMatrix_det]
    exact hgap.ne'
  let path := normalizedSingletonPathOfRootSequence
    reward roots child owner hsolo hquit habsorb weight hweight hbalance hfloor htie
  let coefficient := Matrix.vecMul
    (fun i => quittingSingletonMatrix reward who (child i))
    ((quittingSingletonMatrix reward).submatrix child child)⁻¹
  have hcriterion := dotProduct_nonneg_on_tail_iff (weight := weight) ha hb hc hd he hf
  rw [← hmatrix] at hcriterion
  have hiff := hcriterion path coefficient start
  have hvalue (time : ℕ) : dotProduct coefficient (path.value time) =
      quittingRootSequenceSingletonSurplus reward roots time who := by
    exact (quittingRootSequenceSingletonSurplus_eq_inverseRow
      reward roots child owner hsolo hquit habsorb hdet who time).symm
  change (∀ time, start ≤ time → quittingSoloReward reward who who ≤
    quittingRootSequenceTerminalValue reward roots who time) ↔ ∀ j, 0 ≤ coefficient j
  constructor
  · intro hparent
    apply hiff.mp
    intro time htime
    rw [hvalue]
    exact sub_nonneg.mpr (hparent time htime)
  · intro hcoefficient time htime
    have hnonneg := hiff.mpr hcoefficient time htime
    rw [hvalue] at hnonneg
    exact sub_nonneg.mp hnonneg

end GameTheory
