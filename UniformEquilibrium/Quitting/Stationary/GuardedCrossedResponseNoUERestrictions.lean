import UniformEquilibrium.Quitting.Classification.PlayerReindex
import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardReindex
import UniformEquilibrium.Quitting.Stationary.OneSidedWeakUnitProducer
import UniformEquilibrium.Quitting.Stationary.GuardedCrossedResponseWeakBoundaryProducer

/-!
# Necessary all-pair raw restrictions for a hypothetical no-UE game

These are contrapositives of actual source producers. No assertion that every
table has a passing pair is made. Reindexing transports a fixed uniform target
back to the original game, with its full behavioral quantifiers unchanged.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.LinearProgramming

/-- No matrix condition is needed for failure of every ordered-pair one-sided test. -/
theorem not_oneSidedWeakUnitRawGuards_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnoUE : ¬∃ value : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none value)
    (owner passive : Fin 4) (hdistinct : owner ≠ passive) :
    ¬QuittingOneSidedWeakUnitRawGuards reward owner passive := by
  intro hraw
  exact hnoUE (exists_uniformPayoff_of_oneSidedWeakUnitRawGuards
    reward owner passive hdistinct hraw)

/-- The same necessary restriction holds after every relabeling and for every pair. -/
theorem not_oneSidedWeakUnitRawGuards_reindex_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnoUE : ¬∃ value : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none value)
    (e : Equiv.Perm (Fin 4)) (owner passive : Fin 4) (hdistinct : owner ≠ passive) :
    ¬QuittingOneSidedWeakUnitRawGuards (quittingRewardReindex e reward) owner passive := by
  intro hraw
  apply hnoUE
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex e reward
    (exists_uniformPayoff_of_oneSidedWeakUnitRawGuards
      (quittingRewardReindex e reward) owner passive hdistinct hraw)

/-- In the original positive-determinant/nonnegative-inverse matrix region,
every relabeled half-ceiling raw test must fail for a hypothetical no-UE game. -/
theorem not_halfWeakRawGuards_reindex_of_no_uniformPayoff
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hdet : 0 < (quittingSingletonMatrix reward).det)
    (hinverse : ∀ row column, 0 ≤ (quittingSingletonMatrix reward)⁻¹ row column)
    (hnoUE : ¬∃ value : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none value)
    (e : Equiv.Perm (Fin 4)) :
    ¬QuittingHalfWeakRawGuards (quittingRewardReindex e reward) := by
  intro hraw
  have hdet' : 0 < (quittingSingletonMatrix (quittingRewardReindex e reward)).det := by
    rw [quittingSingletonMatrix_rewardReindex, Matrix.det_reindex_self]
    exact hdet
  have hinverse' : ∀ row column,
      0 ≤ (quittingSingletonMatrix (quittingRewardReindex e reward))⁻¹ row column := by
    intro row column
    rw [quittingSingletonMatrix_rewardReindex, Matrix.inv_reindex]
    exact hinverse (e.symm row) (e.symm column)
  exact hnoUE (quittingGame_exists_uniformEquilibriumPayoff_of_reindex e reward
    (exists_uniformEquilibriumPayoff_of_weakHalfRaw
      (quittingRewardReindex e reward) hdet' hinverse' hraw))

/-- The general guarded R0 source test forces index one in any hypothetical no-UE game.
No positive-inverse condition or unswapped R0 hypothesis is substituted for crossed R0. -/
theorem quittingCrossed_degree_eq_one_of_no_uniformPayoff {n : ℕ}
    (reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n))
    (first second : Fin n) (hdistinct : first ≠ second)
    (height : ℝ) (hheight : 0 < height) (hheightOne : height ≤ 1)
    (hguard : QuittingCrossedSourceGuards reward first second height)
    (hfirst : 0 < quittingSingletonMatrix reward first second)
    (hsecond : 0 < quittingSingletonMatrix reward second first)
    (hR0 : IsR0Matrix (quittingCrossedSingletonMatrix reward first second))
    (hnoUE : ¬∃ value : Payoff (Fin n),
      (quittingGame reward).IsUniformEquilibriumPayoff none value) :
    r0Degree (quittingCrossedSingletonMatrix reward first second) hR0 = 1 := by
  by_contra hdegree
  obtain ⟨_, value, _, _, _, _, _, _, _, _, hUE⟩ :=
    exists_guardedCrossed_stationaryTerminalNash_uniformPayoff_of_sourceGuards
      reward first second hdistinct height hheight hheightOne hguard hfirst hsecond
      hR0 hdegree
  exact hnoUE ⟨value, hUE⟩

end GameTheory
