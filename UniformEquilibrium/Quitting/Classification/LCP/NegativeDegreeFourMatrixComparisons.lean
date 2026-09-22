import MathUE.LinearProgramming.Examples.NegativeDegreeFourMatrix
import UniformEquilibrium.Quitting.Classification.LCP.ElementaryMatrixObstructions
import UniformEquilibrium.Quitting.Cycles.PairedCycleSchedule
import UniformEquilibrium.Quitting.Cycles.SignedFourCycleRewardAdapter
import UniformEquilibrium.Quitting.Root.PlayerwiseAffineReward

/-!
# Named matrix-class comparisons for the negative-degree example

The `{0,3}` principal is the existing negative-pair obstruction to projective
Q. Thus the full standard-Q matrix is not projective Q-bar. Every recipient
has a negative singleton gap, so the full normal core is retained.

The negative graph excludes the literal signed-four-cycle singleton input,
including all coordinate reorderings and positive row/column rescalings.
Two negative entries in one row also exclude the literal paired raw region,
including positive playerwise affine transforms of any table with this matrix.
These conclusions do not exclude arbitrary singleton calendars or other
reward-dependent equilibrium constructions.
-/

noncomputable section

namespace GameTheory

open _root_.Math.LinearProgramming QuittingLCPClassification

namespace NegativeDegreeFourMatrixComparisons

open _root_.Math.LinearProgramming.NegativeDegreeFourMatrix

def cornerPair : Finset (Fin 4) := {0, 3}

def cornerPairEquiv : Fin 2 ≃ cornerPair where
  toFun who := if who = 0 then ⟨0, by decide⟩ else ⟨3, by decide⟩
  invFun who := if who.1 = 0 then 0 else 1
  left_inv who := by fin_cases who <;> rfl
  right_inv who := by
    apply Subtype.ext
    have hwho : who.1 = 0 ∨ who.1 = 3 := by
      simpa only [cornerPair, Finset.mem_insert, Finset.mem_singleton] using who.2
    rcases hwho with hwho | hwho <;> simp [hwho]

/-- The literal corner principal is the canonical negative-pair matrix. -/
theorem reindex_cornerPair :
    reindexMatrix cornerPairEquiv.symm (principalMatrix matrix cornerPair) =
      negativePairMatrix 1 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [reindexMatrix, principalMatrix, cornerPairEquiv, matrix, negativePairMatrix]

theorem cornerPrincipal_not_projectiveQ :
    ¬IsProjectiveQMatrix (principalMatrix matrix cornerPair) := by
  intro hprincipal
  have hpair := (isProjectiveQMatrix_reindexMatrix_iff
    cornerPairEquiv.symm (principalMatrix matrix cornerPair)).mpr hprincipal
  rw [reindex_cornerPair] at hpair
  exact negativePairMatrix_not_projectiveQ 1 1 (by norm_num) (by norm_num) hpair

theorem cornerPrincipal_noHomogeneous :
    ¬HasHomogeneousSimplexSolution (principalMatrix matrix cornerPair) := by
  intro hhomogeneous
  exact cornerPrincipal_not_projectiveQ
    ((isProjectiveQMatrix_iff_standard_or_homogeneous _).mpr (Or.inr hhomogeneous))

/-- A standard-Q full matrix need not be projective Q on every principal. -/
theorem not_projectiveQBar : ¬IsProjectiveQBarMatrix matrix := by
  intro hQbar
  exact cornerPrincipal_not_projectiveQ (hQbar cornerPair (by simp [cornerPair]))

/-- Iterated normal-core deletion removes no coordinate of this matrix. -/
theorem normalCore_eq_univ : normalCore matrix = Finset.univ := by
  classical
  apply normalCore_eq_univ_of_fixed_blocker matrix
    (fun who => (negative_rows who).choose)
  · intro who
    exact (negative_rows who).choose_spec.1
  · intro who
    exact (negative_rows who).choose_spec.2.le

/-- No positive row/column rescaling and relabeling of the example can supply
the literal signed-four-cycle singleton data. -/
theorem not_nonempty_signedFourCycleSingletonData_of_positive_scaled_reindex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (order : Equiv.Perm (Fin 4)) (left right : Fin 4 → ℝ)
    (hleft : ∀ who, 0 < left who) (hright : ∀ who, 0 < right who)
    (hmatrix : ∀ row column, quittingSingletonMatrix reward row column =
      left row * matrix (order row) (order column) * right column) :
    ¬Nonempty (SignedFourCycleSingletonData reward) := by
  rintro ⟨data⟩
  apply not_negative_hamiltonianCycle_of_positive_scaling order left right hleft hright
  intro who
  rw [← hmatrix, data.successor]
  exact neg_neg_of_pos (data.b_pos who)

theorem not_nonempty_signedFourCycleSingletonData
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = matrix) :
    ¬Nonempty (SignedFourCycleSingletonData reward) := by
  apply not_nonempty_signedFourCycleSingletonData_of_positive_scaled_reindex
    reward (Equiv.refl _) (fun _ => 1) (fun _ => 1)
    (by intro _; norm_num) (by intro _; norm_num)
  intro row column
  simp only [hmatrix, Equiv.refl_apply, one_mul, mul_one]

/-- Two distinct negative singleton gaps in one row cannot both be the unique
partner gap required by a paired raw region, regardless of the ordering or scales. -/
theorem not_pairedRawRegion_of_positive_scaled_reindex
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (order : Equiv.Perm (Fin 4)) (left right : Fin 4 → ℝ)
    (hleft : ∀ who, 0 < left who) (hright : ∀ who, 0 < right who)
    (hmatrix : ∀ row column, quittingSingletonMatrix reward row column =
      left row * matrix (order row) (order column) * right column)
    {period : ℕ} (schedule : PairedCycle.Schedule (Fin 4) period) :
    ¬PairedCycle.RawRegion reward schedule := by
  intro hregion
  have hpartner (quitter : Fin 4) (hentry : matrix 0 (order quitter) < 0) :
      quitter = schedule.partner (order.symm 0) := by
    have hnegative : quittingSingletonMatrix reward (order.symm 0) quitter < 0 := by
      rw [hmatrix, order.apply_symm_apply]
      exact mul_neg_of_neg_of_pos
        (mul_neg_of_pos_of_neg (hleft (order.symm 0)) hentry) (hright quitter)
    change reward (quittingSingletonTerminal quitter) (order.symm 0) -
      PairedCycle.singleton reward (order.symm 0) < 0 at hnegative
    exact hregion.eq_partner_of_singleton_lt (sub_neg.mp hnegative)
  have htwo := hpartner (order.symm 2) (by
    rw [order.apply_symm_apply]
    norm_num [matrix])
  have hthree := hpartner (order.symm 3) (by
    rw [order.apply_symm_apply]
    norm_num [matrix])
  have hequal : (2 : Fin 4) = 3 := order.symm.injective (htwo.trans hthree.symm)
  norm_num at hequal

/-- The literal raw singleton-matrix cylinder is disjoint from every paired raw region. -/
theorem not_pairedRawRegion
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = matrix)
    {period : ℕ} (schedule : PairedCycle.Schedule (Fin 4) period) :
    ¬PairedCycle.RawRegion reward schedule := by
  apply not_pairedRawRegion_of_positive_scaled_reindex reward (Equiv.refl _)
    (fun _ => 1) (fun _ => 1) (by intro _; norm_num) (by intro _; norm_num) _ schedule
  intro row column
  simp only [hmatrix, Equiv.refl_apply, one_mul, mul_one]

/-- Positive playerwise affine reward changes preserve the singleton-gap
obstruction. This is not an assertion of strategic affine invariance. -/
theorem not_pairedRawRegion_playerwiseAffine
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hmatrix : quittingSingletonMatrix reward = matrix)
    (scale shift : Payoff (Fin 4)) (hscale : ∀ who, 0 < scale who)
    {period : ℕ} (schedule : PairedCycle.Schedule (Fin 4) period) :
    ¬PairedCycle.RawRegion (quittingPlayerwiseAffineReward reward scale shift) schedule := by
  apply not_pairedRawRegion_of_positive_scaled_reindex
    (quittingPlayerwiseAffineReward reward scale shift) (Equiv.refl _)
    scale (fun _ => 1) hscale (by intro _; norm_num) _ schedule
  intro row column
  have hentry := congrFun (congrFun hmatrix row) column
  change reward (quittingSingletonTerminal column) row -
    reward (quittingSingletonTerminal row) row = matrix row column at hentry
  change scale row * reward (quittingSingletonTerminal column) row + shift row -
      (scale row * reward (quittingSingletonTerminal row) row + shift row) =
    scale row * matrix row column * 1
  rw [← hentry]
  ring

end NegativeDegreeFourMatrixComparisons

end GameTheory
