import UniformEquilibrium.Quitting.Classification.LCP.QuittingRewardAdapter
import UniformEquilibrium.Quitting.Root.PlayerReindex

/-! # Covariance of the actual singleton comparison matrix -/

noncomputable section

namespace GameTheory.QuittingLCPClassification

/-- The actual singleton matrix is covariant under player relabeling. -/
theorem quittingSingletonMatrix_rewardReindex {ι κ : Type}
    (e : ι ≃ κ) (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingSingletonMatrix (quittingRewardReindex e reward) =
      Matrix.reindex e e (quittingSingletonMatrix reward) := by
  classical
  ext row column
  simp [quittingSingletonMatrix, quittingRewardReindex, quittingCoalitionEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply]

end GameTheory.QuittingLCPClassification
