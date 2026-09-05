import UniformEquilibrium.Quitting.Root.SinglePivotNormalization
import UniformEquilibrium.Quitting.Classification.LCP.MatrixPositiveScaling

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem quittingProjectiveLCPMatrix_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot) =
      fun who owner => quittingProjectiveLCPMatrix reward who owner /
        reward (quittingSingletonTerminal pivot) pivot := by
  funext who owner
  unfold quittingProjectiveLCPMatrix quittingSinglePivotNormalizedReward
  ring_nf

omit [Fintype ι] in
private theorem singlePivotMatrix_eq_posScale
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι) :
    quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot) =
      fun who owner =>
        (1 / reward (quittingSingletonTerminal pivot) pivot) *
          quittingProjectiveLCPMatrix reward who owner := by
  rw [quittingProjectiveLCPMatrix_singlePivotNormalized]
  funext who owner
  ring_nf

omit [Fintype ι] in
theorem singlePivotNormalized_matrix_sign_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot who owner : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    let normalized := quittingProjectiveLCPMatrix
      (quittingSinglePivotNormalizedReward reward pivot) who owner
    let original := quittingProjectiveLCPMatrix reward who owner
    (normalized < 0 ↔ original < 0) ∧ (normalized = 0 ↔ original = 0) ∧
      (0 < normalized ↔ 0 < original) := by
  rw [singlePivotMatrix_eq_posScale]
  exact matrix_entry_posScale_sign_iff _ (one_div_pos.mpr hpivot) _ who owner

theorem singlePivotNormalized_normalLayer_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) (n : ℕ) :
    normalLayer
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) n =
      normalLayer (quittingProjectiveLCPMatrix reward) n := by
  rw [singlePivotMatrix_eq_posScale]
  exact normalLayer_posScale _ (one_div_pos.mpr hpivot) _ n

theorem singlePivotNormalized_normalCore_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    normalCore
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) =
      normalCore (quittingProjectiveLCPMatrix reward) := by
  rw [singlePivotMatrix_eq_posScale]
  exact normalCore_posScale _ (one_div_pos.mpr hpivot) _

theorem singlePivotNormalized_standardQ_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    IsStandardQMatrix
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) ↔
      IsStandardQMatrix (quittingProjectiveLCPMatrix reward) := by
  rw [singlePivotMatrix_eq_posScale]
  exact isStandardQMatrix_posScale_iff _ (one_div_pos.mpr hpivot) _

theorem singlePivotNormalized_homogeneous_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    HasHomogeneousSimplexSolution
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) ↔
      HasHomogeneousSimplexSolution (quittingProjectiveLCPMatrix reward) := by
  rw [singlePivotMatrix_eq_posScale]
  exact hasHomogeneousSimplexSolution_posScale_iff _ (one_div_pos.mpr hpivot) _

theorem singlePivotNormalized_projectiveQ_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    IsProjectiveQMatrix
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) ↔
      IsProjectiveQMatrix (quittingProjectiveLCPMatrix reward) := by
  rw [singlePivotMatrix_eq_posScale]
  exact isProjectiveQMatrix_posScale_iff _ (one_div_pos.mpr hpivot) _

omit [Fintype ι] in
theorem singlePivotNormalized_projectiveQBar_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot) :
    IsProjectiveQBarMatrix
        (quittingProjectiveLCPMatrix (quittingSinglePivotNormalizedReward reward pivot)) ↔
      IsProjectiveQBarMatrix (quittingProjectiveLCPMatrix reward) := by
  rw [singlePivotMatrix_eq_posScale]
  exact isProjectiveQBarMatrix_posScale_iff _ (one_div_pos.mpr hpivot) _

end QuittingLCPClassification
end GameTheory
