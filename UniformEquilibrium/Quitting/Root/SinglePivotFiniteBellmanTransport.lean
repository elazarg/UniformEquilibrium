import UniformEquilibrium.Quitting.Root.SinglePivotNormalization
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! # Finite Bellman transport through single-pivot normalization -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingSinglePivotNormalizedPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (value : Payoff ι) : Payoff ι :=
  fun who => (value who - quittingSinglePivotOffset reward pivot who) /
    reward (quittingSingletonTerminal pivot) pivot

omit [Fintype ι] in
theorem quittingSinglePivotNormalizedPayoff_eq_playerwiseAffine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (value : Payoff ι) :
    quittingSinglePivotNormalizedPayoff reward pivot value =
      quittingPlayerwiseAffinePayoff
        (fun _ => 1 / reward (quittingSingletonTerminal pivot) pivot)
        (fun who => -quittingSinglePivotOffset reward pivot who /
          reward (quittingSingletonTerminal pivot) pivot) value := by
  funext who
  dsimp [quittingSinglePivotNormalizedPayoff, quittingPlayerwiseAffinePayoff]
  ring

/-- Exact finite Bellman steps commute with the raw zero-Never normalization. -/
theorem quittingRootSuccessorPayoff_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (tail : Payoff ι) (root : ι → PMF Bool) :
    quittingRootSuccessorPayoff (quittingSinglePivotNormalizedReward reward pivot)
        (quittingSinglePivotNormalizedPayoff reward pivot tail) root =
      quittingSinglePivotNormalizedPayoff reward pivot
        (quittingRootSuccessorPayoff reward tail root) := by
  rw [quittingSinglePivotNormalizedReward_eq_playerwiseAffine,
    quittingSinglePivotNormalizedPayoff_eq_playerwiseAffine]
  funext who
  rw [quittingRootSuccessorPayoff_playerwiseAffine]
  simp [quittingSinglePivotNormalizedPayoff]
  ring

/-- Every forced root endpoint difference scales by the reciprocal pivot singleton. -/
theorem quittingRootEndpointDifference_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootEndpointDifference (quittingSinglePivotNormalizedReward reward pivot)
        (quittingSinglePivotNormalizedPayoff reward pivot tail) root who =
      quittingRootEndpointDifference reward tail root who /
        reward (quittingSingletonTerminal pivot) pivot := by
  rw [quittingSinglePivotNormalizedReward_eq_playerwiseAffine,
    quittingSinglePivotNormalizedPayoff_eq_playerwiseAffine,
    quittingRootEndpointDifference_playerwiseAffine]
  ring

theorem isQuittingRootSupportApproxNash_singlePivotNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (error : ℝ)
    (hpivot : 0 < reward (quittingSingletonTerminal pivot) pivot)
    (hsupport : IsQuittingRootSupportApproxNash reward tail error root) :
    IsQuittingRootSupportApproxNash (quittingSinglePivotNormalizedReward reward pivot)
      (quittingSinglePivotNormalizedPayoff reward pivot tail)
      (error / reward (quittingSingletonTerminal pivot) pivot) root := by
  intro who
  obtain ⟨hquit, hcontinue⟩ := hsupport who
  constructor
  · intro hplayed
    rw [quittingRootEndpointDifference_singlePivotNormalized]
    rw [← neg_div]
    exact (div_le_div_iff_of_pos_right hpivot).2 (hquit hplayed)
  · intro hplayed
    rw [quittingRootEndpointDifference_singlePivotNormalized]
    exact (div_le_div_iff_of_pos_right hpivot).2 (hcontinue hplayed)

def quittingSinglePivotNormalizedCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    (carrier : Set (Payoff ι)) : Set (Payoff ι) :=
  quittingSinglePivotNormalizedPayoff reward pivot '' carrier

omit [Fintype ι] in
theorem isCompact_quittingSinglePivotNormalizedCarrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (pivot : ι)
    {carrier : Set (Payoff ι)} (hcarrier : IsCompact carrier) :
    IsCompact (quittingSinglePivotNormalizedCarrier reward pivot carrier) := by
  apply hcarrier.image
  unfold quittingSinglePivotNormalizedPayoff
  fun_prop

end GameTheory
