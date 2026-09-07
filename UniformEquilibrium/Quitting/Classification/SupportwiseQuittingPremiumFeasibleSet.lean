import Mathlib.Analysis.Convex.StdSimplex
import UniformEquilibrium.Quitting.Classification.SupportwiseQuittingPremiumBalanceAt

/-! # Compact supportwise premium feasibility sets -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The literal feasible weight set for supportwise balance on one support. -/
def supportwiseQuittingPremiumFeasibleSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) : Set (ι → ℝ) :=
  {weight | IsSupportwiseQuittingPremiumWeightCertificate
    reward active weight}

omit [Fintype ι] [DecidableEq ι] in
theorem hasSupportwiseQuittingPremiumBalanceAt_iff_feasibleSet_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) :
    HasSupportwiseQuittingPremiumBalanceAt reward active ↔
      (supportwiseQuittingPremiumFeasibleSet reward active).Nonempty := by
  rfl

omit [Fintype ι] in
theorem isClosed_supportwiseQuittingPremiumFeasibleSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) :
    IsClosed (supportwiseQuittingPremiumFeasibleSet reward active) := by
  have hnonneg : IsClosed {weight : ι → ℝ |
      ∀ player, 0 ≤ weight player} := by
    rw [show {weight : ι → ℝ | ∀ player, 0 ≤ weight player} =
        ⋂ player, {weight | weight player ∈ Set.Ici (0 : ℝ)} by
      ext weight
      simp]
    exact isClosed_iInter fun player ↦
      isClosed_Ici.preimage (continuous_apply player)
  have hsupport : IsClosed {weight : ι → ℝ |
      ∀ player, player ∉ active → weight player = 0} := by
    rw [show {weight : ι → ℝ |
        ∀ player, player ∉ active → weight player = 0} =
        ⋂ player, {weight | player ∉ active → weight player = 0} by
      ext weight
      simp]
    apply isClosed_iInter
    intro player
    by_cases hplayer : player ∈ active
    · simp only [hplayer, not_true_eq_false, false_implies]
      exact isClosed_univ
    · simp only [hplayer, not_false_eq_true, true_implies]
      exact isClosed_eq (continuous_apply player) continuous_const
  have hsum : IsClosed {weight : ι → ℝ |
      (∑ player ∈ active, weight player) = 1} := by
    apply isClosed_singleton.preimage
    exact continuous_finsetSum active fun player _ ↦ continuous_apply player
  have hpremium : IsClosed {weight : ι → ℝ |
      ∀ terminal : {S : Finset ι // S.Nonempty},
        terminal.val ⊆ active →
        (∑ player ∈ terminal.val, weight player *
          (reward terminal player -
            reward (quittingSingletonTerminal player) player)) ≤ 0} := by
    rw [show {weight : ι → ℝ |
        ∀ terminal : {S : Finset ι // S.Nonempty},
          terminal.val ⊆ active →
          (∑ player ∈ terminal.val, weight player *
            (reward terminal player -
              reward (quittingSingletonTerminal player) player)) ≤ 0} =
        ⋂ terminal, {weight | terminal.val ⊆ active →
          (∑ player ∈ terminal.val, weight player *
            (reward terminal player -
              reward (quittingSingletonTerminal player) player)) ≤ 0} by
      ext weight
      simp]
    apply isClosed_iInter
    intro terminal
    by_cases hsubset : terminal.val ⊆ active
    · simp only [hsubset, true_implies]
      exact isClosed_le
        (continuous_finsetSum terminal.val fun player _ ↦
          (continuous_apply player).mul continuous_const)
        continuous_const
    · simp only [hsubset, false_implies]
      exact isClosed_univ
  change IsClosed (_ ∩ (_ ∩ (_ ∩ _)))
  exact hnonneg.inter (hsupport.inter (hsum.inter hpremium))

/-- The finite supportwise feasible set is a closed subset of the standard
probability simplex, hence compact. -/
theorem isCompact_supportwiseQuittingPremiumFeasibleSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) :
    IsCompact (supportwiseQuittingPremiumFeasibleSet reward active) := by
  apply IsCompact.of_isClosed_subset (isCompact_stdSimplex ℝ ι)
    (isClosed_supportwiseQuittingPremiumFeasibleSet reward active)
  intro weight hweight
  refine ⟨hweight.1, ?_⟩
  calc
    (∑ player, weight player) = ∑ player ∈ active, weight player := by
      symm
      exact Finset.sum_subset (fun _ _ ↦ Finset.mem_univ _)
        (fun player _ houtside ↦ hweight.2.1 player houtside)
    _ = 1 := hweight.2.2.1

end GameTheory
