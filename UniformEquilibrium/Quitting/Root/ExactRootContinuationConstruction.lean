import UniformEquilibrium.Quitting.Root.OpponentCoalitionPayoff
import UniformEquilibrium.Quitting.Root.SuccessorCertificate
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-! # Continuations realizing prescribed roots exactly -/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The pure-Continue endpoint is affine in its own continuation coordinate,
with coefficient equal to the opponents' all-Continue probability. -/
theorem quittingRootContinuePayoff_eq_zero_add_emptyMass_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (player : ι) :
    quittingRootContinuePayoff reward tail root player =
      quittingRootContinuePayoff reward 0 root player +
        quittingOpponentCoalitionMass root player ∅ * tail player := by
  unfold quittingRootContinuePayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  simp only [Pi.zero_apply, mul_zero, add_zero]
  congr 1
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  rw [prod_factor_erase
    (fun _ (coin : PMF Bool) => (coin false).toReal) player
      (Function.update root player (PMF.pure false))]
  simp only [Function.update_self]
  norm_num
  rw [prod_erase_update_eq
    (fun _ (coin : PMF Bool) => (coin false).toReal) player root
      (PMF.pure false)]
  simp [quittingOpponentCoalitionMass]

/-- On a prescribed active support, solve the active indifference equations
coordinatewise. Outsiders use a supplied cap and only need Continue to weakly
dominate Quit there. -/
theorem exactRootNash_of_indifferenceContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (active : Finset ι) (cap : Payoff ι)
    (houtsideZero : ∀ player, player ∉ active →
      (root player true).toReal = 0)
    (hempty : ∀ player, player ∈ active →
      0 < quittingOpponentCoalitionMass root player ∅)
    (houtside : ∀ player, player ∉ active →
      quittingRootQuitPayoff reward 0 root player ≤
        quittingRootContinuePayoff reward cap root player) :
    let tail : Payoff ι := fun player =>
      if player ∈ active then
        (quittingRootQuitPayoff reward 0 root player -
          quittingRootContinuePayoff reward 0 root player) /
            quittingOpponentCoalitionMass root player ∅
      else cap player
    IsεQuittingRootNash reward tail 0 root := by
  dsimp only
  rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
  intro player
  by_cases hmem : player ∈ active
  · have hendpoint : quittingRootEndpointDifference reward
        (fun other => if other ∈ active then
          (quittingRootQuitPayoff reward 0 root other -
            quittingRootContinuePayoff reward 0 root other) /
              quittingOpponentCoalitionMass root other ∅
          else cap other) root player = 0 := by
      unfold quittingRootEndpointDifference
      rw [quittingRootQuitPayoff_continuation_invariant reward _ 0 root player]
      rw [quittingRootContinuePayoff_eq_zero_add_emptyMass_mul]
      simp only [hmem, if_true]
      field_simp [ne_of_gt (hempty player hmem)]
      ring
    rw [hendpoint]
    simp
  · have hquitZero : (root player true).toReal = 0 :=
      houtsideZero player hmem
    have hendpoint : quittingRootEndpointDifference reward
        (fun other => if other ∈ active then
          (quittingRootQuitPayoff reward 0 root other -
            quittingRootContinuePayoff reward 0 root other) /
              quittingOpponentCoalitionMass root other ∅
          else cap other) root player ≤ 0 := by
      unfold quittingRootEndpointDifference
      rw [quittingRootQuitPayoff_continuation_invariant reward _ 0 root player]
      rw [quittingRootContinuePayoff_eq_zero_add_emptyMass_mul,
        quittingRootContinuePayoff_eq_zero_add_emptyMass_mul]
      have hout := sub_nonpos.mpr (houtside player hmem)
      rw [quittingRootContinuePayoff_eq_zero_add_emptyMass_mul] at hout
      simpa [hmem] using hout
    refine ⟨?_, ?_⟩
    · simpa using mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg hendpoint
    · simp [hquitZero]

end GameTheory
