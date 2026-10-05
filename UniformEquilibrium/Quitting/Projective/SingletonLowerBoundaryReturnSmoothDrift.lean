import UniformEquilibrium.Quitting.Projective.ProtectedSingletonReturnDomainSmoothDrift

/-! # Boundary-only regularity for singleton lower-boundary return -/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem not_isQuittingFullExactRootPotential_of_singletonLowerBoundaryReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} (protectedPlayer : ι)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (hreturn : ∀ tail, (∀ player, |tail player| ≤ bound) →
      quittingSoloReward reward protectedPlayer protectedPlayer ≤ tail protectedPlayer →
      ∀ root, IsεQuittingRootNash reward tail 0 root →
      0 < quittingRootAbsorptionMass root →
        (∀ player, quittingSoloReward reward player player ≤
          quittingRootSuccessorPayoff reward tail root player) ∧
        ∃ player, quittingRootSuccessorPayoff reward tail root player =
          quittingSoloReward reward player player)
    (potential : Payoff ι → ℝ)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  apply not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain
    protectedPlayer hreward hbound (Math.lowerBoxBoundary lower upper)
    (Math.isCompact_lowerBoxBoundary lower upper) (Subset.rfl)
  · intro point hpoint
    refine ⟨fun player => abs_le.mpr ⟨?_, hpoint.1.2 player⟩, hpoint.1.1 protectedPlayer⟩
    have hsolo := (abs_le.mp
      ((hreward (quittingSingletonTerminal player) player).trans hbound.le)).1
    exact hsolo.trans (hpoint.1.1 player)
  · intro point hpoint
    obtain ⟨player, hplayer⟩ := hpoint.2
    exact ⟨player, hplayer.le⟩
  · intro tail hbox hfloor root hnash hpositive
    obtain ⟨hlower, player, hplayer⟩ := hreturn tail hbox hfloor root hnash hpositive
    refine ⟨⟨hlower, fun coordinate => ?_⟩, player, hplayer⟩
    exact (le_abs_self _).trans
      (abs_quittingRootSuccessorPayoff_le_bound reward tail root coordinate
        (fun terminal who => (hreward terminal who).trans hbound.le) hbox)
  · exact fun point hpoint => (hdiff point hpoint).continuousAt.continuousWithinAt
  · exact hdiff

end GameTheory
