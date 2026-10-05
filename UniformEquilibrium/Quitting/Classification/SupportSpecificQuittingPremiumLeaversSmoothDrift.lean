import UniformEquilibrium.Quitting.Classification.SupportSpecificQuittingPremiumLeavers
import UniformEquilibrium.Quitting.Projective.ConvexReturnDomainSmoothDrift

/-! # Signed support-specific leavers produce a convex return domain

The raw criterion supplies successor protected floors at all boxed sources,
and singleton-sublevel return only at sources in the protected region. The
analytic proof is the canonical convex-return theorem, not a root selector.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem isClosed_quittingProtectedSetBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (protectedPlayers : Finset ι) :
    IsClosed (quittingProtectedSetBox reward bound protectedPlayers) := by
  apply isClosed_Icc.inter
  have hclosed : IsClosed (⋂ player : {player // player ∈ protectedPlayers},
      {point : Payoff ι | quittingSoloReward reward player.val player.val ≤ point player.val}) :=
    isClosed_iInter fun player =>
      isClosed_le (continuous_const (y := quittingSoloReward reward player.val player.val))
        (continuous_apply player.val)
  have hset : {point : Payoff ι | ∀ player ∈ protectedPlayers,
      quittingSoloReward reward player player ≤ point player} =
      ⋂ player : {player // player ∈ protectedPlayers},
        {point : Payoff ι |
          quittingSoloReward reward player.val player.val ≤ point player.val} := by
    ext point
    simp
  rw [← hset] at hclosed
  exact hclosed

omit [Fintype ι] [DecidableEq ι] in
theorem convex_quittingProtectedSetBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (protectedPlayers : Finset ι) :
    Convex ℝ (quittingProtectedSetBox reward bound protectedPlayers) := by
  intro first hfirst last hlast a b ha hb hab
  refine ⟨(convex_Icc (fun _ : ι => -bound) (fun _ => bound))
    hfirst.1 hlast.1 ha hb hab, ?_⟩
  intro player hplayer
  change quittingSoloReward reward player player ≤ a * first player + b * last player
  calc
    quittingSoloReward reward player player =
        a * quittingSoloReward reward player player +
          b * quittingSoloReward reward player player := by
      rw [← add_mul, hab, one_mul]
    _ ≤ a * first player + b * last player := add_le_add
      (mul_le_mul_of_nonneg_left (hfirst.2 player hplayer) ha)
      (mul_le_mul_of_nonneg_left (hlast.2 player hplayer) hb)

/-- Signed singleton levels and signed unprotected participant premiums are
allowed. An empty protected set is also allowed: its leaver premise forces
trap-freeness. The analytic finite player type is nonempty. -/
theorem not_isQuittingFullExactRootPotential_of_supportSpecific_strictLeave
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (protectedPlayers : Finset ι)
    (hpremiums : HasProtectedParticipantPremiums reward protectedPlayers)
    (hleavers : HasSupportSpecificQuittingLeavers reward protectedPlayers (· < ·))
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential
      (quittingProtectedSetSublevelDomain reward bound protectedPlayers))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_convexReturnDomain hreward hbound
    (quittingProtectedSetBox reward bound protectedPlayers)
    (isClosed_quittingProtectedSetBox reward bound protectedPlayers)
    (convex_quittingProtectedSetBox reward bound protectedPlayers)
  · exact fun _ hpoint => hpoint.1
  · intro point hpoint
    refine ⟨⟨fun player => ?_, hpoint.2⟩, fun player _ => hpoint.1 player⟩
    have hlower := (abs_le.mp
      ((hreward (quittingSingletonTerminal player) player).trans hbound.le)).1
    exact hlower.trans (hpoint.1 player)
  · intro tail hbox root hnash
    exact exactRootSuccessor_mem_protectedSetBox reward protectedPlayers hpremiums bound
      (fun terminal player => (hreward terminal player).trans hbound.le) tail hbox root hnash
  · intro tail htail root hnash hpositive
    exact (exactRootSuccessor_protectedSet_sublevel_of_supportSpecific_strictLeave
      reward protectedPlayers hpremiums hleavers tail htail.2 root hnash hpositive).2
  · exact hcontinuous
  · exact hdiff

end GameTheory
