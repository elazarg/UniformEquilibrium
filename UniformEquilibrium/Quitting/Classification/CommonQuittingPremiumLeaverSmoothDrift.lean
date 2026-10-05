import UniformEquilibrium.Quitting.Classification.CommonQuittingPremiumLeaver
import UniformEquilibrium.Quitting.Projective.ProtectedSingletonReturnDomainSmoothDrift

/-! # Signed common-leaver potential exclusion on the protected sublevel domain -/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Boxed annotations protecting one singleton and meeting some singleton
sublevel. Other coordinates need not satisfy their singleton floors. -/
def quittingProtectedSingletonSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (player : ι) : Set (Payoff ι) :=
  Icc (fun _ => -bound) (fun _ => bound) ∩
    {point | quittingSoloReward reward player player ≤ point player ∧
      ∃ other, point other ≤ quittingSoloReward reward other other}

omit [DecidableEq ι] in
theorem isCompact_quittingProtectedSingletonSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) (player : ι) :
    IsCompact (quittingProtectedSingletonSublevelDomain reward bound player) := by
  apply isCompact_Icc.inter_right
  apply IsClosed.inter (isClosed_le continuous_const (continuous_apply player))
  have hclosed := isClosed_iUnion_of_finite fun other : ι =>
    isClosed_le (continuous_apply other)
      (continuous_const (y := quittingSoloReward reward other other))
  have hset : {point : Payoff ι | ∃ other,
      point other ≤ quittingSoloReward reward other other} =
      ⋃ other : ι, {point : Payoff ι |
        point other ≤ quittingSoloReward reward other other} := by
    ext point
    simp
  rw [← hset] at hclosed
  exact hclosed

/-- Signed unprotected premiums are allowed. Continuity is needed only on
the compact protected sublevel domain, and differentiability on the singleton
lower boundary. -/
theorem not_isQuittingFullExactRootPotential_of_commonLeaver_strictLeave
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (player : ι)
    (hcommon : IsCommonQuittingPremiumLeaver reward player)
    (hleave : ∀ (coalition : Finset ι) (hcoalition : coalition.Nonempty),
      coalition ⊆ (quittingPremiumCore reward).erase player →
        reward ⟨insert player coalition, Finset.insert_nonempty _ _⟩ player <
          reward ⟨coalition, hcoalition⟩ player)
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential
      (quittingProtectedSingletonSublevelDomain reward bound player))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun who => quittingSoloReward reward who who) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  apply not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain
    player hreward hbound (quittingProtectedSingletonSublevelDomain reward bound player)
    (isCompact_quittingProtectedSingletonSublevelDomain reward bound player)
  · intro point hpoint
    refine ⟨⟨fun who => ?_, hpoint.1.2⟩, hpoint.1.1 player, ?_⟩
    · have hlower := (abs_le.mp
        ((hreward (quittingSingletonTerminal who) who).trans hbound.le)).1
      exact hlower.trans (hpoint.1.1 who)
    · obtain ⟨who, hwho⟩ := hpoint.2
      exact ⟨who, hwho.le⟩
  · intro point hpoint
    exact ⟨fun who => abs_le.mpr ⟨hpoint.1.1 who, hpoint.1.2 who⟩, hpoint.2.1⟩
  · intro point hpoint
    exact hpoint.2.2
  · intro tail hbox hfloor root hnash hpositive
    obtain ⟨hprotected, hsublevel⟩ :=
      exactRootSuccessor_protected_sublevel_of_commonLeaver_strictLeave
        reward player hcommon hleave tail hfloor root hnash hpositive
    refine ⟨⟨fun who => ?_, fun who => ?_⟩, hprotected, hsublevel⟩
    · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound reward tail root who
        (fun terminal coordinate => (hreward terminal coordinate).trans hbound.le) hbox)).1
    · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound reward tail root who
        (fun terminal coordinate => (hreward terminal coordinate).trans hbound.le) hbox)).2
  · exact hcontinuous
  · exact hdiff

end GameTheory
