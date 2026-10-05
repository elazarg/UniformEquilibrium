import MathUE.Analysis.LowerBoxBoundaryMinimum
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction
import UniformEquilibrium.Quitting.Root.BelowSingletonRootAbsorption
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Boundary.Exceptional.TailFallback

/-! # Boundary localization of a compact singleton-sublevel minimum

Only absorbing exact-root return from the compact region is needed. No
participant-premium sign, protected player, or successor-wide singleton floor
is assumed. Zero absorption is concluded at the actual attained minimum only.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem IsQuittingFullExactRootPotential.exists_lowerBoundary_minimum_of_compactSublevelReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (region : Set (Payoff ι)) (hcompact : IsCompact region)
    (hboundary : Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound) ⊆ region)
    (hbox : ∀ point ∈ region, ∀ player, |point player| ≤ bound)
    (hsublevel : ∀ point ∈ region, ∃ player,
      point player ≤ quittingSoloReward reward player player)
    (hreturn : ∀ point ∈ region, ∀ root, IsεQuittingRootNash reward point 0 root →
      0 < quittingRootAbsorptionMass root → quittingRootSuccessorPayoff reward point root ∈ region)
    {potential : Payoff ι → ℝ} (hcontinuous : ContinuousOn potential region)
    (hpotential : IsQuittingFullExactRootPotential reward bound potential) :
    ∃ point, point ∈ Math.lowerBoxBoundary
        (fun player => quittingSoloReward reward player player) (fun _ => bound) ∧
      point ∈ region ∧ IsMinOn potential region point ∧
      ∀ root, IsεQuittingRootNash reward point 0 root → quittingRootAbsorptionMass root = 0 := by
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let player : ι := Classical.choice inferInstance
  have hM : 0 ≤ M := (abs_nonneg _).trans
    (hreward (quittingSingletonTerminal player) player)
  have hwidth : ∀ who, lower who < upper who := fun who =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal who) who)).trans_lt hbound
  obtain ⟨point, hpointRegion, hminRegion⟩ := hcompact.exists_isMinOn
    ((Math.lowerBoxBoundary_nonempty lower upper
      fun who => (hwidth who).le).mono hboundary) hcontinuous
  have hpointBox := hbox point hpointRegion
  have hpointLower : ∀ who, lower who ≤ point who := by
    intro who
    by_contra hnot
    have hgap : 0 < lower who - point who := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) point
    have hmass := belowSingleton_exactRoot_absorptionMass_lowerBound reward point root
      who hgap hreward (by
        change point who ≤ lower who - (lower who - point who)
        linarith) hnash
    have hpositive : 0 < quittingRootAbsorptionMass root :=
      (div_pos hgap (by positivity : 0 < 2 * M + (lower who - point who))).trans_le hmass
    have hminimum := hminRegion (hreturn point hpointRegion root hnash hpositive)
    change potential point ≤ potential (quittingRootSuccessorPayoff reward point root)
      at hminimum
    have hdecrease := hpotential point hpointBox root hnash
    linarith
  have hpoint : point ∈ Math.lowerBoxBoundary lower upper := by
    refine ⟨⟨hpointLower, fun who => (abs_le.mp (hpointBox who)).2⟩, ?_⟩
    obtain ⟨who, hwho⟩ := hsublevel point hpointRegion
    exact ⟨who, le_antisymm hwho (hpointLower who)⟩
  refine ⟨point, hpoint, hpointRegion, hminRegion, ?_⟩
  intro root hnash
  by_contra hzero
  have hpositive : 0 < quittingRootAbsorptionMass root :=
    lt_of_le_of_ne (quittingRootAbsorptionMass_nonneg root) (Ne.symm hzero)
  have hminimum := hminRegion (hreturn point hpointRegion root hnash hpositive)
  change potential point ≤ potential (quittingRootSuccessorPayoff reward point root) at hminimum
  have hdecrease := hpotential point hpointBox root hnash
  linarith

end GameTheory
