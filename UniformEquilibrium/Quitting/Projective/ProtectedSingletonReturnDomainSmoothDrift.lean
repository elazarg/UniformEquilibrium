import MathUE.Analysis.LowerBoxBoundaryMinimum
import UniformEquilibrium.Quitting.Projective.CompactSingletonSublevelMinimum
import UniformEquilibrium.Quitting.Projective.SingletonSublevelDownwardCharge
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift

/-! # Smooth exclusion from a compact protectedPlayer singleton return domain -/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A compact return region between the singleton boundary and its protectedPlayer
sublevel domain excludes a full exact-root potential. Continuity is required
only on that region, and differentiation only on the singleton boundary. -/
theorem not_isQuittingFullExactRootPotential_of_protectedSingletonReturnDomain
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (protectedPlayer : ι)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (region : Set (Payoff ι)) (hcompact : IsCompact region)
    (hboundary : Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound) ⊆ region)
    (hregion : ∀ point ∈ region,
      (∀ player, |point player| ≤ bound) ∧
      quittingSoloReward reward protectedPlayer protectedPlayer ≤ point protectedPlayer)
    (hsublevel : ∀ point ∈ region,
      ∃ player, point player ≤ quittingSoloReward reward player player)
    (hreturn : ∀ tail, (∀ player, |tail player| ≤ bound) →
      quittingSoloReward reward protectedPlayer protectedPlayer ≤ tail protectedPlayer →
      ∀ root, IsεQuittingRootNash reward tail 0 root →
      0 < quittingRootAbsorptionMass root →
        quittingRootSuccessorPayoff reward tail root ∈ region)
    (potential : Payoff ι → ℝ) (hcontinuous : ContinuousOn potential region)
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬ IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let : Nonempty ι := ⟨protectedPlayer⟩
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let face : ι → Payoff ι := quittingSoloReward reward
  obtain ⟨point, hpoint, _hpointRegion, hminRegion, _hzero⟩ :=
    hpotential.exists_lowerBoundary_minimum_of_compactSublevelReturn hreward hbound
      region hcompact hboundary (fun point hpoint => (hregion point hpoint).1) hsublevel
      (fun point hpoint root hnash hpositive => hreturn point (hregion point hpoint).1
        (hregion point hpoint).2 root hnash hpositive) hcontinuous
  have hmin : IsMinOn potential (Math.lowerBoxBoundary lower upper) point :=
    fun other hother => hminRegion (hboundary hother)
  let derivative := fderiv ℝ potential point
  have hderivative : HasFDerivAt potential derivative point :=
    (hdiff point hpoint).hasFDerivAt
  have hwidth : ∀ player, lower player < upper player := fun player =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal player) player)).trans_lt
      hbound
  have hfaceUpper : ∀ owner player, face owner player ≤ upper player :=
    fun owner player => (le_abs_self _).trans
      ((hreward (quittingSingletonTerminal owner) player).trans hbound.le)
  have hdrift : ∀ owner, point owner = lower owner →
      0 < derivative (point - face owner) := by
    intro owner howner
    exact (show (0 : ℝ) < 1 by norm_num).trans_le
      (hpotential.singletonFace_drift hreward hbound point owner
        (fun player => ⟨hpoint.1.1 player, hpoint.1.2 player⟩)
        howner derivative hderivative)
  have htwo := Math.lowerBoxBoundary_minimum_has_two_bindings
    lower upper point potential derivative face hpoint hmin hderivative hwidth
    (fun _ => rfl) hfaceUpper hdrift
  obtain ⟨player, hbind, hplayerProtected⟩ := htwo protectedPlayer
  obtain ⟨other, hother, hotherPlayer⟩ := htwo player
  have hpartial : 0 ≤ derivative (Pi.single player 1) :=
    Math.lowerBoxBoundary_minimum_partial_nonneg lower upper point potential
      derivative hpoint hmin hderivative player other hotherPlayer hbind hother
      (hwidth player)
  apply not_isQuittingFullExactRootPotential_of_lowerBinding_downwardReturn
    hreward hbound region point hpoint player hbind potential derivative hminRegion
    hderivative hpartial _ hpotential
  intro rate _hpositive hbox root hnash hpositive
  have hfloor : lower protectedPlayer ≤
      (point + rate • (-Pi.single player (1 : ℝ)) : Payoff ι) protectedPlayer := by
    simpa [Pi.single_eq_of_ne hplayerProtected.symm] using hpoint.1.1 protectedPlayer
  exact hreturn _ hbox hfloor root hnash hpositive
end GameTheory
