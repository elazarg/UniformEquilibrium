import UniformEquilibrium.Quitting.Projective.CompactSingletonSublevelMinimum
import UniformEquilibrium.Quitting.Projective.SingletonSublevelDownwardCharge
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift

/-! # Chosen singleton-sublevel roots exclude full exact-root potentials

The selected-return hypothesis is conditional source data, not a proof of any
raw signed-pair, boxed-charge, or mixed-trap criterion. The same full boxed
sublevel domain is minimized and receives the chosen downward-path successors.
No assertion about all exact roots at its minimum is made.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingBoxedSingletonSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Set (Payoff ι) :=
  Icc (fun _ => -bound) (fun _ => bound) ∩
    {point | ∃ player, point player ≤ quittingSoloReward reward player player}

/-- At every boxed source strictly below some own singleton, choose one exact
root with some successor singleton sublevel. No continuous selector is required. -/
def HasBoxedSelectedSingletonSublevelReturn
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) : Prop :=
  ∀ tail : Payoff ι, (∀ player, |tail player| ≤ bound) →
    (∃ player, tail player < quittingSoloReward reward player player) →
      ∃ root, IsεQuittingRootNash reward tail 0 root ∧
        ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
          quittingSoloReward reward player player

omit [DecidableEq ι] in
theorem isCompact_quittingBoxedSingletonSublevelDomain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (bound : ℝ) :
    IsCompact (quittingBoxedSingletonSublevelDomain reward bound) := by
  have hclosed := isClosed_iUnion_of_finite fun player : ι =>
    isClosed_le (continuous_apply player)
      (continuous_const (y := quittingSoloReward reward player player))
  have hset : {point : Payoff ι | ∃ player,
      point player ≤ quittingSoloReward reward player player} =
      ⋃ player : ι, {point : Payoff ι |
        point player ≤ quittingSoloReward reward player player} := by
    ext point
    simp
  rw [← hset] at hclosed
  exact isCompact_Icc.inter_right hclosed

/-- Signed arbitrary-finite analytic scope, with continuity only on the
minimized domain and ambient differentiability only on the singleton boundary. -/
theorem not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound)
    (hreturn : HasBoxedSelectedSingletonSublevelReturn reward bound)
    (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential (quittingBoxedSingletonSublevelDomain reward bound))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  let lower : Payoff ι := fun player => quittingSoloReward reward player player
  let upper : Payoff ι := fun _ => bound
  let region := quittingBoxedSingletonSublevelDomain reward bound
  have hboundary : Math.lowerBoxBoundary lower upper ⊆ region := by
    intro point hpoint
    refine ⟨⟨fun player => ?_, hpoint.1.2⟩, ?_⟩
    · exact (abs_le.mp ((hreward (quittingSingletonTerminal player) player).trans
        hbound.le)).1.trans (hpoint.1.1 player)
    · obtain ⟨player, hplayer⟩ := hpoint.2
      exact ⟨player, hplayer.le⟩
  have hchosen : ∀ tail, (∀ player, |tail player| ≤ bound) →
      (∃ player, tail player < lower player) →
        ∃ root, IsεQuittingRootNash reward tail 0 root ∧
          quittingRootSuccessorPayoff reward tail root ∈ region := by
    intro tail hbox hbelow
    obtain ⟨root, hnash, hlow⟩ := hreturn tail hbox hbelow
    refine ⟨root, hnash, ⟨⟨fun player => ?_, fun player => ?_⟩, hlow⟩⟩
    · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound reward tail root player
        (fun terminal who => (hreward terminal who).trans hbound.le) hbox)).1
    · exact (abs_le.mp (abs_quittingRootSuccessorPayoff_le_bound reward tail root player
        (fun terminal who => (hreward terminal who).trans hbound.le) hbox)).2
  obtain ⟨point, hpoint, _hpointRegion, hminRegion⟩ :=
    hpotential.exists_lowerBoundary_minimum_of_selectedSublevelReturn hreward hbound region
      (isCompact_quittingBoxedSingletonSublevelDomain reward bound) hboundary
      (fun point hpoint player => abs_le.mpr ⟨hpoint.1.1 player, hpoint.1.2 player⟩)
      (fun _ hpoint => hpoint.2) (fun point hpoint hbelow => by
        obtain ⟨root, hnash, hregion⟩ := hchosen point
          (fun player => abs_le.mpr ⟨hpoint.1.1 player, hpoint.1.2 player⟩) hbelow
        exact ⟨root, hnash, fun _ => hregion⟩) hcontinuous
  have hmin : IsMinOn potential (Math.lowerBoxBoundary lower upper) point :=
    fun other hother => hminRegion (hboundary hother)
  let derivative := fderiv ℝ potential point
  have hderivative : HasFDerivAt potential derivative point :=
    (hdiff point hpoint).hasFDerivAt
  have hwidth : ∀ player, lower player < upper player := fun player =>
    ((le_abs_self _).trans (hreward (quittingSingletonTerminal player) player)).trans_lt hbound
  have hfaceUpper : ∀ owner player, quittingSoloReward reward owner player ≤ upper player :=
    fun owner player => (le_abs_self _).trans
      ((hreward (quittingSingletonTerminal owner) player).trans hbound.le)
  have hdrift : ∀ owner, point owner = lower owner →
      0 < derivative (point - quittingSoloReward reward owner) := by
    intro owner howner
    exact (show (0 : ℝ) < 1 by norm_num).trans_le
      (hpotential.singletonFace_drift hreward hbound point owner
        (fun player => ⟨hpoint.1.1 player, hpoint.1.2 player⟩)
        howner derivative hderivative)
  obtain ⟨player, hbind, hpartial⟩ := Math.lowerBoxBoundary_minimum_pos_lower_partial
    lower upper point potential derivative (quittingSoloReward reward) hpoint hmin
    hderivative hwidth (fun _ => rfl) hfaceUpper hdrift
  apply not_isQuittingFullExactRootPotential_of_lowerBinding_selectedDownwardReturn
    hreward hbound region point hpoint player hbind potential derivative hminRegion
    hderivative hpartial.le _ hpotential
  intro rate hrate hbox
  have hbelow : ∃ who,
      (point + rate • (-Pi.single player (1 : ℝ)) : Payoff ι) who < lower who := by
    refine ⟨player, ?_⟩
    change point player + rate * (-Pi.single player (1 : ℝ) : Payoff ι) player < lower player
    simp only [Pi.neg_apply, Pi.single_eq_same]
    rw [hbind]
    linarith
  obtain ⟨root, hnash, hregion⟩ := hchosen _ hbox hbelow
  exact ⟨root, hnash, fun _ => hregion⟩

end GameTheory
