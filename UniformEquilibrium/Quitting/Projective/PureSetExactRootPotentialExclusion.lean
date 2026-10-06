import UniformEquilibrium.Quitting.Root.PureSetRootNashAnnotationInvariance
import UniformEquilibrium.Quitting.Projective.ExactRootPotentialRestriction

/-! # An actual pure sure coalition excludes exact-root charged potentials

Two sure quitters make Nash annotation-independent. Its boxed absorbing
payoff is therefore a literal exact self-loop of absorption one. No analytic
regularity or participant-premium sign is needed for this alternative.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem not_isQuittingFullExactRootPotential_of_pureSetNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (active : Finset ι) (hcard : 2 ≤ active.card)
    (hnash : IsεQuittingRootNash reward tail 0 (quittingPureSetRoot active))
    (bound : ℝ) (hbox : ∀ player, |quittingSetReward reward active player| ≤ bound)
    (potential : Payoff ι → ℝ) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  intro hpotential
  have hnonempty : active.Nonempty := Finset.card_pos.mp (by omega)
  have hfixedNash := isZeroQuittingRootNash_pureSetRoot_at_annotation reward tail
    (quittingSetReward reward active) active hcard hnash
  have hcharge := hpotential (quittingSetReward reward active) hbox
    (quittingPureSetRoot active) hfixedNash
  rw [quittingRootSuccessorPayoff_pureSetRoot_eq_setReward_of_nonempty reward _ hnonempty,
    quittingRootAbsorptionMass_pureSetRoot_of_nonempty hnonempty] at hcharge
  linarith

end GameTheory
