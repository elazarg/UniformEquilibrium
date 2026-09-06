import UniformEquilibrium.Quitting.Root.ForcedContinuePayoffDisplacement
import UniformEquilibrium.Quitting.Root.ImmediateQuitCapDisplacement

/-! # Bellman and outsider endpoint seam for literal nested children -/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal nesting of source profiles and owner-forced children induces both
actual Bellman identities at every date. -/
theorem quittingNestedSourceAndChild_terminalPayoff_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles children : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsourceNested : ∀ depth, profiles (depth + 1) =
      quittingRootThenContinuationProfile reward (roots depth)
        (profiles depth))
    (hchildNested : ∀ depth, children (depth + 1) =
      quittingRootThenContinuationProfile reward
        (Function.update (roots depth) owner (PMF.pure false))
        (children depth)) :
    ∀ depth,
      (fun player => quittingTerminalPayoff reward (profiles (depth + 1)) player) =
          quittingRootSuccessorPayoff reward
            (fun player => quittingTerminalPayoff reward (profiles depth) player)
            (roots depth) ∧
        (fun player => quittingTerminalPayoff reward (children (depth + 1)) player) =
          quittingRootSuccessorPayoff reward
            (fun player => quittingTerminalPayoff reward (children depth) player)
            (Function.update (roots depth) owner (PMF.pure false)) := by
  intro depth
  constructor
  · funext player
    rw [hsourceNested depth, quittingTerminalPayoff_rootThenContinuation_eq]
    rfl
  · funext player
    rw [hchildNested depth, quittingTerminalPayoff_rootThenContinuation_eq]
    rfl

/-- The exact outsider seam between an actual source root and the matching
owner-forced child root.  The only nonlocal term is the displayed payoff
displacement in the same outsider coordinate. -/
theorem quittingNestedSourceAndChild_outsiderEndpointSeam
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles children : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) {owner who : ι} (hne : who ≠ owner)
    (depth : ℕ) :
    quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward (children depth) player)
          (Function.update (roots depth) owner (PMF.pure false)) who -
        quittingRootEndpointDifference reward
          (fun player => quittingTerminalPayoff reward (profiles depth) player)
          (roots depth) who =
      -quittingRootOpponentContinueMass
          (Function.update (roots depth) owner (PMF.pure false)) who *
          (quittingTerminalPayoff reward (children depth) who -
            quittingTerminalPayoff reward (profiles depth) who) +
        quittingForcedContinueEndpointRemainder reward
          (fun player => quittingTerminalPayoff reward (profiles depth) player)
          (roots depth) owner who := by
  exact quittingRootEndpointDifference_forcedContinue_sub_eq reward
    (fun player => quittingTerminalPayoff reward (profiles depth) player)
    (fun player => quittingTerminalPayoff reward (children depth) player)
    (roots depth) hne

/-- Fully expanded `Quit - Continue` version of the outsider seam.  The
second term is the change in the Continue absorbing numerator, the third is
the child displacement, and the fourth is the change in opponent survival
applied to the literal source payoff. -/
theorem quittingNestedSourceAndChild_outsiderEndpointSeam_expanded
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles children : ℕ → (quittingGame reward).BehaviorProfile)
    (roots : ℕ → ι → PMF Bool) (owner who : ι) (depth : ℕ) :
    let source := fun player =>
      quittingTerminalPayoff reward (profiles depth) player
    let child := fun player =>
      quittingTerminalPayoff reward (children depth) player
    let forced := Function.update (roots depth) owner (PMF.pure false)
    quittingRootEndpointDifference reward child forced who -
        quittingRootEndpointDifference reward source (roots depth) who =
      (quittingRootQuitPayoff reward child forced who -
          quittingRootQuitPayoff reward source (roots depth) who) -
        (quittingRootAbsorbingContribution reward
              (Function.update forced who (PMF.pure false)) who -
          quittingRootAbsorbingContribution reward
              (Function.update (roots depth) who (PMF.pure false)) who) -
        quittingRootOpponentContinueMass forced who *
          (child who - source who) -
        (quittingRootOpponentContinueMass forced who -
          quittingRootOpponentContinueMass (roots depth) who) * source who := by
  dsimp only
  unfold quittingRootEndpointDifference quittingRootContinuePayoff
    quittingRootOpponentContinueMass
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

end GameTheory
