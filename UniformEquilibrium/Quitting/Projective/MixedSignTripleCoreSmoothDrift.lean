import UniformEquilibrium.Quitting.Classification.MixedSignTripleCoreSelectedReturn
import UniformEquilibrium.Quitting.Projective.PureSetExactRootPotentialExclusion

/-! # Explicit strict mixed-sign analytic alternatives

Either the positive pair supplies its actual sure-exit payoff, or every
strict singleton-deficit annotation has a selected absorbing exact root
returning to a singleton sublevel. Potential exclusion keeps the stronger
continuity-on-D and boundary-only ambient differentiability scope.
-/

noncomputable section

namespace GameTheory

open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem purePairSureExit_or_selectedReturn_of_mixedSignTriple_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third) :
    (IsQuittingSureExitSet reward {first, second} ∧
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSetReward reward {first, second})) ∨
    (∀ tail : Payoff ι,
      (∃ player, tail player < reward (quittingSingletonTerminal player) player) →
      ∃ root, IsεQuittingRootNash reward tail 0 root ∧
        0 < quittingRootAbsorptionMass root ∧
        ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
          reward (quittingSingletonTerminal player) player) := by
  classical
  by_cases hpure : ∃ tail : Payoff ι, IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))
  · obtain ⟨tail, hnash⟩ := hpure
    have hsure := isQuittingSureExitSet_pair_of_purePairNash reward tail
      hjoining.pairwise_distinct.1 hnash
    exact Or.inl ⟨hsure,
      isUniformEquilibriumPayoff_setReward_of_isQuittingSureExitSet reward hsure⟩
  · right
    intro tail hbelow
    obtain ⟨root, hnash, hlow⟩ := exists_exactRoot_singletonSublevel_of_mixedSignTriple_core
      reward tail hcore hjoining hbelow (fun hnash => hpure ⟨tail, hnash⟩)
    exact ⟨root, hnash,
      exactRoot_absorptionMass_pos_of_below_singleton reward tail root hnash hbelow, hlow⟩

theorem not_isQuittingFullExactRootPotential_of_mixedSignTriple_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second third : ι} (hcore : quittingPremiumCore reward = {first, second, third})
    (hjoining : HasMixedSignTripleJoining reward first second third)
    {M bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hbound : M < bound) (potential : Payoff ι → ℝ)
    (hcontinuous : ContinuousOn potential (quittingBoxedSingletonSublevelDomain reward bound))
    (hdiff : ∀ point ∈ Math.lowerBoxBoundary
      (fun player => quittingSoloReward reward player player) (fun _ => bound),
        DifferentiableAt ℝ potential point) :
    ¬IsQuittingFullExactRootPotential reward bound potential := by
  classical
  by_cases hpure : ∃ tail : Payoff ι, IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))
  · obtain ⟨tail, hnash⟩ := hpure
    have hne := hjoining.pairwise_distinct.1
    have hnonempty : ({first, second} : Finset ι).Nonempty := by simp
    have hbox : ∀ player, |quittingSetReward reward {first, second} player| ≤ bound := by
      intro player
      rw [quittingSetReward_of_nonempty reward hnonempty]
      exact (hreward ⟨{first, second}, hnonempty⟩ player).trans hbound.le
    rw [pairedRoot_pure_true_eq_pureSetRoot hne] at hnash
    exact not_isQuittingFullExactRootPotential_of_pureSetNash reward tail
      {first, second} (by simp [hne]) hnash bound
      hbox potential
  · let : Nonempty ι := ⟨first⟩
    exact not_isQuittingFullExactRootPotential_of_selectedSingletonSublevelReturn reward
      hreward hbound
      (hasBoxedSelectedSingletonSublevelReturn_of_mixedSignTriple_core reward hcore hjoining
        (fun tail hnash => hpure ⟨tail, hnash⟩) bound)
      potential hcontinuous hdiff

end GameTheory
