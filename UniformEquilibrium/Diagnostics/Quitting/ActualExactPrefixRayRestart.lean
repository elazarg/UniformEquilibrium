import MathUE.EventuallyPositiveLastZero
import UniformEquilibrium.Diagnostics.Quitting.FinFourActualPrefixHazard
import UniformEquilibrium.Diagnostics.Quitting.FirstExactRootUniqueSureLimit
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawExploitabilityFloor
import UniformEquilibrium.Quitting.Paths.ActualExactPrefixRay
import UniformEquilibrium.Quitting.Root.TerminalGapPrefixDebtorTransport
import UniformEquilibrium.Quitting.Terminal.FiniteDeadlineCapSelection

/-! # Last-zero restart of an actual Fin4 exact-prefix ray -/

noncomputable section
namespace GameTheory

open Math.Probability

namespace QuittingActualExactPrefixRay

/-- Every supplied actual Fin4 exact-prefix ray from a finite sure-Quit,
zero-debt anchor either carries a shifted cap from its initial profile or has
a last zero-survival root.  In the second case that root's unique sure
quitter carries the full supplied gap at the literal child and starts the
shifted cap tail there. -/
theorem initial_or_lastZero_uniqueSure_shiftedCapTail
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (hnot : ¬ ∃ payoff : Payoff (Fin 4),
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff)
    {gap : ℝ} (hexploit : HasTerminalExploitabilityGap reward gap)
    (hgap : 0 < gap)
    (source : (quittingGame reward).BehaviorProfile)
    (ray : QuittingActualExactPrefixRay reward source)
    (anchor : Fin 4) (deadline : ℕ)
    (hsure : quittingProfileLiveRoot reward source deadline anchor =
      PMF.pure true)
    (hanchorDebt : quittingTerminalDeviationDebt reward source anchor = 0) :
    (∀ depth, quittingProfileLiveRoot reward (ray.profiles depth)
        (deadline + depth) anchor = PMF.pure true) ∧
    (∀ depth,
      quittingTerminalDeviationDebt reward (ray.profiles depth) anchor = 0) ∧
    ((∃ tail : ShiftedCapTail ray,
        tail.start = 0 ∧ tail.owner ≠ anchor ∧
        (tail.initialChoice = none ∨
          ∃ time ≤ deadline, tail.initialChoice = some time) ∧
        gap ≤ quittingTerminalDeviationDebt reward source tail.owner) ∨
      ∃ (last : ℕ) (owner : Fin 4) (tail : ShiftedCapTail ray),
        quittingStationaryContinueMass (ray.roots last) = 0 ∧
        ray.roots last owner = PMF.pure true ∧
        (∀ other, other ≠ owner →
          ray.roots last other ≠ PMF.pure true) ∧
        owner ≠ anchor ∧ tail.start = last + 1 ∧ tail.owner = owner ∧
        (tail.initialChoice = none ∨
          ∃ time ≤ deadline + (last + 1),
            tail.initialChoice = some time) ∧
        gap ≤ quittingTerminalDeviationDebt reward
          (ray.profiles (last + 1)) owner) := by
  have hsummable :=
    finFour_summable_actualExactPrefix_hazard_of_no_uniformPayoff
      reward hnot ray.profiles ray.roots ray.profiles_succ ray.roots_exact
  have heventually :=
    eventually_jointSurvival_pos_of_summable_marginalHazard ray.roots hsummable
  have hsureAll := ray.anchor_sureQuit_at_shiftedDeadline anchor deadline hsure
  have hanchorZero := ray.anchor_debt_eq_zero anchor hanchorDebt
  refine ⟨hsureAll, hanchorZero, ?_⟩
  by_cases hzeroRoot : ∃ depth,
      quittingStationaryContinueMass (ray.roots depth) = 0
  · obtain ⟨last, hlastZero, hpositiveAfter⟩ :=
      Math.exists_last_zero_of_eventually_positive
        (fun depth => quittingStationaryContinueMass (ray.roots depth))
        (fun depth => quittingStationaryContinueMass_nonneg (ray.roots depth))
        heventually hzeroRoot
    let pair := quittingTerminalSemanticPair reward (ray.profiles last)
    have hpair : pair ∈ quittingTerminalSemanticCarrier reward :=
      subset_closure ⟨ray.profiles last, rfl⟩
    have hprefixCarrier : quittingTerminalSemanticPrefix reward
        (ray.roots last) pair ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPrefix_mem_carrier reward (ray.roots last) pair hpair
    have htotal : gap ≤ quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward (ray.roots last) pair) :=
      terminalExploitabilityGap_le_terminalSemanticDebtSum_of_mem_carrier
        reward _ hexploit hprefixCarrier
    obtain ⟨owner, howner, hunique, -, hownerDebtSemantic⟩ :=
      uniqueSureQuitter_of_terminalSemanticPrefix_positiveDebtFloor
        reward pair (ray.roots last) (floor := gap) hgap hpair
          (ray.roots_exact last) hlastZero htotal
    have hownerDebt : gap ≤ quittingTerminalDeviationDebt reward
        (ray.profiles (last + 1)) owner := by
      change gap ≤ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (ray.profiles (last + 1))) owner
      rw [ray.profiles_succ,
        quittingTerminalSemanticPair_rootThenContinuation]
      exact hownerDebtSemantic
    have hownerNe : owner ≠ anchor := by
      intro heq
      subst owner
      rw [hanchorZero (last + 1)] at hownerDebt
      linarith
    obtain ⟨choice, hchoiceBound, hcap⟩ :=
      exists_pureTime_le_deadline_or_never_terminalPayoff_eq_cap
        reward (ray.profiles (last + 1)) (deadline + (last + 1))
          hownerNe.symm (hsureAll (last + 1))
    have hpositiveTail : ∀ fuel,
        0 < quittingStationaryContinueMass
          (ray.roots ((last + 1) + fuel)) := by
      intro fuel
      exact hpositiveAfter _ (by omega)
    obtain ⟨tail, htailStart, htailOwner, htailChoice⟩ :=
      nonempty_shiftedCapTail_of_attainedCap ray (last + 1) owner choice
        hcap (hgap.trans_le hownerDebt) hpositiveTail hsummable
    subst choice
    exact Or.inr ⟨last, owner, tail, hlastZero, howner, hunique,
      hownerNe, htailStart, htailOwner, hchoiceBound, hownerDebt⟩
  · have hpositive : ∀ depth,
        0 < quittingStationaryContinueMass (ray.roots depth) := by
      intro depth
      exact lt_of_le_of_ne
        (quittingStationaryContinueMass_nonneg (ray.roots depth))
        (fun h => hzeroRoot ⟨depth, h.symm⟩)
    obtain ⟨owner, choice, hownerNe, hchoiceBound, hcap, hownerDebt, -, -⟩ :=
      hexploit.exists_outsider_pureTimeCap_with_prefix_debt reward source
        anchor deadline (by rw [hanchorDebt]; exact hgap) hsure [] 1
          (by simp [quittingLiteralRootStackJointSurvival])
    have hcapRay : quittingTerminalPayoff reward
        (Function.update (ray.profiles 0) owner
          (quittingPureTimeBehaviorStrategy reward owner choice)) owner =
      quittingContinuationBestResponseValue reward (ray.profiles 0) owner := by
      simpa [ray.profiles_zero] using hcap
    have hdebtRay : 0 < quittingTerminalDeviationDebt reward
        (ray.profiles 0) owner := by
      simpa [ray.profiles_zero] using hgap.trans_le hownerDebt
    obtain ⟨tail, htailStart, htailOwner, htailChoice⟩ :=
      nonempty_shiftedCapTail_of_attainedCap ray 0 owner choice hcapRay
        hdebtRay (by simpa using hpositive) hsummable
    subst owner
    subst choice
    exact Or.inl ⟨tail, htailStart, hownerNe, hchoiceBound, by
      simpa [ray.profiles_zero] using hownerDebt⟩

end QuittingActualExactPrefixRay
end GameTheory
