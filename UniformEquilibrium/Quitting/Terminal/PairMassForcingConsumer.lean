import MathUE.AffinePairRootCrossing
import UniformEquilibrium.Quitting.Paths.BehaviorFirstStoppingPairLaw
import UniformEquilibrium.Quitting.Terminal.TerminalDebtPrefixDescent

/-! # Quantitative consumer for forced first-quitter pair masses -/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Actual affine pair-mass forcing places each profile's exploitability in
the square-root crossing set. -/
theorem affinePairRootSum_exploitability_le_one_of_forcedPairMasses
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition)
    (profile : (quittingGame reward).BehaviorProfile) :
    Math.affinePairRootSum firstIntercept firstSlope secondIntercept secondSlope
      (quittingTerminalExploitability reward profile) ≤ 1 := by
  have hforced := hforcing profile
  have hfirst : max (firstIntercept - firstSlope *
      quittingTerminalExploitability reward profile) 0 ≤
      quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition :=
    max_le hforced.1
      (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile firstCoalition)
  have hsecond : max (secondIntercept - secondSlope *
      quittingTerminalExploitability reward profile) 0 ≤
      quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition :=
    max_le hforced.2
      (quittingBehaviorExactFiniteFirstCoalitionMass_nonneg profile secondCoalition)
  calc
    Math.affinePairRootSum firstIntercept firstSlope secondIntercept secondSlope
        (quittingTerminalExploitability reward profile) ≤
      Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
          profile firstCoalition) +
        Real.sqrt (quittingBehaviorExactFiniteFirstCoalitionMass
          profile secondCoalition) := by
      exact add_le_add (Real.sqrt_le_sqrt hfirst) (Real.sqrt_le_sqrt hsecond)
    _ ≤ 1 := quittingBehaviorFirstStoppingPairMass_sqrt_add_sqrt_le_one
      profile firstCoalition secondCoalition hfirstCard hsecondCard hne

/-- Two actual pair-mass lower bounds force the least square-root crossing
below every behavioral profile's terminal exploitability. -/
theorem quittingTerminalExploitability_ge_affinePairRootLeastCrossing
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition)
    (profile : (quittingGame reward).BehaviorProfile) :
    Math.affinePairRootLeastCrossing firstIntercept firstSlope secondIntercept
      secondSlope ≤ quittingTerminalExploitability reward profile := by
  let error := quittingTerminalExploitability reward profile
  have herror : 0 ≤ error := quittingTerminalExploitability_nonneg reward profile
  apply Math.affinePairRootLeastCrossing_le _ _ _ _ error herror
  exact affinePairRootSum_exploitability_le_one_of_forcedPairMasses
    firstCoalition secondCoalition hfirstCard hsecondCard hne
    firstIntercept firstSlope secondIntercept secondSlope hforcing profile

/-- A forbidden zero-error pair corner makes the least crossing positive.
Feasibility is derived from the actual all-Continue behavioral profile. -/
theorem affinePairRootLeastCrossing_pos_of_forcedPairMasses
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hcorner : 1 < Math.affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope 0)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition) :
    0 < Math.affinePairRootLeastCrossing firstIntercept firstSlope
      secondIntercept secondSlope := by
  let profile := quittingAlwaysContinueProfile reward
  let error := quittingTerminalExploitability reward profile
  have hroot : Math.affinePairRootSum firstIntercept firstSlope secondIntercept
      secondSlope error ≤ 1 := by
    exact affinePairRootSum_exploitability_le_one_of_forcedPairMasses
      firstCoalition secondCoalition hfirstCard hsecondCard hne
      firstIntercept firstSlope secondIntercept secondSlope hforcing profile
  exact Math.affinePairRootLeastCrossing_pos firstIntercept firstSlope
    secondIntercept secondSlope error hcorner
    (quittingTerminalExploitability_nonneg reward profile) hroot

/-- A forbidden forced pair corner produces a literal all-behavior terminal
gap equal to half the least square-root crossing. -/
theorem hasTerminalExploitabilityGap_half_affinePairRootLeastCrossing
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hcorner : 1 < Math.affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope 0)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition) :
    HasTerminalExploitabilityGap reward
      (Math.affinePairRootLeastCrossing firstIntercept firstSlope
        secondIntercept secondSlope / 2) := by
  let crossing := Math.affinePairRootLeastCrossing firstIntercept firstSlope
    secondIntercept secondSlope
  have hpositive : 0 < crossing :=
    affinePairRootLeastCrossing_pos_of_forcedPairMasses firstCoalition
      secondCoalition hfirstCard hsecondCard hne firstIntercept firstSlope
      secondIntercept secondSlope hcorner hforcing
  apply hasTerminalExploitabilityGap_of_lt_quittingTerminalExploitabilityInf
  have hinf : crossing ≤ quittingTerminalExploitabilityInf reward := by
    apply le_csInf
    · exact ⟨quittingTerminalExploitability reward
        (quittingAlwaysContinueProfile reward), ⟨_, rfl⟩⟩
    · rintro value ⟨profile, rfl⟩
      exact quittingTerminalExploitability_ge_affinePairRootLeastCrossing
        firstCoalition secondCoalition hfirstCard hsecondCard hne
        firstIntercept firstSlope secondIntercept secondSlope hforcing profile
  linarith

/-- The same forbidden forced pair corner rules out a uniform-equilibrium
payoff. -/
theorem no_uniformEquilibriumPayoff_of_forcedPairMasses
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hcorner : 1 < Math.affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope 0)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition) :
    ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hgap := hasTerminalExploitabilityGap_half_affinePairRootLeastCrossing
    firstCoalition secondCoalition hfirstCard hsecondCard hne firstIntercept
    firstSlope secondIntercept secondSlope hcorner hforcing
  apply quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    (gap := Math.affinePairRootLeastCrossing firstIntercept firstSlope
      secondIntercept secondSlope / 2) reward
  · have hpositive := affinePairRootLeastCrossing_pos_of_forcedPairMasses
      firstCoalition secondCoalition hfirstCard hsecondCard hne firstIntercept
      firstSlope secondIntercept secondSlope hcorner hforcing
    linarith
  · exact hgap

/-- Every profile admits a deterministic finite quit time or `Never` whose
gain is at least half the least square-root crossing. -/
theorem exists_pureTime_gain_half_affinePairRootLeastCrossing
    (firstCoalition secondCoalition : {C : Finset ι // C.Nonempty})
    (hfirstCard : firstCoalition.1.card = 2)
    (hsecondCard : secondCoalition.1.card = 2)
    (hne : firstCoalition ≠ secondCoalition)
    (firstIntercept firstSlope secondIntercept secondSlope : ℝ)
    (hcorner : 1 < Math.affinePairRootSum firstIntercept firstSlope
      secondIntercept secondSlope 0)
    (hforcing : ∀ profile : (quittingGame reward).BehaviorProfile,
      firstIntercept - firstSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile firstCoalition ∧
        secondIntercept - secondSlope * quittingTerminalExploitability reward profile ≤
          quittingBehaviorExactFiniteFirstCoalitionMass profile secondCoalition)
    (profile : (quittingGame reward).BehaviorProfile) :
    ∃ who : ι, ∃ quitTime : Option ℕ,
      quittingTerminalPayoff reward profile who +
          Math.affinePairRootLeastCrossing firstIntercept firstSlope
            secondIntercept secondSlope / 2 ≤
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who := by
  let crossing := Math.affinePairRootLeastCrossing firstIntercept firstSlope
    secondIntercept secondSlope
  have hpositive : 0 < crossing :=
    affinePairRootLeastCrossing_pos_of_forcedPairMasses firstCoalition
      secondCoalition hfirstCard hsecondCard hne firstIntercept firstSlope
      secondIntercept secondSlope hcorner hforcing
  have hexploit := quittingTerminalExploitability_ge_affinePairRootLeastCrossing
    firstCoalition secondCoalition hfirstCard hsecondCard hne firstIntercept
    firstSlope secondIntercept secondSlope hforcing profile
  unfold quittingTerminalExploitability at hexploit
  obtain ⟨who, -, hwho⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty fun player : ι =>
      max 0 (quittingContinuationBestResponseValue reward profile player -
        quittingTerminalPayoff reward profile player)
  unfold QuittingBoundaryHolonomy.finitePlayerMax at hexploit
  rw [hwho] at hexploit
  change crossing ≤ max 0 (quittingTerminalDeviationDebt reward profile who) at hexploit
  rw [max_eq_right (quittingTerminalDeviationDebt_nonneg reward profile who)] at hexploit
  change crossing ≤ quittingContinuationBestResponseValue reward profile who -
    quittingTerminalPayoff reward profile who at hexploit
  have hpureSup := sSup_range_quittingTerminalPayoff_update_eq_pureTime
    reward profile who
  have hlt : quittingTerminalPayoff reward profile who + crossing / 2 <
      sSup (Set.range fun quitTime : Option ℕ =>
        quittingTerminalPayoff reward
          (Function.update profile who
            (quittingPureTimeBehaviorStrategy reward who quitTime)) who) := by
    rw [← hpureSup]
    change quittingTerminalPayoff reward profile who + crossing / 2 <
      quittingContinuationBestResponseValue reward profile who
    linarith
  obtain ⟨value, ⟨quitTime, rfl⟩, hvalue⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
  exact ⟨who, quitTime, hvalue.le⟩

end GameTheory
