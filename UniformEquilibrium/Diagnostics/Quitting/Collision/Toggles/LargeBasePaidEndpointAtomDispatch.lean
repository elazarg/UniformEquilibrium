/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.Collision.Toggles.LargeBaseStationarySemanticHandoff
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption

/-!
# Source-matched endpoint atoms from the large-base handoff

The checked large-base handoff ends at an actual stationary behavioral
profile and exposes one player's unrestricted stationary cap as the maximum
of two literal deviations: immediate Quit and Never.  This file keeps that
source and those opponents fixed.  It selects a high endpoint, extracts a
quantitative terminal atom from the endpoint's own terminal law, and records
the exhaustive incidence of that atom with the deviating player.

The result is a behavioral source-event theorem.  A positive collision mass
in the selected endpoint law is not asserted to be absorption of an exact
Nash--Bellman predecessor.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The five mutually typed incidences of a terminal atom selected from an
immediate-Quit or Never endpoint. -/
inductive QuittingPaidEndpointIncidence (who : ι) :
    Option ℕ → QuittingTerminalOutcome ι → Prop
  | quitSingleton :
      QuittingPaidEndpointIncidence who (some 0)
        (some (quittingSingletonTerminal who))
  | quitCollision (terminal : {S : Finset ι // S.Nonempty})
      (hwho : who ∈ terminal.val) (hcard : 1 < terminal.val.card) :
      QuittingPaidEndpointIncidence who (some 0) (some terminal)
  | never : QuittingPaidEndpointIncidence who none none
  | neverOtherSingleton (other : ι) (hne : other ≠ who) :
      QuittingPaidEndpointIncidence who none
        (some (quittingSingletonTerminal other))
  | neverDisjointCollision (terminal : {S : Finset ι // S.Nonempty})
      (hwho : who ∉ terminal.val) (hcard : 1 < terminal.val.card) :
      QuittingPaidEndpointIncidence who none (some terminal)

/-- A source-matched quantitative atom at one of the two attained pure-time
endpoints.  The receiving profile is definitionally the unilateral update
of `source`; hence all opponent behavioral strategies are unchanged. -/
structure QuittingPaidEndpointAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile)
    (who : ι) (gap bound : ℝ) where
  endpoint : Option ℕ
  endpoint_extreme : endpoint = some 0 ∨ endpoint = none
  endpoint_gap : gap ≤
    quittingTerminalPayoff reward
        (Function.update source who
          (quittingPureTimeBehaviorStrategy reward who endpoint)) who -
      quittingTerminalPayoff reward source who
  outcome : QuittingTerminalOutcome ι
  mass_floor :
    gap /
        (4 * bound * (Fintype.card (QuittingTerminalOutcome ι) : ℝ)) ≤
      quittingTerminalOutcomeMass reward
        (Function.update source who
          (quittingPureTimeBehaviorStrategy reward who endpoint)) outcome
  reward_gap : quittingTerminalPayoff reward source who + gap / 2 ≤
    quittingTerminalOutcomeReward reward outcome who
  good_mass_floor : gap / (4 * bound) ≤
    ∑ candidate ∈ (Finset.univ.filter fun candidate =>
        quittingTerminalPayoff reward source who + gap / 2 ≤
          quittingTerminalOutcomeReward reward candidate who),
      quittingTerminalOutcomeMass reward
        (Function.update source who
          (quittingPureTimeBehaviorStrategy reward who endpoint)) candidate
  incidence : QuittingPaidEndpointIncidence who endpoint outcome

/-- Terminal probability carried by simultaneous quitting coalitions. -/
def quittingTerminalCollisionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) : ℝ := by
  classical
  exact ∑ outcome ∈ (Finset.univ.filter fun outcome =>
    match outcome with
    | none => False
    | some terminal => 1 < terminal.val.card),
      quittingTerminalOutcomeMass reward profile outcome

omit [DecidableEq ι] in
/-- A bounded finite terminal law whose expectation exceeds a baseline by
`gap` has a half-gap atom carrying at least
`gap / (4 * bound * card outcomes)` mass. -/
theorem exists_quittingTerminalOutcome_halfGap_atom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι)
    (baseline gap bound : ℝ)
    (hgap : 0 < gap) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hbaseline : |baseline| ≤ bound)
    (hpayoff : baseline + gap ≤
      quittingTerminalPayoff reward profile who) :
    ∃ outcome : QuittingTerminalOutcome ι,
      gap /
          (4 * bound * (Fintype.card (QuittingTerminalOutcome ι) : ℝ)) ≤
        quittingTerminalOutcomeMass reward profile outcome ∧
      baseline + gap / 2 ≤
        quittingTerminalOutcomeReward reward outcome who ∧
      gap / (4 * bound) ≤
        ∑ candidate ∈ (Finset.univ.filter fun candidate =>
            baseline + gap / 2 ≤
              quittingTerminalOutcomeReward reward candidate who),
          quittingTerminalOutcomeMass reward profile candidate := by
  let mass := quittingTerminalOutcomeMass reward profile
  let value := quittingTerminalOutcomeReward reward
  let good : Finset (QuittingTerminalOutcome ι) :=
    Finset.univ.filter fun outcome => baseline + gap / 2 ≤ value outcome who
  let bad : Finset (QuittingTerminalOutcome ι) :=
    Finset.univ.filter fun outcome => ¬ baseline + gap / 2 ≤ value outcome who
  let goodMass := ∑ outcome ∈ good, mass outcome
  have hmass := quittingTerminalOutcomeMass_mem_stdSimplex reward profile
  have hmoment := quittingTerminalRewardMoment_outcomeMass reward profile
  have hpayoffBound :
      |quittingTerminalPayoff reward profile who| ≤ bound :=
    abs_quittingTerminalPayoff_le reward profile who hreward
  have hgapBound : gap ≤ 2 * bound := by
    have hpayoffUpper := (abs_le.mp hpayoffBound).2
    have hbaselineLower := (abs_le.mp hbaseline).1
    linarith
  have hgoodMassNonneg : 0 ≤ goodMass := by
    apply Finset.sum_nonneg
    intro outcome _
    exact hmass.1 outcome
  have hgoodMassLeOne : goodMass ≤ 1 := by
    calc
      goodMass ≤ ∑ outcome : QuittingTerminalOutcome ι, mass outcome := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro outcome _ _
        exact hmass.1 outcome
      _ = 1 := hmass.2
  have hvalueUpper : ∀ outcome, value outcome who ≤ bound := by
    intro outcome
    cases outcome with
    | none =>
        simpa [value, quittingTerminalOutcomeReward] using hbound.le
    | some terminal =>
        exact (abs_le.mp (hreward terminal who)).2
  have hbadUpper : ∀ outcome ∉ good,
      value outcome who ≤ baseline + gap / 2 := by
    intro outcome houtcome
    have hnot : ¬ baseline + gap / 2 ≤ value outcome who := by
      simpa [good] using houtcome
    exact (le_of_lt (lt_of_not_ge hnot))
  have hmomentSplit :
      quittingTerminalPayoff reward profile who =
        (∑ outcome ∈ good, mass outcome * value outcome who) +
          ∑ outcome ∈ bad, mass outcome * value outcome who := by
    have hcoord := congrFun hmoment who
    change (∑ outcome, mass outcome * value outcome who) =
      quittingTerminalPayoff reward profile who at hcoord
    rw [← hcoord]
    symm
    simpa [good, bad] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun outcome => baseline + gap / 2 ≤ value outcome who)
        (fun outcome => mass outcome * value outcome who))
  have hgoodUpper :
      (∑ outcome ∈ good, mass outcome * value outcome who) ≤
        goodMass * bound := by
    calc
      (∑ outcome ∈ good, mass outcome * value outcome who) ≤
          ∑ outcome ∈ good, mass outcome * bound := by
        apply Finset.sum_le_sum
        intro outcome houtcome
        exact mul_le_mul_of_nonneg_left (hvalueUpper outcome)
          (hmass.1 outcome)
      _ = goodMass * bound := by
        rw [Finset.sum_mul]
  have hbadMass : (∑ outcome ∈ bad, mass outcome) = 1 - goodMass := by
    have hpartition :
        (∑ outcome ∈ good, mass outcome) +
            ∑ outcome ∈ bad, mass outcome =
          ∑ outcome : QuittingTerminalOutcome ι, mass outcome := by
      simpa [good, bad] using
        (Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun outcome => baseline + gap / 2 ≤ value outcome who) mass)
    dsimp only [goodMass]
    rw [hmass.2] at hpartition
    linarith
  have hbadUpperSum :
      (∑ outcome ∈ bad, mass outcome * value outcome who) ≤
        (1 - goodMass) * (baseline + gap / 2) := by
    calc
      (∑ outcome ∈ bad, mass outcome * value outcome who) ≤
          ∑ outcome ∈ bad,
            mass outcome * (baseline + gap / 2) := by
        apply Finset.sum_le_sum
        intro outcome houtcome
        have hnotGood : outcome ∉ good := by
          simpa [bad, good] using houtcome
        exact mul_le_mul_of_nonneg_left (hbadUpper outcome hnotGood)
          (hmass.1 outcome)
      _ = (1 - goodMass) * (baseline + gap / 2) := by
        rw [← Finset.sum_mul, hbadMass]
  have hgoodMassFloor : gap / (4 * bound) ≤ goodMass := by
    have hupper : quittingTerminalPayoff reward profile who ≤
        goodMass * bound +
          (1 - goodMass) * (baseline + gap / 2) := by
      rw [hmomentSplit]
      exact add_le_add hgoodUpper hbadUpperSum
    have hbaselineLower := (abs_le.mp hbaseline).1
    have hcoefficient :
        bound - baseline - gap / 2 ≤ 2 * bound := by
      linarith
    have hraw : gap / 2 ≤ goodMass * (2 * bound) := by
      have hfirst : gap / 2 ≤
          goodMass * (bound - baseline - gap / 2) := by
        nlinarith
      calc
        gap / 2 ≤ goodMass * (bound - baseline - gap / 2) := hfirst
        _ ≤ goodMass * (2 * bound) :=
          mul_le_mul_of_nonneg_left hcoefficient hgoodMassNonneg
    have hdenom : 0 < 4 * bound := by positivity
    apply (div_le_iff₀ hdenom).2
    nlinarith
  have hgoodNonempty : good.Nonempty := by
    by_contra hempty
    have hempty' : good = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    simp [goodMass, hempty'] at hgoodMassFloor
    exact (not_lt_of_ge hgoodMassFloor) (div_pos hgap (by positivity))
  obtain ⟨outcome, houtcome, hmax⟩ :=
    Finset.exists_max_image good mass hgoodNonempty
  have haverage :
      goodMass /
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ≤ mass outcome := by
    have hsum := Finset.sum_le_card_nsmul good mass (mass outcome)
      (fun other hother => hmax other hother)
    have hcardGood : (good.card : ℝ) ≤
        Fintype.card (QuittingTerminalOutcome ι) := by
      exact_mod_cast Finset.card_le_univ good
    have hmassOutcomeNonneg : 0 ≤ mass outcome := hmass.1 outcome
    have hsumBound : goodMass ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) * mass outcome := by
      calc
        goodMass ≤ (good.card : ℝ) * mass outcome := by
          simpa [goodMass, nsmul_eq_mul] using hsum
        _ ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            mass outcome :=
          mul_le_mul_of_nonneg_right hcardGood hmassOutcomeNonneg
    have hcardPos :
        0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
      positivity
    exact (div_le_iff₀ hcardPos).2 (by simpa [mul_comm] using hsumBound)
  refine ⟨outcome, ?_, ?_, ?_⟩
  · calc
      gap /
          (4 * bound * (Fintype.card (QuittingTerminalOutcome ι) : ℝ)) =
          (gap / (4 * bound)) /
            (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by ring
      _ ≤ goodMass /
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
        gcongr
      _ ≤ mass outcome := haverage
  · simpa [good] using (Finset.mem_filter.mp houtcome).2
  · simpa [goodMass, good, mass, value] using hgoodMassFloor

/-- The pure endpoint fixes the incidence of every positive-mass terminal
outcome with the deviating player. -/
theorem quittingPaidEndpointIncidence_of_positiveMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (who : ι)
    (endpoint : Option ℕ) (outcome : QuittingTerminalOutcome ι)
    (hextreme : endpoint = some 0 ∨ endpoint = none)
    (hpositive : 0 < quittingTerminalOutcomeMass reward
      (Function.update source who
        (quittingPureTimeBehaviorStrategy reward who endpoint)) outcome) :
    QuittingPaidEndpointIncidence who endpoint outcome := by
  rcases hextreme with rfl | rfl
  · cases outcome with
    | none =>
        have hzero : quittingTerminalOutcomeMass reward
            (Function.update source who
              (quittingPureTimeBehaviorStrategy reward who (some 0))) none = 0 := by
          change quittingLiveMassLimit reward _ = 0
          exact quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
            reward source who 0
        linarith
    | some terminal =>
        have hmem : who ∈ terminal.val := by
          by_contra hnot
          have hzero := quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
            reward source who 0 terminal hnot
          simp at hzero
          rw [hzero] at hpositive
          exact (lt_irrefl 0 hpositive)
        by_cases hcard : terminal.val.card = 1
        · obtain ⟨owner, hterminal⟩ := Finset.card_eq_one.mp hcard
          have hterminalEq : terminal = quittingSingletonTerminal owner := by
            apply Subtype.ext
            exact hterminal
          subst terminal
          have howner : who = owner := by
            simpa [quittingSingletonTerminal] using hmem
          subst owner
          exact QuittingPaidEndpointIncidence.quitSingleton
        · exact QuittingPaidEndpointIncidence.quitCollision terminal hmem
            (by have := terminal.property.card_pos; omega)
  · cases outcome with
    | none => exact QuittingPaidEndpointIncidence.never
    | some terminal =>
        have hnot : who ∉ terminal.val := by
          intro hmem
          have hzero := quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero
            reward source who terminal hmem
          rw [hzero] at hpositive
          exact (lt_irrefl 0 hpositive)
        by_cases hcard : terminal.val.card = 1
        · obtain ⟨other, hterminal⟩ := Finset.card_eq_one.mp hcard
          have hterminalEq : terminal = quittingSingletonTerminal other := by
            apply Subtype.ext
            exact hterminal
          subst terminal
          have hne : other ≠ who := by
            intro heq
            subst other
            exact hnot (by simp [quittingSingletonTerminal])
          exact QuittingPaidEndpointIncidence.neverOtherSingleton other hne
        · exact QuittingPaidEndpointIncidence.neverDisjointCollision
            terminal hnot (by have := terminal.property.card_pos; omega)

/-- If the own singleton is below the half-gap threshold, every good atom of
the literal immediate-Quit law is paid by a simultaneous quitting
coalition. -/
theorem quittingImmediateQuit_goodMass_le_collisionMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source : (quittingGame reward).BehaviorProfile) (who : ι)
    (baseline gap : ℝ)
    (hsingleton : reward (quittingSingletonTerminal who) who <
      baseline + gap / 2) :
    (∑ outcome ∈ (Finset.univ.filter fun outcome =>
        baseline + gap / 2 ≤
          quittingTerminalOutcomeReward reward outcome who),
      quittingTerminalOutcomeMass reward
        (Function.update source who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) outcome) ≤
      quittingTerminalCollisionMass reward
        (Function.update source who
          (quittingPureTimeBehaviorStrategy reward who (some 0))) := by
  classical
  let receiving := Function.update source who
    (quittingPureTimeBehaviorStrategy reward who (some 0))
  let mass := quittingTerminalOutcomeMass reward receiving
  change (∑ outcome ∈ Finset.univ.filter (fun outcome =>
      baseline + gap / 2 ≤
        quittingTerminalOutcomeReward reward outcome who), mass outcome) ≤
    ∑ outcome ∈ Finset.univ.filter (fun outcome =>
      match outcome with
      | none => False
      | some terminal => 1 < terminal.val.card), mass outcome
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hgood : baseline + gap / 2 ≤
      quittingTerminalOutcomeReward reward outcome who
  · by_cases hcollision : match outcome with
      | none => False
      | some terminal => 1 < terminal.val.card
    · simp [hgood, hcollision]
    · have hzero : mass outcome = 0 := by
        cases outcome with
        | none =>
            change quittingTerminalOutcomeMass reward receiving none = 0
            change quittingLiveMassLimit reward receiving = 0
            exact quittingLiveMassLimit_update_pureTimeBehaviorStrategy_some_eq_zero
              reward source who 0
        | some terminal =>
            by_cases hmem : who ∈ terminal.val
            · have hcardPos := terminal.property.card_pos
              have hcard : terminal.val.card = 1 := by
                dsimp only at hcollision
                omega
              obtain ⟨owner, hterminal⟩ := Finset.card_eq_one.mp hcard
              have hterminalEq : terminal = quittingSingletonTerminal owner := by
                apply Subtype.ext
                exact hterminal
              subst terminal
              have howner : who = owner := by
                simpa [quittingSingletonTerminal] using hmem
              subst owner
              simp [quittingTerminalOutcomeReward] at hgood
              exact (not_lt_of_ge hgood hsingleton).elim
            · change quittingTerminalOutcomeMass reward receiving
                (some terminal) = 0
              rw [quittingTerminalOutcomeMass_update_pureTime_some_notMem_eq_before
                reward source who 0 terminal hmem]
              simp
      simp [hgood, hcollision, hzero]
  · by_cases hcollision : match outcome with
      | none => False
      | some terminal => 1 < terminal.val.card
    · simpa [hgood, hcollision] using
        (quittingTerminalOutcomeMass_mem_stdSimplex reward receiving).1 outcome
    · simp [hgood, hcollision]

/-- **Immediate-Quit endpoint dispatch.**  Either the literal own singleton
already has the half-gap premium, or the same receiving profile carries both
a total collision mass `gap / (4*bound)` and one fixed collision atom with
the full quantitative atom bound. -/
theorem QuittingPaidEndpointAtom.quitNow_singleton_or_collision
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : (quittingGame reward).BehaviorProfile}
    {who : ι} {gap bound : ℝ}
    (atom : QuittingPaidEndpointAtom reward source who gap bound)
    (hquit : atom.endpoint = some 0) :
    quittingTerminalPayoff reward source who + gap / 2 ≤
        reward (quittingSingletonTerminal who) who ∨
      (gap / (4 * bound) ≤
          quittingTerminalCollisionMass reward
            (Function.update source who
              (quittingPureTimeBehaviorStrategy reward who (some 0))) ∧
        ∃ terminal : {S : Finset ι // S.Nonempty},
          atom.outcome = some terminal ∧
          who ∈ terminal.val ∧
          1 < terminal.val.card ∧
          gap /
              (4 * bound *
                (Fintype.card (QuittingTerminalOutcome ι) : ℝ)) ≤
            quittingTerminalOutcomeMass reward
              (Function.update source who
                (quittingPureTimeBehaviorStrategy reward who (some 0)))
              (some terminal) ∧
          quittingTerminalPayoff reward source who + gap / 2 ≤
            reward terminal who) := by
  by_cases hsingleton : quittingTerminalPayoff reward source who + gap / 2 ≤
      reward (quittingSingletonTerminal who) who
  · exact Or.inl hsingleton
  · right
    have hsingleton' : reward (quittingSingletonTerminal who) who <
        quittingTerminalPayoff reward source who + gap / 2 :=
      lt_of_not_ge hsingleton
    have hcollisionMass : gap / (4 * bound) ≤
        quittingTerminalCollisionMass reward
          (Function.update source who
            (quittingPureTimeBehaviorStrategy reward who (some 0))) := by
      calc
        gap / (4 * bound) ≤
            ∑ outcome ∈ (Finset.univ.filter fun outcome =>
                quittingTerminalPayoff reward source who + gap / 2 ≤
                  quittingTerminalOutcomeReward reward outcome who),
              quittingTerminalOutcomeMass reward
                (Function.update source who
                  (quittingPureTimeBehaviorStrategy reward who atom.endpoint))
                outcome := atom.good_mass_floor
        _ = ∑ outcome ∈ (Finset.univ.filter fun outcome =>
                quittingTerminalPayoff reward source who + gap / 2 ≤
                  quittingTerminalOutcomeReward reward outcome who),
              quittingTerminalOutcomeMass reward
                (Function.update source who
                  (quittingPureTimeBehaviorStrategy reward who (some 0)))
                outcome := by rw [hquit]
        _ ≤ _ := quittingImmediateQuit_goodMass_le_collisionMass
          reward source who (quittingTerminalPayoff reward source who) gap
            hsingleton'
    have hincidence : QuittingPaidEndpointIncidence who (some 0) atom.outcome := by
      simpa only [hquit] using atom.incidence
    refine ⟨hcollisionMass, ?_⟩
    generalize houtcome : atom.outcome = outcome at hincidence
    cases hincidence with
    | quitSingleton =>
        have hreward := atom.reward_gap
        rw [houtcome] at hreward
        exact (not_lt_of_ge hreward hsingleton').elim
    | quitCollision terminal hmem hcard =>
        refine ⟨terminal, rfl, hmem, hcard, ?_, ?_⟩
        · have hmass := atom.mass_floor
          rw [hquit, houtcome] at hmass
          exact hmass
        · have hreward := atom.reward_gap
          rw [houtcome] at hreward
          simpa [quittingTerminalOutcomeReward] using hreward

/-- In the singleton arm, every exact endpoint-Nash root at the actual source
payoff has the packet's fixed absorption charge
`gap / (gap + 8*bound)`.  The extra half-gap reserve is left available for a
later moving-tail stack. -/
theorem QuittingPaidEndpointAtom.quitNow_singleton_absorption
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : (quittingGame reward).BehaviorProfile}
    {who : ι} {gap bound : ℝ}
    (_atom : QuittingPaidEndpointAtom reward source who gap bound)
    (hgap : 0 < gap)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hsingleton : quittingTerminalPayoff reward source who + gap / 2 ≤
      reward (quittingSingletonTerminal who) who)
    (root : ι → PMF Bool)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingTerminalPayoff reward source) 0 root) :
    gap / (gap + 8 * bound) ≤ quittingRootAbsorptionMass root := by
  have heta : 0 < gap / 4 := by positivity
  have htail : quittingTerminalPayoff reward source who ≤
      reward (quittingSingletonTerminal who) who - gap / 4 := by
    linarith
  have hbound := gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
    reward (quittingTerminalPayoff reward source) root who heta hreward
      htail hnash
  have hboundNonneg : 0 ≤ bound :=
    quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hleft : gap + 8 * bound ≠ 0 := by positivity
  have hright : gap / 4 + 2 * bound ≠ 0 := by positivity
  convert hbound using 1
  field_simp [hleft, hright]
  ring

/-- A positive stationary cap debt selects one of the two literal attained
endpoints and equips it with a source-matched quantitative terminal atom. -/
theorem exists_quittingPaidEndpointAtom_of_stationaryCapDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) (gap bound : ℝ)
    (hgap : 0 < gap) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hdebt : gap ≤ quittingStationaryUnilateralCap reward root who -
      quittingTerminalPayoff reward
        (quittingStationaryProfile reward root) who) :
    Nonempty (QuittingPaidEndpointAtom reward
      (quittingStationaryProfile reward root) who gap bound) := by
  let source := quittingStationaryProfile reward root
  let quitNow := quittingPureTimeDeviationPayoff reward source who (some 0)
  let never := quittingPureTimeDeviationPayoff reward source who none
  have hcap : quittingStationaryUnilateralCap reward root who =
      max quitNow never := by
    exact quittingStationaryUnilateralCap_eq_max_quitNow_never reward root who
  have hbaseline :
      |quittingTerminalPayoff reward source who| ≤ bound :=
    abs_quittingTerminalPayoff_le reward source who hreward
  by_cases horder : never ≤ quitNow
  · have hendpoint : gap ≤ quitNow -
        quittingTerminalPayoff reward source who := by
      rw [hcap, max_eq_left horder] at hdebt
      exact hdebt
    let receiving := Function.update source who
      (quittingPureTimeBehaviorStrategy reward who (some 0))
    have hreceiving : quittingTerminalPayoff reward receiving who = quitNow := rfl
    have hendpoint' : gap ≤ quittingTerminalPayoff reward receiving who -
        quittingTerminalPayoff reward source who := by
      rw [hreceiving]
      exact hendpoint
    obtain ⟨outcome, hmass, hrewardGap, hgoodMass⟩ :=
      exists_quittingTerminalOutcome_halfGap_atom reward receiving who
        (quittingTerminalPayoff reward source who) gap bound hgap hbound
        hreward hbaseline (by rw [hreceiving]; linarith)
    have hmassPositive : 0 < quittingTerminalOutcomeMass reward receiving outcome :=
      lt_of_lt_of_le (div_pos hgap (by positivity)) hmass
    exact ⟨{
      endpoint := some 0
      endpoint_extreme := Or.inl rfl
      endpoint_gap := hendpoint'
      outcome := outcome
      mass_floor := hmass
      reward_gap := hrewardGap
      good_mass_floor := hgoodMass
      incidence := quittingPaidEndpointIncidence_of_positiveMass
        reward source who (some 0) outcome (Or.inl rfl) hmassPositive }⟩
  · have horder' : quitNow ≤ never := le_of_not_ge horder
    have hendpoint : gap ≤ never -
        quittingTerminalPayoff reward source who := by
      rw [hcap, max_eq_right horder'] at hdebt
      exact hdebt
    let receiving := Function.update source who
      (quittingPureTimeBehaviorStrategy reward who none)
    have hreceiving : quittingTerminalPayoff reward receiving who = never := rfl
    have hendpoint' : gap ≤ quittingTerminalPayoff reward receiving who -
        quittingTerminalPayoff reward source who := by
      rw [hreceiving]
      exact hendpoint
    obtain ⟨outcome, hmass, hrewardGap, hgoodMass⟩ :=
      exists_quittingTerminalOutcome_halfGap_atom reward receiving who
        (quittingTerminalPayoff reward source who) gap bound hgap hbound
        hreward hbaseline (by rw [hreceiving]; linarith)
    have hmassPositive : 0 < quittingTerminalOutcomeMass reward receiving outcome :=
      lt_of_lt_of_le (div_pos hgap (by positivity)) hmass
    exact ⟨{
      endpoint := none
      endpoint_extreme := Or.inr rfl
      endpoint_gap := hendpoint'
      outcome := outcome
      mass_floor := hmass
      reward_gap := hrewardGap
      good_mass_floor := hgoodMass
      incidence := quittingPaidEndpointIncidence_of_positiveMass
        reward source who none outcome (Or.inr rfl) hmassPositive }⟩

namespace QuittingSingletonBaseStationaryHandoff

/-- The one-debtor stationary handoff has a literal source-matched endpoint
atom.  Its cap debt is unrestricted because it comes from the checked
stationary stopping theorem used by the handoff. -/
theorem paidEndpointAtom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {owner : ι} {free : Finset ι}
    {point : mixedPolytope (quittingBinaryForm free).sig}
    {delta terminalGap bound : ℝ}
    (handoff : QuittingSingletonBaseStationaryHandoff reward owner free point
      delta terminalGap)
    (hgap : 0 < terminalGap) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    Nonempty (QuittingPaidEndpointAtom reward
      (quittingSingletonBaseRepairedProfile reward owner free point)
      handoff.outsideDebtor terminalGap bound) := by
  exact exists_quittingPaidEndpointAtom_of_stationaryCapDebt reward
    (quittingSingletonBaseRepairedRoot owner free point)
    handoff.outsideDebtor terminalGap bound hgap hbound hreward
    handoff.outside_debt

end QuittingSingletonBaseStationaryHandoff

namespace QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

/-- **Actual large-base endpoint-atom adapter.**  The four-player paid-chain
residual retains its original labels and source route while the selected
stationary handoff supplies a literal high endpoint and quantitative atom on
unchanged opponents. -/
theorem LargeBasePaidStationaryHandoff.paidEndpointAtom
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {seed : Finset ι}
    {cycle : witness.ReachableStrictToggleSimpleCycle seed}
    (handoff : cycle.LargeBasePaidStationaryHandoff)
    (bound : ℝ) (hbound : 0 < bound)
    (hreward : ∀ terminal player, |reward terminal player| ≤ bound) :
    ∃ semantic : QuittingSingletonBaseStationaryHandoff reward
        handoff.owner {handoff.paid, handoff.first, handoff.second}
          handoff.point handoff.delta witness.terminalGap,
      Nonempty (QuittingPaidEndpointAtom reward
        (quittingSingletonBaseRepairedProfile reward handoff.owner
          {handoff.paid, handoff.first, handoff.second} handoff.point)
        semantic.outsideDebtor witness.terminalGap bound) := by
  obtain ⟨semantic⟩ := handoff.semanticHandoff
  exact ⟨semantic, semantic.paidEndpointAtom witness.terminalGap_pos
    hbound hreward⟩

end QuittingTerminalExploitabilityWitness.ReachableStrictToggleSimpleCycle

end GameTheory
