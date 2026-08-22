/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Toggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.ImmediateSingletonCollision
import UniformEquilibrium.Quitting.Classification.PreemptionCycle
import MathUE.Topology.FiniteLabelSubsequence

/-!
# Strict preemption cycles in a quitting counterexample regime

The stationary terminal-gap inequality first forces one full-gap solo
preemption edge.  A two-rate stationary probe propagates every reached edge.
Finiteness then closes the resulting strict directed walk into a positive-period
preemption cycle.
-/

noncomputable section

namespace GameTheory

variable {player : Type} [Fintype player] [DecidableEq player]
variable {reward : {S : Finset player // S.Nonempty} → Payoff player}

namespace QuittingCounterexampleRegime

/-- At every positive owner-solo rate, a viable owner forces some distinct
opponent's affine immediate-Quit endpoint to beat the owner's solo payoff by
the full terminal gap. -/
theorem exists_soloRate_joiningGain
    (regime : QuittingCounterexampleRegime reward) {owner : player}
    (howner : -regime.terminalGap <
      quittingSoloReward reward owner owner)
    {rate : ℝ} (hrate0 : 0 < rate) (hrate1 : rate ≤ 1) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other + regime.terminalGap ≤
        (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other := by
  let rateCoin := quittingHazardCoin rate hrate0.le hrate1
  let root := quittingSoloStationaryRoot owner rateCoin
  obtain ⟨who, hgain⟩ := regime.exists_stationaryCap_gain root
  have hpositive : 0 < (rateCoin true).toReal := by
    simpa only [rateCoin, quittingHazardCoin_true_toReal] using hrate0
  have hactual : quittingTerminalPayoff reward
      (quittingStationaryProfile reward root) who =
        quittingSoloReward reward owner who := by
    exact quittingTerminalPayoff_soloStationary
      reward owner who rateCoin hpositive
  by_cases hwho : who = owner
  · subst who
    rw [hactual, quittingStationaryUnilateralCap_solo_owner] at hgain
    rcases le_max_iff.mp hgain with hself | hnever
    · linarith [regime.terminalGap_pos]
    · linarith
  · refine ⟨who, hwho, ?_⟩
    rw [hactual,
      quittingStationaryUnilateralCap_solo_other reward hwho rateCoin
        hpositive,
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho rateCoin] at hgain
    simp only [rateCoin, quittingHazardCoin_false_toReal,
      quittingHazardCoin_true_toReal] at hgain
    rcases le_max_iff.mp hgain with hquit | hcontinue
    · exact hquit
    · linarith [regime.terminalGap_pos]

/-- Every viable solo owner has a strict full-gap preemptor.  The conclusion
is the zero-rate endpoint of `exists_soloRate_joiningGain`; finiteness turns
the limiting argument into one explicit minimum-slack contradiction. -/
theorem exists_soloPreemptor
    (regime : QuittingCounterexampleRegime reward) {owner : player}
    (howner : -regime.terminalGap <
      quittingSoloReward reward owner owner) :
    ∃ other, QuittingSoloPreempts reward regime.terminalGap owner other := by
  by_contra hnot
  simp only [QuittingSoloPreempts, not_exists, not_and, not_le] at hnot
  obtain ⟨witness, hwitnessNe, -⟩ :=
    regime.exists_soloRate_joiningGain howner (rate := 1) one_pos le_rfl
  have hwitnessMem : witness ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hwitnessNe, Finset.mem_univ witness⟩
  have hopponents : (Finset.univ.erase owner).Nonempty :=
    ⟨witness, hwitnessMem⟩
  obtain ⟨gapArg, hgapMem, hgapMin⟩ := Finset.exists_min_image
    (Finset.univ.erase owner)
    (fun other ↦ quittingSoloReward reward owner other +
      regime.terminalGap - quittingSoloReward reward other other)
    hopponents
  obtain ⟨spreadArg, _, hspreadMax⟩ := Finset.exists_max_image
    (Finset.univ.erase owner)
    (fun other ↦ |quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other|) hopponents
  set slack := quittingSoloReward reward owner gapArg +
    regime.terminalGap - quittingSoloReward reward gapArg gapArg with hslack
  set spread := |quittingSingletonCollisionReward reward owner spreadArg -
    quittingSoloReward reward spreadArg spreadArg| with hspread
  have hgapArgNe : gapArg ≠ owner := (Finset.mem_erase.mp hgapMem).1
  have hslackPos : 0 < slack := by
    rw [hslack]
    exact sub_pos.mpr (hnot gapArg hgapArgNe)
  have hspreadNonneg : 0 ≤ spread := by
    rw [hspread]
    exact abs_nonneg _
  set rate := slack / (spread + slack) with hrate
  have hdenom : 0 < spread + slack := by linarith
  have hrate0 : 0 < rate := by
    rw [hrate]
    exact div_pos hslackPos hdenom
  have hrate1 : rate ≤ 1 := by
    rw [hrate]
    exact (div_le_one hdenom).mpr (by linarith)
  obtain ⟨other, hotherNe, hgain⟩ :=
    regime.exists_soloRate_joiningGain howner hrate0 hrate1
  have hotherMem : other ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hotherNe, Finset.mem_univ other⟩
  have hslackMin : slack ≤ quittingSoloReward reward owner other +
      regime.terminalGap - quittingSoloReward reward other other := by
    simpa only [hslack] using hgapMin other hotherMem
  have hspreadBound :
      quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward other other ≤ spread :=
    le_trans (le_abs_self _) (by
      simpa only [hspread] using hspreadMax other hotherMem)
  have hrateSpread : rate * spread < slack := by
    rw [hrate, div_mul_eq_mul_div, div_lt_iff₀ hdenom]
    nlinarith
  have hmix :
      (1 - rate) * quittingSoloReward reward other other +
          rate * quittingSingletonCollisionReward reward owner other =
        quittingSoloReward reward other other +
          rate * (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward other other) := by
    ring
  rw [hmix] at hgain
  have hscaled := mul_le_mul_of_nonneg_left hspreadBound hrate0.le
  nlinarith

/-- Every full-gap preemption edge can be extended by another full-gap edge.
The two-rate probe makes the supplied predecessor vanish one order faster than
the current owner, while retaining enough provenance to rule out a spurious
self-witness in the limit. -/
theorem exists_soloPreemptor_of_soloPreempts
    (regime : QuittingCounterexampleRegime reward)
    {predecessor current : player}
    (hedge : QuittingSoloPreempts reward regime.terminalGap
      predecessor current) :
    ∃ next, QuittingSoloPreempts reward regime.terminalGap current next := by
  let rate : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hrate0 : ∀ n, 0 < rate n := by
    intro n
    dsimp only [rate]
    positivity
  have hrate1 : ∀ n, rate n ≤ 1 := by
    intro n
    dsimp only [rate]
    apply (div_le_one (by positivity)).2
    exact_mod_cast (show (1 : ℕ) ≤ n + 1 by omega)
  have hrate : Filter.Tendsto rate Filter.atTop (nhds 0) := by
    simpa only [rate] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1))
          Filter.atTop (nhds 0))
  let root : ℕ → player → PMF Bool := fun n ↦
    quittingPreemptionRoot predecessor current (rate n)
      (hrate0 n).le (hrate1 n)
  have hwitness : ∀ n, ∃ who,
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward (root n)) who +
          regime.terminalGap ≤
        quittingStationaryUnilateralCap reward (root n) who := by
    intro n
    exact regime.exists_stationaryCap_gain (root n)
  have hfrequent : ∃ᶠ n in Filter.atTop, ∃ who,
      quittingTerminalPayoff reward
          (quittingStationaryProfile reward (root n)) who +
          regime.terminalGap ≤
        quittingStationaryUnilateralCap reward (root n) who :=
    Filter.Frequently.of_forall hwitness
  rw [Filter.frequently_exists] at hfrequent
  obtain ⟨who, hwhoFrequent⟩ := hfrequent
  obtain ⟨subseq, hsubseq, hgain⟩ :=
    Filter.extraction_of_frequently_atTop hwhoFrequent
  have hpayoff :=
    (tendsto_quittingTerminalPayoff_preemptionRoot
      (reward := reward) hedge.1.symm rate hrate0 hrate1 hrate who).comp
        hsubseq.tendsto_atTop
  have hcap :=
    (tendsto_quittingStationaryUnilateralCap_preemptionRoot
      (reward := reward) hedge regime.terminalGap_pos.le
        rate hrate0 hrate1 hrate who).comp hsubseq.tendsto_atTop
  have hlimit : quittingSoloReward reward current who + regime.terminalGap ≤
      max (quittingSoloReward reward who who)
        (quittingSoloReward reward current who) := by
    apply le_of_tendsto_of_tendsto
      (hpayoff.add_const regime.terminalGap) hcap
    exact Filter.Eventually.of_forall hgain
  have hwho : who ≠ current := by
    intro heq
    subst who
    simp only [max_self] at hlimit
    linarith [regime.terminalGap_pos]
  refine ⟨who, hwho, ?_⟩
  rcases le_max_iff.mp hlimit with hquit | hcontinue
  · exact hquit
  · linarith [regime.terminalGap_pos]

/-- Every quitting counterexample regime forces a finite strict full-gap
preemption cycle.  Finiteness is used only after the two-rate propagation
theorem has made the preemption relation serial on its reached carrier. -/
theorem nonempty_soloPreemptionCycle
    (regime : QuittingCounterexampleRegime reward) :
    Nonempty (QuittingSoloPreemptionCycle reward regime.terminalGap) := by
  classical
  let Carrier := {current : player // ∃ predecessor,
    QuittingSoloPreempts reward regime.terminalGap predecessor current}
  obtain ⟨owner, howner⟩ := regime.exists_terminalGap_le_soloReward
  have hownerViable : -regime.terminalGap <
      quittingSoloReward reward owner owner := by
    linarith [regime.terminalGap_pos]
  obtain ⟨first, hfirst⟩ := regime.exists_soloPreemptor hownerViable
  letI : Nonempty Carrier := ⟨⟨first, owner, hfirst⟩⟩
  let R : Carrier → Carrier → Prop := fun current next ↦
    QuittingSoloPreempts reward regime.terminalGap current.1 next.1
  have hserial : ∀ state : Carrier, ∃ next, R state next := by
    intro state
    obtain ⟨next, hedge⟩ := regime.exists_soloPreemptor_of_soloPreempts
      (Classical.choose_spec state.2)
    exact ⟨⟨next, state.1, hedge⟩, hedge⟩
  obtain ⟨cycle⟩ :=
    Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial R hserial
  exact ⟨cycle.map Subtype.val (fun hedge ↦ hedge)⟩

/-- Strongest current counterexample localization: the executable immediate
singleton collision and the payoff-table preemption cycle hold together. -/
theorem immediateSingletonCollision_and_soloPreemptionCycle
    (regime : QuittingCounterexampleRegime reward) :
    Nonempty (QuittingImmediateSingletonCollision reward regime.terminalGap) ∧
      Nonempty (QuittingSoloPreemptionCycle reward regime.terminalGap) :=
  ⟨regime.exists_immediateSingletonCollision,
    regime.nonempty_soloPreemptionCycle⟩

end QuittingCounterexampleRegime

end GameTheory
