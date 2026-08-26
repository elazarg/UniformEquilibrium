/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteSerialRelation
import MathUE.Finset.InsertExtremum
import UniformEquilibrium.Quitting.Classification.ExistenceBranches
import UniformEquilibrium.Quitting.Classification.PreemptionCycle
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalTargetSemantics

/-!
# Acyclic augmented solo preemption

Adjoin a bottom vertex to the strict solo-preemption relation.  An edge from
bottom records a positive own singleton reward, while an edge to bottom
records a negative one.  A finite augmented graph with no directed periodic
cycle has a sink.  A bottom sink is the zero-solo branch; a player sink is a
nonnegative singleton owner whose solo row weakly dominates every outsider's
own singleton payoff.

At a player sink, letting only the owner quit with rate `q` gives literal
all-behavior terminal exploitability at most `q` times the largest positive
singleton-collision premium.  The target payoff is the fixed owner singleton
row.  Thus the acyclic augmented architecture always has a uniform-equilibrium
payoff and cannot force positive terminal mass on designated pair rows.

No restriction is placed on rewards of coalitions with at least three
players.  The theorem says nothing about the cyclic residual class.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The augmented strict solo-preemption edge on `Option ι`, with `none` as
the bottom vertex. -/
def QuittingAugmentedSoloPreemptionEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Option ι → Option ι → Prop
  | none, some who => 0 < quittingSoloReward reward who who
  | some who, none => quittingSoloReward reward who who < 0
  | some owner, some other =>
      other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSoloReward reward other other
  | none, none => False

/-- A positive-period directed cycle in the augmented solo-preemption graph. -/
abbrev QuittingAugmentedSoloPreemptionCycle
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  Math.FiniteSerialRelation.PeriodicCycle
    (QuittingAugmentedSoloPreemptionEdge reward)

/-- Acyclicity of the finite augmented graph, expressed by absence of a
positive-period directed cycle. -/
def IsQuittingAugmentedSoloPreemptionAcyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ¬Nonempty (QuittingAugmentedSoloPreemptionCycle reward)

omit [Fintype ι] [DecidableEq ι] in
/-- A strict natural-valued rank certifies augmented acyclicity.  This is a
finite-table-friendly adapter for concrete regressions and producers. -/
theorem isQuittingAugmentedSoloPreemptionAcyclic_of_rank
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rank : Option ι → ℕ)
    (hedge : ∀ {source target},
      QuittingAugmentedSoloPreemptionEdge reward source target →
        rank source < rank target) :
    IsQuittingAugmentedSoloPreemptionAcyclic reward := by
  rintro ⟨cycle⟩
  have hstep : ∀ time,
      rank (cycle.vertex time) < rank (cycle.vertex (time + 1)) :=
    fun time => hedge (cycle.edge time)
  have hchain : ∀ time,
      rank (cycle.vertex 0) < rank (cycle.vertex (time + 1)) := by
    intro time
    induction time with
    | zero => simpa using hstep 0
    | succ time ih => exact ih.trans (hstep (time + 1))
  have hperiod := hchain (cycle.period - 1)
  have hperiodPos := cycle.period_pos
  have hsucc : cycle.period - 1 + 1 = cycle.period := by omega
  rw [hsucc] at hperiod
  have hreturn := cycle.vertex_periodic 0
  simp only [zero_add] at hreturn
  rw [hreturn] at hperiod
  exact (Nat.lt_irrefl _ hperiod)

/-- The largest positive pair-collision premium against an owner's singleton
row.  Inserting zero makes the definition total when there is no outsider. -/
def quittingSoloPairPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) : ℝ :=
  Math.Finset.insertMax 0 (Finset.univ.erase owner) fun other =>
    quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other

/-- The collision premium is nonnegative by construction. -/
theorem quittingSoloPairPremium_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    0 ≤ quittingSoloPairPremium reward owner :=
  Math.Finset.base_le_insertMax _ _ _

/-- Every outsider's collision premium is bounded by the owner's clamped
maximum. -/
theorem quittingSingletonCollisionReward_sub_soloReward_le_pairPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) :
    quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other ≤
      quittingSoloPairPremium reward owner := by
  unfold quittingSoloPairPremium
  exact Math.Finset.le_insertMax 0
    (fun other => quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward owner other)
    (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ other⟩)

omit [DecidableEq ι] in
/-- Every finite acyclic augmented solo-preemption graph has a sink. -/
theorem exists_sink_of_isQuittingAugmentedSoloPreemptionAcyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hacyclic : IsQuittingAugmentedSoloPreemptionAcyclic reward) :
    ∃ sink : Option ι,
      ∀ target, ¬QuittingAugmentedSoloPreemptionEdge reward sink target := by
  by_contra hnot
  push Not at hnot
  exact hacyclic
    (Math.FiniteSerialRelation.nonempty_periodicCycle_of_serial
      (QuittingAugmentedSoloPreemptionEdge reward) hnot)

omit [DecidableEq ι] in
/-- The exact sink dispatch: either every own singleton payoff is nonpositive,
or some nonnegative owner singleton row weakly dominates each outsider's own
singleton payoff. -/
theorem isQuittingZeroSolo_or_exists_nonnegative_noHarmSingleton_of_acyclic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hacyclic : IsQuittingAugmentedSoloPreemptionAcyclic reward) :
    IsQuittingZeroSolo reward ∨
      ∃ owner : ι,
        0 ≤ quittingSoloReward reward owner owner ∧
          ∀ other, other ≠ owner →
            quittingSoloReward reward other other ≤
              quittingSoloReward reward owner other := by
  obtain ⟨sink, hsink⟩ :=
    exists_sink_of_isQuittingAugmentedSoloPreemptionAcyclic reward hacyclic
  cases sink with
  | none =>
      left
      intro who
      have hedge := hsink (some who)
      simp only [QuittingAugmentedSoloPreemptionEdge] at hedge
      exact le_of_not_gt hedge
  | some owner =>
      right
      refine ⟨owner, ?_, ?_⟩
      · have hedge := hsink none
        simp only [QuittingAugmentedSoloPreemptionEdge] at hedge
        exact le_of_not_gt hedge
      · intro other hne
        have hedge := hsink (some other)
        have hnot : ¬quittingSoloReward reward owner other <
            quittingSoloReward reward other other := fun hlt =>
          hedge ⟨hne, hlt⟩
        exact le_of_not_gt hnot

/-- Any terminal `ε`-Nash certificate bounds literal maximum all-behavior
terminal exploitability by `ε`. -/
theorem quittingTerminalExploitability_le_of_isεAsymptoticNash
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) :
    quittingTerminalExploitability reward profile ≤ ε := by
  unfold quittingTerminalExploitability
  apply QuittingBoundaryHolonomy.finitePlayerMax_le
  intro who
  apply max_le hε
  have hbest : quittingContinuationBestResponseValue reward profile who ≤
      quittingTerminalPayoff reward profile who + ε := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le
    · exact ⟨_, profile who, rfl⟩
    · rintro value ⟨deviation, rfl⟩
      exact hnash who deviation
  linarith

/-- Quantitative diffuse escape from a player sink.  Only the owner quits,
with live-date probability `q`; the profile controls every unilateral
behavioral deviation with error `q * quittingSoloPairPremium`. -/
theorem isεAsymptoticNash_soloStationary_le_pairPremium
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hnoHarm : ∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward)
      (q * quittingSoloPairPremium reward owner)
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin q hq0.le hq1))) := by
  let hazard := quittingHazardCoin q hq0.le hq1
  let premium := quittingSoloPairPremium reward owner
  have hpremium : 0 ≤ premium :=
    quittingSoloPairPremium_nonneg reward owner
  have herror : 0 ≤ q * premium := mul_nonneg hq0.le hpremium
  have hpositive : 0 < (hazard true).toReal := by
    simpa [hazard] using hq0
  intro who deviation
  rw [quittingTerminalPayoff_soloStationary reward owner who hazard hpositive]
  by_cases hwho : who = owner
  · subst who
    have hcap := quittingTerminalPayoff_update_solo_owner_le
      reward owner hazard deviation
    exact hcap.trans (by
      apply max_le
      · exact add_nonneg howner herror
      · exact le_add_of_nonneg_right herror)
  · have hcap :=
      quittingTerminalPayoff_update_stationary_le_unilateralCap
        reward (quittingSoloStationaryRoot owner hazard) who deviation
        (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
          hwho hazard hpositive)
    apply hcap.trans
    rw [quittingStationaryUnilateralCap_solo_other reward hwho hazard hpositive]
    apply max_le
    · rw [quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho hazard]
      have htrue : (hazard true).toReal = q := by simp [hazard]
      have hfalse : (hazard false).toReal = 1 - q := by simp [hazard]
      rw [htrue, hfalse]
      have hcontinue : 0 ≤ 1 - q := sub_nonneg.mpr hq1
      have hpremiumBound :=
        quittingSingletonCollisionReward_sub_soloReward_le_pairPremium
          reward hwho
      calc
        (1 - q) * quittingSoloReward reward who who +
              q * quittingSingletonCollisionReward reward owner who ≤
            (1 - q) * quittingSoloReward reward owner who +
              q * quittingSingletonCollisionReward reward owner who := by
          gcongr
          exact hnoHarm who hwho
        _ = quittingSoloReward reward owner who +
              q * (quittingSingletonCollisionReward reward owner who -
                quittingSoloReward reward owner who) := by ring
        _ ≤ quittingSoloReward reward owner who + q * premium := by
          gcongr
    · exact le_add_of_nonneg_right herror

/-- Literal maximum all-behavior exploitability obeys the same `q J` bound. -/
theorem terminalExploitability_soloStationary_le_pairPremium
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hnoHarm : ∀ other, other ≠ owner →
      quittingSoloReward reward other other ≤
        quittingSoloReward reward owner other) :
    quittingTerminalExploitability reward
        (quittingStationaryProfile reward
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin q hq0.le hq1))) ≤
      q * quittingSoloPairPremium reward owner := by
  apply quittingTerminalExploitability_le_of_isεAsymptoticNash
  · exact mul_nonneg hq0.le
      (quittingSoloPairPremium_nonneg reward owner)
  · exact isεAsymptoticNash_soloStationary_le_pairPremium
      reward owner hq0 hq1 howner hnoHarm

/-- **Acyclic augmented solo-preemption escape.**  Either all-Continue is an
exact terminal Nash profile, or one player is a sink and every positive solo
hazard supplies the packet's `q J` all-behavior bound.  The latter profile
delivers the fixed singleton payoff and every outsider surely Continues at
every live date; hence no pair coalition can absorb. -/
theorem exactTerminalNash_or_soloEscape_of_acyclic_augmentedSoloPreemption
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hacyclic : IsQuittingAugmentedSoloPreemptionAcyclic reward) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) 0
        (quittingAlwaysContinueProfile reward) ∨
      ∃ owner : ι,
        0 ≤ quittingSoloReward reward owner owner ∧
          (∀ other, other ≠ owner →
            quittingSoloReward reward other other ≤
              quittingSoloReward reward owner other) ∧
          ∀ (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1),
            let hazard := quittingHazardCoin q hq0.le hq1
            let profile := quittingStationaryProfile reward
              (quittingSoloStationaryRoot owner hazard)
            quittingTerminalExploitability reward profile ≤
                q * quittingSoloPairPremium reward owner ∧
              quittingTerminalPayoff reward profile =
                quittingSoloReward reward owner ∧
              ∀ other, other ≠ owner →
                quittingSoloStationaryRoot owner hazard other =
                  PMF.pure false := by
  rcases isQuittingZeroSolo_or_exists_nonnegative_noHarmSingleton_of_acyclic
      reward hacyclic with hzero | ⟨owner, howner, hnoHarm⟩
  · exact Or.inl
      (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo reward hzero)
  · right
    refine ⟨owner, howner, hnoHarm, ?_⟩
    intro q hq0 hq1
    dsimp only
    refine ⟨terminalExploitability_soloStationary_le_pairPremium
      reward owner hq0 hq1 howner hnoHarm, ?_, ?_⟩
    · funext who
      exact quittingTerminalPayoff_soloStationary reward owner who
        (quittingHazardCoin q hq0.le hq1) (by simpa using hq0)
    · intro other hne
      exact quittingSoloStationaryRoot_apply_other hne _

/-- A strict no-harm gap makes sufficiently small owner hazards exact. -/
theorem isεAsymptoticNash_soloStationary_exact_of_strictSink
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {gap q : ℝ} (_hgap : 0 < gap)
    (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hq : q * (gap + quittingSoloPairPremium reward owner) ≤ gap)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hstrict : ∀ other, other ≠ owner →
      gap ≤ quittingSoloReward reward owner other -
        quittingSoloReward reward other other) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin q hq0.le hq1))) := by
  apply isεAsymptoticNash_soloStationary_exact
    reward owner (quittingHazardCoin q hq0.le hq1)
  · simpa using hq0
  · exact howner
  · intro other hne
    rw [quittingHazardCoin_false_toReal, quittingHazardCoin_true_toReal]
    have hpremiumBound :=
      quittingSingletonCollisionReward_sub_soloReward_le_pairPremium
        reward hne
    have hgapBound := hstrict other hne
    nlinarith [_hgap]

/-- The acyclic augmented solo-preemption construction has stationary
strength: at every positive tolerance it supplies a stationary terminal
approximate equilibrium.  This retains the strategy provenance erased by the
uniform-payoff projection below. -/
theorem quittingStationaryεEquilibriumExistence_of_acyclic_augmentedSoloPreemption
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hacyclic : IsQuittingAugmentedSoloPreemptionAcyclic reward) :
    QuittingStationaryεEquilibriumExistence reward := by
  rcases isQuittingZeroSolo_or_exists_nonnegative_noHarmSingleton_of_acyclic
      reward hacyclic with hzero | ⟨owner, howner, hnoHarm⟩
  · intro ε hε
    refine ⟨quittingAllContinueRoot, ?_⟩
    change (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε
        (quittingAlwaysContinueProfile reward)
    exact (isZeroAsymptoticNash_quittingAlwaysContinue_of_zeroSolo
      reward hzero).mono hε.le
  · intro ε hε
    let premium := quittingSoloPairPremium reward owner
    let q := min (1 / 2 : ℝ) (ε / (2 * (premium + 1)))
    have hpremium : 0 ≤ premium :=
      quittingSoloPairPremium_nonneg reward owner
    have hdenominator : 0 < 2 * (premium + 1) := by positivity
    have hq0 : 0 < q := by
      dsimp only [q]
      exact lt_min (by norm_num) (div_pos hε hdenominator)
    have hq1 : q ≤ 1 :=
      (min_le_left _ _).trans (by norm_num)
    have hqSmall : q ≤ ε / (2 * (premium + 1)) := min_le_right _ _
    have hscaled : q * (premium + 1) ≤ ε / 2 := by
      calc
        q * (premium + 1) ≤
            (ε / (2 * (premium + 1))) * (premium + 1) := by
          gcongr
        _ = ε / 2 := by field_simp
    have herror : q * premium ≤ ε := by
      calc
        q * premium ≤ q * (premium + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hq0.le
        _ ≤ ε / 2 := hscaled
        _ ≤ ε := by linarith
    let hazard := quittingHazardCoin q hq0.le hq1
    let root := quittingSoloStationaryRoot owner hazard
    refine ⟨root, ?_⟩
    exact (isεAsymptoticNash_soloStationary_le_pairPremium
      reward owner hq0 hq1 howner hnoHarm).mono herror

/-- Consequently failure of branch `S.1` forces a directed periodic cycle in
the augmented solo-preemption graph. -/
theorem nonempty_augmentedSoloPreemptionCycle_of_not_stationaryExistence
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hstationary : ¬QuittingStationaryεEquilibriumExistence reward) :
    Nonempty (QuittingAugmentedSoloPreemptionCycle reward) := by
  by_contra hcycle
  exact hstationary
    (quittingStationaryεEquilibriumExistence_of_acyclic_augmentedSoloPreemption
      reward hcycle)

/-- The augmented acyclic class always has a uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_acyclic_augmentedSoloPreemption
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hacyclic : IsQuittingAugmentedSoloPreemptionAcyclic reward) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases isQuittingZeroSolo_or_exists_nonnegative_noHarmSingleton_of_acyclic
      reward hacyclic with hzero | ⟨owner, howner, hnoHarm⟩
  · exact exists_uniformEquilibriumPayoff_of_zeroSolo reward hzero
  · refine ⟨quittingSoloReward reward owner, ?_⟩
    apply quittingGame_isUniformEquilibriumPayoff_of_terminalNash_all_errors_fixedTarget
    intro ε hε
    let premium := quittingSoloPairPremium reward owner
    let q := min (1 / 2 : ℝ) (ε / (2 * (premium + 1)))
    have hpremium : 0 ≤ premium :=
      quittingSoloPairPremium_nonneg reward owner
    have hdenominator : 0 < 2 * (premium + 1) := by positivity
    have hq0 : 0 < q := by
      dsimp only [q]
      exact lt_min (by norm_num) (div_pos hε hdenominator)
    have hq1 : q ≤ 1 := by
      exact (min_le_left _ _).trans (by norm_num)
    have hqSmall : q ≤ ε / (2 * (premium + 1)) := min_le_right _ _
    have hscaled : q * (premium + 1) ≤ ε / 2 := by
      calc
        q * (premium + 1) ≤
            (ε / (2 * (premium + 1))) * (premium + 1) := by
          gcongr
        _ = ε / 2 := by field_simp
    have herror : q * premium ≤ ε := by
      calc
        q * premium ≤ q * (premium + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hq0.le
        _ ≤ ε / 2 := hscaled
        _ ≤ ε := by linarith
    let hazard := quittingHazardCoin q hq0.le hq1
    let profile := quittingStationaryProfile reward
      (quittingSoloStationaryRoot owner hazard)
    refine ⟨profile, ?_, ?_⟩
    · exact (isεAsymptoticNash_soloStationary_le_pairPremium
        reward owner hq0 hq1 howner hnoHarm).mono herror
    · funext who
      exact quittingTerminalPayoff_soloStationary
        reward owner who hazard (by simpa [hazard] using hq0)

end GameTheory
