/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.PeriodicCompiler
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass
import UniformEquilibrium.Quitting.Root.TailStability
import UniformEquilibrium.Quitting.Root.TerminalDebtGreenAccount

/-!
# Finite cyclic Green debt from opponent atom coverage

An approximate finite cyclic Nash--Bellman word selects an actual periodic
terminal payoff.  If every player is excluded from a positive nonempty
coalition atom at some phase, then the word has two distinct contractions:

* the largest atom floor contracts joint survival and controls attachment of
  the annotated values to the actual periodic values; and
* each player's own atom floor contracts that player's opponent-only Green
  account and controls unrestricted behavioral terminal debt.

Marked phases may depend on the player, may coincide, and carry no quietness
or own-face assumption.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {K : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Playerwise positive nonempty opponent atoms located anywhere in a finite
cyclic word. -/
structure QuittingCyclicOpponentAtomCover
    (cycle : Fin K → ι → PMF Bool) where
  floor : ι → ℝ
  markedPhase : ι → Fin K
  coalition : ι → Finset ι
  floor_pos : ∀ who, 0 < floor who
  coalition_nonempty : ∀ who, (coalition who).Nonempty
  excludes : ∀ who, who ∉ coalition who
  floor_le_mass : ∀ who,
    floor who ≤
      quittingRootCoalitionMass (cycle (markedPhase who)) (coalition who)

/-- The largest playerwise atom floor in a nonempty player set. -/
def QuittingCyclicOpponentAtomCover.maxFloor
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty cover.floor

theorem QuittingCyclicOpponentAtomCover.floor_le_maxFloor
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) (who : ι) :
    cover.floor who ≤ cover.maxFloor := by
  exact Finset.le_sup' cover.floor (Finset.mem_univ who)

theorem QuittingCyclicOpponentAtomCover.exists_floor_eq_maxFloor
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) :
    ∃ who, cover.floor who = cover.maxFloor := by
  obtain ⟨who, -, hwho⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty cover.floor
  exact ⟨who, hwho.symm⟩

theorem QuittingCyclicOpponentAtomCover.maxFloor_pos
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) :
    0 < cover.maxFloor := by
  obtain ⟨who, hwho⟩ := cover.exists_floor_eq_maxFloor
  rw [← hwho]
  exact cover.floor_pos who

omit [Nonempty ι] in
/-- A nonempty exact coalition atom is bounded by total root absorption. -/
theorem quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (root : ι → PMF Bool) (coalition : Finset ι)
    (hne : coalition.Nonempty) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootAbsorptionMass root := by
  obtain ⟨other, hother⟩ := hne
  have hatom := quittingRootCoalitionMass_le_quitProbability_of_mem
    root coalition other hother
  have hcontinue :=
    quittingStationaryContinueMass_le_ownContinueProbability root other
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability root other
  unfold quittingRootAbsorptionMass
  linarith

omit [Nonempty ι] in
/-- A nonempty exact coalition excluding `who` is bounded by absorption among
`who`'s opponents.  This is the elementary atom-to-Green adapter. -/
theorem quittingRootCoalitionMass_le_opponentAbsorptionMass_of_nonempty_excludes
    (root : ι → PMF Bool) (coalition : Finset ι) (who : ι)
    (hne : coalition.Nonempty) (hexcludes : who ∉ coalition) :
    quittingRootCoalitionMass root coalition ≤
      quittingRootOpponentAbsorptionMass root who := by
  obtain ⟨other, hother⟩ := hne
  have hother_ne : other ≠ who := by
    intro h
    subst other
    exact hexcludes hother
  have hatom := quittingRootCoalitionMass_le_quitProbability_of_mem
    root coalition other hother
  have hcontinue := quittingStationaryContinueMass_le_ownContinueProbability
    (Function.update root who (PMF.pure false)) other
  rw [Function.update_of_ne hother_ne] at hcontinue
  have hsum :=
    quittingRoot_continueProbability_add_quitProbability root other
  unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass
  linarith

/-- The largest covered atom contracts the product of joint continuation
masses around the cycle. -/
theorem QuittingCyclicOpponentAtomCover.prod_continueMass_le_one_sub_maxFloor
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) :
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) ≤
      1 - cover.maxFloor := by
  obtain ⟨who, hwho⟩ := cover.exists_floor_eq_maxFloor
  let marked := cover.markedPhase who
  have hsplit := Finset.mul_prod_erase Finset.univ
    (fun phase : Fin K ↦ quittingStationaryContinueMass (cycle phase))
    (Finset.mem_univ marked)
  have hrest : (∏ phase ∈ Finset.univ.erase marked,
      quittingStationaryContinueMass (cycle phase)) ≤ 1 :=
    Finset.prod_le_one
      (fun phase _ ↦ quittingStationaryContinueMass_nonneg (cycle phase))
      (fun phase _ ↦ quittingStationaryContinueMass_le_one (cycle phase))
  have hmarked0 : 0 ≤ quittingStationaryContinueMass (cycle marked) :=
    quittingStationaryContinueMass_nonneg _
  have hmass := cover.floor_le_mass who
  have habsorb := quittingRootCoalitionMass_le_absorptionMass_of_nonempty
    (cycle marked) (cover.coalition who) (cover.coalition_nonempty who)
  have hmarked : quittingStationaryContinueMass (cycle marked) ≤
      1 - cover.maxFloor := by
    rw [← hwho]
    unfold quittingRootAbsorptionMass at habsorb
    linarith
  calc
    (∏ phase : Fin K, quittingStationaryContinueMass (cycle phase)) =
        quittingStationaryContinueMass (cycle marked) *
          ∏ phase ∈ Finset.univ.erase marked,
            quittingStationaryContinueMass (cycle phase) := hsplit.symm
    _ ≤ quittingStationaryContinueMass (cycle marked) * 1 :=
      mul_le_mul_of_nonneg_left hrest hmarked0
    _ ≤ 1 - cover.maxFloor := by simpa using hmarked

omit [Nonempty ι] in
/-- A player's covered atom contracts the product of that player's
opponent-continuation masses around the cycle. -/
theorem QuittingCyclicOpponentAtomCover.prod_opponentContinueMass_le_one_sub_floor
    {cycle : Fin K → ι → PMF Bool}
    (cover : QuittingCyclicOpponentAtomCover cycle) (who : ι) :
    (∏ phase : Fin K,
      quittingStationaryFixedOpponentsContinueMass (cycle phase) who) ≤
        1 - cover.floor who := by
  let marked := cover.markedPhase who
  let coefficient : Fin K → ℝ := fun phase ↦
    quittingStationaryFixedOpponentsContinueMass (cycle phase) who
  have hsplit := Finset.mul_prod_erase Finset.univ coefficient
    (Finset.mem_univ marked)
  have hrest : (∏ phase ∈ Finset.univ.erase marked,
      coefficient phase) ≤ 1 :=
    Finset.prod_le_one
      (fun phase _ ↦
        quittingStationaryFixedOpponentsContinueMass_nonneg
          (cycle phase) who)
      (fun phase _ ↦ quittingStationaryContinueMass_le_one
        (Function.update (cycle phase) who (PMF.pure false)))
  have hmarked0 : 0 ≤ coefficient marked :=
    quittingStationaryFixedOpponentsContinueMass_nonneg _ _
  have hmass := cover.floor_le_mass who
  have habsorb :=
    quittingRootCoalitionMass_le_opponentAbsorptionMass_of_nonempty_excludes
      (cycle marked) (cover.coalition who) who
      (cover.coalition_nonempty who) (cover.excludes who)
  have hmarked : coefficient marked ≤ 1 - cover.floor who := by
    change quittingStationaryContinueMass
        (Function.update (cycle marked) who (PMF.pure false)) ≤ _
    unfold quittingRootOpponentAbsorptionMass quittingRootAbsorptionMass at habsorb
    linarith
  change (∏ phase : Fin K, coefficient phase) ≤ 1 - cover.floor who
  calc
    (∏ phase : Fin K, coefficient phase) = coefficient marked *
          ∏ phase ∈ Finset.univ.erase marked, coefficient phase :=
      hsplit.symm
    _ ≤ coefficient marked * 1 :=
      mul_le_mul_of_nonneg_left hrest hmarked0
    _ ≤ 1 - cover.floor who := by simpa using hmarked

/-- Coordinatewise attachment of an approximate cyclic Bellman annotation to
the actual terminal values selected by the periodic root profile. -/
theorem abs_sub_quittingCyclicTerminalValue_le_card_mul_div_maxFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (cover : QuittingCyclicOpponentAtomCover cycle)
    (value : Fin K → Payoff ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤ δ)
    (phase : Fin K) (who : ι) :
    |value phase who -
        quittingCyclicTerminalValue reward cycle phase who| ≤
      (K : ℝ) * δ / cover.maxFloor := by
  let terminal := quittingCyclicTerminalValue reward cycle
  let coefficient : Fin K → ℝ := fun cyclePhase ↦
    quittingStationaryContinueMass (cycle cyclePhase)
  let difference : Fin K → ℝ := fun cyclePhase ↦
    value cyclePhase who - terminal cyclePhase who
  have hcoefficient0 : ∀ cyclePhase, 0 ≤ coefficient cyclePhase :=
    fun cyclePhase ↦ quittingStationaryContinueMass_nonneg _
  have hcoefficient1 : ∀ cyclePhase, coefficient cyclePhase ≤ 1 :=
    fun cyclePhase ↦ quittingStationaryContinueMass_le_one _
  have hstep : ∀ cyclePhase,
      |difference cyclePhase| ≤ δ +
        coefficient cyclePhase *
          |difference (finRotate K cyclePhase)| := by
    intro cyclePhase
    have hterminal := congrFun
      (quittingCyclicTerminalValue_eq_rootSuccessorPayoff
        reward cycle cyclePhase) who
    have hsplit : difference cyclePhase =
        (value cyclePhase who -
          quittingRootSuccessorPayoff reward
            (value (finRotate K cyclePhase)) (cycle cyclePhase) who) +
        (quittingRootSuccessorPayoff reward
            (value (finRotate K cyclePhase)) (cycle cyclePhase) who -
          quittingRootSuccessorPayoff reward
            (terminal (finRotate K cyclePhase))
            (cycle cyclePhase) who) := by
      dsimp only [difference, terminal]
      rw [hterminal]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add (hpolicy cyclePhase who) ?_)
    rw [quittingRootSuccessorPayoff_sub_eq_continueMass_mul,
      abs_mul, abs_of_nonneg (quittingStationaryContinueMass_nonneg _)]
  have hunroll := cyclicValue_le_residualCharge_add_weight
    coefficient (fun _ ↦ δ) (fun cyclePhase ↦ |difference cyclePhase|)
    hcoefficient0 hstep phase K
  rw [quittingCyclicPrefixWeight_card, quittingCyclicOrbit_card] at hunroll
  have hcharge :
      quittingCyclicResidualCharge coefficient (fun _ ↦ δ) phase K ≤
        (K : ℝ) * δ := by
    unfold quittingCyclicResidualCharge
    calc
      (∑ offset ∈ Finset.range K,
          quittingCyclicPrefixWeight coefficient phase offset * δ) ≤
          ∑ _offset ∈ Finset.range K, δ := by
        apply Finset.sum_le_sum
        intro offset _
        have hweight := (antitone_quittingCyclicPrefixWeight
          coefficient hcoefficient0 hcoefficient1 phase)
          (Nat.zero_le offset)
        simp only [quittingCyclicPrefixWeight_zero] at hweight
        exact mul_le_of_le_one_left hδ hweight
      _ = (K : ℝ) * δ := by simp
  have hproduct := cover.prod_continueMass_le_one_sub_maxFloor
  have hscaled := mul_le_mul_of_nonneg_right hproduct
    (abs_nonneg (difference phase))
  have hfloor := cover.maxFloor_pos
  apply (le_div_iff₀ hfloor).2
  nlinarith

/-- Sup-norm form of cyclic value attachment. -/
theorem norm_sub_quittingCyclicTerminalValue_le_card_mul_div_maxFloor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (cover : QuittingCyclicOpponentAtomCover cycle)
    (value : Fin K → Payoff ι) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤ δ)
    (phase : Fin K) :
    ‖value phase - quittingCyclicTerminalValue reward cycle phase‖ ≤
      (K : ℝ) * δ / cover.maxFloor := by
  have hbound0 : 0 ≤ (K : ℝ) * δ / cover.maxFloor :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) cover.maxFloor_pos.le
  apply (pi_norm_le_iff_of_nonneg hbound0).2
  intro who
  simpa [Real.norm_eq_abs] using
    abs_sub_quittingCyclicTerminalValue_le_card_mul_div_maxFloor
      reward cycle cover value hδ hpolicy phase who

/-- Tail stability turns local Nash error against the annotation into local
Nash defect against the actual periodic continuation. -/
theorem quittingRootCoordinateNashDefect_cyclicTerminalValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (cover : QuittingCyclicOpponentAtomCover cycle)
    (value : Fin K → Payoff ι) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤ δ)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (value (finRotate K phase)) ε (cycle phase))
    (phase : Fin K) (who : ι) :
    quittingRootCoordinateNashDefect reward
        (quittingCyclicTerminalValue reward cycle (finRotate K phase))
        (cycle phase) who ≤
      ε + (K : ℝ) * δ / cover.maxFloor := by
  let attachment := (K : ℝ) * δ / cover.maxFloor
  have hattachment0 : 0 ≤ attachment :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) cover.maxFloor_pos.le
  have hclose : ∀ player,
      |value (finRotate K phase) player -
        quittingCyclicTerminalValue reward cycle
          (finRotate K phase) player| ≤ attachment := by
    intro player
    exact abs_sub_quittingCyclicTerminalValue_le_card_mul_div_maxFloor
      reward cycle cover value hδ hpolicy (finRotate K phase) player
  have hendpoint : IsεQuittingRootEndpointNash reward
      (value (finRotate K phase)) ε (cycle phase) :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (value (finRotate K phase)) ε (cycle phase)).2 (hnash phase)
  have hactualEndpoint := isεQuittingRootEndpointNash_of_tail_close
    reward (value (finRotate K phase))
      (quittingCyclicTerminalValue reward cycle (finRotate K phase))
      (cycle phase) hattachment0 hendpoint hclose
  have hactualNash :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (quittingCyclicTerminalValue reward cycle (finRotate K phase))
      (ε + attachment) (cycle phase)).1 hactualEndpoint
  exact (isεQuittingRootNash_iff_coordinateNashDefect_le
    reward (quittingCyclicTerminalValue reward cycle (finRotate K phase))
      (ε + attachment) (cycle phase)).1 hactualNash who

omit [Nonempty ι] in
/-- Actual coordinate defect at a time in a cyclic root sequence is the
coordinate defect at the corresponding phase against the actual next-phase
terminal value. -/
theorem quittingRootSequenceActualCoordinateDefect_cyclic_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (initial : Fin K) (who : ι) (time : ℕ) :
    quittingRootSequenceActualCoordinateDefect reward
        (quittingCyclicRootSequence cycle initial) who time =
      quittingRootCoordinateNashDefect reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate K (quittingCyclicOrbit initial time)))
        (cycle (quittingCyclicOrbit initial time)) who := by
  unfold quittingRootSequenceActualCoordinateDefect
  congr 2
  · funext player
    change quittingRootSequenceTerminalValue reward
        (quittingCyclicRootSequence cycle initial) player (time + 1) = _
    rw [quittingRootSequenceTerminalValue_cyclic_eq,
      quittingCyclicOrbit_succ]

omit [Nonempty ι] in
/-- Terminal debt of a cyclic root sequence is unchanged after one full
period. -/
theorem quittingRootSequenceTerminalDebt_cyclic_card
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (initial : Fin K) (who : ι) :
    quittingRootSequenceTerminalDebt reward
        (quittingCyclicRootSequence cycle initial) who K =
      quittingRootSequenceTerminalDebt reward
        (quittingCyclicRootSequence cycle initial) who 0 := by
  unfold quittingRootSequenceTerminalDebt
  congr 1
  funext player time history
  unfold quittingRootSequenceProfile
  change cycle (quittingCyclicOrbit initial (K + time)) player =
    cycle (quittingCyclicOrbit initial (0 + time)) player
  rw [zero_add, quittingCyclicOrbit_add, quittingCyclicOrbit_card]

/-- General finite-cycle Green theorem.  The debt on the left is the
unrestricted behavioral terminal deviation debt of the actual periodic
profile, not a cap restricted to periodic or pure-time deviations. -/
theorem quittingRootSequenceTerminalDebt_cyclic_le_card_div_floor_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (cover : QuittingCyclicOpponentAtomCover cycle)
    (value : Fin K → Payoff ι) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤ δ)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (value (finRotate K phase)) ε (cycle phase))
    (initial : Fin K) (who : ι) :
    quittingRootSequenceTerminalDebt reward
        (quittingCyclicRootSequence cycle initial) who 0 ≤
      (K : ℝ) / cover.floor who *
        (ε + (K : ℝ) * δ / cover.maxFloor) := by
  let roots := quittingCyclicRootSequence cycle initial
  let η := ε + (K : ℝ) * δ / cover.maxFloor
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    exact add_nonneg hε
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ)
        cover.maxFloor_pos.le)
  have hdefect : ∀ time,
      quittingRootSequenceActualCoordinateDefect reward roots who time ≤ η := by
    intro time
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl,
      quittingRootSequenceActualCoordinateDefect_cyclic_eq]
    exact quittingRootCoordinateNashDefect_cyclicTerminalValue_le
      reward cycle cover value hδ hpolicy hnash
        (quittingCyclicOrbit initial time) who
  have hsum :
      (∑ offset ∈ Finset.range K,
        quittingOpponentSurvivalWeight roots who 0 offset *
          quittingRootSequenceActualCoordinateDefect reward roots who offset) ≤
        (K : ℝ) * η := by
    calc
      (∑ offset ∈ Finset.range K,
          quittingOpponentSurvivalWeight roots who 0 offset *
            quittingRootSequenceActualCoordinateDefect reward roots who offset) ≤
          ∑ _offset ∈ Finset.range K, η := by
        apply Finset.sum_le_sum
        intro offset _
        have hweight0 :=
          quittingOpponentSurvivalWeight_nonneg roots who 0 offset
        have hweight1 :=
          quittingOpponentSurvivalWeight_le_one roots who 0 offset
        calc
          quittingOpponentSurvivalWeight roots who 0 offset *
              quittingRootSequenceActualCoordinateDefect reward roots who offset ≤
              quittingOpponentSurvivalWeight roots who 0 offset * η :=
            mul_le_mul_of_nonneg_left (hdefect offset) hweight0
          _ ≤ 1 * η := mul_le_mul_of_nonneg_right hweight1 hη0
          _ = η := one_mul _
      _ = (K : ℝ) * η := by simp
  have hweight :
      quittingOpponentSurvivalWeight roots who 0 K ≤
        1 - cover.floor who := by
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl,
      quittingOpponentSurvivalWeight_cyclicRootSequence]
    simp only [quittingCyclicOrbit_zero, quittingCyclicPrefixWeight_card]
    exact cover.prod_opponentContinueMass_le_one_sub_floor who
  have hfinite :=
    quittingRootSequenceTerminalDebt_le_opponentGreenDefectSum_add_tail
      reward roots who 0 K
  have hperiod : quittingRootSequenceTerminalDebt reward roots who K =
      quittingRootSequenceTerminalDebt reward roots who 0 := by
    rw [show roots = quittingCyclicRootSequence cycle initial by rfl]
    exact quittingRootSequenceTerminalDebt_cyclic_card
      reward cycle initial who
  simp only [zero_add] at hfinite
  rw [hperiod] at hfinite
  have hdebt0 : 0 ≤ quittingRootSequenceTerminalDebt reward roots who 0 :=
    quittingTerminalDeviationDebt_nonneg reward
      (quittingRootSequenceProfile reward roots 0) who
  have htail := mul_le_mul_of_nonneg_right hweight hdebt0
  have hfloor := cover.floor_pos who
  change quittingRootSequenceTerminalDebt reward roots who 0 ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hfloor).2
  nlinarith [hfinite, hsum, htail]

/-- Combined statement of the sharp global attachment estimate and the
playerwise unrestricted behavioral-debt estimate. -/
theorem quittingCyclic_norm_attachment_and_terminalDebt_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cycle : Fin K → ι → PMF Bool)
    (cover : QuittingCyclicOpponentAtomCover cycle)
    (value : Fin K → Payoff ι) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hpolicy : ∀ phase who,
      |value phase who -
        quittingRootSuccessorPayoff reward
          (value (finRotate K phase)) (cycle phase) who| ≤ δ)
    (hnash : ∀ phase,
      IsεQuittingRootNash reward
        (value (finRotate K phase)) ε (cycle phase))
    (initial : Fin K) :
    ‖value initial - quittingCyclicTerminalValue reward cycle initial‖ ≤
        (K : ℝ) * δ / cover.maxFloor ∧
      ∀ who,
        quittingRootSequenceTerminalDebt reward
            (quittingCyclicRootSequence cycle initial) who 0 ≤
          (K : ℝ) / cover.floor who *
            (ε + (K : ℝ) * δ / cover.maxFloor) := by
  refine ⟨norm_sub_quittingCyclicTerminalValue_le_card_mul_div_maxFloor
    reward cycle cover value hδ hpolicy initial, ?_⟩
  intro who
  exact quittingRootSequenceTerminalDebt_cyclic_le_card_div_floor_mul
    reward cycle cover value hε hδ hpolicy hnash initial who

end GameTheory
