import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# Cleared endpoint gaps for period-three quitting blocks

This module records the algebra linking the usual three-phase closed form to
the semantic endpoint differences used by the unrestricted behavioral
periodic compiler.  It is independent of any concrete reward table or support
word.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- The unconditional immediate terminal contribution at one phase. -/
def quittingPeriodThreeImmediateContribution
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) (who : Player) : ℝ :=
  ∑ coalition : Finset Player,
    coalitionMass (hazard phase) coalition * weightOfReward reward coalition who

/-- The joint Continue mass at one phase. -/
def quittingPeriodThreeContinueMass
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) : ℝ :=
  continueMass (hazard phase)

/-- The probability of absorption during one full period, written from phase
zero. -/
def quittingPeriodThreeAbsorptionDenominator
    (hazard : Fin 3 → Player → ℝ) : ℝ :=
  1 - quittingPeriodThreeContinueMass hazard 0 *
    quittingPeriodThreeContinueMass hazard 1 *
      quittingPeriodThreeContinueMass hazard 2

/-- Immediate rewards accumulated over the next three phases, without the
geometric repetitions of the period. -/
def quittingPeriodThreeImmediateWindow
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) : Fin 3 → Payoff Player
  | 0, who =>
      quittingPeriodThreeImmediateContribution reward hazard 0 who +
        quittingPeriodThreeContinueMass hazard 0 *
          quittingPeriodThreeImmediateContribution reward hazard 1 who +
        quittingPeriodThreeContinueMass hazard 0 *
          quittingPeriodThreeContinueMass hazard 1 *
            quittingPeriodThreeImmediateContribution reward hazard 2 who
  | 1, who =>
      quittingPeriodThreeImmediateContribution reward hazard 1 who +
        quittingPeriodThreeContinueMass hazard 1 *
          quittingPeriodThreeImmediateContribution reward hazard 2 who +
        quittingPeriodThreeContinueMass hazard 1 *
          quittingPeriodThreeContinueMass hazard 2 *
            quittingPeriodThreeImmediateContribution reward hazard 0 who
  | 2, who =>
      quittingPeriodThreeImmediateContribution reward hazard 2 who +
        quittingPeriodThreeContinueMass hazard 2 *
          quittingPeriodThreeImmediateContribution reward hazard 0 who +
        quittingPeriodThreeContinueMass hazard 2 *
          quittingPeriodThreeContinueMass hazard 0 *
            quittingPeriodThreeImmediateContribution reward hazard 1 who

/-- The closed-form phase values of an absorbing period-three block. -/
def quittingPeriodThreeClosedValue
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) : Payoff Player :=
  fun who => quittingPeriodThreeImmediateWindow reward hazard phase who /
    quittingPeriodThreeAbsorptionDenominator hazard

omit [DecidableEq Player] in
/-- The phase-zero denominator is invariant under cyclic rotation. -/
theorem quittingPeriodThreeAbsorptionDenominator_eq_rotated
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) :
    quittingPeriodThreeAbsorptionDenominator hazard =
      1 - quittingPeriodThreeContinueMass hazard phase *
        quittingPeriodThreeContinueMass hazard (finRotate 3 phase) *
          quittingPeriodThreeContinueMass hazard
            (finRotate 3 (finRotate 3 phase)) := by
  fin_cases phase <;>
    simp [quittingPeriodThreeAbsorptionDenominator, finRotate_apply] <;>
    ring

/-- The three-phase numerator satisfies the denominator-cleared Bellman
recursion. -/
theorem quittingPeriodThreeImmediateWindow_recursion
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) (who : Player) :
    quittingPeriodThreeImmediateWindow reward hazard phase who =
      quittingPeriodThreeAbsorptionDenominator hazard *
          quittingPeriodThreeImmediateContribution reward hazard phase who +
        quittingPeriodThreeContinueMass hazard phase *
          quittingPeriodThreeImmediateWindow reward hazard
            (finRotate 3 phase) who := by
  fin_cases phase <;>
    simp [quittingPeriodThreeImmediateWindow,
      quittingPeriodThreeAbsorptionDenominator,
      quittingPeriodThreeContinueMass, finRotate_apply] <;>
    ring

/-- With positive one-cycle absorption, the closed form solves the exact
phasewise policy recursion. -/
theorem isQuittingBlockOnPathValue_quittingPeriodThreeClosedValue
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ)
    (hdenominator : quittingPeriodThreeAbsorptionDenominator hazard ≠ 0) :
    IsQuittingBlockOnPathValue reward hazard
      (quittingPeriodThreeClosedValue reward hazard) := by
  intro phase who
  rw [show (∑ coalition : Finset Player,
      coalitionMass (hazard phase) coalition *
        weightOfReward reward coalition who) =
      quittingPeriodThreeImmediateContribution reward hazard phase who from rfl]
  rw [show continueMass (hazard phase) =
      quittingPeriodThreeContinueMass hazard phase from rfl]
  unfold quittingPeriodThreeClosedValue
  rw [div_eq_iff hdenominator]
  rw [quittingPeriodThreeImmediateWindow_recursion]
  field_simp

omit [DecidableEq Player] in
/-- The displayed denominator is exactly one minus the product of the three
phase Continue masses. -/
theorem prod_continueMass_eq_one_sub_quittingPeriodThreeAbsorptionDenominator
    (hazard : Fin 3 → Player → ℝ) :
    (∏ phase : Fin 3, continueMass (hazard phase)) =
      1 - quittingPeriodThreeAbsorptionDenominator hazard := by
  simp [quittingPeriodThreeAbsorptionDenominator,
    quittingPeriodThreeContinueMass, Fin.prod_univ_succ]
  ring

/-- The closed form is the actual cyclic terminal value whenever the block
absorbs over one period. -/
theorem quittingPeriodThreeClosedValue_eq_cyclicTerminalValue
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ)
    (h0 : ∀ phase who, 0 ≤ hazard phase who)
    (h1 : ∀ phase who, hazard phase who ≤ 1)
    (hdenominator : 0 < quittingPeriodThreeAbsorptionDenominator hazard) :
    quittingPeriodThreeClosedValue reward hazard =
      quittingCyclicTerminalValue reward
        (quittingBlockCycle hazard h0 h1) := by
  apply eq_cyclicTerminalValue_of_isQuittingBlockOnPathValue_of_absorbing
    h0 h1
  · exact isQuittingBlockOnPathValue_quittingPeriodThreeClosedValue reward hazard
      hdenominator.ne'
  · rw [prod_continueMass_eq_one_sub_quittingPeriodThreeAbsorptionDenominator]
    linarith

/-- The denominator-cleared pure-Quit minus pure-Continue endpoint gap. -/
def quittingPeriodThreeClearedEndpointDifference
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) (phase : Fin 3) (who : Player) : ℝ :=
  quittingPeriodThreeAbsorptionDenominator hazard *
      (sigmaValue (weightOfReward reward) (hazard phase) who -
        excludedValue (weightOfReward reward) (hazard phase) who) -
    continueMassExcl (hazard phase) who *
      quittingPeriodThreeImmediateWindow reward hazard
        (finRotate 3 phase) who

/-- Clearing the positive absorption denominator preserves the exact semantic
Quit-minus-Continue endpoint difference. -/
theorem quittingPeriodThreeClearedEndpointDifference_eq_mul_endpointDifference
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ)
    (h0 : ∀ phase who, 0 ≤ hazard phase who)
    (h1 : ∀ phase who, hazard phase who ≤ 1)
    (hdenominator : quittingPeriodThreeAbsorptionDenominator hazard ≠ 0)
    (phase : Fin 3) (who : Player) :
    quittingPeriodThreeClearedEndpointDifference reward hazard phase who =
      quittingPeriodThreeAbsorptionDenominator hazard *
        quittingRootEndpointDifference reward
          (quittingPeriodThreeClosedValue reward hazard (finRotate 3 phase))
          (quittingBlockCycle hazard h0 h1 phase) who := by
  rw [quittingRootEndpointDifference_quittingBlockCycle reward h0 h1]
  simp only [gainValue, gammaValue, quittingPeriodThreeClosedValue]
  unfold quittingPeriodThreeClearedEndpointDifference
  field_simp
  ring

/-- Under positive absorption, signs and zeroes of cleared gaps are exactly
the corresponding signs and zeroes of semantic endpoint differences. -/
theorem quittingPeriodThreeClearedEndpointDifference_signs
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ)
    (h0 : ∀ phase who, 0 ≤ hazard phase who)
    (h1 : ∀ phase who, hazard phase who ≤ 1)
    (hdenominator : 0 < quittingPeriodThreeAbsorptionDenominator hazard)
    (phase : Fin 3) (who : Player) :
    let cleared :=
      quittingPeriodThreeClearedEndpointDifference reward hazard phase who
    let semantic := quittingRootEndpointDifference reward
      (quittingPeriodThreeClosedValue reward hazard (finRotate 3 phase))
      (quittingBlockCycle hazard h0 h1 phase) who
    (cleared = 0 ↔ semantic = 0) ∧
      (cleared < 0 ↔ semantic < 0) ∧
      (0 < cleared ↔ 0 < semantic) := by
  dsimp only
  rw [quittingPeriodThreeClearedEndpointDifference_eq_mul_endpointDifference
    reward hazard h0 h1 hdenominator.ne']
  constructor
  · exact mul_eq_zero_iff_left hdenominator.ne'
  constructor
  · constructor
    · intro hproduct
      exact lt_of_not_ge fun hsemantic =>
        (not_lt_of_ge (mul_nonneg hdenominator.le hsemantic)) hproduct
    · exact mul_neg_of_pos_of_neg hdenominator
  · constructor
    · intro hproduct
      exact lt_of_not_ge fun hsemantic =>
        (not_lt_of_ge
          (mul_nonpos_of_nonneg_of_nonpos hdenominator.le hsemantic)) hproduct
    · exact mul_pos hdenominator

/-- Cleared endpoint complementarity for every player at every phase.  This
is the denominator-free form of exact one-step Nash: Continue mass times the
gap is nonpositive and Quit mass times the gap is nonnegative. -/
def IsQuittingPeriodThreeClearedGapComplementary
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ) : Prop :=
  ∀ phase who,
    (1 - hazard phase who) *
          quittingPeriodThreeClearedEndpointDifference reward hazard phase who ≤ 0 ∧
      0 ≤ hazard phase who *
        quittingPeriodThreeClearedEndpointDifference reward hazard phase who

/-- A contracting period-three block whose cleared endpoint gaps satisfy
exact complementarity yields an unrestricted behavioral uniform-equilibrium
payoff at every selected initial phase. -/
theorem isUniformEquilibriumPayoff_of_periodThreeClearedGapComplementarity
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (hazard : Fin 3 → Player → ℝ)
    (h0 : ∀ phase who, 0 ≤ hazard phase who)
    (h1 : ∀ phase who, hazard phase who ≤ 1)
    (hdenominator : 0 < quittingPeriodThreeAbsorptionDenominator hazard)
    (hcomplementary :
      IsQuittingPeriodThreeClearedGapComplementary reward hazard)
    (hcontracts : ∀ who,
      (∏ phase : Fin 3,
        quittingStationaryFixedOpponentsContinueMass
          (quittingBlockCycle hazard h0 h1 phase) who) < 1)
    (initial : Fin 3) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingCyclicTerminalValue reward
        (quittingBlockCycle hazard h0 h1) initial) := by
  let value := quittingPeriodThreeClosedValue reward hazard
  have hvalue : IsQuittingBlockOnPathValue reward hazard value :=
    isQuittingBlockOnPathValue_quittingPeriodThreeClosedValue
      reward hazard hdenominator.ne'
  have hpolicy : ∀ phase,
      value phase = quittingRootSuccessorPayoff reward
        (value (finRotate 3 phase))
        (quittingBlockCycle hazard h0 h1 phase) :=
    (isQuittingBlockOnPathValue_iff_rootSuccessorPayoff h0 h1 value).mp hvalue
  have hnash : ∀ phase,
      IsεQuittingRootNash reward (value (finRotate 3 phase)) 0
        (quittingBlockCycle hazard h0 h1 phase) := by
    intro phase
    rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    intro who
    let semantic := quittingRootEndpointDifference reward
      (value (finRotate 3 phase))
      (quittingBlockCycle hazard h0 h1 phase) who
    have hcleared :
        quittingPeriodThreeClearedEndpointDifference reward hazard phase who =
          quittingPeriodThreeAbsorptionDenominator hazard * semantic := by
      simpa [value, semantic] using
        quittingPeriodThreeClearedEndpointDifference_eq_mul_endpointDifference
          reward hazard h0 h1 hdenominator.ne' phase who
    have hsign := hcomplementary phase who
    rw [hcleared] at hsign
    have hcontinueScaled :
        quittingPeriodThreeAbsorptionDenominator hazard *
            ((1 - hazard phase who) * semantic) ≤ 0 := by
      calc
        quittingPeriodThreeAbsorptionDenominator hazard *
              ((1 - hazard phase who) * semantic) =
            (1 - hazard phase who) *
              (quittingPeriodThreeAbsorptionDenominator hazard * semantic) := by ring
        _ ≤ 0 := hsign.1
    have hquitScaled :
        0 ≤ quittingPeriodThreeAbsorptionDenominator hazard *
          (hazard phase who * semantic) := by
      calc
        0 ≤ hazard phase who *
            (quittingPeriodThreeAbsorptionDenominator hazard * semantic) := hsign.2
        _ = quittingPeriodThreeAbsorptionDenominator hazard *
            (hazard phase who * semantic) := by ring
    have hcontinue : (1 - hazard phase who) * semantic ≤ 0 := by
      by_contra hpositive
      have : 0 < (1 - hazard phase who) * semantic := lt_of_not_ge hpositive
      exact (not_lt_of_ge hcontinueScaled) (mul_pos hdenominator this)
    have hquit : 0 ≤ hazard phase who * semantic := by
      by_contra hnegative
      have : hazard phase who * semantic < 0 := lt_of_not_ge hnegative
      exact (not_lt_of_ge hquitScaled) (mul_neg_of_pos_of_neg hdenominator this)
    rw [quittingBlockCycle_false, quittingBlockCycle_true, neg_zero]
    simpa [semantic] using And.intro hcontinue hquit
  exact isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward (quittingBlockCycle hazard h0 h1) value initial hpolicy hnash hcontracts

/-- One positive opponent hazard anywhere in a finite block cycle gives the
strict fixed-opponent contraction required for that player. -/
theorem prod_fixedOpponentsContinueMass_quittingBlockCycle_lt_one_of_pos
    {period : ℕ} {hazard : Fin (period + 1) → Player → ℝ}
    (h0 : ∀ phase who, 0 ≤ hazard phase who)
    (h1 : ∀ phase who, hazard phase who ≤ 1)
    (who other : Player) (phase : Fin (period + 1))
    (hother : other ≠ who) (hpositive : 0 < hazard phase other) :
    (∏ cyclePhase : Fin (period + 1),
      quittingStationaryFixedOpponentsContinueMass
        (quittingBlockCycle hazard h0 h1 cyclePhase) who) < 1 := by
  let cycle := quittingBlockCycle hazard h0 h1
  have hfactor0 : ∀ cyclePhase,
      0 ≤ quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) who :=
    fun cyclePhase =>
      quittingStationaryFixedOpponentsContinueMass_nonneg _ _
  have hfactor1 : ∀ cyclePhase,
      quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who ≤ 1 :=
    fun cyclePhase => quittingStationaryContinueMass_le_one
      (Function.update (cycle cyclePhase) who (PMF.pure false))
  have hphase :
      quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who < 1 := by
    rw [quittingStationaryFixedOpponentsContinueMass_quittingBlockCycle]
    apply continueMass_lt_one_of_pos (i₀ := other)
      (quittingBlockDeletedHazard_nonneg h0 who phase)
      (quittingBlockDeletedHazard_le_one h1 who phase)
    simpa [quittingBlockDeletedHazard, Function.update_of_ne hother] using
      hpositive
  exact Math.Finset.prod_lt_one_of_mem Finset.univ
    (fun cyclePhase =>
      quittingStationaryFixedOpponentsContinueMass
        (cycle cyclePhase) who)
    phase (Finset.mem_univ phase)
    (fun cyclePhase _ _ => hfactor0 cyclePhase)
    (fun cyclePhase _ _ => hfactor1 cyclePhase) hphase

end GameTheory

end
