import MathUE.Topology.RectangularPoincareMiranda
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# Periodic quitting blocks from rectangular face signs

A continuous active-gap field with strict opposite signs on the faces of a
coordinate rectangle has an interior zero.  Pointwise identification of its
coordinates with the semantic endpoint gaps, strict inactive Continue gaps,
and one positive opponent hazard per player then give an unrestricted
behavioral uniform-equilibrium payoff through the periodic compiler.
-/

noncomputable section

open Function Set

namespace GameTheory

open Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {n period : ℕ}
variable {Player : Type} [Fintype Player] [DecidableEq Player]

/-- A phase/player pair occurs in the supplied active-coordinate
enumeration. -/
def IsEnumeratedPeriodicActiveSlot
    (slot : Fin n → Fin (period + 1) × Player)
    (phase : Fin (period + 1)) (who : Player) : Prop :=
  ∃ coordinate, slot coordinate = (phase, who)

/-- A rectangular strict-face sign argument supplies an exact periodic
quitting block and its unrestricted behavioral uniform-equilibrium payoff.

The active-gap adapter is pointwise: a zero of one field coordinate must
identify the corresponding semantic endpoint gap as zero.  It need not make
any global or uniqueness assertion about the field. -/
theorem exists_uniformEquilibriumPayoff_of_periodic_rectangular_face_signs
    (reward : {coalition : Finset Player // coalition.Nonempty} → Payoff Player)
    (lower upper : Fin n → ℝ)
    (field : (Fin n → ℝ) → Fin n → ℝ)
    (hazard : (Fin n → ℝ) → Fin (period + 1) → Player → ℝ)
    (slot : Fin n → Fin (period + 1) × Player)
    (initial : Fin (period + 1))
    (hlowerUpper : ∀ coordinate, lower coordinate < upper coordinate)
    (hfield : Continuous field)
    (hlower : ∀ x ∈ Icc lower upper, ∀ coordinate,
      x coordinate = lower coordinate → field x coordinate < 0)
    (hupper : ∀ x ∈ Icc lower upper, ∀ coordinate,
      x coordinate = upper coordinate → 0 < field x coordinate)
    (hhazard0 : ∀ x ∈ Icc lower upper, ∀ phase who,
      0 ≤ hazard x phase who)
    (hhazard1 : ∀ x ∈ Icc lower upper, ∀ phase who,
      hazard x phase who ≤ 1)
    (hactivePos : ∀ x ∈ Icc lower upper, ∀ coordinate,
      0 < hazard x (slot coordinate).1 (slot coordinate).2)
    (hinactiveHazard : ∀ x ∈ Icc lower upper, ∀ phase who,
      ¬ IsEnumeratedPeriodicActiveSlot slot phase who →
        hazard x phase who = 0)
    (hactiveGap : ∀ x (hx : x ∈ Icc lower upper) coordinate,
      field x coordinate = 0 →
        quittingRootEndpointDifference reward
          (quittingCyclicTerminalValue reward
            (quittingBlockCycle (hazard x) (hhazard0 x hx)
              (hhazard1 x hx))
            (finRotate (period + 1) (slot coordinate).1))
          (quittingBlockCycle (hazard x) (hhazard0 x hx)
            (hhazard1 x hx) (slot coordinate).1)
          (slot coordinate).2 = 0)
    (hinactiveGap : ∀ x (hx : x ∈ Icc lower upper), ∀ phase who,
      ¬ IsEnumeratedPeriodicActiveSlot slot phase who →
        quittingRootEndpointDifference reward
          (quittingCyclicTerminalValue reward
            (quittingBlockCycle (hazard x) (hhazard0 x hx)
              (hhazard1 x hx))
            (finRotate (period + 1) phase))
          (quittingBlockCycle (hazard x) (hhazard0 x hx)
            (hhazard1 x hx) phase) who < 0)
    (hopponent : ∀ who, ∃ coordinate, (slot coordinate).2 ≠ who) :
    ∃ x ∈ Icc lower upper,
      (∀ coordinate,
        lower coordinate < x coordinate ∧ x coordinate < upper coordinate) ∧
      (∀ coordinate, field x coordinate = 0) ∧
      ∃ h0 : ∀ phase who, 0 ≤ hazard x phase who,
      ∃ h1 : ∀ phase who, hazard x phase who ≤ 1,
        let cycle := quittingBlockCycle (hazard x) h0 h1
        (∀ phase, IsεQuittingRootNash reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate (period + 1) phase)) 0 (cycle phase)) ∧
        (∀ who,
          (∏ phase : Fin (period + 1),
            quittingStationaryFixedOpponentsContinueMass
              (cycle phase) who) < 1) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none
          (quittingCyclicTerminalValue reward cycle initial) := by
  obtain ⟨x, hx, hinterior, hzero⟩ :=
    Math.Topology.exists_rectangular_zero_of_strict_face_signs
      lower upper field hlowerUpper hfield hlower hupper
  let h0 : ∀ phase who, 0 ≤ hazard x phase who := hhazard0 x hx
  let h1 : ∀ phase who, hazard x phase who ≤ 1 := hhazard1 x hx
  let cycle := quittingBlockCycle (hazard x) h0 h1
  have hnash : ∀ phase,
      IsεQuittingRootNash reward
        (quittingCyclicTerminalValue reward cycle
          (finRotate (period + 1) phase)) 0 (cycle phase) := by
    intro phase
    rw [← isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
    intro who
    by_cases hcovered : IsEnumeratedPeriodicActiveSlot slot phase who
    · obtain ⟨coordinate, hcoordinate⟩ := hcovered
      have hphase : (slot coordinate).1 = phase :=
        congrArg Prod.fst hcoordinate
      have hwho : (slot coordinate).2 = who :=
        congrArg Prod.snd hcoordinate
      have hgap := hactiveGap x hx coordinate (hzero coordinate)
      rw [hphase, hwho] at hgap
      have hsemantic : quittingRootEndpointDifference reward
          (quittingCyclicTerminalValue reward cycle
            (finRotate (period + 1) phase))
          (cycle phase) who = 0 := by
        simpa [cycle, h0, h1] using hgap
      change
        (cycle phase who false).toReal *
              quittingRootEndpointDifference reward
                (quittingCyclicTerminalValue reward cycle
                  (finRotate (period + 1) phase)) (cycle phase) who ≤ 0 ∧
          -0 ≤ (cycle phase who true).toReal *
              quittingRootEndpointDifference reward
                (quittingCyclicTerminalValue reward cycle
                  (finRotate (period + 1) phase)) (cycle phase) who
      rw [hsemantic]
      simp
    · have hgap := (hinactiveGap x hx phase who hcovered).le
      have hhazard := hinactiveHazard x hx phase who hcovered
      have hquit : (cycle phase who true).toReal = 0 := by
        simpa [cycle, h0, h1] using hhazard
      have hcontinue : (cycle phase who false).toReal = 1 := by
        rw [quittingBlockCycle_false]
        simp [hhazard]
      rw [hquit, hcontinue]
      simpa using hgap
  have hcontracts : ∀ who,
      (∏ phase : Fin (period + 1),
        quittingStationaryFixedOpponentsContinueMass
          (cycle phase) who) < 1 := by
    intro who
    obtain ⟨coordinate, hother⟩ := hopponent who
    let phase := (slot coordinate).1
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
    have hphase : quittingStationaryFixedOpponentsContinueMass
        (cycle phase) who < 1 := by
      rw [quittingStationaryFixedOpponentsContinueMass_quittingBlockCycle]
      apply continueMass_lt_one_of_pos (i₀ := (slot coordinate).2)
        (quittingBlockDeletedHazard_nonneg h0 who phase)
        (quittingBlockDeletedHazard_le_one h1 who phase)
      simpa [cycle, phase, quittingBlockDeletedHazard,
        Function.update_of_ne hother] using hactivePos x hx coordinate
    exact Math.Finset.prod_lt_one_of_mem Finset.univ
      (fun cyclePhase =>
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who)
      phase (Finset.mem_univ phase)
      (fun cyclePhase _ _ => hfactor0 cyclePhase)
      (fun cyclePhase _ _ => hfactor1 cyclePhase) hphase
  refine ⟨x, hx, hinterior, hzero, h0, h1, hnash, hcontracts, ?_⟩
  exact isUniformEquilibriumPayoff_quittingCyclicTerminalValue_of_certificate
    reward cycle (quittingCyclicTerminalValue reward cycle) initial
    (quittingCyclicTerminalValue_eq_rootSuccessorPayoff reward cycle)
    hnash hcontracts

end GameTheory

end
