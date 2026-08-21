/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.FullCore.DeadlockChargedReturn
import MathUE.Topology.FiniteLimitDecomposition

/-!
# Global contraction of the four-player deadlock return

The four singleton owners of the charged return cover every coordinate, so
the complete cap map is a strict coordinatewise contraction. The
prescribed-payoff part is an affine contraction with coefficient `2/9`.
Consequently the whole terminal-semantic return has one explicit fixed pair,
and the orbit of every starting pair converges to it.

For every reward completion whose normalized singleton matrix is the displayed
deadlock matrix, the fixed pair belongs to the actual compact semantic carrier:
start from the perpetual-Continue boundary and iterate the carrier-preserving
ideal singleton blocks. Its total semantic debt is exactly `1/14`, without a
zero-clearance hypothesis and without fixing the nonsingleton rewards.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlock

open Filter Finset
open QuittingLCPClassification
open IdealSingletonBlockApproximation
open IdealSingletonCarrierBridge
open scoped Topology

/-- Coordinatewise sensitivity of one ideal singleton cap block.  The owner
coordinate is fixed; every other coordinate is contracted by `α`. -/
theorem abs_idealSingletonClearance_sub_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (owner : ι) (α : ℝ) (hα : 0 ≤ α)
    (t s : ι → ℝ) (who : ι) :
    |idealSingletonClearance M owner α t who -
        idealSingletonClearance M owner α s who| ≤
      (if who = owner then 1 else α) * |t who - s who| := by
  by_cases hwho : who = owner
  · subst who
    simp [idealSingletonClearance]
  · rw [idealSingletonClearance, idealSingletonClearance,
      if_neg hwho, if_neg hwho]
    calc
      |max 0 (α * t who + (1 - α) * M who owner) -
          max 0 (α * s who + (1 - α) * M who owner)| ≤
          max |(0 : ℝ) - 0|
            |(α * t who + (1 - α) * M who owner) -
              (α * s who + (1 - α) * M who owner)| :=
        abs_max_sub_max_le_max _ _ _ _
      _ = α * |t who - s who| := by
        rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
        rw [show
          α * t who + (1 - α) * M who owner -
              (α * s who + (1 - α) * M who owner) =
            α * (t who - s who) by ring]
        rw [abs_mul, abs_of_nonneg hα]
      _ = (if who = owner then 1 else α) * |t who - s who| := by
        simp [hwho]

/-- The autonomous four-block cap return. -/
def chargedCapReturn (t : Player → ℝ) : Player → ℝ :=
  idealSingletonClearance deadlockMatrix 3 (3 / 4)
    (idealSingletonClearance deadlockMatrix 0 (2 / 3)
      (idealSingletonClearance deadlockMatrix 2 (1 / 2)
        (idealSingletonClearance deadlockMatrix 1 (8 / 9) t)))

/-- The displayed charged base is the cap fixed point. -/
theorem chargedCapReturn_chargedBase :
    chargedCapReturn chargedBase = chargedBase := by
  unfold chargedCapReturn
  rw [returnFirst_clearance, returnSecond_clearance,
    returnThird_clearance, returnBase_clearance]

private def singletonFactor (owner : Player) (α : ℝ) (who : Player) : ℝ :=
  if who = owner then 1 else α

private theorem singletonFactor_nonneg
    (owner who : Player) {α : ℝ} (hα : 0 ≤ α) :
    0 ≤ singletonFactor owner α who := by
  unfold singletonFactor
  split <;> positivity

/-- The coordinatewise contraction factors of the complete charged word. -/
def chargedCoordinateFactor : Player → ℝ :=
  ![1 / 3, 1 / 4, 4 / 9, 8 / 27]

private theorem chargedFactor_eq (who : Player) :
    singletonFactor 3 (3 / 4) who *
        singletonFactor 0 (2 / 3) who *
        singletonFactor 2 (1 / 2) who *
        singletonFactor 1 (8 / 9) who =
      chargedCoordinateFactor who := by
  fin_cases who <;>
    norm_num [singletonFactor, chargedCoordinateFactor, Fin.ext_iff]

theorem chargedCoordinateFactor_nonneg (who : Player) :
    0 ≤ chargedCoordinateFactor who := by
  fin_cases who <;> norm_num [chargedCoordinateFactor]

theorem chargedCoordinateFactor_le_four_ninths (who : Player) :
    chargedCoordinateFactor who ≤ 4 / 9 := by
  fin_cases who <;> norm_num [chargedCoordinateFactor]

theorem chargedCoordinateFactor_lt_one (who : Player) :
    chargedCoordinateFactor who < 1 := by
  fin_cases who <;> norm_num [chargedCoordinateFactor]

/-- The complete cap word contracts coordinates by the respective factors
`1/3`, `1/4`, `4/9`, and `8/27`. No sign hypothesis on the initial
clearances is needed. -/
theorem chargedCapReturn_coordinate_contraction
    (t s : Player → ℝ) (who : Player) :
    |chargedCapReturn t who - chargedCapReturn s who| ≤
      chargedCoordinateFactor who * |t who - s who| := by
  let t₁ := idealSingletonClearance deadlockMatrix 1 (8 / 9) t
  let s₁ := idealSingletonClearance deadlockMatrix 1 (8 / 9) s
  let t₂ := idealSingletonClearance deadlockMatrix 2 (1 / 2) t₁
  let s₂ := idealSingletonClearance deadlockMatrix 2 (1 / 2) s₁
  let t₃ := idealSingletonClearance deadlockMatrix 0 (2 / 3) t₂
  let s₃ := idealSingletonClearance deadlockMatrix 0 (2 / 3) s₂
  have h₁ : |t₁ who - s₁ who| ≤
      singletonFactor 1 (8 / 9) who * |t who - s who| := by
    simpa [t₁, s₁, singletonFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 1 (8 / 9)
        (by norm_num) t s who
  have h₂ : |t₂ who - s₂ who| ≤
      singletonFactor 2 (1 / 2) who * |t₁ who - s₁ who| := by
    simpa [t₂, s₂, singletonFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 2 (1 / 2)
        (by norm_num) t₁ s₁ who
  have h₃ : |t₃ who - s₃ who| ≤
      singletonFactor 0 (2 / 3) who * |t₂ who - s₂ who| := by
    simpa [t₃, s₃, singletonFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 0 (2 / 3)
        (by norm_num) t₂ s₂ who
  have h₄ :
      |idealSingletonClearance deadlockMatrix 3 (3 / 4) t₃ who -
          idealSingletonClearance deadlockMatrix 3 (3 / 4) s₃ who| ≤
        singletonFactor 3 (3 / 4) who * |t₃ who - s₃ who| := by
    simpa [singletonFactor] using
      abs_idealSingletonClearance_sub_le deadlockMatrix 3 (3 / 4)
        (by norm_num) t₃ s₃ who
  have hf₁ := singletonFactor_nonneg 1 who (by norm_num : (0 : ℝ) ≤ 8 / 9)
  have hf₂ := singletonFactor_nonneg 2 who (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hf₃ := singletonFactor_nonneg 0 who (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hf₄ := singletonFactor_nonneg 3 who (by norm_num : (0 : ℝ) ≤ 3 / 4)
  unfold chargedCapReturn
  change
    |idealSingletonClearance deadlockMatrix 3 (3 / 4) t₃ who -
      idealSingletonClearance deadlockMatrix 3 (3 / 4) s₃ who| ≤ _
  calc
    _ ≤ singletonFactor 3 (3 / 4) who * |t₃ who - s₃ who| := h₄
    _ ≤ singletonFactor 3 (3 / 4) who *
        (singletonFactor 0 (2 / 3) who * |t₂ who - s₂ who|) :=
      mul_le_mul_of_nonneg_left h₃ hf₄
    _ ≤ singletonFactor 3 (3 / 4) who *
        (singletonFactor 0 (2 / 3) who *
          (singletonFactor 2 (1 / 2) who * |t₁ who - s₁ who|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h₂ hf₃) hf₄
    _ ≤ singletonFactor 3 (3 / 4) who *
        (singletonFactor 0 (2 / 3) who *
          (singletonFactor 2 (1 / 2) who *
            (singletonFactor 1 (8 / 9) who * |t who - s who|))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h₁ hf₂) hf₃) hf₄
    _ = (singletonFactor 3 (3 / 4) who *
          singletonFactor 0 (2 / 3) who *
          singletonFactor 2 (1 / 2) who *
          singletonFactor 1 (8 / 9) who) * |t who - s who| := by
      ring
    _ = chargedCoordinateFactor who * |t who - s who| := by
      rw [chargedFactor_eq]

/-- Uniform contraction corollary using the worst coordinate factor `4/9`. -/
theorem chargedCapReturn_coordinate_contraction_le_four_ninths
    (t s : Player → ℝ) (who : Player) :
    |chargedCapReturn t who - chargedCapReturn s who| ≤
      (4 / 9) * |t who - s who| := by
  calc
    _ ≤ chargedCoordinateFactor who * |t who - s who| :=
      chargedCapReturn_coordinate_contraction t s who
    _ ≤ (4 / 9) * |t who - s who| :=
      mul_le_mul_of_nonneg_right
        (chargedCoordinateFactor_le_four_ninths who) (abs_nonneg _)

/-- Cap dynamics of the semantic return are exactly the autonomous cap map. -/
theorem capClearance_chargedReturn_eq_chargedCapReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    capClearance reward (chargedReturn reward pair).2 =
      chargedCapReturn (capClearance reward pair.2) := by
  unfold chargedReturn chargedCapReturn
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    hmatrix]

/-- The explicit fixed prescribed payoff of the four-block word. -/
def chargedFixedPrescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    Payoff Player :=
  fun who =>
    (reward (quittingProjectiveSingletonTerminal 1) who +
      9 * (reward (quittingProjectiveSingletonTerminal 0) who +
        reward (quittingProjectiveSingletonTerminal 2) who +
        reward (quittingProjectiveSingletonTerminal 3) who)) / 28

/-- One full word contracts prescribed payoffs toward the explicit fixed
payoff with coefficient `2/9`. -/
theorem chargedReturn_prescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player) (who : Player) :
    (chargedReturn reward pair).1 who =
      (2 / 9) * pair.1 who +
        (7 / 9) * chargedFixedPrescribed reward who := by
  unfold chargedReturn chargedFixedPrescribed
  simp only [idealSingletonSemanticPair]
  ring

/-- The unique candidate fixed semantic pair: explicit prescribed payoff and
continuation cap `ownSingleton + chargedBase`. -/
def chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    QuittingTerminalSemanticPair Player :=
  (chargedFixedPrescribed reward,
    fun who => ownSingleton reward who + chargedBase who)

@[simp] theorem capClearance_chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    capClearance reward (chargedFixedPair reward).2 = chargedBase := by
  funext who
  simp [chargedFixedPair, capClearance]

/-- The candidate is an exact fixed point whenever the normalized singleton
matrix is the displayed deadlock matrix. -/
theorem chargedReturn_chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    chargedReturn reward (chargedFixedPair reward) =
      chargedFixedPair reward := by
  apply Prod.ext
  · funext who
    rw [chargedReturn_prescribed]
    simp [chargedFixedPair]
    ring
  · have hcap := capClearance_chargedReturn_eq_chargedCapReturn reward
      (chargedFixedPair reward) hmatrix
    rw [capClearance_chargedFixedPair, chargedCapReturn_chargedBase] at hcap
    funext who
    have hwho := congrFun hcap who
    unfold capClearance at hwho
    change (chargedReturn reward (chargedFixedPair reward)).2 who =
      ownSingleton reward who + chargedBase who
    linarith [hwho]

/-- The explicit fixed pair is the unique fixed point of the charged return. -/
theorem chargedReturn_fixedPoint_unique
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (pair : QuittingTerminalSemanticPair Player)
    (hfixed : chargedReturn reward pair = pair) :
    pair = chargedFixedPair reward := by
  apply Prod.ext
  · funext who
    have hprescribed := chargedReturn_prescribed reward pair who
    rw [hfixed] at hprescribed
    change pair.1 who = chargedFixedPrescribed reward who
    linarith [hprescribed]
  · have hcap := capClearance_chargedReturn_eq_chargedCapReturn reward
      pair hmatrix
    rw [hfixed] at hcap
    funext who
    have hstep := chargedCapReturn_coordinate_contraction
      (capClearance reward pair.2) chargedBase who
    rw [chargedCapReturn_chargedBase,
      ← congrFun hcap who] at hstep
    have hzero :
        |capClearance reward pair.2 who - chargedBase who| = 0 := by
      nlinarith [abs_nonneg
        (capClearance reward pair.2 who - chargedBase who),
        chargedCoordinateFactor_nonneg who,
        chargedCoordinateFactor_lt_one who]
    have hclearance := abs_eq_zero.mp hzero
    change pair.2 who = ownSingleton reward who + chargedBase who
    unfold capClearance at hclearance
    linarith [hclearance]

theorem chargedReturn_eq_self_iff
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (pair : QuittingTerminalSemanticPair Player) :
    chargedReturn reward pair = pair ↔ pair = chargedFixedPair reward := by
  constructor
  · exact chargedReturn_fixedPoint_unique reward hmatrix pair
  · rintro rfl
    exact chargedReturn_chargedFixedPair reward hmatrix

/-- Exact prescribed-coordinate formula along the semantic orbit. -/
theorem chargedReturnOrbit_prescribed
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (n : ℕ) (who : Player) :
    (chargedReturnOrbit reward start n).1 who =
      (2 / 9) ^ n *
          (start.1 who - chargedFixedPrescribed reward who) +
        chargedFixedPrescribed reward who := by
  induction n with
  | zero => simp [chargedReturnOrbit]
  | succ n ih =>
      rw [chargedReturnOrbit, chargedReturn_prescribed, ih, pow_succ]
      ring

/-- Geometric cap error bound along every semantic orbit. -/
theorem chargedReturnOrbit_cap_error_le
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward)
    (n : ℕ) (who : Player) :
    |capClearance reward (chargedReturnOrbit reward start n).2 who -
        chargedBase who| ≤
      (chargedCoordinateFactor who) ^ n *
        |capClearance reward start.2 who - chargedBase who| := by
  induction n with
  | zero => simp [chargedReturnOrbit]
  | succ n ih =>
      have hstep := chargedCapReturn_coordinate_contraction
        (capClearance reward (chargedReturnOrbit reward start n).2)
        chargedBase who
      rw [chargedCapReturn_chargedBase] at hstep
      rw [chargedReturnOrbit,
        capClearance_chargedReturn_eq_chargedCapReturn reward _ hmatrix]
      calc
        _ ≤ chargedCoordinateFactor who *
            |capClearance reward (chargedReturnOrbit reward start n).2 who -
              chargedBase who| := hstep
        _ ≤ chargedCoordinateFactor who *
            ((chargedCoordinateFactor who) ^ n *
            |capClearance reward start.2 who - chargedBase who|) :=
          mul_le_mul_of_nonneg_left ih
            (chargedCoordinateFactor_nonneg who)
        _ = (chargedCoordinateFactor who) ^ (n + 1) *
            |capClearance reward start.2 who - chargedBase who| := by
          rw [pow_succ]
          ring

/-- Every semantic orbit converges to the explicit fixed pair. -/
theorem chargedReturnOrbit_tendsto_chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    Tendsto (chargedReturnOrbit reward start) atTop
      (𝓝 (chargedFixedPair reward)) := by
  apply Filter.Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto (fun n : ℕ => (2 / 9 : ℝ) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hlimit : Tendsto (fun n : ℕ =>
        (2 / 9 : ℝ) ^ n *
            (start.1 who - chargedFixedPrescribed reward who) +
          chargedFixedPrescribed reward who)
        atTop (𝓝 (chargedFixedPrescribed reward who)) := by
      simpa using (hpow.mul_const
        (start.1 who - chargedFixedPrescribed reward who)).add_const
          (chargedFixedPrescribed reward who)
    exact hlimit.congr' (Eventually.of_forall fun n =>
      (chargedReturnOrbit_prescribed reward start n who).symm)
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto
        (fun n : ℕ => (chargedCoordinateFactor who) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (chargedCoordinateFactor_nonneg who)
        (chargedCoordinateFactor_lt_one who)
    let bound := fun n : ℕ => (chargedCoordinateFactor who) ^ n *
      |capClearance reward start.2 who - chargedBase who|
    have hbound : Tendsto bound atTop (𝓝 0) := by
      simpa [bound] using hpow.mul_const
        |capClearance reward start.2 who - chargedBase who|
    have hdiff : Tendsto (fun n =>
        capClearance reward (chargedReturnOrbit reward start n).2 who -
          chargedBase who) atTop (𝓝 0) := by
      apply Math.tendsto_zero_of_abs_le_of_tendsto_zero _ bound hbound
      exact Eventually.of_forall fun n =>
        chargedReturnOrbit_cap_error_le reward start hmatrix n who
    have hcap : Tendsto (fun n =>
        capClearance reward (chargedReturnOrbit reward start n).2 who)
        atTop (𝓝 (chargedBase who)) := by
      simpa using hdiff.add_const (chargedBase who)
    have hcontinuation := hcap.add_const (ownSingleton reward who)
    simpa [capClearance, chargedFixedPair, add_comm] using hcontinuation

/-- A full charged return preserves nonnegative cap clearance. -/
theorem chargedReturn_cap_nonneg
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    ∀ who, 0 ≤ capClearance reward (chargedReturn reward pair).2 who := by
  unfold chargedReturn
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  apply capClearance_idealSingletonSemanticPair_nonneg
  exact hclearance

/-- The perpetual-Continue semantic boundary has nonnegative clearance for
arbitrary rewards. -/
theorem genericNever_capClearance_nonneg
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    ∀ who, 0 ≤ capClearance reward
      (quittingNeverBoundarySemanticPair reward).2 who := by
  intro who
  have hterminal : quittingSingletonTerminal who =
      quittingProjectiveSingletonTerminal who := by
    apply Subtype.ext
    rfl
  rw [capClearance]
  simp only [quittingNeverBoundarySemanticPair, hterminal, ownSingleton]
  exact sub_nonneg.mpr (le_max_right _ _)

/-- The perpetual-Continue semantic boundary is in the actual carrier for
arbitrary rewards. -/
theorem genericNever_mem_carrier
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player) :
    quittingNeverBoundarySemanticPair reward ∈
      quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  refine ⟨quittingRootSequenceProfile reward
    (quittingElementaryCapRoots (.never : QuittingElementaryTailCap Player)) 0,
    ?_⟩
  exact quittingTerminalSemanticPair_elementaryCap_never reward

/-- Every iterate from a carrier point with nonnegative clearance stays in the
carrier and retains nonnegative clearance. -/
theorem chargedReturnOrbit_mem_and_nonneg
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hstartMem : start ∈ quittingTerminalSemanticCarrier reward)
    (hstartNonneg : ∀ who, 0 ≤ capClearance reward start.2 who) :
    ∀ n,
      chargedReturnOrbit reward start n ∈
          quittingTerminalSemanticCarrier reward ∧
      ∀ who, 0 ≤ capClearance reward
        (chargedReturnOrbit reward start n).2 who := by
  intro n
  induction n with
  | zero => exact ⟨hstartMem, hstartNonneg⟩
  | succ n ih =>
      rw [chargedReturnOrbit]
      exact ⟨chargedReturn_mem_carrier reward _ ih.2 ih.1,
        chargedReturn_cap_nonneg reward _ ih.2⟩

/-- Universal carrier realization of the fixed pair.  Only the normalized
singleton matrix is constrained; all other coalition rewards are arbitrary. -/
theorem chargedFixedPair_mem_carrier
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    chargedFixedPair reward ∈ quittingTerminalSemanticCarrier reward := by
  apply isClosed_closure.mem_of_tendsto
    (chargedReturnOrbit_tendsto_chargedFixedPair reward
      (quittingNeverBoundarySemanticPair reward) hmatrix)
  exact Eventually.of_forall fun n =>
    (chargedReturnOrbit_mem_and_nonneg reward
      (quittingNeverBoundarySemanticPair reward)
      (genericNever_mem_carrier reward)
      (genericNever_capClearance_nonneg reward) n).1

/-- The universally realized fixed pair has exact total semantic debt
`1/14`. -/
theorem chargedFixedPair_debtSum
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : IsFullCoreDeadlockCompletion reward) :
    quittingTerminalSemanticDebtSum (chargedFixedPair reward) = 1 / 14 := by
  have hreturn := debtSum_chargedReturn reward (chargedFixedPair reward)
    hmatrix (capClearance_chargedFixedPair reward)
  rw [chargedReturn_chargedFixedPair reward hmatrix] at hreturn
  linarith

/-- Every completion of the deadlock singleton matrix has an actual carrier
point whose total semantic debt is exactly `1/14`. -/
theorem IsFullCoreDeadlockCompletion.exists_carrierPair_debtSum_eq_one_fourteenth
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward) :
    ∃ pair ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum pair = 1 / 14 := by
  exact ⟨chargedFixedPair reward,
    chargedFixedPair_mem_carrier reward hcompletion,
    chargedFixedPair_debtSum reward hcompletion⟩

/-- Every global terminal-semantic debt floor is at most `1/14` for every
completion of the displayed deadlock singleton matrix. -/
theorem IsFullCoreDeadlockCompletion.globalDebtFloor_le_one_fourteenth
    {reward : {S : Finset Player // S.Nonempty} → Payoff Player}
    (hcompletion : IsFullCoreDeadlockCompletion reward)
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1 / 14 := by
  rw [← chargedFixedPair_debtSum reward hcompletion]
  exact hfloor (chargedFixedPair reward)
    (chargedFixedPair_mem_carrier reward hcompletion)

end FullCoreDeadlock
end GameTheory
