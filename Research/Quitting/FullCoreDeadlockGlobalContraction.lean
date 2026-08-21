/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.FullCoreDeadlockChargedReturn
import MathUE.Topology.FiniteLimitDecomposition

/-!
# Global contraction of the four-player deadlock return

The charged return isolated in `FullCoreDeadlockChargedReturn` is not confined
to its displayed cap cycle.  Its four singleton owners cover every coordinate,
so the complete cap map is a strict coordinatewise contraction.  The
prescribed-payoff part is an affine contraction with coefficient `2/9`.
Consequently the whole terminal-semantic return has one explicit fixed pair,
and the orbit of every starting pair converges to it.

For every reward completion whose normalized singleton matrix is the Q193
deadlock matrix, the fixed pair belongs to the actual compact semantic carrier:
start from the perpetual-Continue boundary and iterate the carrier-preserving
ideal singleton blocks.  Its total semantic debt is exactly `1/14`.  Thus the
Q193 membership caveat disappears universally, without a zero-clearance
hypothesis and without fixing the nonsingleton rewards.
-/

noncomputable section

namespace GameTheory
namespace FullCoreDeadlockChargedReturn

open Filter Finset
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
        rw [sub_self, abs_zero, zero_max]
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

private theorem chargedFactor_le (who : Player) :
    singletonFactor 3 (3 / 4) who *
        singletonFactor 0 (2 / 3) who *
        singletonFactor 2 (1 / 2) who *
        singletonFactor 1 (8 / 9) who ≤
      4 / 9 := by
  fin_cases who <;> norm_num [singletonFactor]

/-- The complete cap word is globally contractive, with worst coordinate
factor `4/9`.  No sign hypothesis on the initial clearances is needed. -/
theorem chargedCapReturn_coordinate_contraction
    (t s : Player → ℝ) (who : Player) :
    |chargedCapReturn t who - chargedCapReturn s who| ≤
      (4 / 9) * |t who - s who| := by
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
    _ ≤ (4 / 9) * |t who - s who| :=
      mul_le_mul_of_nonneg_right (chargedFactor_le who) (abs_nonneg _)

/-- Cap dynamics of the semantic return are exactly the autonomous cap map. -/
theorem capClearance_chargedReturn_eq_chargedCapReturn
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (pair : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix) :
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
matrix is the Q193 deadlock matrix. -/
theorem chargedReturn_chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix) :
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
    exact sub_left_injective (ownSingleton reward who) hwho

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
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix)
    (n : ℕ) (who : Player) :
    |capClearance reward (chargedReturnOrbit reward start n).2 who -
        chargedBase who| ≤
      (4 / 9) ^ n *
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
        _ ≤ (4 / 9) *
            |capClearance reward (chargedReturnOrbit reward start n).2 who -
              chargedBase who| := hstep
        _ ≤ (4 / 9) * ((4 / 9) ^ n *
            |capClearance reward start.2 who - chargedBase who|) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (4 / 9) ^ (n + 1) *
            |capClearance reward start.2 who - chargedBase who| := by
          rw [pow_succ]
          ring

/-- Every semantic orbit converges to the explicit fixed pair. -/
theorem chargedReturnOrbit_tendsto_chargedFixedPair
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix) :
    Tendsto (chargedReturnOrbit reward start) atTop
      (𝓝 (chargedFixedPair reward)) := by
  apply Filter.Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto (fun n : ℕ => (2 / 9 : ℝ) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hlimit := (hpow.mul_const
      (start.1 who - chargedFixedPrescribed reward who)).add_const
        (chargedFixedPrescribed reward who)
    exact hlimit.congr' (Eventually.of_forall fun n =>
      (chargedReturnOrbit_prescribed reward start n who).symm)
  · apply tendsto_pi_nhds.2
    intro who
    have hpow : Tendsto (fun n : ℕ => (4 / 9 : ℝ) ^ n)
        atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    let bound := fun n : ℕ => (4 / 9 : ℝ) ^ n *
      |capClearance reward start.2 who - chargedBase who|
    have hbound : Tendsto bound atTop (𝓝 0) := by
      exact hpow.mul_const _
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
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix) :
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
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix) :
    quittingTerminalSemanticDebtSum (chargedFixedPair reward) = 1 / 14 := by
  have hreturn := debtSum_chargedReturn reward (chargedFixedPair reward)
    hmatrix (capClearance_chargedFixedPair reward)
  rw [chargedReturn_chargedFixedPair reward hmatrix] at hreturn
  linarith

/-- Universal Q193 consequence: every global terminal-semantic debt floor is
at most `1/14`, for every completion of the deadlock singleton matrix. -/
theorem universal_globalDebtFloor_le_one_fourteenth
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (hmatrix : normalizedSoloMatrix reward = deadlockMatrix)
    (δ : ℝ)
    (hfloor : ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ 1 / 14 := by
  rw [← chargedFixedPair_debtSum reward hmatrix]
  exact hfloor (chargedFixedPair reward)
    (chargedFixedPair_mem_carrier reward hmatrix)

end FullCoreDeadlockChargedReturn
end GameTheory
