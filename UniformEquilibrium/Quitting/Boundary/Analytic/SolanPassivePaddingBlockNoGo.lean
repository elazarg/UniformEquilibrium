/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Analytic.PassivePaddingBlockCertificateRetraction
import UniformEquilibrium.Quitting.Cycles.PerturbedCyclicWeightCycleExistenceHoleOccupied

/-!
# A rational four-player table with no exact finite block certificate

The three-player perturbed Solan table has no absorbing exact cycle at any
finite period.  If its one-passive-player padding had an admissible exact
block certificate, passive-player retraction would produce precisely such an
old cycle.  This file makes that contradiction literal for the rational
parameter `ε = 1`.

The result is about exact finite certificates.  It gives no positive lower
bound on approximate exploitability and does not exclude nonperiodic uniform
equilibria.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open GameTheory.CyclicThreePlayerQuitting.Minimality
open GameTheory.CyclicThreePlayerQuitting.PerturbedCycleExclusion

/-! ## The projected old cyclic continuation -/

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The old real hazards displayed by a one-passive-player block. -/
def quittingPassivePaddingProjectedBlockHazard {m : ℕ}
    (hazard : Fin (m + 1) → I ⊕ PUnit → ℝ) :
    Fin (m + 1) → I → ℝ :=
  fun phase old ↦ hazard phase (.inl old)

/-- The old coordinates of every displayed value, including the repeated
terminal endpoint. -/
def quittingPassivePaddingProjectedDisplayedValue {m : ℕ}
    (U : Fin (m + 2) → Payoff (I ⊕ PUnit)) :
    Fin (m + 2) → Payoff I :=
  fun stage old ↦ U stage (.inl old)

omit [Fintype I] [DecidableEq I] in
theorem quittingBlockCycle_projectedPassivePadding {m : ℕ}
    (hazard : Fin (m + 1) → I ⊕ PUnit → ℝ)
    (h0 : ∀ phase player, 0 ≤ hazard phase player)
    (h1 : ∀ phase player, hazard phase player ≤ 1) :
    quittingBlockCycle (quittingPassivePaddingProjectedBlockHazard hazard)
        (fun phase old ↦ h0 phase (.inl old))
        (fun phase old ↦ h1 phase (.inl old)) =
      quittingPassivePaddingProjectedBlockCycle hazard h0 h1 := by
  rfl

/-- Deleting the passive coordinate from a padded block certificate also
produces an old cyclic continuation block.  The reward-box field is recovered
from the old Bellman recursion and strict one-turn contraction, rather than
inherited from the generally larger padded reward box. -/
theorem isQuittingCyclicContinuationBlock_projectedPassivePadding
    {m : ℕ}
    (reward : {S : Finset I // S.Nonempty} → Payoff I)
    (upper : I → ℝ)
    (hupper : ∀ terminal old, reward terminal old ≤ upper old)
    {penalty : ℝ} (hpenalty : 0 < penalty)
    {hazard : Fin (m + 1) → I ⊕ PUnit → ℝ}
    {U : Fin (m + 2) → Payoff (I ⊕ PUnit)}
    (hcert : IsQuittingBlockCertificate
      (quittingPassivePaddingReward (J := PUnit) reward upper penalty) hazard U) :
    let oldHazard := quittingPassivePaddingProjectedBlockHazard hazard
    let oldU := quittingPassivePaddingProjectedDisplayedValue U
    IsQuittingCyclicContinuationBlock reward (oldU 0) (m + 1)
      (quittingBlockPath (hazard := oldHazard)
        (fun phase old ↦ hcert.hazard_nonneg phase (.inl old))
        (fun phase old ↦ hcert.hazard_le_one phase (.inl old)) oldU) := by
  let oldHazard := quittingPassivePaddingProjectedBlockHazard hazard
  let oldU := quittingPassivePaddingProjectedDisplayedValue U
  let old0 : ∀ phase old, 0 ≤ oldHazard phase old :=
    fun phase old ↦ hcert.hazard_nonneg phase (.inl old)
  let old1 : ∀ phase old, oldHazard phase old ≤ 1 :=
    fun phase old ↦ hcert.hazard_le_one phase (.inl old)
  let oldBlock := quittingBlockPath old0 old1 oldU
  have hcycle : quittingBlockCycle oldHazard old0 old1 =
      quittingPassivePaddingProjectedBlockCycle hazard
        hcert.hazard_nonneg hcert.hazard_le_one := by
    exact quittingBlockCycle_projectedPassivePadding hazard
      hcert.hazard_nonneg hcert.hazard_le_one
  have hcontractRoot := prod_projectedPassivePaddingBlockCycle_lt_one
    reward upper hpenalty hcert
  have hcontract : (∏ phase : Fin (m + 1), continueMass (oldHazard phase)) < 1 := by
    rw [← hcycle] at hcontractRoot
    simpa only [quittingStationaryContinueMass_quittingBlockCycle] using hcontractRoot
  have hpaddedBlock :=
    isQuittingCyclicContinuationBlock_of_isQuittingBlockCertificate hcert
  have hnext : ∀ phase : Fin (m + 1),
      quittingPassivePaddingProjectedBlockValue U (finRotate (m + 1) phase) =
        oldU (Fin.succ phase) := by
    intro phase
    funext old
    exact congrFun
      (quittingCyclicContinuationBlockValue_finRotate
        (quittingPassivePaddingReward (J := PUnit) reward upper penalty)
        (U 0) m
        (quittingBlockPath hcert.hazard_nonneg hcert.hazard_le_one U)
        hpaddedBlock phase) (.inl old)
  have honPath : IsQuittingBlockOnPathValue reward oldHazard
      (quittingPassivePaddingProjectedBlockValue U) := by
    intro phase old
    have hphase :=
      isQuittingRootSuccessorCertificate_projectedPassivePaddingBlockPhase
        reward upper hupper hpenalty hcert phase
    have hpolicy := congrFun hphase.1 old
    rw [← hcycle] at hpolicy
    rwa [quittingRootSuccessorPayoff_eq_coalitionSum,
      hazardOfRoot_quittingBlockCycle] at hpolicy
  have hboxPhase : ∀ phase : Fin (m + 1), ∀ old,
      |oldU (Fin.castSucc phase) old| ≤ quittingRewardBound reward := by
    intro phase old
    exact abs_le_quittingRewardBound_of_isQuittingBlockOnPathValue_of_absorbing
      old0 old1 honPath hcontract phase old
  change IsQuittingCyclicContinuationBlock reward (oldU 0) (m + 1) oldBlock
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ?_⟩
  · intro stage
    change oldU stage ∈ Set.Icc (fun _ ↦ -quittingRewardBound reward)
      (fun _ ↦ quittingRewardBound reward)
    rcases Fin.eq_castSucc_or_eq_last stage with ⟨phase, rfl⟩ | rfl
    · constructor
      · intro old
        exact (abs_le.mp (hboxPhase phase old)).1
      · intro old
        exact (abs_le.mp (hboxPhase phase old)).2
    · have hlast : oldU (Fin.last (m + 1)) = oldU 0 := by
        funext old
        exact congrFun hcert.last (.inl old)
      rw [hlast]
      constructor
      · intro old
        exact (abs_le.mp (hboxPhase 0 old)).1
      · intro old
        exact (abs_le.mp (hboxPhase 0 old)).2
  · funext old
    exact congrFun hcert.last (.inl old)
  · intro phase
    unfold IsQuittingNashBellmanEdge
    change oldU (Fin.castSucc phase) =
        quittingRootSuccessorPayoff reward (oldU (Fin.succ phase))
          (quittingRootOfSimplex (oldBlock (Fin.castSucc phase)).2) ∧
      IsεQuittingRootEndpointNash reward (oldU (Fin.succ phase)) 0
        (quittingRootOfSimplex (oldBlock (Fin.castSucc phase)).2)
    rw [show quittingRootOfSimplex (oldBlock (Fin.castSucc phase)).2 =
        quittingBlockCycle oldHazard old0 old1 phase by
      exact quittingRootOfSimplex_quittingBlockPath old0 old1 oldU phase]
    have hphase :=
      isQuittingRootSuccessorCertificate_projectedPassivePaddingBlockPhase
        reward upper hupper hpenalty hcert phase
    rw [← hcycle] at hphase
    rw [hnext phase] at hphase
    exact hphase
  · have hexists : ∃ phase : Fin (m + 1), continueMass (oldHazard phase) < 1 := by
      by_contra hnone
      push Not at hnone
      have hall : ∀ phase : Fin (m + 1), continueMass (oldHazard phase) = 1 := by
        intro phase
        exact le_antisymm (continueMass_le_one (old0 phase) (old1 phase)) (hnone phase)
      rw [Finset.prod_eq_one (fun phase _ ↦ hall phase)] at hcontract
      exact (lt_irrefl 1) hcontract
    obtain ⟨phase, hphase⟩ := hexists
    refine ⟨phase, ?_⟩
    rw [quittingRootOfSimplex_quittingBlockPath, quittingRootAbsorptionMass]
    rw [quittingStationaryContinueMass_quittingBlockCycle]
    linarith

/-! ## The explicit rational table -/

/-- The integer-scaled three-player Solan perturbation, padded by one passive
player at the literal upper vector `(3,3,3)` and penalty `1`. -/
def solanPassivePaddedReward (epsilon : ℝ) :
    {S : Finset (Player ⊕ PUnit) // S.Nonempty} → Payoff (Player ⊕ PUnit) :=
  quittingPassivePaddingReward (J := PUnit) (perturbedReward epsilon)
    (fun _ ↦ 3) 1

/-- On every old-containing coalition, the padded table restricts literally
to the perturbed Solan table on the old coalition. -/
theorem solanPassivePaddedReward_old_of_oldPart_nonempty
    (epsilon : ℝ)
    (terminal : {S : Finset (Player ⊕ PUnit) // S.Nonempty})
    (hold : (quittingPassivePaddingOldPart terminal.1).Nonempty)
    (who : Player) :
    solanPassivePaddedReward epsilon terminal (.inl who) =
      perturbedReward epsilon
        ⟨quittingPassivePaddingOldPart terminal.1, hold⟩ who := by
  simp [solanPassivePaddedReward, quittingPassivePaddingReward, hold]

/-- On every old-containing coalition, the passive player's payoff is
literally zero. -/
theorem solanPassivePaddedReward_fresh_of_oldPart_nonempty
    (epsilon : ℝ)
    (terminal : {S : Finset (Player ⊕ PUnit) // S.Nonempty})
    (hold : (quittingPassivePaddingOldPart terminal.1).Nonempty)
    (fresh : PUnit) :
    solanPassivePaddedReward epsilon terminal (.inr fresh) = 0 := by
  simp [solanPassivePaddedReward, quittingPassivePaddingReward, hold]

/-- The passive-only terminal row is exactly `(3,3,3,-1)`. -/
theorem solanPassivePaddedReward_dummySingleton (epsilon : ℝ) :
    solanPassivePaddedReward epsilon
      (quittingSingletonTerminal (.inr PUnit.unit)) =
        Sum.elim (fun _ : Player ↦ 3) (fun _ : PUnit ↦ -1) := by
  funext player
  cases player with
  | inl old =>
      simp [solanPassivePaddedReward, quittingPassivePaddingReward,
        quittingPassivePaddingOldPart, quittingSingletonTerminal]
  | inr fresh =>
      cases fresh
      simp [solanPassivePaddedReward, quittingPassivePaddingReward,
        quittingPassivePaddingOldPart, quittingSingletonTerminal]

/-- A quitting reward table is rational when each terminal entry is the real
cast of a rational number. -/
def HasRationalQuittingRewardTable {K : Type} [Fintype K]
    (reward : {S : Finset K // S.Nonempty} → Payoff K) : Prop :=
  ∀ terminal who, ∃ q : ℚ, reward terminal who = (q : ℝ)

/-- At `ε = 1`, every entry of the four-player table is rational (indeed,
integral). -/
theorem hasRationalQuittingRewardTable_solanPassivePaddedReward_one :
    HasRationalQuittingRewardTable (solanPassivePaddedReward 1) := by
  intro terminal player
  have hvalue :
      solanPassivePaddedReward 1 terminal player = -1 ∨
      solanPassivePaddedReward 1 terminal player = 0 ∨
      solanPassivePaddedReward 1 terminal player = 1 ∨
      solanPassivePaddedReward 1 terminal player = 2 ∨
      solanPassivePaddedReward 1 terminal player = 3 := by
    fin_cases terminal <;> cases player with
    | inl old =>
        fin_cases old <;>
          norm_num (config := { decide := true })
            [solanPassivePaddedReward, quittingPassivePaddingReward,
              quittingPassivePaddingOldPart, perturbedReward,
              CyclicThreePlayerQuitting.AdmissibleCycle.reward,
              CyclicThreePlayerQuitting.Minimality.terminalReward,
              quittingSingletonTerminal]
    | inr fresh =>
        cases fresh
        norm_num (config := { decide := true })
          [solanPassivePaddedReward, quittingPassivePaddingReward,
            quittingPassivePaddingOldPart, perturbedReward,
            CyclicThreePlayerQuitting.AdmissibleCycle.reward,
            CyclicThreePlayerQuitting.Minimality.terminalReward,
            quittingSingletonTerminal]
  rcases hvalue with h | h | h | h | h
  · exact ⟨-1, by norm_num [h]⟩
  · exact ⟨0, by norm_num [h]⟩
  · exact ⟨1, by norm_num [h]⟩
  · exact ⟨2, by norm_num [h]⟩
  · exact ⟨3, by norm_num [h]⟩

/-- Every old coordinate of the perturbed Solan table is at most `3` when
`0 ≤ ε ≤ 2`. -/
theorem perturbedReward_le_three (epsilon : ℝ) (hepsilon2 : epsilon ≤ 2)
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    perturbedReward epsilon terminal who ≤ 3 := by
  fin_cases terminal <;> fin_cases who <;>
    simp (config := { decide := true }) [perturbedReward,
      CyclicThreePlayerQuitting.AdmissibleCycle.reward,
      CyclicThreePlayerQuitting.Minimality.terminalReward] <;> linarith

/-- Every entry of the perturbed Solan table is nonnegative for nonnegative
`ε`. -/
theorem perturbedReward_nonneg (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon)
    (terminal : {S : Finset Player // S.Nonempty}) (who : Player) :
    0 ≤ perturbedReward epsilon terminal who := by
  fin_cases terminal <;> fin_cases who <;>
    simp (config := { decide := true }) [perturbedReward,
      CyclicThreePlayerQuitting.AdmissibleCycle.reward,
      CyclicThreePlayerQuitting.Minimality.terminalReward] <;> linarith

/-- The canonical old upper endpoint of the perturbed table is exactly `3`.
Thus the literal padding above is also the canonical padding used by the
quantitative retraction. -/
theorem quittingPassivePaddingUpperEndpoint_perturbedReward_eq_three
    (epsilon : ℝ) (hepsilon2 : epsilon ≤ 2) (who : Player) :
    quittingPassivePaddingUpperEndpoint (perturbedReward epsilon) who = 3 := by
  apply le_antisymm
  · unfold quittingPassivePaddingUpperEndpoint
    apply Finset.sup'_le
    intro terminal _
    exact max_le (by norm_num)
      (perturbedReward_le_three epsilon hepsilon2 terminal who)
  · fin_cases who
    · have h := (quittingPassivePaddingReward_mem_canonicalInterval
        (perturbedReward epsilon) (quittingSingletonTerminal (2 : Player)) 0).2
      simpa (config := { decide := true }) [perturbedReward,
        CyclicThreePlayerQuitting.AdmissibleCycle.reward,
        CyclicThreePlayerQuitting.Minimality.terminalReward,
        quittingSingletonTerminal] using h
    · have h := (quittingPassivePaddingReward_mem_canonicalInterval
        (perturbedReward epsilon) (quittingSingletonTerminal (0 : Player)) 1).2
      simpa (config := { decide := true }) [perturbedReward,
        CyclicThreePlayerQuitting.AdmissibleCycle.reward,
        CyclicThreePlayerQuitting.Minimality.terminalReward,
        quittingSingletonTerminal] using h
    · have h := (quittingPassivePaddingReward_mem_canonicalInterval
        (perturbedReward epsilon) (quittingSingletonTerminal (1 : Player)) 2).2
      simpa (config := { decide := true }) [perturbedReward,
        CyclicThreePlayerQuitting.AdmissibleCycle.reward,
        CyclicThreePlayerQuitting.Minimality.terminalReward,
        quittingSingletonTerminal] using h

/-- The canonical old lower endpoint of the perturbed table is zero. -/
theorem quittingPassivePaddingLowerEndpoint_perturbedReward_eq_zero
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (who : Player) :
    quittingPassivePaddingLowerEndpoint (perturbedReward epsilon) who = 0 := by
  apply le_antisymm
  · exact quittingPassivePaddingLowerEndpoint_nonpos
      (perturbedReward epsilon) who
  · unfold quittingPassivePaddingLowerEndpoint
    have hle : Finset.univ.sup'
        ⟨quittingSingletonTerminal (0 : Player), Finset.mem_univ _⟩
        (fun terminal : {S : Finset Player // S.Nonempty} ↦
          max 0 (-perturbedReward epsilon terminal who)) ≤ 0 := by
      apply Finset.sup'_le
      intro terminal _
      exact max_le le_rfl (neg_nonpos.mpr (perturbedReward_nonneg epsilon
        hepsilon0 terminal who))
    linarith

/-- The largest canonical coordinate width is exactly `3`. -/
theorem quittingPassivePaddingWidth_perturbedReward_eq_three
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon2 : epsilon ≤ 2) :
    quittingPassivePaddingWidth (perturbedReward epsilon) = 3 := by
  unfold quittingPassivePaddingWidth quittingPassivePaddingCoordinateWidth
  simp_rw [quittingPassivePaddingUpperEndpoint_perturbedReward_eq_three
      epsilon hepsilon2,
    quittingPassivePaddingLowerEndpoint_perturbedReward_eq_zero epsilon hepsilon0]
  simp

/-- The supplied-upper and canonical versions of the padded table coincide
for `0 ≤ ε ≤ 2`. -/
theorem solanPassivePaddedReward_eq_canonical
    (epsilon : ℝ) (hepsilon2 : epsilon ≤ 2) :
    solanPassivePaddedReward epsilon =
      quittingOnePassivePlayerPaddingReward (perturbedReward epsilon) 1 := by
  unfold solanPassivePaddedReward quittingOnePassivePlayerPaddingReward
  rw [show quittingPassivePaddingUpperEndpoint (perturbedReward epsilon) =
      fun _ ↦ 3 by
    funext who
    exact quittingPassivePaddingUpperEndpoint_perturbedReward_eq_three
      epsilon hepsilon2 who]

/-- On the explicit Solan family the one-passive-player projection loses at
most the literal factor `4`; deviations on both sides remain arbitrary
behavioral deviations. -/
theorem quittingTerminalExploitability_project_solanPassivePaddedReward_le_four
    (epsilon : ℝ) (hepsilon0 : 0 ≤ epsilon) (hepsilon2 : epsilon ≤ 2)
    (profile : (quittingGame
      (quittingOnePassivePlayerPaddingReward
        (perturbedReward epsilon) 1)).BehaviorProfile) :
    quittingTerminalExploitability (perturbedReward epsilon)
        (quittingPassivePaddingProjectProfile (perturbedReward epsilon) profile) ≤
      4 * quittingTerminalExploitability
        (quittingOnePassivePlayerPaddingReward
          (perturbedReward epsilon) 1) profile := by
  have h := quittingTerminalExploitability_project_onePassivePlayer_le
    (perturbedReward epsilon) (penalty := 1) (by norm_num) profile
  rw [quittingPassivePaddingWidth_perturbedReward_eq_three
    epsilon hepsilon0 hepsilon2] at h
  norm_num at h
  simpa [quittingOnePassivePlayerPaddingReward] using h

/-- Quiet lift into the explicit Solan padding does not increase terminal
exploitability. -/
theorem quittingTerminalExploitability_quiet_solanPassivePaddedReward_le
    (epsilon : ℝ)
    (profile : (quittingGame (perturbedReward epsilon)).BehaviorProfile) :
    quittingTerminalExploitability
        (quittingOnePassivePlayerPaddingReward (perturbedReward epsilon) 1)
        (quittingPassivePaddingQuietProfile (J := PUnit)
          (perturbedReward epsilon) 1 profile) ≤
      quittingTerminalExploitability (perturbedReward epsilon) profile := by
  exact quittingTerminalExploitability_passivePaddingQuietProfile_le
    (J := PUnit) (perturbedReward epsilon) (by norm_num) profile

/-- No exact finite absorbing punishment-admissible block certificate exists
for the literal four-player padded Solan table, for any `0 < ε ≤ 2`. -/
theorem no_isQuittingBlockCertificate_solanPassivePaddedReward
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon2 : epsilon ≤ 2) :
    ¬ ∃ (m : ℕ) (hazard : Fin (m + 1) → Player ⊕ PUnit → ℝ)
        (U : Fin (m + 2) → Payoff (Player ⊕ PUnit)),
      IsQuittingBlockCertificate (solanPassivePaddedReward epsilon) hazard U := by
  rintro ⟨m, hazard, U, hcert⟩
  have hblock := isQuittingCyclicContinuationBlock_projectedPassivePadding
    (perturbedReward epsilon) (fun _ ↦ 3)
    (perturbedReward_le_three epsilon hepsilon2) (by norm_num) hcert
  have cycle := hblock.toExactCycle
  rw [weightOfReward_perturbedReward_eq_perturbedWeight] at cycle
  exact no_exactCycle epsilon hepsilon hepsilon2 cycle

/-- **Concrete rational Fin4 no-go.**  The parameter `ε = 1` makes every
entry of the displayed table integral, hence rational, and the table admits
no exact finite block certificate of any period. -/
theorem no_isQuittingBlockCertificate_solanPassivePaddedReward_one :
    ¬ ∃ (m : ℕ) (hazard : Fin (m + 1) → Player ⊕ PUnit → ℝ)
        (U : Fin (m + 2) → Payoff (Player ⊕ PUnit)),
      IsQuittingBlockCertificate (solanPassivePaddedReward 1) hazard U := by
  exact no_isQuittingBlockCertificate_solanPassivePaddedReward 1 (by norm_num) (by norm_num)

end GameTheory
