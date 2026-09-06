/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.BackwardOrbitSelection
import MathUE.MeshContraction
import UniformEquilibrium.Quitting.Classification.Existence.PerfectAbsorbingRow
import UniformEquilibrium.Quitting.Classification.TableExistenceBranches
import UniformEquilibrium.Quitting.Paths.SurvivalWindowLanding
import UniformEquilibrium.Quitting.Root.TailStability
import UniformEquilibrium.Quitting.Root.TerminalDebtPrefix

/-!
# Self-consistent perfect absorbing root sequences

Proposition 2.3 of Solan and Vieille, *Quitting games*, Math. Oper. Res. 26
(2001), in this development's root-sequence vocabulary.  Under unit solo exit
and a low active Quit endpoint at every absorbing root, for every `ε > 0` there is a periodic sequence of
product rows and a uniform absorption floor `δ > 0` such that every stage's
row absorbs with probability at least `δ` and is one-stage `ε`-perfect
against the sequence's own continuation vector at the next stage.

The construction discretizes the reward cube at a mesh tied to `ε`, runs the
one-shot perturbation `exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff`
through a choice function on grid keys, and closes the chain with a pigeonhole
on the finite key range: a forward orbit of the induced key dynamics must
revisit a key, and reading the revealed cycle backwards in time yields an
infinite backward orbit.  The gap between the intended representative tails
and the sequence's actual continuation vectors then contracts geometrically,
because every stage retains at least the absorption floor: the survival slope
of the value recursion is at most `1 - δ`, so the accumulated key-rounding
error stays below `η / δ`.

No fixed-point theorem beyond the one-shot mixed Nash existence is used; the
discretization replaces the source's upper-semicontinuity argument, exactly
as in the source's own proof.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Stability of one-stage perfectness -/

/-- One-stage perfectness is monotone in its tolerance. -/
theorem quittingRowεPerfect_mono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail : Payoff ι} {root : ι → PMF Bool} {ε ε' : ℝ}
    (h : QuittingRowεPerfect reward tail root ε) (hle : ε ≤ ε') :
    QuittingRowεPerfect reward tail root ε' := by
  intro who
  obtain ⟨h1, h2, h3, h4⟩ := h who
  exact ⟨by linarith, by linarith, fun hne => by linarith [h3 hne],
    fun hne => by linarith [h4 hne]⟩

/-- One-stage perfectness survives moving the continuation coordinatewise by
`c`, at tolerance widened by `2 * c`: pure Quit never reads the continuation,
while pure Continue and the prescribed value are `1`-Lipschitz in the
player's own continuation coordinate. -/
theorem quittingRowεPerfect_of_tail_close
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {tail tail' : Payoff ι} {root : ι → PMF Bool} {ε c : ℝ}
    (h : QuittingRowεPerfect reward tail root ε) (hc : 0 ≤ c)
    (hclose : ∀ who, |tail who - tail' who| ≤ c) :
    QuittingRowεPerfect reward tail' root (ε + 2 * c) := by
  intro who
  obtain ⟨h1, h2, h3, h4⟩ := h who
  have hquit : quittingRootQuitPayoff reward tail' root who =
      quittingRootQuitPayoff reward tail root who :=
    quittingRootQuitPayoff_continuation_invariant reward tail' tail root who
  have hcont : |quittingRootContinuePayoff reward tail' root who -
      quittingRootContinuePayoff reward tail root who| ≤ c :=
    abs_quittingRootExpectedPayoff_sub_of_tail_close reward tail' tail
      (Function.update root who (PMF.pure false)) who hc
      (by rw [abs_sub_comm]; exact hclose who)
  have hsucc : |quittingRootSuccessorPayoff reward tail' root who -
      quittingRootSuccessorPayoff reward tail root who| ≤ c :=
    abs_quittingRootExpectedPayoff_sub_of_tail_close reward tail' tail
      root who hc (by rw [abs_sub_comm]; exact hclose who)
  obtain ⟨hcont₁, hcont₂⟩ := abs_le.mp hcont
  obtain ⟨hsucc₁, hsucc₂⟩ := abs_le.mp hsucc
  refine ⟨?_, ?_, fun hne => ?_, fun hne => ?_⟩
  · rw [hquit]
    linarith
  · linarith
  · rw [hquit]
    have := h3 hne
    linarith
  · have := h4 hne
    linarith

/-! ## The geometric contraction -/

omit [DecidableEq ι] in
/-- **Rounding-error contraction.**  If every stage's row is produced against
a plan vector within `η` of the previous stage's produced value, and every
stage absorbs at least `δ`, then the sequence's actual continuation values
stay within `(1 - δ) * η / δ` of the produced values: the successor value at
a stage differs from the actual terminal value only through survival of that
stage, so the geometric error bound retains the factor `1 - δ`. -/
theorem abs_terminalValue_sub_successor_le_of_approximate_chain_sharp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (plan : ℕ → Payoff ι)
    {R δ η : ℝ} (hR0 : 0 ≤ R) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hplanBound : ∀ n who, |plan n who| ≤ R)
    (hmass : ∀ n, quittingStationaryContinueMass (roots n) ≤ 1 - δ)
    (hclose : ∀ n who,
      |plan n who -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤ η) :
    ∀ n who,
      |quittingRootSequenceTerminalValue reward roots who n -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤
        (1 - δ) * η / δ := by
  have hηδ0 : 0 ≤ η / δ := div_nonneg hη0 hδ0.le
  have hvalueBound : ∀ n who,
      |quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤ R :=
    fun n who => abs_quittingRootExpectedPayoff_le_bound reward (plan (n + 1))
      (roots n) who hreward (hplanBound (n + 1))
  have hγBound : ∀ n who,
      |quittingRootSequenceTerminalValue reward roots who n| ≤ R :=
    fun n who =>
      abs_quittingRootSequenceTerminalValue_le reward roots who n hR0 hreward
  have honestep : ∀ n who,
      |quittingRootSequenceTerminalValue reward roots who n -
          quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤
        (1 - δ) *
          (|quittingRootSequenceTerminalValue reward roots who (n + 1) -
              quittingRootSuccessorPayoff reward (plan (n + 2))
                (roots (n + 1)) who| + η) := by
    intro n who
    have hrec :=
      quittingRootSequenceTerminalValue_eq_successorPayoff_tailVector
        reward roots who n
    have haffineActual :=
      quittingRootExpectedPayoff_eq_absorbingContribution_add reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) who
    have haffinePlan :=
      quittingRootExpectedPayoff_eq_absorbingContribution_add reward
        (plan (n + 1)) (roots n) who
    have hdiff : quittingRootSequenceTerminalValue reward roots who n -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who =
        quittingStationaryContinueMass (roots n) *
          (quittingRootSequenceTerminalValue reward roots who (n + 1) -
            plan (n + 1) who) := by
      rw [hrec]
      have hleft : quittingRootSuccessorPayoff reward
          (quittingRootSequenceTailVector reward roots (n + 1))
          (roots n) who =
          quittingRootAbsorbingContribution reward (roots n) who +
            quittingStationaryContinueMass (roots n) *
              quittingRootSequenceTerminalValue reward roots who (n + 1) :=
        haffineActual
      have hright : quittingRootSuccessorPayoff reward (plan (n + 1))
          (roots n) who =
          quittingRootAbsorbingContribution reward (roots n) who +
            quittingStationaryContinueMass (roots n) * plan (n + 1) who :=
        haffinePlan
      rw [hleft, hright]
      ring
    rw [hdiff, abs_mul,
      abs_of_nonneg (quittingStationaryContinueMass_nonneg (roots n))]
    have htriangle :
        |quittingRootSequenceTerminalValue reward roots who (n + 1) -
            plan (n + 1) who| ≤
          |quittingRootSequenceTerminalValue reward roots who (n + 1) -
              quittingRootSuccessorPayoff reward (plan (n + 2))
                (roots (n + 1)) who| + η := by
      have hstep := hclose (n + 1) who
      rw [abs_sub_comm] at hstep
      calc |quittingRootSequenceTerminalValue reward roots who (n + 1) -
            plan (n + 1) who| ≤
          |quittingRootSequenceTerminalValue reward roots who (n + 1) -
              quittingRootSuccessorPayoff reward (plan (n + 2))
                (roots (n + 1)) who| +
            |quittingRootSuccessorPayoff reward (plan (n + 2))
                (roots (n + 1)) who - plan (n + 1) who| :=
          abs_sub_le _ _ _
        _ ≤ _ + η := by linarith
    have hslope0 : (0 : ℝ) ≤ 1 - δ := by linarith
    exact mul_le_mul (hmass n) htriangle (abs_nonneg _) hslope0
  intro n who
  have hgapBound : ∀ m,
      |quittingRootSequenceTerminalValue reward roots who m -
        quittingRootSuccessorPayoff reward (plan (m + 1)) (roots m) who| ≤
        2 * R := by
    intro m
    obtain ⟨hγ₁, hγ₂⟩ := abs_le.mp (hγBound m who)
    obtain ⟨hv₁, hv₂⟩ := abs_le.mp (hvalueBound m who)
    rw [abs_le]
    constructor <;> linarith
  have hscalar := Math.le_div_of_forall_le_mul_succ_add
    (u := fun m => |quittingRootSequenceTerminalValue reward roots who m -
      quittingRootSuccessorPayoff reward (plan (m + 1)) (roots m) who|)
    (slope := 1 - δ) (slack := η) (bound := 2 * R)
    (by linarith) (by linarith) hη0 hgapBound
    (fun m => honestep m who) n
  have hslope : 1 - (1 - δ) = δ := by ring
  rw [hslope] at hscalar
  exact hscalar

omit [DecidableEq ι] in
/-- Compatibility form of rounding-error contraction, with the survival
factor weakened away. -/
theorem abs_terminalValue_sub_successor_le_of_approximate_chain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (plan : ℕ → Payoff ι)
    {R δ η : ℝ} (hR0 : 0 ≤ R) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η)
    (hreward : ∀ terminal player, |reward terminal player| ≤ R)
    (hplanBound : ∀ n who, |plan n who| ≤ R)
    (hmass : ∀ n, quittingStationaryContinueMass (roots n) ≤ 1 - δ)
    (hclose : ∀ n who,
      |plan n who -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤ η) :
    ∀ n who,
      |quittingRootSequenceTerminalValue reward roots who n -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤
        η / δ := by
  intro n who
  have hsharp :=
    abs_terminalValue_sub_successor_le_of_approximate_chain_sharp reward roots
      plan hR0 hδ0 hδ1 hη0 hreward hplanBound hmass hclose n who
  have hfactor : (1 - δ) * η / δ ≤ η / δ := by
    gcongr
    nlinarith
  exact hsharp.trans hfactor

/-! ## The perfect absorbing sequence -/

/-- **A periodic perfect absorbing root sequence.**  Under unit solo exit and
a low active Quit endpoint at every absorbing root, every positive row tolerance admits a periodic sequence
with a positive uniform absorption floor whose rows are perfect against their
actual next-stage continuation values. -/
theorem exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hlowRoot : HasLowActiveQuittingRootQuitPayoff reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (δ : ℝ) (period : ℕ),
      0 < δ ∧ 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) ∧
      ∀ n, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) ε := by
  classical
  set R := quittingRewardBound reward with hRdef
  have hR0 : 0 ≤ R := quittingRewardBound_nonneg reward
  have hrewardR : ∀ terminal player, |reward terminal player| ≤ R :=
    abs_reward_le_quittingRewardBound reward
  set δ := min 1 (ε / (8 * R + 1)) with hδdef
  have hδ0 : 0 < δ :=
    lt_min one_pos (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  set η := δ ^ 2 * ε / 8 with hηdef
  have hη0 : 0 < η := by positivity
  -- The one-shot row selector, as a total choice function.
  have hselect : ∀ tail : Payoff ι, ∃ root : ι → PMF Bool,
      ((∀ who, |tail who| ≤ R) ∧ ∃ who, tail who ≤ 1) →
        QuittingRowεPerfect reward tail root (4 * R * δ) ∧
          δ ≤ quittingRootAbsorptionMass root ∧
          ∃ who, quittingRootSuccessorPayoff reward tail root who ≤ 1 := by
    intro tail
    by_cases htail : (∀ who, |tail who| ≤ R) ∧ ∃ who, tail who ≤ 1
    · obtain ⟨root, hroot⟩ :=
        exists_quittingPerfectAbsorbingRow_of_lowActiveQuitPayoff hunit hlowRoot
          tail htail.1 htail.2 hδ0 hδ1
      exact ⟨root, fun _ => hroot⟩
    · exact ⟨fun _ => PMF.pure false, fun hcontra => absurd hcontra htail⟩
  choose rowOf hrowOf using hselect
  -- The representative selector on grid keys.
  have hrepExists : ∀ key : ι → ℤ, ∃ tail : Payoff ι,
      ((∀ who, |tail who| ≤ R) ∧ ∃ who, tail who ≤ 1) ∧
        ((∃ tail' : Payoff ι,
            ((∀ who, |tail' who| ≤ R) ∧ ∃ who, tail' who ≤ 1) ∧
              ∀ who, ⌊tail' who / η⌋ = key who) →
          ∀ who, ⌊tail who / η⌋ = key who) := by
    intro key
    by_cases hkey : ∃ tail' : Payoff ι,
        ((∀ who, |tail' who| ≤ R) ∧ ∃ who, tail' who ≤ 1) ∧
          ∀ who, ⌊tail' who / η⌋ = key who
    · obtain ⟨tail', htail', hkey'⟩ := hkey
      exact ⟨tail', htail', fun _ => hkey'⟩
    · refine ⟨fun _ => 0, ⟨fun who => by simpa using hR0, ?_⟩,
        fun hcontra => absurd hcontra hkey⟩
      obtain ⟨someone⟩ := ‹Nonempty ι›
      exact ⟨someone, by norm_num⟩
  choose rep hrepCarrier hrepKey using hrepExists
  -- The induced key dynamics has a finite absorbing range.
  set dynamics : (ι → ℤ) → (ι → ℤ) := fun key who =>
    ⌊quittingRootSuccessorPayoff reward (rep key) (rowOf (rep key)) who / η⌋
    with hdynamics
  have hsuccessorBound : ∀ key who,
      |quittingRootSuccessorPayoff reward (rep key) (rowOf (rep key)) who| ≤
        R := fun key who =>
    abs_quittingRootExpectedPayoff_le_bound reward (rep key) (rowOf (rep key))
      who hrewardR (hrepCarrier key).1
  have hrange : ∀ key, dynamics key ∈
      {key : ι → ℤ | ∀ who, key who ∈ Set.Icc ⌊(-R) / η⌋ ⌊R / η⌋} := by
    intro key who
    obtain ⟨hlow, hhigh⟩ := abs_le.mp (hsuccessorBound key who)
    constructor
    · exact Int.floor_le_floor (by gcongr)
    · exact Int.floor_le_floor (by gcongr)
  have hrangeFinite :
      ({key : ι → ℤ | ∀ who, key who ∈ Set.Icc ⌊(-R) / η⌋ ⌊R / η⌋}).Finite := by
    apply Set.Finite.subset
      (Set.Finite.pi fun _ : ι => Set.finite_Icc ⌊(-R) / η⌋ ⌊R / η⌋)
    intro key hkey
    rw [Set.mem_pi]
    exact fun who _ => hkey who
  obtain ⟨period, keyChain, hperiod0, hkeyPeriodic, hkeyChain⟩ :=
    Math.exists_periodic_backward_orbit dynamics (fun _ => 0)
      hrangeFinite hrange
  -- The plan and the row sequence.
  set plan : ℕ → Payoff ι := fun n => rep (keyChain n) with hplan
  set roots : ℕ → ι → PMF Bool := fun n => rowOf (plan (n + 1)) with hrootsdef
  have hplanCarrier : ∀ n,
      (∀ who, |plan n who| ≤ R) ∧ ∃ who, plan n who ≤ 1 :=
    fun n => hrepCarrier (keyChain n)
  have hrowSpec : ∀ n,
      QuittingRowεPerfect reward (plan (n + 1)) (roots n) (4 * R * δ) ∧
        δ ≤ quittingRootAbsorptionMass (roots n) ∧
        ∃ who,
          quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who ≤
            1 :=
    fun n => hrowOf (plan (n + 1)) (hplanCarrier (n + 1))
  -- Each produced value achieves the chain's key, so the representative and
  -- the produced value agree to within one mesh.
  have hvalueKey : ∀ n who,
      ⌊quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who / η⌋ =
        keyChain n who := by
    intro n who
    have h := congrFun (hkeyChain n) who
    exact h.symm
  have hvalueCarrier : ∀ n,
      (∀ who,
          |quittingRootSuccessorPayoff reward (plan (n + 1))
            (roots n) who| ≤ R) ∧
        ∃ who,
          quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who ≤
            1 := by
    intro n
    refine ⟨fun who => ?_, (hrowSpec n).2.2⟩
    exact abs_quittingRootExpectedPayoff_le_bound reward (plan (n + 1))
      (roots n) who hrewardR (hplanCarrier (n + 1)).1
  have hplanKey : ∀ n who, ⌊plan n who / η⌋ = keyChain n who := by
    intro n who
    exact hrepKey (keyChain n)
      ⟨quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n),
        hvalueCarrier n, hvalueKey n⟩ who
  have hclose : ∀ n who,
      |plan n who -
        quittingRootSuccessorPayoff reward (plan (n + 1)) (roots n) who| ≤
        η := by
    intro n who
    exact Math.abs_sub_le_of_floor_div_eq hη0
      ((hplanKey n who).trans (hvalueKey n who).symm)
  -- The contraction bounds the actual continuation error by `η / δ`.
  have hmass : ∀ n, quittingStationaryContinueMass (roots n) ≤ 1 - δ := by
    intro n
    have habsorb := (hrowSpec n).2.1
    unfold quittingRootAbsorptionMass at habsorb
    linarith
  have hcontraction := abs_terminalValue_sub_successor_le_of_approximate_chain
    reward roots plan hR0 hδ0 hδ1 hη0.le hrewardR
    (fun n who => (hplanCarrier n).1 who) hmass hclose
  have hrootsPeriodic : ∀ n, roots (n + period) = roots n := by
    intro n
    simp only [hrootsdef, hplan]
    rw [show n + period + 1 = (n + 1) + period by omega,
      hkeyPeriodic (n + 1)]
  refine ⟨roots, δ, period, hδ0, hperiod0, hrootsPeriodic,
    fun n => (hrowSpec n).2.1, fun n => ?_⟩
  -- Transfer perfectness from the plan tail to the actual tail.
  have hplanToActual : ∀ who,
      |plan (n + 1) who -
        quittingRootSequenceTailVector reward roots (n + 1) who| ≤
        η / δ + η := by
    intro who
    have hcontractionStep := hcontraction (n + 1) who
    have hcloseStep := hclose (n + 1) who
    calc |plan (n + 1) who -
          quittingRootSequenceTailVector reward roots (n + 1) who| ≤
        |plan (n + 1) who -
            quittingRootSuccessorPayoff reward (plan (n + 2))
              (roots (n + 1)) who| +
          |quittingRootSuccessorPayoff reward (plan (n + 2))
              (roots (n + 1)) who -
            quittingRootSequenceTailVector reward roots (n + 1) who| :=
          abs_sub_le _ _ _
      _ ≤ η + (η / δ) := by
          rw [abs_sub_comm] at hcontractionStep
          exact add_le_add hcloseStep hcontractionStep
      _ = η / δ + η := by ring
  have hηδ0 : (0 : ℝ) ≤ η / δ + η := by positivity
  have htransfer := quittingRowεPerfect_of_tail_close (hrowSpec n).1 hηδ0
    hplanToActual
  apply quittingRowεPerfect_mono htransfer
  -- Arithmetic: `4 R δ + 2 (η/δ + η) ≤ ε` by the choices of `δ` and `η`.
  have hδle : δ ≤ ε / (8 * R + 1) := min_le_right _ _
  have hδmul : δ * (8 * R + 1) ≤ ε := by
    have h := mul_le_mul_of_nonneg_right hδle
      (by linarith : (0 : ℝ) ≤ 8 * R + 1)
    rwa [div_mul_cancel₀ ε (by linarith : (8 : ℝ) * R + 1 ≠ 0)] at h
  have hηδ : η / δ = δ * ε / 8 := by
    rw [hηdef, show δ ^ 2 * ε / 8 = δ * (δ * ε / 8) from by ring]
    exact mul_div_cancel_left₀ _ hδ0.ne'
  have hηsmall : η ≤ δ * ε / 8 := by
    rw [hηdef]
    nlinarith [mul_nonneg (mul_nonneg hδ0.le (sub_nonneg.mpr hδ1)) hε.le]
  have hδε : δ * ε ≤ ε := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ1) hε.le]
  rw [hηδ]
  linarith [hδmul, hηsmall, hδε]

/-- The capped-joint-exit source is the direct stronger-assumption
corollary of the low-active-Quit construction. -/
theorem exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (δ : ℝ) (period : ℕ),
      0 < δ ∧ 0 < period ∧
      (∀ n, roots (n + period) = roots n) ∧
      (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) ∧
      ∀ n, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) ε :=
  exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff
    hunit (hasLowActiveQuittingRootQuitPayoff_of_cappedJointExit hcap) hε

/-- Projection of the generic periodic construction for callers that do
not need its literal period. -/
theorem exists_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hlowRoot : HasLowActiveQuittingRootQuitPayoff reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (δ : ℝ), 0 < δ ∧
      (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) ∧
      ∀ n, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) ε := by
  obtain ⟨roots, δ, _period, hδ0, _hperiod0, _hperiodic, hfloor, hperfect⟩ :=
    exists_periodic_quittingPerfectAbsorbingRootSequence_of_lowActiveQuitPayoff
      hunit hlowRoot hε
  exact ⟨roots, δ, hδ0, hfloor, hperfect⟩

/-- The capped-joint-exit construction, with its periodicity omitted from the conclusion. -/
theorem exists_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (roots : ℕ → ι → PMF Bool) (δ : ℝ), 0 < δ ∧
      (∀ n, δ ≤ quittingRootAbsorptionMass (roots n)) ∧
      ∀ n, QuittingRowεPerfect reward
        (quittingRootSequenceTailVector reward roots (n + 1)) (roots n) ε := by
  obtain ⟨roots, δ, _period, hδ0, _hperiod0, _hperiodic, hfloor, hperfect⟩ :=
    exists_periodic_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
      hunit hcap hε
  exact ⟨roots, δ, hδ0, hfloor, hperfect⟩

/-- Unit solo exit and capped joint exit imply branch S.3: for every positive
tolerance there is a completely absorbing sequentially perfect root sequence. -/
theorem quittingSequentiallyεPerfectAbsorbingExistence_of_soloExitPreference
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward)
    (hcap : QuittingCappedJointExit reward) :
    QuittingSequentiallyεPerfectAbsorbingExistence reward := by
  intro ε hε
  obtain ⟨roots, δ, hδ0, hfloor, hperfect⟩ :=
    exists_quittingPerfectAbsorbingRootSequence_of_soloExitPreference
      hunit hcap hε
  refine ⟨roots, ?_, hperfect⟩
  have hδ1 : δ ≤ 1 := by
    have hstage := hfloor 0
    have hmass := quittingStationaryContinueMass_nonneg (roots 0)
    unfold quittingRootAbsorptionMass at hstage
    linarith
  have hbase0 : 0 ≤ 1 - δ := by linarith
  have hbase1 : 1 - δ < 1 := by linarith
  have hsurvival : ∀ fuel,
      quittingSurvivalPrefix roots fuel ≤ (1 - δ) ^ fuel := by
    intro fuel
    induction fuel with
    | zero => simp
    | succ fuel ih =>
        rw [show fuel + 1 = Nat.succ fuel by omega,
          show Nat.succ fuel = fuel + 1 by omega,
          quittingSurvivalPrefix_succ, pow_succ]
        have hmass0 := quittingStationaryContinueMass_nonneg (roots fuel)
        have hmass : quittingStationaryContinueMass (roots fuel) ≤ 1 - δ := by
          have hstage := hfloor fuel
          unfold quittingRootAbsorptionMass at hstage
          linarith
        exact mul_le_mul ih hmass hmass0 (pow_nonneg hbase0 fuel)
  unfold IsCompletelyAbsorbing
  exact squeeze_zero
    (quittingSurvivalPrefix_nonneg roots)
    hsurvival
    (tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1)

/-- Positive own-solo payoffs and weak solo-exit preference imply branch S.3.
Playerwise positive scaling normalizes every own-solo payoff to one, after
which weak preference is exactly the capped-joint-exit hypothesis. -/
theorem quittingSequentiallyεPerfectAbsorbingExistence_of_positiveSolo_of_weakPreference
    [Nonempty ι] {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hsolo : ∀ who, 0 < quittingSoloReward reward who who)
    (hweak : QuittingWeakSoloExitPreference reward) :
    QuittingSequentiallyεPerfectAbsorbingExistence reward := by
  let factor : Payoff ι := fun who => (quittingSoloReward reward who who)⁻¹
  let scaledReward : {S : Finset ι // S.Nonempty} → Payoff ι :=
    fun S who => factor who * reward S who
  have hunit : QuittingUnitSoloExit scaledReward := by
    intro who
    change factor who * quittingSoloReward reward who who = 1
    dsimp [factor]
    exact inv_mul_cancel₀ (ne_of_gt (hsolo who))
  have hcap : QuittingCappedJointExit scaledReward := by
    intro quitters who hmem
    change factor who * reward quitters who ≤ 1
    have hle := hweak quitters who hmem
    calc
      factor who * reward quitters who ≤
          factor who * quittingSoloReward reward who who :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr (hsolo who).le)
      _ = 1 := by
        dsimp [factor]
        exact inv_mul_cancel₀ (ne_of_gt (hsolo who))
  have hscaled : QuittingSequentiallyεPerfectAbsorbingExistence scaledReward :=
    quittingSequentiallyεPerfectAbsorbingExistence_of_soloExitPreference
      hunit hcap
  let scaledTable := repositoryQuittingPayoffTable scaledReward
  have hscaledTable : scaledTable.SequentiallyεPerfectAbsorbingExistence := by
    rw [scaledTable.sequentiallyεPerfectAbsorbingExistence_iff]
    have hzero : scaledTable.zeroNeverReward = scaledReward := by
      funext S who
      simp [scaledTable, QuittingPayoffTable.zeroNeverReward,
        repositoryQuittingPayoffTable]
    rw [hzero]
    exact hscaled
  let solo : Payoff ι := fun who => quittingSoloReward reward who who
  have hsoloNonneg : ∀ who, 0 ≤ solo who := fun who => (hsolo who).le
  have hrescaled := scaledTable.sequentiallyεPerfectAbsorbingExistence_scale
    solo hsoloNonneg hscaledTable
  have htable : scaledTable.scale solo = repositoryQuittingPayoffTable reward := by
    ext S who
    · change solo who * (factor who * reward S who) = reward S who
      have hproduct : solo who * factor who = 1 := by
        dsimp [solo, factor]
        exact mul_inv_cancel₀ (ne_of_gt (hsolo who))
      calc
        solo who * (factor who * reward S who) =
            (solo who * factor who) * reward S who := by ring
        _ = reward S who := by rw [hproduct, one_mul]
    · simp [scaledTable, QuittingPayoffTable.scale,
        repositoryQuittingPayoffTable]
  rw [htable] at hrescaled
  have horiginal :=
    (QuittingPayoffTable.sequentiallyεPerfectAbsorbingExistence_iff
      (repositoryQuittingPayoffTable reward)).mp hrescaled
  have hzero : (repositoryQuittingPayoffTable reward).zeroNeverReward =
      reward := by
    funext S who
    simp [QuittingPayoffTable.zeroNeverReward,
      repositoryQuittingPayoffTable]
  rwa [hzero] at horiginal

/-- Table-level form of the positive-solo weak-preference S.3 producer.  The
conditions are imposed after subtracting the never payoff, as required by
playerwise translation invariance. -/
theorem QuittingPayoffTable.sequentiallyεPerfectAbsorbingExistence_of_positiveSolo_of_weakPreference
    [Nonempty ι] (table : QuittingPayoffTable ι)
    (hsolo : ∀ who, 0 < quittingSoloReward table.zeroNeverReward who who)
    (hweak : QuittingWeakSoloExitPreference table.zeroNeverReward) :
    table.SequentiallyεPerfectAbsorbingExistence := by
  rw [table.sequentiallyεPerfectAbsorbingExistence_iff]
  exact quittingSequentiallyεPerfectAbsorbingExistence_of_positiveSolo_of_weakPreference
    hsolo hweak
