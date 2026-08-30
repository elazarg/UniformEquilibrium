/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel

/-!
# Summable seams in chronological terminal-semantic chains

This module separates arbitrary finite-dimensional annotations from the
literal semantic pairs of the executed root sequence.  A flattened seam
chain supplies, at every date, an artificial successor pair from which the
current candidate pair is computed exactly.  The artificial successor need
not equal the next candidate pair; their two coordinate discrepancies are
the seams.

Summable seams provide all non-survival fields of chronological debt
shadowing.  The same literal roots must separately satisfy joint and every
player-deleted survival.  A second result shows that bounded annotations
cannot conceal a different literal terminal semantic pair: its discrepancy
is bounded by the corresponding seam toll.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## One-root coordinate estimates -/

/-- The prescribed coordinate of one semantic prefix transports a successor
difference by exactly the joint Continue mass. -/
theorem abs_quittingTerminalSemanticPrefix_prescribed_sub_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (first second : QuittingTerminalSemanticPair ι)
    (who : ι) :
    |(quittingTerminalSemanticPrefix reward root first).1 who -
        (quittingTerminalSemanticPrefix reward root second).1 who| =
      quittingStationaryContinueMass root *
        |first.1 who - second.1 who| := by
  change |quittingRootSuccessorPayoff reward first.1 root who -
      quittingRootSuccessorPayoff reward second.1 root who| = _
  unfold quittingRootSuccessorPayoff
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  have hmass : 0 ≤ quittingStationaryContinueMass root :=
    quittingStationaryContinueMass_nonneg root
  rw [show
      quittingRootAbsorbingContribution reward root who +
          quittingStationaryContinueMass root * first.1 who -
        (quittingRootAbsorbingContribution reward root who +
          quittingStationaryContinueMass root * second.1 who) =
        quittingStationaryContinueMass root *
          (first.1 who - second.1 who) by ring,
    abs_mul, abs_of_nonneg hmass]

/-- Exact positive-seam regression: at a unit joint-survival row a positive
prescribed successor seam is transmitted without attenuation. -/
theorem quittingTerminalSemanticPrefix_prescribed_positiveSeam_regression
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (first second : QuittingTerminalSemanticPair ι)
    (who : ι) (delta : ℝ)
    (hmass : quittingStationaryContinueMass root = 1)
    (hdelta : |first.1 who - second.1 who| = delta)
    (_hpositive : 0 < delta) :
    |(quittingTerminalSemanticPrefix reward root first).1 who -
        (quittingTerminalSemanticPrefix reward root second).1 who| = delta := by
  rw [abs_quittingTerminalSemanticPrefix_prescribed_sub_eq,
    hmass, one_mul, hdelta]

/-- The cap coordinate of one semantic prefix is Lipschitz with the sharp
player-deleted Continue mass.  Max-branch switches are allowed. -/
theorem abs_quittingTerminalSemanticPrefix_cap_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (first second : QuittingTerminalSemanticPair ι)
    (who : ι) :
    |(quittingTerminalSemanticPrefix reward root first).2 who -
        (quittingTerminalSemanticPrefix reward root second).2 who| ≤
      quittingRootOpponentContinueMass root who *
        |first.2 who - second.2 who| := by
  have hquit : quittingRootQuitPayoff reward first.1 root who =
      quittingRootQuitPayoff reward second.1 root who :=
    quittingRootQuitPayoff_continuation_invariant reward first.1 second.1 root who
  have hfirst : quittingRootContinuePayoff
      reward (Function.update first.1 who (first.2 who)) root who =
      quittingRootContinuePayoff
        reward (Function.update second.1 who (first.2 who)) root who := by
    unfold quittingRootContinuePayoff
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  have hcontinue :
      quittingRootContinuePayoff
          reward (Function.update first.1 who (first.2 who)) root who -
        quittingRootContinuePayoff
          reward (Function.update second.1 who (second.2 who)) root who =
      quittingRootOpponentContinueMass root who *
        (first.2 who - second.2 who) := by
    rw [hfirst]
    have hadd := quittingRootContinuePayoff_update_add reward
      (Function.update second.1 who (second.2 who)) root who
      (first.2 who - second.2 who)
    simpa using congrArg
      (fun value => value - quittingRootContinuePayoff
        reward (Function.update second.1 who (second.2 who)) root who) hadd
  unfold quittingTerminalSemanticPrefix
  dsimp only
  rw [hquit]
  calc
    |max (quittingRootQuitPayoff reward second.1 root who)
          (quittingRootContinuePayoff reward
            (Function.update first.1 who (first.2 who)) root who) -
        max (quittingRootQuitPayoff reward second.1 root who)
          (quittingRootContinuePayoff reward
            (Function.update second.1 who (second.2 who)) root who)| ≤
        |quittingRootContinuePayoff reward
            (Function.update first.1 who (first.2 who)) root who -
          quittingRootContinuePayoff reward
            (Function.update second.1 who (second.2 who)) root who| := by
      rw [max_comm (quittingRootQuitPayoff reward second.1 root who),
        max_comm (quittingRootQuitPayoff reward second.1 root who)]
      exact abs_max_sub_max_le_abs _ _ _
    _ = quittingRootOpponentContinueMass root who *
        |first.2 who - second.2 who| := by
      rw [hcontinue, abs_mul, abs_of_nonneg
        (quittingRootOpponentContinueMass_nonneg root who)]

/-- Semantic debt inherits the sum of the prescribed and cap coordinate
seam bounds. -/
theorem abs_quittingTerminalSemanticDebt_prefix_sub_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (first second : QuittingTerminalSemanticPair ι)
    (who : ι) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root first) who -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefix reward root second) who| ≤
      quittingStationaryContinueMass root *
          |first.1 who - second.1 who| +
        quittingRootOpponentContinueMass root who *
          |first.2 who - second.2 who| := by
  unfold quittingTerminalSemanticDebt
  rw [show
      ((quittingTerminalSemanticPrefix reward root first).2 who -
          (quittingTerminalSemanticPrefix reward root first).1 who) -
        ((quittingTerminalSemanticPrefix reward root second).2 who -
          (quittingTerminalSemanticPrefix reward root second).1 who) =
      ((quittingTerminalSemanticPrefix reward root first).2 who -
          (quittingTerminalSemanticPrefix reward root second).2 who) -
        ((quittingTerminalSemanticPrefix reward root first).1 who -
          (quittingTerminalSemanticPrefix reward root second).1 who) by ring]
  calc
    |((quittingTerminalSemanticPrefix reward root first).2 who -
          (quittingTerminalSemanticPrefix reward root second).2 who) -
        ((quittingTerminalSemanticPrefix reward root first).1 who -
          (quittingTerminalSemanticPrefix reward root second).1 who)| ≤
      |(quittingTerminalSemanticPrefix reward root first).2 who -
        (quittingTerminalSemanticPrefix reward root second).2 who| +
      |(quittingTerminalSemanticPrefix reward root first).1 who -
        (quittingTerminalSemanticPrefix reward root second).1 who| :=
      abs_sub _ _
    _ ≤ _ := add_le_add
      (abs_quittingTerminalSemanticPrefix_cap_sub_le
        reward root first second who)
      (le_of_eq (abs_quittingTerminalSemanticPrefix_prescribed_sub_eq
        reward root first second who))
    _ = _ := by ring

/-! ## Flattened artificial seam chains -/

/-- A bounded artificial Bellman chain attached to one literal root schedule.
The `candidate` and `successor` pairs are arbitrary annotations.  Only
`exact_step` relates them; neither is asserted to be behaviorally realized. -/
structure QuittingBoundedSeamChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  candidate : ℕ → QuittingTerminalSemanticPair ι
  successor : ℕ → QuittingTerminalSemanticPair ι
  exact_step : ∀ time, candidate time =
    quittingTerminalSemanticPrefix reward (roots time) (successor time)
  debt_nonneg : ∀ time who,
    0 ≤ quittingTerminalSemanticDebt (candidate time) who
  prescribed_bounded : ∃ bound : ℝ,
    ∀ time who, |(candidate time).1 who| ≤ bound
  debt_bounded : ∃ bound : ℝ,
    ∀ time who, |quittingTerminalSemanticDebt (candidate time) who| ≤ bound

namespace QuittingBoundedSeamChain

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (chain : QuittingBoundedSeamChain reward)

private theorem sum_range_nat_add_le_tsum
    (stream : ℕ → ℝ) (hstream0 : ∀ time, 0 ≤ stream time)
    (hsummable : Summable stream) (start length : ℕ) :
    (∑ offset ∈ Finset.range length, stream (start + offset)) ≤
      ∑' time, stream time := by
  have htailSummable : Summable (fun offset => stream (start + offset)) := by
    simpa [Nat.add_comm] using (summable_nat_add_iff start).2 hsummable
  have hfinite :
      (∑ offset ∈ Finset.range length, stream (start + offset)) ≤
        ∑' offset, stream (start + offset) :=
    htailSummable.sum_le_tsum _ (fun offset _ => hstream0 _)
  have hsplit := hsummable.sum_add_tsum_nat_add start
  have hprefix0 : 0 ≤ ∑ offset ∈ Finset.range start, stream offset :=
    Finset.sum_nonneg fun offset _ => hstream0 offset
  have htailLe : (∑' offset, stream (start + offset)) ≤ ∑' time, stream time := by
    have hsplit' : (∑ offset ∈ Finset.range start, stream offset) +
        (∑' offset, stream (start + offset)) = ∑' time, stream time := by
      simpa [Nat.add_comm] using hsplit
    linarith
  exact hfinite.trans htailLe

/-- Prescribed-coordinate seam between the artificial successor and the next
calendar candidate. -/
def prescribedSeam (who : ι) (time : ℕ) : ℝ :=
  |(chain.successor time).1 who - (chain.candidate (time + 1)).1 who|

/-- Cap-coordinate seam between the artificial successor and the next
calendar candidate. -/
def capSeam (who : ι) (time : ℕ) : ℝ :=
  |(chain.successor time).2 who - (chain.candidate (time + 1)).2 who|

/-- Total two-coordinate seam toll for one player. -/
def totalSeam (who : ι) (time : ℕ) : ℝ :=
  chain.prescribedSeam who time + chain.capSeam who time

theorem prescribedSeam_nonneg (who : ι) (time : ℕ) :
    0 ≤ chain.prescribedSeam who time := abs_nonneg _

theorem capSeam_nonneg (who : ι) (time : ℕ) :
    0 ≤ chain.capSeam who time := abs_nonneg _

theorem totalSeam_nonneg (who : ι) (time : ℕ) :
    0 ≤ chain.totalSeam who time :=
  add_nonneg (chain.prescribedSeam_nonneg who time)
    (chain.capSeam_nonneg who time)

/-- The actual semantic pair of the literal suffix beginning at `time`. -/
def actualPair (time : ℕ) : QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPair reward
    (quittingRootSequenceProfile reward chain.roots time)

/-- Generated cap secant comparing the next candidate with the actual next
literal suffix. -/
def generatedSecant (time : ℕ) (who : ι) : ℝ :=
  Classical.choose
    (exists_quittingTerminalSemanticPrefix_secant reward (chain.roots time)
      (chain.candidate (time + 1)) (chain.actualPair (time + 1)) who)

private theorem generatedSecant_spec (time : ℕ) (who : ι) :
    0 ≤ chain.generatedSecant time who ∧
      chain.generatedSecant time who ≤
        quittingRootOpponentContinueMass (chain.roots time) who ∧
      (quittingTerminalSemanticPrefix reward (chain.roots time)
          (chain.actualPair (time + 1))).2 who -
        (quittingTerminalSemanticPrefix reward (chain.roots time)
          (chain.candidate (time + 1))).2 who =
      chain.generatedSecant time who *
        ((chain.actualPair (time + 1)).2 who -
          (chain.candidate (time + 1)).2 who) :=
  Classical.choose_spec
    (exists_quittingTerminalSemanticPrefix_secant reward (chain.roots time)
      (chain.candidate (time + 1)) (chain.actualPair (time + 1)) who)

/-- Exact chronological data obtained from the arbitrary candidate pairs and
the same literal roots. -/
def chronologicalData : QuittingChronologicalDebtData ι where
  roots := chain.roots
  prescribed := fun time => (chain.candidate time).1
  debt := fun time who => quittingTerminalSemanticDebt (chain.candidate time) who
  secant := chain.generatedSecant

@[simp] theorem chronologicalData_root (time : ℕ) :
    chain.chronologicalData.root time = chain.roots time := rfl

@[simp] theorem chronologicalData_semanticPair (time : ℕ) :
    chain.chronologicalData.semanticPair reward time = chain.actualPair time :=
  rfl

@[simp] theorem chronologicalData_candidateSuccessorPair (time : ℕ) :
    chain.chronologicalData.candidateSuccessorPair time =
      chain.candidate (time + 1) := by
  apply Prod.ext
  · rfl
  · funext who
    simp [chronologicalData, QuittingChronologicalDebtData.candidateSuccessorPair,
      quittingTerminalSemanticDebt]

theorem chronologicalData_secant_nonneg (time : ℕ) (who : ι) :
    0 ≤ chain.chronologicalData.secant time who :=
  (chain.generatedSecant_spec time who).1

theorem chronologicalData_secant_le_opponentContinue
    (time : ℕ) (who : ι) :
    chain.chronologicalData.secant time who ≤
      quittingRootOpponentContinueMass
        (chain.chronologicalData.root time) who :=
  (chain.generatedSecant_spec time who).2.1

theorem chronologicalData_secant_generated (time : ℕ) (who : ι) :
    (chain.chronologicalData.semanticPair reward time).2 who -
        (quittingTerminalSemanticPrefix reward
          (chain.chronologicalData.root time)
          (chain.chronologicalData.candidateSuccessorPair time)).2 who =
      chain.chronologicalData.secant time who *
        ((chain.chronologicalData.semanticPair reward (time + 1)).2 who -
          (chain.chronologicalData.candidateSuccessorPair time).2 who) := by
  have hprefix := congrArg
    (fun pair : QuittingTerminalSemanticPair ι => pair.2 who)
    (QuittingChronologicalDebtData.semanticPair_eq_prefix
      chain.chronologicalData reward time)
  rw [hprefix, chain.chronologicalData_candidateSuccessorPair]
  exact (chain.generatedSecant_spec time who).2.2

theorem abs_chronologicalData_prescribedDefect_le
    (time : ℕ) (who : ι) :
    |chain.chronologicalData.prescribedDefect reward time who| ≤
      chain.prescribedSeam who time := by
  have hstep := congrArg
    (fun pair : QuittingTerminalSemanticPair ι => pair.1 who)
    (chain.exact_step time)
  unfold QuittingChronologicalDebtData.prescribedDefect
  rw [chain.chronologicalData_candidateSuccessorPair,
    chain.chronologicalData_root]
  change |(chain.candidate time).1 who -
    (quittingTerminalSemanticPrefix reward (chain.roots time)
      (chain.candidate (time + 1))).1 who| ≤ _
  rw [hstep]
  rw [abs_quittingTerminalSemanticPrefix_prescribed_sub_eq]
  exact mul_le_of_le_one_left (abs_nonneg _)
    (quittingStationaryContinueMass_le_one (chain.roots time))

theorem abs_chronologicalData_directDebtDefect_le
    (time : ℕ) (who : ι) :
    |chain.chronologicalData.directDebtDefect reward time who| ≤
      chain.totalSeam who time := by
  have hstep := congrArg
    (fun pair : QuittingTerminalSemanticPair ι =>
      quittingTerminalSemanticDebt pair who) (chain.exact_step time)
  unfold QuittingChronologicalDebtData.directDebtDefect
  rw [chain.chronologicalData_candidateSuccessorPair,
    chain.chronologicalData_root]
  change |quittingTerminalSemanticDebt (chain.candidate time) who -
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefix reward (chain.roots time)
        (chain.candidate (time + 1))) who| ≤ _
  rw [hstep]
  refine (abs_quittingTerminalSemanticDebt_prefix_sub_le reward
    (chain.roots time) (chain.successor time)
    (chain.candidate (time + 1)) who).trans ?_
  unfold totalSeam prescribedSeam capSeam
  exact add_le_add
    (mul_le_of_le_one_left (abs_nonneg _)
      (quittingStationaryContinueMass_le_one (chain.roots time)))
    (mul_le_of_le_one_left (abs_nonneg _)
      (quittingRootOpponentContinueMass_le_one (chain.roots time) who))

/-- Summable seam budgets and a small initial candidate debt provide the full
chronological certificate.  The survival fields refer to exactly the roots
stored in `chain`. -/
theorem nonempty_chronologicalDebtShadowingCertificate
    (eta : ℝ) (heta : 0 < eta)
    (hprescribedSummable : ∀ who, Summable (chain.prescribedSeam who))
    (htotalSummable : ∀ who, Summable (chain.totalSeam who))
    (hprescribedTsum : ∀ who, ∑' time, chain.prescribedSeam who time ≤ eta)
    (htotalTsum : ∀ who, ∑' time, chain.totalSeam who time ≤ eta)
    (hinitial : ∀ who,
      quittingTerminalSemanticDebt (chain.candidate 0) who ≤ eta)
    (hjoint : ∀ start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingStationaryContinueMass (chain.roots time)) start)
        atTop (nhds 0))
    (hopponent : ∀ who start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingRootOpponentContinueMass (chain.roots time) who)
          start) atTop (nhds 0)) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  refine ⟨{
    data := chain.chronologicalData
    eta_pos := heta
    debt_nonneg := chain.debt_nonneg
    prescribed_bounded := chain.prescribed_bounded
    debt_bounded := chain.debt_bounded
    secant_nonneg := chain.chronologicalData_secant_nonneg
    secant_le_opponentContinue :=
      chain.chronologicalData_secant_le_opponentContinue
    secant_generated := chain.chronologicalData_secant_generated
    prescribed_discrepancy := ?_
    adverse_direct_forcing := ?_
    joint_survival := hjoint
    opponent_survival := hopponent
    initial_debt_le := hinitial }⟩
  · intro who start length
    calc
      |∑ offset ∈ Finset.range length,
          chain.chronologicalData.prescribedDefect reward
            (start + offset) who| ≤
          ∑ offset ∈ Finset.range length,
            |chain.chronologicalData.prescribedDefect reward
              (start + offset) who| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ offset ∈ Finset.range length,
          chain.prescribedSeam who (start + offset) := by
        exact Finset.sum_le_sum fun offset _ =>
          chain.abs_chronologicalData_prescribedDefect_le
            (start + offset) who
      _ ≤ ∑' time, chain.prescribedSeam who time := by
        exact sum_range_nat_add_le_tsum (chain.prescribedSeam who)
          (chain.prescribedSeam_nonneg who) (hprescribedSummable who)
          start length
      _ ≤ eta := hprescribedTsum who
  · intro who start slack hslack
    filter_upwards [] with length
    calc
      -∑ offset ∈ Finset.range length,
          Math.survivalProduct
              (fun time => chain.chronologicalData.secant time who)
              start offset *
            chain.chronologicalData.directDebtDefect reward
              (start + offset) who ≤
          ∑ offset ∈ Finset.range length,
            chain.totalSeam who (start + offset) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro offset _
        let weight := Math.survivalProduct
          (fun time => chain.chronologicalData.secant time who) start offset
        have hsec0 : ∀ time,
            0 ≤ chain.chronologicalData.secant time who :=
          fun time => chain.chronologicalData_secant_nonneg time who
        have hsec1 : ∀ time,
            chain.chronologicalData.secant time who ≤ 1 := fun time =>
          (chain.chronologicalData_secant_le_opponentContinue time who).trans
            (quittingRootOpponentContinueMass_le_one _ who)
        have hweight0 : 0 ≤ weight :=
          Math.survivalProduct_nonneg _ hsec0 start offset
        have hweight1 : weight ≤ 1 :=
          Math.survivalProduct_le_one _ hsec0 hsec1 start offset
        calc
          -(weight * chain.chronologicalData.directDebtDefect reward
              (start + offset) who) ≤
              |weight * chain.chronologicalData.directDebtDefect reward
                (start + offset) who| := neg_le_abs _
          _ = weight *
              |chain.chronologicalData.directDebtDefect reward
                (start + offset) who| := by
            rw [abs_mul, abs_of_nonneg hweight0]
          _ ≤ |chain.chronologicalData.directDebtDefect reward
                (start + offset) who| :=
            mul_le_of_le_one_left (abs_nonneg _) hweight1
          _ ≤ chain.totalSeam who (start + offset) :=
            chain.abs_chronologicalData_directDebtDefect_le _ who
      _ ≤ ∑' time, chain.totalSeam who time := by
        exact sum_range_nat_add_le_tsum (chain.totalSeam who)
          (chain.totalSeam_nonneg who) (htotalSummable who) start length
      _ ≤ eta := htotalTsum who
      _ ≤ eta + slack := le_add_of_nonneg_right hslack.le

/-- The same certificate constructor with survival obtained from two
persistent marginal labels on the same literal root sequence. -/
theorem nonempty_chronologicalDebtShadowingCertificate_of_twoPersistent
    (hcard : 2 ≤ Fintype.card ι)
    (hpersistent : HasTwoPersistentQuittingMarginals chain.roots)
    (eta : ℝ) (heta : 0 < eta)
    (hprescribedSummable : ∀ who, Summable (chain.prescribedSeam who))
    (htotalSummable : ∀ who, Summable (chain.totalSeam who))
    (hprescribedTsum : ∀ who, ∑' time, chain.prescribedSeam who time ≤ eta)
    (htotalTsum : ∀ who, ∑' time, chain.totalSeam who time ≤ eta)
    (hinitial : ∀ who,
      quittingTerminalSemanticDebt (chain.candidate 0) who ≤ eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  obtain ⟨hopponent, hjoint⟩ := hpersistent.survival hcard
  apply chain.nonempty_chronologicalDebtShadowingCertificate eta heta
    hprescribedSummable htotalSummable hprescribedTsum htotalTsum hinitial hjoint
  intro who start
  have hfun : Math.survivalProduct
      (fun time => quittingRootOpponentContinueMass
        (chain.roots time) who) start =
      quittingOpponentSurvivalWeight chain.roots who start := by
    funext fuel
    rfl
  rw [hfun]
  exact hopponent who start

/-! ## Semantic rigidity -/

private theorem abs_le_tsum_of_discounted_recursion
    (error cost discount : ℕ → ℝ)
    (hcost0 : ∀ time, 0 ≤ cost time)
    (hcost : Summable cost)
    (hdiscount0 : ∀ time, 0 ≤ discount time)
    (hdiscount1 : ∀ time, discount time ≤ 1)
    (hstep : ∀ time,
      |error time| ≤ cost time + discount time * |error (time + 1)|)
    (hsurvival : Tendsto (Math.survivalProduct discount 0) atTop (nhds 0))
    (hbound : ∃ bound : ℝ, ∀ time, |error time| ≤ bound) :
    |error 0| ≤ ∑' time, cost time := by
  have hfinite : ∀ start length,
      |error start| ≤
        (∑ offset ∈ Finset.range length, cost (start + offset)) +
        Math.survivalProduct discount start length *
          |error (start + length)| := by
    intro start length
    induction length generalizing start with
    | zero => simp [Math.survivalProduct]
    | succ length ih =>
        have htail := ih (start + 1)
        have hsum0 : 0 ≤
            ∑ offset ∈ Finset.range length, cost (start + 1 + offset) :=
          Finset.sum_nonneg fun offset _ => hcost0 _
        calc
          |error start| ≤
              cost start + discount start * |error (start + 1)| :=
            hstep start
          _ ≤ cost start + discount start *
              ((∑ offset ∈ Finset.range length,
                  cost (start + 1 + offset)) +
                Math.survivalProduct discount (start + 1) length *
                  |error (start + 1 + length)|) :=
            add_le_add_right (mul_le_mul_of_nonneg_left htail
              (hdiscount0 start)) _
          _ ≤ cost start +
              (∑ offset ∈ Finset.range length,
                cost (start + 1 + offset)) +
              discount start *
                (Math.survivalProduct discount (start + 1) length *
                  |error (start + 1 + length)|) := by
            have hcostMul : discount start *
                (∑ offset ∈ Finset.range length,
                  cost (start + 1 + offset)) ≤
                ∑ offset ∈ Finset.range length,
                  cost (start + 1 + offset) :=
              mul_le_of_le_one_left hsum0 (hdiscount1 start)
            linarith
          _ = (∑ offset ∈ Finset.range (length + 1),
                cost (start + offset)) +
              Math.survivalProduct discount start (length + 1) *
                |error (start + (length + 1))| := by
            rw [Finset.sum_range_succ', Math.survivalProduct_succ_left]
            ring_nf
  have hfinite' : ∀ length,
      |error 0| ≤ (∑' time, cost time) +
        Math.survivalProduct discount 0 length * |error length| := by
    intro length
    simpa using (hfinite 0 length).trans (add_le_add
      (sum_range_nat_add_le_tsum cost hcost0 hcost 0 length) le_rfl)
  have hterminal : Tendsto (fun length =>
      Math.survivalProduct discount 0 length * |error length|)
      atTop (nhds 0) := by
    simpa using Math.tendsto_survivalProduct_mul_bounded_zero discount
      (fun time => |error time|) 0 hsurvival
      ⟨hbound.choose, fun time => by simpa using hbound.choose_spec time⟩
  have hlimit : Tendsto (fun length => (∑' time, cost time) +
      Math.survivalProduct discount 0 length * |error length|)
      atTop (nhds (∑' time, cost time)) := by
    simpa using tendsto_const_nhds.add hterminal
  exact ge_of_tendsto' hlimit hfinite'

theorem actualPair_eq_prefix (time : ℕ) :
    chain.actualPair time =
      quittingTerminalSemanticPrefix reward (chain.roots time)
        (chain.actualPair (time + 1)) := by
  exact QuittingChronologicalDebtData.semanticPair_eq_prefix
    chain.chronologicalData reward time

private theorem prescribedError_step (who : ι) (time : ℕ) :
    |(chain.actualPair time).1 who - (chain.candidate time).1 who| ≤
      chain.prescribedSeam who time +
        quittingStationaryContinueMass (chain.roots time) *
          |(chain.actualPair (time + 1)).1 who -
            (chain.candidate (time + 1)).1 who| := by
  rw [congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.1 who)
      (chain.actualPair_eq_prefix time),
    congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.1 who)
      (chain.exact_step time)]
  calc
    |_ - _| ≤
        |(quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.actualPair (time + 1))).1 who -
          (quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.candidate (time + 1))).1 who| +
        |(quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.candidate (time + 1))).1 who -
          (quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.successor time)).1 who| := abs_sub_le _ _ _
    _ ≤ quittingStationaryContinueMass (chain.roots time) *
          |(chain.actualPair (time + 1)).1 who -
            (chain.candidate (time + 1)).1 who| +
        chain.prescribedSeam who time := by
      rw [abs_quittingTerminalSemanticPrefix_prescribed_sub_eq,
        abs_quittingTerminalSemanticPrefix_prescribed_sub_eq]
      gcongr
      unfold prescribedSeam
      rw [abs_sub_comm]
      exact mul_le_of_le_one_left (abs_nonneg _)
        (quittingStationaryContinueMass_le_one (chain.roots time))
    _ = _ := by ring

private theorem capError_step (who : ι) (time : ℕ) :
    |(chain.actualPair time).2 who - (chain.candidate time).2 who| ≤
      chain.capSeam who time +
        quittingRootOpponentContinueMass (chain.roots time) who *
          |(chain.actualPair (time + 1)).2 who -
            (chain.candidate (time + 1)).2 who| := by
  rw [congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.2 who)
      (chain.actualPair_eq_prefix time),
    congrArg (fun pair : QuittingTerminalSemanticPair ι => pair.2 who)
      (chain.exact_step time)]
  calc
    |_ - _| ≤
        |(quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.actualPair (time + 1))).2 who -
          (quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.candidate (time + 1))).2 who| +
        |(quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.candidate (time + 1))).2 who -
          (quittingTerminalSemanticPrefix reward (chain.roots time)
            (chain.successor time)).2 who| := abs_sub_le _ _ _
    _ ≤ quittingRootOpponentContinueMass (chain.roots time) who *
          |(chain.actualPair (time + 1)).2 who -
            (chain.candidate (time + 1)).2 who| +
        chain.capSeam who time := by
      exact add_le_add
        (abs_quittingTerminalSemanticPrefix_cap_sub_le reward
          (chain.roots time) (chain.actualPair (time + 1))
          (chain.candidate (time + 1)) who)
        ((abs_quittingTerminalSemanticPrefix_cap_sub_le reward
          (chain.roots time) (chain.candidate (time + 1))
          (chain.successor time) who).trans (by
            unfold capSeam
            rw [abs_sub_comm]
            exact mul_le_of_le_one_left (abs_nonneg _)
              (quittingRootOpponentContinueMass_le_one _ who)))
    _ = _ := by ring

/-- Bounded-chain rigidity for the prescribed coordinate at the initial
literal suffix. -/
theorem abs_actualPair_prescribed_sub_le_tsum
    (who : ι) (hsummable : Summable (chain.prescribedSeam who))
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) 0)
      atTop (nhds 0)) :
    |(chain.actualPair 0).1 who - (chain.candidate 0).1 who| ≤
      ∑' time, chain.prescribedSeam who time := by
  apply abs_le_tsum_of_discounted_recursion
    (fun time => (chain.actualPair time).1 who -
      (chain.candidate time).1 who)
    (chain.prescribedSeam who)
    (fun time => quittingStationaryContinueMass (chain.roots time))
    (chain.prescribedSeam_nonneg who) hsummable
    (fun time => quittingStationaryContinueMass_nonneg _)
    (fun time => quittingStationaryContinueMass_le_one _)
    (chain.prescribedError_step who) hjoint
  obtain ⟨bound, hbound⟩ := chain.prescribed_bounded
  refine ⟨quittingRewardBound reward + bound, fun time => ?_⟩
  exact (abs_sub _ _).trans (add_le_add
    (abs_quittingTerminalPayoff_le_quittingRewardBound reward
      (quittingRootSequenceProfile reward chain.roots time) who)
    (hbound time who))

/-- Bounded-chain rigidity for the all-behavior cap coordinate at the initial
literal suffix. -/
theorem abs_actualPair_cap_sub_le_tsum
    (who : ι) (hsummable : Summable (chain.capSeam who))
    (hopponent : Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who) 0)
      atTop (nhds 0)) :
    |(chain.actualPair 0).2 who - (chain.candidate 0).2 who| ≤
      ∑' time, chain.capSeam who time := by
  apply abs_le_tsum_of_discounted_recursion
    (fun time => (chain.actualPair time).2 who -
      (chain.candidate time).2 who)
    (chain.capSeam who)
    (fun time => quittingRootOpponentContinueMass (chain.roots time) who)
    (chain.capSeam_nonneg who) hsummable
    (fun time => quittingRootOpponentContinueMass_nonneg _ who)
    (fun time => quittingRootOpponentContinueMass_le_one _ who)
    (chain.capError_step who) hopponent
  obtain ⟨prescribedBound, hprescribed⟩ := chain.prescribed_bounded
  obtain ⟨debtBound, hdebt⟩ := chain.debt_bounded
  refine ⟨quittingRewardBound reward + prescribedBound + debtBound,
    fun time => ?_⟩
  calc
    |(chain.actualPair time).2 who - (chain.candidate time).2 who| ≤
        |(chain.actualPair time).2 who| +
          |(chain.candidate time).1 who| +
          |quittingTerminalSemanticDebt (chain.candidate time) who| := by
      unfold quittingTerminalSemanticDebt
      have hcandidate : (chain.candidate time).2 who =
          (chain.candidate time).1 who +
            ((chain.candidate time).2 who -
              (chain.candidate time).1 who) := by ring
      rw [hcandidate]
      calc
        |(chain.actualPair time).2 who -
            ((chain.candidate time).1 who +
              ((chain.candidate time).2 who -
                (chain.candidate time).1 who))| ≤
            |(chain.actualPair time).2 who| +
              |(chain.candidate time).1 who +
                ((chain.candidate time).2 who -
                  (chain.candidate time).1 who)| := abs_sub _ _
        _ ≤ |(chain.actualPair time).2 who| +
            (|(chain.candidate time).1 who| +
              |(chain.candidate time).2 who -
                (chain.candidate time).1 who|) :=
          add_le_add_right (abs_add_le _ _) _
        _ = _ := by ring_nf
    _ ≤ _ := add_le_add (add_le_add
      (abs_quittingContinuationBestResponseValue_le reward
        (quittingRootSequenceProfile reward chain.roots time) who
        (abs_reward_le_quittingRewardBound reward))
      (hprescribed time who)) (hdebt time who)

/-- The actual initial semantic debt differs from the candidate initial debt
by at most the sum of the two seam series. -/
theorem abs_actualDebt_sub_candidateDebt_le_tsum
    (who : ι)
    (hprescribed : Summable (chain.prescribedSeam who))
    (hcap : Summable (chain.capSeam who))
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) 0)
      atTop (nhds 0))
    (hopponent : Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who) 0)
      atTop (nhds 0)) :
    |quittingTerminalSemanticDebt (chain.actualPair 0) who -
        quittingTerminalSemanticDebt (chain.candidate 0) who| ≤
      (∑' time, chain.prescribedSeam who time) +
        ∑' time, chain.capSeam who time := by
  unfold quittingTerminalSemanticDebt
  rw [show
    ((chain.actualPair 0).2 who - (chain.actualPair 0).1 who) -
      ((chain.candidate 0).2 who - (chain.candidate 0).1 who) =
    ((chain.actualPair 0).2 who - (chain.candidate 0).2 who) -
      ((chain.actualPair 0).1 who - (chain.candidate 0).1 who) by ring]
  exact (abs_sub _ _).trans (add_le_add
    (chain.abs_actualPair_cap_sub_le_tsum who hcap hopponent)
    (chain.abs_actualPair_prescribed_sub_le_tsum who hprescribed hjoint) |>.trans_eq
      (add_comm _ _))

/-- A uniform lower bound on total debt of every actual behavior profile is
paid by the candidate initial debt plus the two seam series. -/
theorem actualDebtGap_le_candidate_add_seams
    (delta : ℝ)
    (hgap : ∀ profile : (quittingGame reward).BehaviorProfile,
      delta ≤ ∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who)
    (hprescribed : ∀ who, Summable (chain.prescribedSeam who))
    (hcap : ∀ who, Summable (chain.capSeam who))
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) 0)
      atTop (nhds 0))
    (hopponent : ∀ who, Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who) 0)
      atTop (nhds 0)) :
    delta ≤ ∑ who,
      (quittingTerminalSemanticDebt (chain.candidate 0) who +
        ((∑' time, chain.prescribedSeam who time) +
          ∑' time, chain.capSeam who time)) := by
  calc
    delta ≤ ∑ who, quittingTerminalSemanticDebt (chain.actualPair 0) who :=
      hgap (quittingRootSequenceProfile reward chain.roots 0)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro who _
      have hdiff := chain.abs_actualDebt_sub_candidateDebt_le_tsum who
        (hprescribed who) (hcap who) hjoint (hopponent who)
      have hone := (le_abs_self
        (quittingTerminalSemanticDebt (chain.actualPair 0) who -
          quittingTerminalSemanticDebt (chain.candidate 0) who)).trans hdiff
      linarith

/-- Quantitative seam obstruction: initial candidate debt at most `eta` and
total seam toll at most `eta` force every actual total-debt lower bound below
`2 * card ι * eta`. -/
theorem actualDebtGap_le_two_mul_card_eta
    (delta eta : ℝ)
    (hgap : ∀ profile : (quittingGame reward).BehaviorProfile,
      delta ≤ ∑ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who)
    (hprescribed : ∀ who, Summable (chain.prescribedSeam who))
    (hcap : ∀ who, Summable (chain.capSeam who))
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) 0)
      atTop (nhds 0))
    (hopponent : ∀ who, Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who) 0)
      atTop (nhds 0))
    (hinitial : ∀ who,
      quittingTerminalSemanticDebt (chain.candidate 0) who ≤ eta)
    (hseam : ∀ who,
      (∑' time, chain.prescribedSeam who time) +
        ∑' time, chain.capSeam who time ≤ eta) :
    delta ≤ 2 * (Fintype.card ι : ℝ) * eta := by
  refine (chain.actualDebtGap_le_candidate_add_seams delta hgap
    hprescribed hcap hjoint hopponent).trans ?_
  calc
    (∑ who,
      (quittingTerminalSemanticDebt (chain.candidate 0) who +
        ((∑' time, chain.prescribedSeam who time) +
          ∑' time, chain.capSeam who time))) ≤
        ∑ _who : ι, (2 * eta) := by
      exact Finset.sum_le_sum fun who _ => by
        linarith [hinitial who, hseam who]
    _ = 2 * (Fintype.card ι : ℝ) * eta := by
      simp
      ring

/-- A bounded zero-seam artificial chain equals the actual terminal semantic
pair of its literal root profile at the initial suffix. -/
theorem actualPair_zeroSeam_eq_candidate
    (hprescribed : ∀ time who, chain.prescribedSeam who time = 0)
    (hcap : ∀ time who, chain.capSeam who time = 0)
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) 0)
      atTop (nhds 0))
    (hopponent : ∀ who, Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who) 0)
      atTop (nhds 0)) :
    chain.actualPair 0 = chain.candidate 0 := by
  apply Prod.ext <;> funext who
  · have hfun : chain.prescribedSeam who = fun _ => 0 := by
      funext time
      exact hprescribed time who
    have hsum : (∑' time, chain.prescribedSeam who time) = 0 := by
      rw [hfun]
      exact tsum_zero
    have h := chain.abs_actualPair_prescribed_sub_le_tsum who (by
      rw [hfun]
      exact summable_zero) hjoint
    rw [hsum] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  · have hfun : chain.capSeam who = fun _ => 0 := by
      funext time
      exact hcap time who
    have hsum : (∑' time, chain.capSeam who time) = 0 := by
      rw [hfun]
      exact tsum_zero
    have h := chain.abs_actualPair_cap_sub_le_tsum who (by
      rw [hfun]
      exact summable_zero) (hopponent who)
    rw [hsum] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

end QuittingBoundedSeamChain

/-- Accuracy-indexed producer interface for the summable-seam reduction.  It
contains artificial annotations and literal-root survival as separate fields. -/
structure QuittingSummableSeamSource
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (eta : ℝ) where
  chain : QuittingBoundedSeamChain reward
  prescribed_summable : ∀ who, Summable (chain.prescribedSeam who)
  total_summable : ∀ who, Summable (chain.totalSeam who)
  prescribed_tsum_le : ∀ who,
    ∑' time, chain.prescribedSeam who time ≤ eta
  total_tsum_le : ∀ who, ∑' time, chain.totalSeam who time ≤ eta
  initial_debt_le : ∀ who,
    quittingTerminalSemanticDebt (chain.candidate 0) who ≤ eta
  joint_survival : ∀ start,
    Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (chain.roots time)) start)
      atTop (nhds 0)
  opponent_survival : ∀ who start,
    Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass (chain.roots time) who)
        start) atTop (nhds 0)

namespace QuittingSummableSeamSource

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {eta : ℝ}

/-- Theorem A in packaged form. -/
theorem toChronologicalDebtShadowingCertificate
    (source : QuittingSummableSeamSource reward eta) (heta : 0 < eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) :=
  source.chain.nonempty_chronologicalDebtShadowingCertificate eta heta
    source.prescribed_summable source.total_summable
    source.prescribed_tsum_le source.total_tsum_le source.initial_debt_le
    source.joint_survival source.opponent_survival

end QuittingSummableSeamSource

/-- Direct all-behavior consumer: summable-seam sources at every positive
accuracy give a fixed uniform-equilibrium payoff through the checked
chronological compiler. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_summableSeams_all_errors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hsources : ∀ eta : ℝ, 0 < eta →
      Nonempty (QuittingSummableSeamSource reward eta)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_chronologicalDebtShadowing_all_errors
      reward
  intro eta heta
  obtain ⟨source⟩ := hsources eta heta
  exact source.toChronologicalDebtShadowingCertificate heta

/-! ## Canonical flattening of variable-length blocks -/

private theorem exists_consecutiveBlock_upper
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    ∃ block, time < consecutiveBlockStart length (block + 1) := by
  refine ⟨time, ?_⟩
  have hstart : time ≤ consecutiveBlockStart length time := by
    induction time with
    | zero => rfl
    | succ time ih =>
        rw [consecutiveBlockStart]
        have hpos := hpositive time
        omega
  rw [consecutiveBlockStart]
  have hpos := hpositive time
  omega

theorem consecutiveBlock_le_start
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (block : ℕ) :
    block ≤ consecutiveBlockStart length block := by
  induction block with
  | zero => rfl
  | succ block ih =>
      rw [consecutiveBlockStart]
      have hpos := hpositive block
      omega

/-- Canonical block containing a calendar time. -/
def consecutiveBlockIndex (length : ℕ → ℕ)
    (hpositive : ∀ block, 0 < length block) (time : ℕ) : ℕ :=
  Nat.find (exists_consecutiveBlock_upper length hpositive time)

/-- Offset of a calendar time inside its canonical block. -/
def consecutiveBlockOffset (length : ℕ → ℕ)
    (hpositive : ∀ block, 0 < length block) (time : ℕ) : ℕ :=
  time - consecutiveBlockStart length
    (consecutiveBlockIndex length hpositive time)

theorem consecutiveBlockIndex_upper
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    time < consecutiveBlockStart length
      (consecutiveBlockIndex length hpositive time + 1) :=
  Nat.find_spec (exists_consecutiveBlock_upper length hpositive time)

theorem consecutiveBlockStart_index_le
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    consecutiveBlockStart length
        (consecutiveBlockIndex length hpositive time) ≤ time := by
  generalize hindex : consecutiveBlockIndex length hpositive time = index
  cases index with
  | zero =>
      exact Nat.zero_le time
  | succ block =>
      have hnot : ¬time < consecutiveBlockStart length (block + 1) := by
        intro hlt
        have hfind : consecutiveBlockIndex length hpositive time ≤ block := by
          exact Nat.find_min'
            (exists_consecutiveBlock_upper length hpositive time) hlt
        rw [hindex] at hfind
        omega
      simpa [hindex] using le_of_not_gt hnot

theorem consecutiveBlockOffset_lt
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    consecutiveBlockOffset length hpositive time <
      length (consecutiveBlockIndex length hpositive time) := by
  have hlower := consecutiveBlockStart_index_le length hpositive time
  have hupper := consecutiveBlockIndex_upper length hpositive time
  rw [consecutiveBlockStart] at hupper
  unfold consecutiveBlockOffset
  omega

theorem consecutiveBlockStart_add_offset
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) (time : ℕ) :
    consecutiveBlockStart length
        (consecutiveBlockIndex length hpositive time) +
      consecutiveBlockOffset length hpositive time = time := by
  have hlower := consecutiveBlockStart_index_le length hpositive time
  unfold consecutiveBlockOffset
  omega

private theorem consecutiveBlockStart_strictMono
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) :
    StrictMono (consecutiveBlockStart length) := by
  apply strictMono_nat_of_lt_succ
  intro block
  rw [consecutiveBlockStart]
  have hpos := hpositive block
  omega

theorem consecutiveBlockIndex_eq_of_mem
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (block time : ℕ)
    (hlower : consecutiveBlockStart length block ≤ time)
    (hupper : time < consecutiveBlockStart length (block + 1)) :
    consecutiveBlockIndex length hpositive time = block := by
  apply le_antisymm
  · exact Nat.find_min'
      (exists_consecutiveBlock_upper length hpositive time) hupper
  · by_contra hnot
    have hlt : consecutiveBlockIndex length hpositive time < block := by omega
    have hsucc : consecutiveBlockIndex length hpositive time + 1 ≤ block := by
      omega
    have hmono := (consecutiveBlockStart_strictMono length hpositive).monotone hsucc
    have hcanonical := consecutiveBlockIndex_upper length hpositive time
    omega

theorem consecutiveBlockIndex_start_add
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (block offset : ℕ) (hoffset : offset < length block) :
    consecutiveBlockIndex length hpositive
      (consecutiveBlockStart length block + offset) = block := by
  apply consecutiveBlockIndex_eq_of_mem length hpositive block
  · omega
  · rw [consecutiveBlockStart]
    omega

theorem consecutiveBlockOffset_start_add
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block)
    (block offset : ℕ) (hoffset : offset < length block) :
    consecutiveBlockOffset length hpositive
      (consecutiveBlockStart length block + offset) = offset := by
  unfold consecutiveBlockOffset
  rw [consecutiveBlockIndex_start_add length hpositive block offset hoffset]
  omega

@[simp] theorem consecutiveBlockIndex_zero
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) :
    consecutiveBlockIndex length hpositive 0 = 0 := by
  apply consecutiveBlockIndex_eq_of_mem length hpositive 0
  · rfl
  · rw [consecutiveBlockStart]
    change 0 < 0 + length 0
    simpa using hpositive 0

@[simp] theorem consecutiveBlockOffset_zero
    (length : ℕ → ℕ) (hpositive : ∀ block, 0 < length block) :
    consecutiveBlockOffset length hpositive 0 = 0 := by
  unfold consecutiveBlockOffset
  rw [consecutiveBlockIndex_zero]
  rfl


/-! The public block adapter uses natural offsets together with explicit
range hypotheses.  This keeps packet annotations independent of dependent
index proof terms while retaining the literal bounds `offset < N_k` and
`offset ≤ N_k`. -/

structure QuittingVariableLengthSeamBlocksNat
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  length : ℕ → ℕ
  length_pos : ∀ block, 0 < length block
  roots : ℕ → ℕ → ι → PMF Bool
  candidate : ℕ → ℕ → QuittingTerminalSemanticPair ι
  exact_step : ∀ block offset, offset < length block →
    candidate block offset =
      quittingTerminalSemanticPrefix reward (roots block offset)
        (candidate block (offset + 1))
  debt_nonneg : ∀ block offset, offset ≤ length block → ∀ who,
    0 ≤ quittingTerminalSemanticDebt (candidate block offset) who
  prescribed_bounded : ∃ bound : ℝ,
    ∀ block offset, offset ≤ length block → ∀ who,
      |(candidate block offset).1 who| ≤ bound
  debt_bounded : ∃ bound : ℝ,
    ∀ block offset, offset ≤ length block → ∀ who,
      |quittingTerminalSemanticDebt (candidate block offset) who| ≤ bound

namespace QuittingVariableLengthSeamBlocksNat

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  (blocks : QuittingVariableLengthSeamBlocksNat reward)

def flatRootNat (time : ℕ) : ι → PMF Bool :=
  blocks.roots (consecutiveBlockIndex blocks.length blocks.length_pos time)
    (consecutiveBlockOffset blocks.length blocks.length_pos time)

def flatCandidateNat (time : ℕ) : QuittingTerminalSemanticPair ι :=
  blocks.candidate
    (consecutiveBlockIndex blocks.length blocks.length_pos time)
    (consecutiveBlockOffset blocks.length blocks.length_pos time)

def flatSuccessorNat (time : ℕ) : QuittingTerminalSemanticPair ι :=
  blocks.candidate
    (consecutiveBlockIndex blocks.length blocks.length_pos time)
    (consecutiveBlockOffset blocks.length blocks.length_pos time + 1)

def flatChainNat : QuittingBoundedSeamChain reward where
  roots := blocks.flatRootNat
  candidate := blocks.flatCandidateNat
  successor := blocks.flatSuccessorNat
  exact_step := by
    intro time
    exact blocks.exact_step _ _
      (consecutiveBlockOffset_lt blocks.length blocks.length_pos time)
  debt_nonneg := by
    intro time who
    exact blocks.debt_nonneg _ _
      (consecutiveBlockOffset_lt blocks.length blocks.length_pos time).le who
  prescribed_bounded := by
    obtain ⟨bound, hbound⟩ := blocks.prescribed_bounded
    exact ⟨bound, fun time who => hbound _ _
      (consecutiveBlockOffset_lt blocks.length blocks.length_pos time).le who⟩
  debt_bounded := by
    obtain ⟨bound, hbound⟩ := blocks.debt_bounded
    exact ⟨bound, fun time who => hbound _ _
      (consecutiveBlockOffset_lt blocks.length blocks.length_pos time).le who⟩

def prescribedBlockSeamNat (who : ι) (block : ℕ) : ℝ :=
  |(blocks.candidate block (blocks.length block)).1 who -
    (blocks.candidate (block + 1) 0).1 who|

def capBlockSeamNat (who : ι) (block : ℕ) : ℝ :=
  |(blocks.candidate block (blocks.length block)).2 who -
    (blocks.candidate (block + 1) 0).2 who|

def totalBlockSeamNat (who : ι) (block : ℕ) : ℝ :=
  blocks.prescribedBlockSeamNat who block + blocks.capBlockSeamNat who block

private theorem flatCandidateNat_next_eq (time : ℕ) :
    blocks.flatCandidateNat (time + 1) =
      if consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time)
      then blocks.flatSuccessorNat time
      else blocks.candidate
        (consecutiveBlockIndex blocks.length blocks.length_pos time + 1) 0 := by
  have hreconstruct := consecutiveBlockStart_add_offset
    blocks.length blocks.length_pos time
  have hoffset := consecutiveBlockOffset_lt
    blocks.length blocks.length_pos time
  by_cases hinternal :
      consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
        blocks.length
          (consecutiveBlockIndex blocks.length blocks.length_pos time)
  · rw [if_pos hinternal]
    have htime : time + 1 =
        consecutiveBlockStart blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time) +
          (consecutiveBlockOffset blocks.length blocks.length_pos time + 1) := by
      omega
    unfold flatCandidateNat flatSuccessorNat
    rw [htime,
      consecutiveBlockIndex_start_add blocks.length blocks.length_pos
        _ _ hinternal,
      consecutiveBlockOffset_start_add blocks.length blocks.length_pos
        _ _ hinternal]
  · rw [if_neg hinternal]
    have hboundary :
        consecutiveBlockOffset blocks.length blocks.length_pos time + 1 =
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
      omega
    have htime : time + 1 = consecutiveBlockStart blocks.length
        (consecutiveBlockIndex blocks.length blocks.length_pos time + 1) := by
      rw [consecutiveBlockStart]
      omega
    have hnextPos := blocks.length_pos
      (consecutiveBlockIndex blocks.length blocks.length_pos time + 1)
    unfold flatCandidateNat
    rw [htime,
      show consecutiveBlockStart blocks.length
          (consecutiveBlockIndex blocks.length blocks.length_pos time + 1) =
        consecutiveBlockStart blocks.length
          (consecutiveBlockIndex blocks.length blocks.length_pos time + 1) + 0 by
        omega,
      consecutiveBlockIndex_start_add blocks.length blocks.length_pos
        _ 0 hnextPos,
      consecutiveBlockOffset_start_add blocks.length blocks.length_pos
        _ 0 hnextPos]

theorem flat_prescribedSeamNat_eq (who : ι) (time : ℕ) :
    blocks.flatChainNat.prescribedSeam who time =
      if consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time)
      then 0 else blocks.prescribedBlockSeamNat who
        (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
  change |(blocks.flatSuccessorNat time).1 who -
    (blocks.flatCandidateNat (time + 1)).1 who| = _
  rw [blocks.flatCandidateNat_next_eq time]
  split
  · simp
  · rename_i hboundary
    unfold flatSuccessorNat prescribedBlockSeamNat
    have hoffset := consecutiveBlockOffset_lt
      blocks.length blocks.length_pos time
    have heq : consecutiveBlockOffset blocks.length blocks.length_pos time + 1 =
        blocks.length
          (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
      omega
    rw [heq]

theorem flat_capSeamNat_eq (who : ι) (time : ℕ) :
    blocks.flatChainNat.capSeam who time =
      if consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time)
      then 0 else blocks.capBlockSeamNat who
        (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
  change |(blocks.flatSuccessorNat time).2 who -
    (blocks.flatCandidateNat (time + 1)).2 who| = _
  rw [blocks.flatCandidateNat_next_eq time]
  split
  · simp
  · rename_i hboundary
    unfold flatSuccessorNat capBlockSeamNat
    have hoffset := consecutiveBlockOffset_lt
      blocks.length blocks.length_pos time
    have heq : consecutiveBlockOffset blocks.length blocks.length_pos time + 1 =
        blocks.length
          (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
      omega
    rw [heq]

theorem flat_totalSeamNat_eq (who : ι) (time : ℕ) :
    blocks.flatChainNat.totalSeam who time =
      if consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time)
      then 0 else blocks.totalBlockSeamNat who
        (consecutiveBlockIndex blocks.length blocks.length_pos time) := by
  unfold QuittingBoundedSeamChain.totalSeam totalBlockSeamNat
  rw [blocks.flat_prescribedSeamNat_eq, blocks.flat_capSeamNat_eq]
  split <;> simp

private theorem consecutiveBlockSum_flatSeamNat
    (flat blockSeam : ℕ → ℝ)
    (hflat : ∀ time, flat time =
      if consecutiveBlockOffset blocks.length blocks.length_pos time + 1 <
          blocks.length
            (consecutiveBlockIndex blocks.length blocks.length_pos time)
      then 0 else blockSeam
        (consecutiveBlockIndex blocks.length blocks.length_pos time))
    (block : ℕ) :
    consecutiveBlockSum blocks.length flat block = blockSeam block := by
  unfold consecutiveBlockSum
  have hpos := blocks.length_pos block
  rw [show blocks.length block = (blocks.length block - 1) + 1 by omega,
    Finset.sum_range_succ]
  have hlast : blocks.length block - 1 < blocks.length block := by omega
  have hbefore : ∀ offset ∈ Finset.range (blocks.length block - 1),
      flat (consecutiveBlockStart blocks.length block + offset) = 0 := by
    intro offset hoffset
    have hoffset' := Finset.mem_range.mp hoffset
    rw [hflat,
      consecutiveBlockIndex_start_add blocks.length blocks.length_pos
        block offset (by omega),
      consecutiveBlockOffset_start_add blocks.length blocks.length_pos
        block offset (by omega), if_pos (by omega)]
  rw [Finset.sum_eq_zero hbefore, zero_add, hflat,
    consecutiveBlockIndex_start_add blocks.length blocks.length_pos
      block (blocks.length block - 1) hlast,
    consecutiveBlockOffset_start_add blocks.length blocks.length_pos
      block (blocks.length block - 1) hlast, if_neg (by omega)]

private theorem summable_flatSeamNat_and_tsum_le
    (flat blockSeam : ℕ → ℝ) {eta : ℝ}
    (hflat0 : ∀ time, 0 ≤ flat time)
    (hblock0 : ∀ block, 0 ≤ blockSeam block)
    (hblocks : Summable blockSeam)
    (hblockTsum : ∑' block, blockSeam block ≤ eta)
    (hflatBlock : ∀ block,
      consecutiveBlockSum blocks.length flat block = blockSeam block) :
    Summable flat ∧ ∑' time, flat time ≤ eta := by
  have hprefix : ∀ horizon,
      ∑ time ∈ Finset.range horizon, flat time ≤ eta := by
    intro horizon
    have hstart : horizon ≤
        consecutiveBlockStart blocks.length (horizon + 1) := by
      exact (Nat.le_succ horizon).trans
        (consecutiveBlock_le_start blocks.length blocks.length_pos (horizon + 1))
    calc
      (∑ time ∈ Finset.range horizon, flat time) ≤
          ∑ time ∈ Finset.range
            (consecutiveBlockStart blocks.length (horizon + 1)), flat time := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hstart)
          (fun time _ _ => hflat0 time)
      _ = ∑ block ∈ Finset.range (horizon + 1), blockSeam block := by
        rw [← sum_consecutiveBlockSum_eq_sum_range]
        exact Finset.sum_congr rfl fun block _ => hflatBlock block
      _ ≤ ∑' block, blockSeam block :=
        hblocks.sum_le_tsum _ (fun block _ => hblock0 block)
      _ ≤ eta := hblockTsum
  have hsummable := summable_of_sum_range_le hflat0 hprefix
  exact ⟨hsummable, hsummable.tsum_le_of_sum_range_le hprefix⟩

/-- Summable prescribed seams between consecutive variable-length blocks
remain summable after canonical calendar flattening, with the same total
upper bound. -/
theorem summable_flatPrescribedSeamNat_and_tsum_le
    (who : ι) {bound : ℝ}
    (hsummable : Summable (blocks.prescribedBlockSeamNat who))
    (htsum : ∑' block, blocks.prescribedBlockSeamNat who block ≤ bound) :
    Summable (blocks.flatChainNat.prescribedSeam who) ∧
      ∑' time, blocks.flatChainNat.prescribedSeam who time ≤ bound := by
  apply blocks.summable_flatSeamNat_and_tsum_le
    (blocks.flatChainNat.prescribedSeam who)
    (blocks.prescribedBlockSeamNat who)
    (blocks.flatChainNat.prescribedSeam_nonneg who) (fun _ => abs_nonneg _)
    hsummable htsum
  exact blocks.consecutiveBlockSum_flatSeamNat _ _
    (blocks.flat_prescribedSeamNat_eq who)

/-- Summable total seams between consecutive variable-length blocks remain
summable after canonical calendar flattening, with the same total upper
bound. -/
theorem summable_flatTotalSeamNat_and_tsum_le
    (who : ι) {bound : ℝ}
    (hsummable : Summable (blocks.totalBlockSeamNat who))
    (htsum : ∑' block, blocks.totalBlockSeamNat who block ≤ bound) :
    Summable (blocks.flatChainNat.totalSeam who) ∧
      ∑' time, blocks.flatChainNat.totalSeam who time ≤ bound := by
  apply blocks.summable_flatSeamNat_and_tsum_le
    (blocks.flatChainNat.totalSeam who) (blocks.totalBlockSeamNat who)
    (blocks.flatChainNat.totalSeam_nonneg who)
    (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hsummable htsum
  exact blocks.consecutiveBlockSum_flatSeamNat _ _
    (blocks.flat_totalSeamNat_eq who)

/-- Theorem B directly on nested block annotations: the actual initial
semantic pair is bounded by the two block-end seam series. -/
theorem flat_semanticRigidityNat
    (who : ι)
    (hprescribed : Summable (blocks.prescribedBlockSeamNat who))
    (hcap : Summable (blocks.capBlockSeamNat who))
    (hjoint : Tendsto
      (Math.survivalProduct
        (fun time => quittingStationaryContinueMass (blocks.flatRootNat time)) 0)
      atTop (nhds 0))
    (hopponent : Tendsto
      (Math.survivalProduct
        (fun time => quittingRootOpponentContinueMass
          (blocks.flatRootNat time) who) 0) atTop (nhds 0)) :
    |(blocks.flatChainNat.actualPair 0).1 who -
        (blocks.candidate 0 0).1 who| ≤
        ∑' block, blocks.prescribedBlockSeamNat who block ∧
      |(blocks.flatChainNat.actualPair 0).2 who -
        (blocks.candidate 0 0).2 who| ≤
        ∑' block, blocks.capBlockSeamNat who block ∧
      |quittingTerminalSemanticDebt (blocks.flatChainNat.actualPair 0) who -
        quittingTerminalSemanticDebt (blocks.candidate 0 0) who| ≤
        (∑' block, blocks.prescribedBlockSeamNat who block) +
          ∑' block, blocks.capBlockSeamNat who block := by
  have hflatPrescribed := blocks.summable_flatSeamNat_and_tsum_le
    (blocks.flatChainNat.prescribedSeam who)
    (blocks.prescribedBlockSeamNat who)
    (blocks.flatChainNat.prescribedSeam_nonneg who) (fun _ => abs_nonneg _)
    hprescribed le_rfl
    (blocks.consecutiveBlockSum_flatSeamNat _ _
      (blocks.flat_prescribedSeamNat_eq who))
  have hflatCap := blocks.summable_flatSeamNat_and_tsum_le
    (blocks.flatChainNat.capSeam who) (blocks.capBlockSeamNat who)
    (blocks.flatChainNat.capSeam_nonneg who) (fun _ => abs_nonneg _)
    hcap le_rfl
    (blocks.consecutiveBlockSum_flatSeamNat _ _
      (blocks.flat_capSeamNat_eq who))
  have hprescribedBound :=
    blocks.flatChainNat.abs_actualPair_prescribed_sub_le_tsum who
      hflatPrescribed.1 hjoint
  have hcapBound := blocks.flatChainNat.abs_actualPair_cap_sub_le_tsum who
    hflatCap.1 hopponent
  have hdebtBound := blocks.flatChainNat.abs_actualDebt_sub_candidateDebt_le_tsum
    who hflatPrescribed.1 hflatCap.1 hjoint hopponent
  simpa [flatChainNat, flatCandidateNat] using
    And.intro (hprescribedBound.trans hflatPrescribed.2)
      (And.intro (hcapBound.trans hflatCap.2)
        (hdebtBound.trans (add_le_add hflatPrescribed.2 hflatCap.2)))

/-- Literal nested variable-length block-to-flat-stream adapter for Theorem A. -/
def toSummableSeamSourceNat
    (eta : ℝ)
    (hprescribedSummable : ∀ who,
      Summable (blocks.prescribedBlockSeamNat who))
    (htotalSummable : ∀ who, Summable (blocks.totalBlockSeamNat who))
    (hprescribedTsum : ∀ who,
      ∑' block, blocks.prescribedBlockSeamNat who block ≤ eta)
    (htotalTsum : ∀ who,
      ∑' block, blocks.totalBlockSeamNat who block ≤ eta)
    (hinitial : ∀ who,
      quittingTerminalSemanticDebt (blocks.candidate 0 0) who ≤ eta)
    (hjoint : ∀ start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingStationaryContinueMass (blocks.flatRootNat time))
          start) atTop (nhds 0))
    (hopponent : ∀ who start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingRootOpponentContinueMass
            (blocks.flatRootNat time) who) start) atTop (nhds 0)) :
    QuittingSummableSeamSource reward eta := by
  have hprescribed : ∀ who,
      Summable (blocks.flatChainNat.prescribedSeam who) ∧
        ∑' time, blocks.flatChainNat.prescribedSeam who time ≤ eta := by
    intro who
    apply blocks.summable_flatSeamNat_and_tsum_le
      (blocks.flatChainNat.prescribedSeam who)
      (blocks.prescribedBlockSeamNat who)
      (blocks.flatChainNat.prescribedSeam_nonneg who) (fun _ => abs_nonneg _)
      (hprescribedSummable who) (hprescribedTsum who)
    exact blocks.consecutiveBlockSum_flatSeamNat _ _
      (blocks.flat_prescribedSeamNat_eq who)
  have htotal : ∀ who,
      Summable (blocks.flatChainNat.totalSeam who) ∧
        ∑' time, blocks.flatChainNat.totalSeam who time ≤ eta := by
    intro who
    apply blocks.summable_flatSeamNat_and_tsum_le
      (blocks.flatChainNat.totalSeam who) (blocks.totalBlockSeamNat who)
      (blocks.flatChainNat.totalSeam_nonneg who)
      (fun _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
      (htotalSummable who) (htotalTsum who)
    exact blocks.consecutiveBlockSum_flatSeamNat _ _
      (blocks.flat_totalSeamNat_eq who)
  exact {
    chain := blocks.flatChainNat
    prescribed_summable := fun who => (hprescribed who).1
    total_summable := fun who => (htotal who).1
    prescribed_tsum_le := fun who => (hprescribed who).2
    total_tsum_le := fun who => (htotal who).2
    initial_debt_le := by simpa [flatChainNat, flatCandidateNat] using hinitial
    joint_survival := hjoint
    opponent_survival := hopponent }

end QuittingVariableLengthSeamBlocksNat

end GameTheory
