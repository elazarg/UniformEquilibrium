/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Debt.Dynamic.ChronologicalDebtShadowing

/-!
# Zero chronological forcing from exact Nash--Bellman spines

An exact bounded Nash--Bellman spine makes every non-survival discrepancy and
forcing field of `QuittingChronologicalDebtShadowingCertificate` identically
zero.  The candidate semantic pair is diagonal at every date.  Exact Bellman
evaluation kills its prescribed defect, exact root Nash kills its direct debt
defect, and a generated secant compares the literal executable tail with the
diagonal candidate tail.

This does not give survival for the selected roots.  A full chronological
certificate still requires joint and every player-deleted survival limit for
the same exact Nash--Bellman spine.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open scoped BigOperators Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace QuittingChronologicalDebtData

/-- Generated secant comparing the executable successor tail with a diagonal
candidate successor. -/
def nashBellmanSecant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) : ℝ :=
  Classical.choose
    (exists_quittingTerminalSemanticPrefix_secant reward (roots time)
      (value (time + 1), value (time + 1))
      (quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward roots (time + 1))) who)

/-- Chronological data attached to a candidate Nash--Bellman spine.  Candidate
debt is zero; the executable tail is used to generate the cap secants. -/
def ofNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) :
    QuittingChronologicalDebtData ι where
  roots := roots
  prescribed := value
  debt := 0
  secant := nashBellmanSecant reward value roots

@[simp] theorem ofNashBellmanSpine_root
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (ofNashBellmanSpine reward value roots).root time = roots time :=
  rfl

@[simp] theorem ofNashBellmanSpine_prescribed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (ofNashBellmanSpine reward value roots).prescribed time = value time :=
  rfl

@[simp] theorem ofNashBellmanSpine_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    (ofNashBellmanSpine reward value roots).debt time who = 0 :=
  rfl

@[simp] theorem ofNashBellmanSpine_semanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (ofNashBellmanSpine reward value roots).semanticPair reward time =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward roots time) :=
  rfl

@[simp] theorem ofNashBellmanSpine_candidateSuccessorPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (time : ℕ) :
    (ofNashBellmanSpine reward value roots).candidateSuccessorPair time =
      (value (time + 1), value (time + 1)) := by
  apply Prod.ext
  · rfl
  · funext who
    simp [candidateSuccessorPair]

private theorem nashBellmanSecant_spec
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    0 ≤ nashBellmanSecant reward value roots time who ∧
      nashBellmanSecant reward value roots time who ≤
        quittingRootOpponentContinueMass (roots time) who ∧
      (quittingTerminalSemanticPrefix reward (roots time)
          (quittingTerminalSemanticPair reward
            (quittingRootSequenceProfile reward roots (time + 1)))).2 who -
          (quittingTerminalSemanticPrefix reward (roots time)
            (value (time + 1), value (time + 1))).2 who =
        nashBellmanSecant reward value roots time who *
          ((quittingTerminalSemanticPair reward
              (quittingRootSequenceProfile reward roots (time + 1))).2 who -
            value (time + 1) who) := by
  exact Classical.choose_spec
    (exists_quittingTerminalSemanticPrefix_secant reward (roots time)
      (value (time + 1), value (time + 1))
      (quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward roots (time + 1))) who)

theorem ofNashBellmanSpine_secant_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    0 ≤ (ofNashBellmanSpine reward value roots).secant time who :=
  (nashBellmanSecant_spec reward value roots time who).1

theorem ofNashBellmanSpine_secant_le_opponentContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    (ofNashBellmanSpine reward value roots).secant time who ≤
      quittingRootOpponentContinueMass
        ((ofNashBellmanSpine reward value roots).root time) who :=
  (nashBellmanSecant_spec reward value roots time who).2.1

theorem ofNashBellmanSpine_secant_generated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (time : ℕ) (who : ι) :
    ((ofNashBellmanSpine reward value roots).semanticPair reward time).2 who -
        (quittingTerminalSemanticPrefix reward
          ((ofNashBellmanSpine reward value roots).root time)
          ((ofNashBellmanSpine reward value roots).candidateSuccessorPair
            time)).2 who =
      (ofNashBellmanSpine reward value roots).secant time who *
        (((ofNashBellmanSpine reward value roots).semanticPair reward
            (time + 1)).2 who -
          ((ofNashBellmanSpine reward value roots).candidateSuccessorPair
            time).2 who) := by
  have hprefix := congrArg
    (fun pair : QuittingTerminalSemanticPair ι => pair.2 who)
    (semanticPair_eq_prefix
      (ofNashBellmanSpine reward value roots) reward time)
  rw [hprefix, ofNashBellmanSpine_candidateSuccessorPair]
  exact (nashBellmanSecant_spec reward value roots time who).2.2

/-- Exact Bellman evaluation makes prescribed defect identically zero. -/
@[simp] theorem ofNashBellmanSpine_prescribedDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) :
    (ofNashBellmanSpine reward value roots).prescribedDefect reward time = 0 := by
  funext who
  unfold prescribedDefect
  rw [ofNashBellmanSpine_candidateSuccessorPair,
    ofNashBellmanSpine_root,
    quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
      reward (value (time + 1)) (roots time) (hnash time)]
  simp [hbellman time]

/-- Exact root Nash makes direct debt defect identically zero. -/
@[simp] theorem ofNashBellmanSpine_directDebtDefect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) :
    (ofNashBellmanSpine reward value roots).directDebtDefect reward time = 0 := by
  funext who
  unfold directDebtDefect
  rw [ofNashBellmanSpine_candidateSuccessorPair,
    ofNashBellmanSpine_root,
    quittingTerminalSemanticPrefix_diagonal_eq_of_isZeroNash
      reward (value (time + 1)) (roots time) (hnash time)]
  simp [quittingTerminalSemanticDebt]

theorem ofNashBellmanSpine_prescribedDiscrepancy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (who : ι) (start length : ℕ) :
    |∑ offset ∈ Finset.range length,
      (ofNashBellmanSpine reward value roots).prescribedDefect reward
        (start + offset) who| = 0 := by
  simp [ofNashBellmanSpine_prescribedDefect
    reward value roots hbellman hnash]

theorem ofNashBellmanSpine_adverseDirectForcing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (who : ι) (start length : ℕ) :
    -∑ offset ∈ Finset.range length,
      Math.survivalProduct
          (fun time => (ofNashBellmanSpine reward value roots).secant time who)
          start offset *
        (ofNashBellmanSpine reward value roots).directDebtDefect reward
          (start + offset) who = 0 := by
  simp [ofNashBellmanSpine_directDebtDefect reward value roots hnash]

end QuittingChronologicalDebtData

/-- A bounded exact Nash--Bellman spine whose same roots satisfy the two
survival obligations yields the full certificate at every positive accuracy. -/
theorem nonempty_quittingChronologicalDebtShadowingCertificate_of_exactSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hbound : ∀ time who,
      |value time who| ≤ quittingRewardBound reward)
    (hbellman : ∀ time,
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootNash reward (value (time + 1)) 0 (roots time))
    (hjoint : ∀ start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingStationaryContinueMass (roots time)) start)
        atTop (nhds 0))
    (hopponent : ∀ who start,
      Tendsto
        (Math.survivalProduct
          (fun time => quittingRootOpponentContinueMass (roots time) who)
          start) atTop (nhds 0))
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (QuittingChronologicalDebtShadowingCertificate reward eta) := by
  let data := QuittingChronologicalDebtData.ofNashBellmanSpine
    reward value roots
  refine ⟨{
    data := data
    eta_pos := heta
    debt_nonneg := ?_
    prescribed_bounded := ?_
    debt_bounded := ?_
    secant_nonneg := ?_
    secant_le_opponentContinue := ?_
    secant_generated := ?_
    prescribed_discrepancy := ?_
    adverse_direct_forcing := ?_
    joint_survival := ?_
    opponent_survival := ?_
    initial_debt_le := ?_ }⟩
  · intro time who
    simp [data]
  · exact ⟨quittingRewardBound reward, by
      intro time who
      simpa [data] using hbound time who⟩
  · exact ⟨0, by
      intro time who
      simp [data]⟩
  · intro time who
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_nonneg
      reward value roots time who
  · intro time who
    exact
      QuittingChronologicalDebtData.ofNashBellmanSpine_secant_le_opponentContinue
        reward value roots time who
  · intro time who
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_generated
      reward value roots time who
  · intro who start length
    have hzero : ∀ time, data.prescribedDefect reward time = 0 := by
      intro time
      exact QuittingChronologicalDebtData.ofNashBellmanSpine_prescribedDefect
        reward value roots hbellman hnash time
    simp [hzero, heta.le]
  · intro who start slack hslack
    filter_upwards [] with length
    have hzero : ∀ time, data.directDebtDefect reward time = 0 := by
      intro time
      exact QuittingChronologicalDebtData.ofNashBellmanSpine_directDebtDefect
        reward value roots hnash time
    simp [hzero, (add_pos heta hslack).le]
  · intro start
    simpa [data] using hjoint start
  · intro who start
    simpa [data] using hopponent who start
  · intro who
    simp [data, heta.le]

/-- Every finite quitting game has bounded exact Nash--Bellman chronological
data whose candidate debts, prescribed defects, and direct forcing defects
are all zero.  No survival assertion is included. -/
theorem exists_zeroForcing_quittingChronologicalDebtData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (data : QuittingChronologicalDebtData ι)
        (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      data = QuittingChronologicalDebtData.ofNashBellmanSpine
        reward value roots ∧
      (∀ time who, |data.prescribed time who| ≤ quittingRewardBound reward) ∧
      (∀ time who, data.debt time who = 0) ∧
      (∀ time who, 0 ≤ data.secant time who) ∧
      (∀ time who,
        data.secant time who ≤
          quittingRootOpponentContinueMass (data.root time) who) ∧
      (∀ time who,
        (data.semanticPair reward time).2 who -
            (quittingTerminalSemanticPrefix reward (data.root time)
              (data.candidateSuccessorPair time)).2 who =
          data.secant time who *
            ((data.semanticPair reward (time + 1)).2 who -
              (data.candidateSuccessorPair time).2 who)) ∧
      (∀ time, data.prescribedDefect reward time = 0) ∧
      (∀ time, data.directDebtDefect reward time = 0) := by
  obtain ⟨value, roots, hbound, hbellman, hnash⟩ :=
    exists_exact_quittingNashBellmanSpine reward
  let data := QuittingChronologicalDebtData.ofNashBellmanSpine
    reward value roots
  refine ⟨data, value, roots, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro time who
    simpa [data] using hbound time who
  · intro time who
    simp [data]
  · intro time who
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_nonneg
      reward value roots time who
  · intro time who
    exact
      QuittingChronologicalDebtData.ofNashBellmanSpine_secant_le_opponentContinue
        reward value roots time who
  · intro time who
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_secant_generated
      reward value roots time who
  · intro time
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_prescribedDefect
      reward value roots hbellman hnash time
  · intro time
    exact QuittingChronologicalDebtData.ofNashBellmanSpine_directDebtDefect
      reward value roots hnash time

end GameTheory
