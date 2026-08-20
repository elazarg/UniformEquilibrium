/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtPositiveLimit

/-!
# The exact-debt tail / punishment-prefix bridge

An exact dynamic-debt tail is chronological: its edge at time `t` runs from
the current Nash--Bellman state to its continuation at `t + 1`.  A
punishment-floor prefix has the opposite orientation: it grows outward from
an individually rational terminal anchor by choosing exact predecessors.

Consequently a finite dynamic-debt segment can be reversed into a
punishment-floor prefix whenever its far endpoint dominates the punishment
floor. This is the generic bridge between the two carriers. Counterexample-
specific capacity consequences belong to the diagnostic adapter.

The endpoint hypothesis cannot be dropped merely by translating payoffs.
The quitting game's nonabsorbing payoff is fixed at zero, so a coordinatewise
translation changes the never-absorbed outcome and is not a harmless
normalization of the uniform-equilibrium problem.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Reversing one exact-debt segment -/

/-- Payoffs of a chronological exact-debt segment, read backward from its
far endpoint. -/
def quittingDynamicDebtReverseValue
    (tail : ℕ → QuittingDebtPoint ι) (horizon time : ℕ) : Payoff ι :=
  (tail (horizon - time)).1.1

/-- The predecessor root of a chronological exact-debt segment, read in the
matching backward order. -/
def quittingDynamicDebtReverseRoot
    (tail : ℕ → QuittingDebtPoint ι) (horizon time : ℕ) : ι → PMF Bool :=
  quittingRootOfSimplex (tail (horizon - (time + 1))).1.2

/-- Reverse a boxed exact dynamic-debt segment whose far endpoint dominates
the punishment floor into an exact punishment-floor prefix.  The debt
coordinates are forgotten; the Nash--Bellman edge and its literal root are
retained exactly. -/
def quittingDynamicDebtSegmentToPunishmentFloorPrefix
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    QuittingPunishmentFloorFinitePrefix reward where
  roots := quittingDynamicDebtReverseRoot tail horizon
  value := quittingDynamicDebtReverseValue tail horizon
  horizon := horizon
  value_mem := by
    intro time htime
    exact (hbox (horizon - time) (Nat.sub_le _ _)).1
  anchor_floor := by
    simpa [quittingDynamicDebtReverseValue] using hfloor
  policy := by
    intro time htime
    have hindex : horizon - (time + 1) < horizon := by omega
    have hstep := (hedge (horizon - (time + 1)) hindex).1.1
    have hsucc : horizon - (time + 1) + 1 = horizon - time := by omega
    simpa [quittingDynamicDebtReverseValue,
      quittingDynamicDebtReverseRoot, hsucc] using hstep
  exactNash := by
    intro time htime
    have hindex : horizon - (time + 1) < horizon := by omega
    have hsucc : horizon - (time + 1) + 1 = horizon - time := by omega
    have hnashEndpoint :=
      (hedge (horizon - (time + 1)) hindex).1.2
    rw [hsucc] at hnashEndpoint
    have hnash :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (tail (horizon - time)).1.1
          (quittingRootOfSimplex
            (tail (horizon - (time + 1))).1.2)).1
        hnashEndpoint
    simpa [quittingDynamicDebtReverseValue,
      quittingDynamicDebtReverseRoot, hsucc] using hnash

omit [Nonempty ι] in
/-- Floor dominance at the far endpoint propagates backward through the
underlying Nash--Bellman values of the whole exact-D segment. -/
theorem quittingPunishmentValue_le_dynamicDebtTailValue_of_endpoint_floor
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who)
    (time : ℕ) (htime : time ≤ horizon) (who : ι) :
    quittingPunishmentValue reward who ≤ (tail time).1.1 who := by
  let cert := quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
    hbox hedge hfloor
  have hvalue := quittingPunishmentValue_le_finitePrefixValue cert
    (horizon - time) (Nat.sub_le _ _) who
  change quittingPunishmentValue reward who ≤
    (tail (horizon - (horizon - time))).1.1 who at hvalue
  rwa [Nat.sub_sub_self htime] at hvalue

/-! ## The zero-boundary specialization -/

/-- If the punishment vector is coordinatewise nonpositive, then every
displayed value of every selected finite min-max exact-D annotation dominates
the punishment floor.  Before the cutoff this follows by reversing the exact
segment from its zero endpoint; after the cutoff the annotation is padded by
that same zero endpoint. -/
theorem quittingPunishmentValue_le_finiteMinMaxDynamicDebtTail_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (cutoff time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff time).1.1 who := by
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer reward cutoff
  have hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
      reward cutoff
  have hterminal :
      (quittingFiniteMinMaxDynamicDebtTail reward cutoff cutoff).1.1 = 0 := by
    simp only [quittingFiniteMinMaxDynamicDebtTail,
      quittingFiniteNashBellmanPathDynamicDebtPoint, dif_pos le_rfl]
    have hindex :
        (⟨cutoff, Nat.lt_succ_self cutoff⟩ : Fin (cutoff + 1)) =
          Fin.last cutoff := by
      apply Fin.ext
      rfl
    rw [hindex]
    exact hpath.2.1
  by_cases htime : time ≤ cutoff
  · apply
      quittingPunishmentValue_le_dynamicDebtTailValue_of_endpoint_floor
        (reward := reward)
        (quittingFiniteMinMaxDynamicDebtTail reward cutoff) cutoff
        (fun point _ ↦
          quittingFiniteMinMaxDynamicDebtTail_mem_box reward cutoff point)
        (fun point hpoint ↦
          quittingFiniteMinMaxDynamicDebtTail_edge reward cutoff point hpoint)
        (fun player ↦ by rw [hterminal]; exact hpunishment player)
        time htime who
  · unfold quittingFiniteMinMaxDynamicDebtTail
      quittingFiniteNashBellmanPathDynamicDebtPoint
    rw [dif_neg htime]
    change quittingPunishmentValue reward who ≤
      (path (Fin.last cutoff)).1 who
    rw [congrFun hpath.2.1 who]
    exact hpunishment who

/-- Floor dominance of the finite zero-boundary annotations passes to every
coordinate of any projective limit.  This uses the actual product-topology
convergence supplied by projective extraction, not a heuristic closure
argument. -/
theorem quittingPunishmentValue_le_projectiveDynamicDebtTail_of_nonpos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0)
    (subseq : ℕ → ℕ) (limit : ℕ → QuittingDebtPoint ι)
    (hlimit : Tendsto
      ((fun cutoff ↦ quittingFiniteMinMaxDynamicDebtTail reward cutoff) ∘
        subseq) atTop (nhds limit))
    (time : ℕ) (who : ι) :
    quittingPunishmentValue reward who ≤ (limit time).1.1 who := by
  have hpoint : Tendsto
      (fun family ↦ quittingFiniteMinMaxDynamicDebtTail reward
        (subseq family) time)
      atTop (nhds (limit time)) :=
    ((continuous_apply time).tendsto limit).comp hlimit
  have hcoordinate : Continuous
      (fun point : QuittingDebtPoint ι ↦ point.1.1 who) := by
    fun_prop
  have htend : Tendsto
      (fun family ↦ (quittingFiniteMinMaxDynamicDebtTail reward
        (subseq family) time).1.1 who)
      atTop (nhds ((limit time).1.1 who)) :=
    (hcoordinate.tendsto (limit time)).comp hpoint
  exact ge_of_tendsto' htend fun family ↦
    quittingPunishmentValue_le_finiteMinMaxDynamicDebtTail_of_nonpos
      reward hpunishment (subseq family) time who

/-- Literal joint absorption charge along a chronological exact-debt tail. -/
def quittingDynamicDebtTailAbsorptionCharge
    (tail : ℕ → QuittingDebtPoint ι) (time : ℕ) : ℝ :=
  quittingRootAbsorptionMass
    (quittingRootOfSimplex (tail time).1.2)

omit [DecidableEq ι] [Nonempty ι] in
theorem quittingDynamicDebtTailAbsorptionCharge_nonneg
    (tail : ℕ → QuittingDebtPoint ι) (time : ℕ) :
    0 ≤ quittingDynamicDebtTailAbsorptionCharge tail time := by
  unfold quittingDynamicDebtTailAbsorptionCharge
    quittingRootAbsorptionMass
  exact sub_nonneg.mpr
    (quittingStationaryContinueMass_le_one
      (quittingRootOfSimplex (tail time).1.2))

omit [Nonempty ι] in
/-- Reversal changes chronology but not total joint absorption charge. -/
theorem quittingDynamicDebtSegmentToPunishmentFloorPrefix_charge
    (tail : ℕ → QuittingDebtPoint ι) (horizon : ℕ)
    (hbox : ∀ time, time ≤ horizon → tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time, time < horizon →
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    (quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
        hbox hedge hfloor).charge =
      ∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail time := by
  change
    (∑ time ∈ Finset.range horizon,
      quittingDynamicDebtTailAbsorptionCharge tail
        (horizon - (time + 1))) = _
  calc
    (∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail
          (horizon - (time + 1))) =
        ∑ time ∈ Finset.range horizon,
          quittingDynamicDebtTailAbsorptionCharge tail
            (horizon - 1 - time) := by
          apply Finset.sum_congr rfl
          intro time _
          congr 1
          omega
    _ = _ := Finset.sum_range_reflect
      (quittingDynamicDebtTailAbsorptionCharge tail) horizon

/-! ## The sharp conditional connection -/

/-- Floor-dominating endpoints occur cofinally along a tail.  This is weaker
than requiring every tail value to be individually rational. -/
def HasCofinalQuittingPunishmentFloorEndpoints
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : ℕ → QuittingDebtPoint ι) : Prop :=
  ∀ start, ∃ horizon, start ≤ horizon ∧
    ∀ who, quittingPunishmentValue reward who ≤ (tail horizon).1.1 who

end GameTheory
