/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CycleMismatchContraction

/-!
# Exact-path rigidity of an all-Continue basin

If every exact endpoint-Nash root at a tail is all-Continue, every finite
exact Nash--Bellman chain ending at that tail is the constant all-Continue
chain.  The conclusion propagates backward from the continuation/tail.  It
does not infer anything from a head lying in the basin.

The results are exact.  They give no rigidity for approximate roots or
approximate Bellman seams.
-/

noncomputable section

namespace GameTheory

open Math.Probability
open Filter
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Finite backward rigidity from a terminal tail at which all-Continue is
the unique exact endpoint-Nash root. -/
theorem quittingAnchoredPath_backward_rigidity_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : Payoff ι) (hterminal : terminal ∈ basin)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff) :
    ∀ time, time ≤ cutoff →
      quittingFiniteNashBellmanPathValue cutoff path time = terminal ∧
      (time < cutoff →
        quittingFiniteNashBellmanPathRoots cutoff path time =
          (quittingAllContinueRoot : ι → PMF Bool)) := by
  intro time htime
  refine Nat.decreasingInduction (n := cutoff)
    (motive := fun stage _ =>
      quittingFiniteNashBellmanPathValue cutoff path stage = terminal ∧
      (stage < cutoff →
        quittingFiniteNashBellmanPathRoots cutoff path stage =
          (quittingAllContinueRoot : ι → PMF Bool))) ?_ ?_ htime
  · intro stage hstage ih
    have hnash := quittingAnchoredPathRoots_isZeroEndpointNash
      reward terminal cutoff path hpath stage hstage
    rw [ih.1] at hnash
    have hroot := hunique terminal hterminal
      (quittingFiniteNashBellmanPathRoots cutoff path stage) hnash
    have hbellman := quittingAnchoredPathValue_eq_successor
      reward terminal cutoff path hpath stage hstage
    rw [ih.1, hroot,
      quittingRootSuccessorPayoff_allContinueRoot_eq] at hbellman
    exact ⟨hbellman, fun _ => hroot⟩
  · refine ⟨quittingAnchoredPathValue_at_cutoff
      reward terminal cutoff path hpath, ?_⟩
    omega

/-- Every pre-terminal root of such an anchored path is all-Continue and has
zero absorption. -/
theorem quittingAnchoredPath_root_eq_allContinue_and_absorption_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : Payoff ι) (hterminal : terminal ∈ basin)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathRoots cutoff path time =
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingRootAbsorptionMass
          (quittingFiniteNashBellmanPathRoots cutoff path time) = 0 := by
  have hroot :=
    (quittingAnchoredPath_backward_rigidity_of_unique_allContinue
      reward basin hunique terminal hterminal cutoff path hpath time
        htime.le).2 htime
  rw [hroot]
  exact ⟨rfl, quittingRootAbsorptionMass_allContinueRoot⟩

/-- A tail in an all-Continue basin admits no absorbing exact cyclic
continuation. -/
theorem not_isQuittingCyclicContinuation_of_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : Payoff ι) (hterminal : terminal ∈ basin) :
    ¬ IsQuittingCyclicContinuation reward terminal := by
  rintro ⟨period, block, hblock⟩
  obtain ⟨stage, hstage⟩ := hblock.2.2
  have hzero :=
    (quittingAnchoredPath_root_eq_allContinue_and_absorption_eq_zero
      reward basin hunique terminal hterminal (period + 1) block hblock.1
        stage.val stage.isLt).2
  rw [quittingFiniteNashBellmanPathRoots_of_lt
    (period + 1) block stage.val stage.isLt] at hzero
  have hindex : (⟨stage.val, Nat.lt_succ_of_lt stage.isLt⟩ :
      Fin (period + 2)) = Fin.castSucc stage := Fin.ext rfl
  rw [hindex] at hzero
  exact (ne_of_gt hstage) hzero

/-- A positively absorbing anchored exact block must terminate outside every
all-Continue basin. -/
theorem anchoredPath_terminal_not_mem_of_positiveAbsorption
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (terminal : Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (stage : ℕ) (hstage : stage < cutoff)
    (habsorption : 0 < quittingRootAbsorptionMass
      (quittingFiniteNashBellmanPathRoots cutoff path stage)) :
    terminal ∉ basin := by
  intro hterminal
  have hzero :=
    (quittingAnchoredPath_root_eq_allContinue_and_absorption_eq_zero
      reward basin hunique terminal hterminal cutoff path hpath stage hstage).2
  exact (ne_of_gt habsorption) hzero

/-- Metric seam floor: if a ball around an anchor lies in an all-Continue
basin, the terminal tail of every positively absorbing exact block stays at
least the ball radius away. -/
theorem le_dist_terminal_of_positiveAbsorption_of_ball_subset_allContinueBasin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (anchor terminal : Payoff ι) {radius : ℝ}
    (hball : Metric.ball anchor radius ⊆ basin)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteAnchoredNashBellmanChainSet reward terminal cutoff)
    (stage : ℕ) (hstage : stage < cutoff)
    (habsorption : 0 < quittingRootAbsorptionMass
      (quittingFiniteNashBellmanPathRoots cutoff path stage)) :
    radius ≤ dist terminal anchor := by
  apply le_of_not_gt
  intro hdist
  have hterminal : terminal ∈ basin :=
    hball (by simpa [dist_comm] using hdist)
  exact anchoredPath_terminal_not_mem_of_positiveAbsorption
    reward basin hunique terminal cutoff path hpath stage hstage
      habsorption hterminal

/-- An infinite exact Nash--Bellman path converging to an interior point of
an all-Continue basin is the constant all-Continue path from time zero. -/
theorem exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (basin : Set (Payoff ι)) (hbasinOpen : IsOpen basin)
    (anchor : Payoff ι) (hanchorMem : anchor ∈ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (value : ℕ → Payoff ι) (root : ℕ → ι → PMF Bool)
    (hbellman : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (root time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (root time))
    (hvalue : Tendsto value atTop (𝓝 anchor)) :
    ∀ time, value time = anchor ∧
      root time = (quittingAllContinueRoot : ι → PMF Bool) := by
  have heventually : ∀ᶠ time in atTop, value time ∈ basin :=
    hvalue.eventually (hbasinOpen.mem_nhds hanchorMem)
  obtain ⟨threshold, hlate⟩ := Filter.eventually_atTop.mp heventually
  have hconstant : ∀ time, threshold ≤ time →
      value time = value threshold := by
    intro time htime
    refine Nat.le_induction (m := threshold)
      (P := fun stage _ => value stage = value threshold) rfl ?_ time htime
    intro stage hthreshold ih
    have htail : value (stage + 1) ∈ basin :=
      hlate (stage + 1) (by omega)
    have hroot := hunique (value (stage + 1)) htail
      (root stage) (hnash stage)
    have hedge := hbellman stage
    rw [hroot, quittingRootSuccessorPayoff_allContinueRoot_eq] at hedge
    exact hedge.symm.trans ih
  have heq : value =ᶠ[atTop] fun _ => value threshold :=
    Filter.eventually_atTop.mpr ⟨threshold, hconstant⟩
  have hconstantTendsto : Tendsto (fun _ : ℕ => value threshold)
      atTop (𝓝 anchor) := Filter.Tendsto.congr' heq hvalue
  have hthresholdValue : value threshold = anchor :=
    tendsto_const_nhds_iff.mp hconstantTendsto
  have hbackward : ∀ time, time ≤ threshold →
      value time = anchor ∧
      (time < threshold →
        root time = (quittingAllContinueRoot : ι → PMF Bool)) := by
    intro time htime
    refine Nat.decreasingInduction (n := threshold)
      (motive := fun stage _ => value stage = anchor ∧
        (stage < threshold →
          root stage = (quittingAllContinueRoot : ι → PMF Bool))) ?_ ?_ htime
    · intro stage hstage ih
      have hnashStage := hnash stage
      rw [ih.1] at hnashStage
      have hroot := hunique anchor hanchorMem (root stage) hnashStage
      have hedge := hbellman stage
      rw [ih.1, hroot,
        quittingRootSuccessorPayoff_allContinueRoot_eq] at hedge
      exact ⟨hedge, fun _ => hroot⟩
    · exact ⟨hthresholdValue, by omega⟩
  intro time
  by_cases htime : time < threshold
  · exact ⟨(hbackward time htime.le).1,
      (hbackward time htime.le).2 htime⟩
  · have hthresholdLe : threshold ≤ time := le_of_not_gt htime
    have htimeValue : value time = anchor :=
      (hconstant time hthresholdLe).trans hthresholdValue
    have htail : value (time + 1) ∈ basin :=
      hlate (time + 1) (by omega)
    exact ⟨htimeValue,
      hunique (value (time + 1)) htail (root time) (hnash time)⟩

end GameTheory
