/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.AllContinueBasinRigidity
import UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanValueConvergence
import UniformEquilibrium.Quitting.Bellman.Finite.UnboundedExactBlockHazardCapacity
import UniformEquilibrium.Quitting.Paths.PersistentDeletedClockTwoLabel
import UniformEquilibrium.Quitting.Root.OpponentCoalitionMass

/-!
# Restart moats around an exact all-Continue basin

A compact plateau inside an open basin with a unique exact all-Continue root
has a uniform terminal-seam moat. Positively absorbing finite exact blocks must
cross that moat. Summable restart seams therefore force summable block hazard,
while bounded block displacement turns the moat into the literal hazard floor
`rho / (2 * M)`.

For a supplied canonical exact spine with summable marginal Quit hazards, the
same basin rigidity and value convergence give the constant-all-Continue or
uniformly-separated limit alternative.

These are conditional finite-block and supplied-spine consumers. They do not
construct a source family, prove that the restart seams are summable, or produce
a uniform-equilibrium payoff.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction
open scoped Topology BigOperators

variable {X : Type} [PseudoMetricSpace X]

/-- A compact subset of an open set has one positive metric moat separating
all of its points from the complement. -/
private theorem exists_uniformMoat_of_isCompact_subset_isOpen
    (plateau tube : Set X) (hplateau : IsCompact plateau)
    (htube : IsOpen tube) (hsubset : plateau ⊆ tube) :
    ∃ rho : ℝ, 0 < rho ∧ Metric.thickening rho plateau ⊆ tube ∧
      ∀ anchor ∈ plateau, ∀ terminal ∉ tube,
        rho ≤ dist terminal anchor := by
  obtain ⟨rho, hrho, hthick⟩ :=
    hplateau.exists_thickening_subset_open htube hsubset
  refine ⟨rho, hrho, hthick, ?_⟩
  intro anchor hanchor terminal hterminal
  apply le_of_not_gt
  intro hdist
  exact hterminal (hthick (Metric.mem_thickening_iff.mpr
    ⟨anchor, hanchor, hdist⟩))

/-- A summable sequence cannot cross a fixed positive moat at infinitely
many marked indices. -/
private theorem finite_markedIndices_of_summable_moat
    (seam : ℕ → ℝ) (marked : ℕ → Prop) {rho : ℝ}
    (hrho : 0 < rho) (hseam : Summable seam)
    (hmarked : ∀ index, marked index → rho ≤ seam index) :
    Set.Finite {index | marked index} := by
  have heventually : ∀ᶠ index in atTop, seam index < rho :=
    hseam.tendsto_atTop_zero.eventually (Iio_mem_nhds hrho)
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.mp heventually
  refine (Set.finite_Iio threshold).subset ?_
  intro index hindex
  by_contra hnot
  have hlarge := hmarked index hindex
  have hsmall := hthreshold index (not_lt.mp hnot)
  exact (not_lt_of_ge hlarge) hsmall

variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace QuittingFiniteExactNashBellmanBlock

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
  {carrier : Set (QuittingNashBellmanPoint ι)}

/-- If a finite exact block ends inside a basin with a unique all-Continue
exact root, then every displayed root is all-Continue. -/
theorem root_eq_allContinue_of_terminal_mem_uniqueBasin
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : (block.state block.horizon).1 ∈ basin) :
    ∀ time, time < block.horizon →
      block.root time = (quittingAllContinueRoot : ι → PMF Bool) := by
  have hrigid : ∀ time, time ≤ block.horizon →
      (block.state time).1 = (block.state block.horizon).1 ∧
        (time < block.horizon →
          block.root time =
            (quittingAllContinueRoot : ι → PMF Bool)) := by
    intro time htime
    refine Nat.decreasingInduction (n := block.horizon)
      (motive := fun stage _ =>
        (block.state stage).1 = (block.state block.horizon).1 ∧
          (stage < block.horizon →
            block.root stage =
              (quittingAllContinueRoot : ι → PMF Bool))) ?_ ?_ htime
    · intro stage hstage ih
      have hedge := block.edge stage hstage
      have hnash := hedge.2
      rw [ih.1] at hnash
      have hroot := hunique (block.state block.horizon).1 hterminal
        (block.root stage) hnash
      have hbellman := hedge.1
      change (block.state stage).1 = quittingRootSuccessorPayoff reward
        (block.state (stage + 1)).1 (block.root stage) at hbellman
      rw [ih.1, hroot,
        quittingRootSuccessorPayoff_allContinueRoot_eq] at hbellman
      exact ⟨hbellman, fun _ => hroot⟩
    · exact ⟨rfl, by omega⟩
  exact fun time htime => (hrigid time htime.le).2 htime

/-- A finite exact block with a positively absorbing stage terminates outside
every basin whose unique exact root is all-Continue. -/
theorem terminal_not_mem_uniqueBasin_of_positiveAbsorption
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (basin : Set (Payoff ι))
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (stage : ℕ) (hstage : stage < block.horizon)
    (habsorption : 0 < quittingRootAbsorptionMass (block.root stage)) :
    (block.state block.horizon).1 ∉ basin := by
  intro hterminal
  have hroot := block.root_eq_allContinue_of_terminal_mem_uniqueBasin
    basin hunique hterminal stage hstage
  rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at habsorption
  exact lt_irrefl 0 habsorption

/-- A compact plateau inside an exact all-Continue basin has one uniform
endpoint-seam floor for every positively absorbing exact block. -/
theorem exists_uniform_terminal_separation_of_positiveAbsorption
    (plateau basin : Set (Payoff ι)) (hplateau : IsCompact plateau)
    (hbasin : IsOpen basin) (hsubset : plateau ⊆ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ (blockCarrier : Set (QuittingNashBellmanPoint ι))
          (anchor : Payoff ι), anchor ∈ plateau →
        ∀ block : QuittingFiniteExactNashBellmanBlock reward blockCarrier,
          ∀ stage, stage < block.horizon →
            0 < quittingRootAbsorptionMass (block.root stage) →
              rho ≤ dist (block.state block.horizon).1 anchor := by
  obtain ⟨rho, hrho, _hthick, hseparation⟩ :=
    exists_uniformMoat_of_isCompact_subset_isOpen
      plateau basin hplateau hbasin hsubset
  refine ⟨rho, hrho, ?_⟩
  intro _blockCarrier anchor hanchor block stage hstage habsorption
  exact hseparation anchor hanchor (block.state block.horizon).1
    (block.terminal_not_mem_uniqueBasin_of_positiveAbsorption
      basin hunique stage hstage habsorption)

/-- Summable ordinary endpoint seams permit only finitely many restart blocks
with a positively absorbing stage. -/
theorem finite_positiveAbsorptionBlocks_of_summable_restartSeams
    (plateau basin : Set (Payoff ι)) (hplateau : IsCompact plateau)
    (hbasin : IsOpen basin) (hsubset : plateau ⊆ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (block : ℕ → QuittingFiniteExactNashBellmanBlock reward carrier)
    (anchor : ℕ → Payoff ι) (hanchor : ∀ index, anchor index ∈ plateau)
    (hseam : Summable (fun index ↦
      dist ((block index).state (block index).horizon).1 (anchor index))) :
    Set.Finite {index | ∃ stage, stage < (block index).horizon ∧
      0 < quittingRootAbsorptionMass ((block index).root stage)} := by
  obtain ⟨rho, hrho, hseparation⟩ :=
    exists_uniform_terminal_separation_of_positiveAbsorption
      plateau basin hplateau hbasin hsubset hunique
  apply finite_markedIndices_of_summable_moat
    (fun index ↦
      dist ((block index).state (block index).horizon).1 (anchor index))
    (fun index ↦ ∃ stage, stage < (block index).horizon ∧
      0 < quittingRootAbsorptionMass ((block index).root stage))
    hrho hseam
  intro index hmarked
  obtain ⟨stage, hstage, habsorption⟩ := hmarked
  exact hseparation carrier (anchor index) (hanchor index) (block index)
    stage hstage habsorption

/-- Summable ordinary endpoint restart seams force the sequence of literal
aggregate block hazards itself to be summable. -/
theorem summable_hazardCharge_of_summable_restartSeams
    (plateau basin : Set (Payoff ι)) (hplateau : IsCompact plateau)
    (hbasin : IsOpen basin) (hsubset : plateau ⊆ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (block : ℕ → QuittingFiniteExactNashBellmanBlock reward carrier)
    (anchor : ℕ → Payoff ι) (hanchor : ∀ index, anchor index ∈ plateau)
    (hseam : Summable (fun index ↦
      dist ((block index).state (block index).horizon).1 (anchor index))) :
    Summable (fun index ↦ (block index).hazardCharge) := by
  have hfinite := finite_positiveAbsorptionBlocks_of_summable_restartSeams
    plateau basin hplateau hbasin hsubset hunique block anchor hanchor hseam
  apply summable_of_hasFiniteSupport
  apply hfinite.subset
  intro index hsupport
  change (block index).hazardCharge ≠ 0 at hsupport
  by_contra hnotMarked
  apply hsupport
  unfold hazardCharge
  apply Finset.sum_eq_zero
  intro stage hstage
  unfold stageHazardCharge marginalQuitHazard
  apply Finset.sum_eq_zero
  intro who _
  have habsorptionNonneg :=
    quittingRootAbsorptionMass_nonneg ((block index).root stage)
  have habsorptionNotPos :
      ¬ 0 < quittingRootAbsorptionMass ((block index).root stage) := by
    intro habsorption
    exact hnotMarked ⟨stage, Finset.mem_range.mp hstage, habsorption⟩
  have habsorptionZero :
      quittingRootAbsorptionMass ((block index).root stage) = 0 :=
    le_antisymm (not_lt.mp habsorptionNotPos) habsorptionNonneg
  have hcontinue :
      quittingStationaryContinueMass ((block index).root stage) = 1 := by
    unfold quittingRootAbsorptionMass at habsorptionZero
    linarith
  rw [eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue who]
  simp

/-- The endpoint displacement of a bounded exact block is controlled by its
literal total marginal-Quit hazard. -/
theorem dist_terminal_start_le_two_mul_bound_mul_hazardCharge
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (M : ℝ)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hstate : ∀ time, time ≤ block.horizon → ∀ player,
      |(block.state time).1 player| ≤ M) :
    dist (block.state block.horizon).1 (block.state 0).1 ≤
      2 * M * block.hazardCharge := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    have heq : (block.state block.horizon).1 = (block.state 0).1 := by
      funext player
      exact isEmptyElim player
    have hcharge : block.hazardCharge = 0 := by
      simp [QuittingFiniteExactNashBellmanBlock.hazardCharge,
        QuittingFiniteExactNashBellmanBlock.stageHazardCharge,
        QuittingFiniteExactNashBellmanBlock.marginalQuitHazard]
    rw [heq, hcharge]
    simp
  letI := hι
  have hM : 0 ≤ M := by
    obtain ⟨player⟩ := hι
    exact (abs_nonneg ((block.state 0).1 player)).trans
      (hstate 0 (Nat.zero_le block.horizon) player)
  apply (dist_pi_le_iff
    (mul_nonneg (mul_nonneg (by norm_num) hM) block.hazardCharge_nonneg)).2
  intro player
  rw [Real.dist_eq, abs_sub_comm, ← Finset.sum_range_sub'
    (fun time ↦ (block.state time).1 player)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    (∑ time ∈ Finset.range block.horizon,
        |(block.state time).1 player -
          (block.state (time + 1)).1 player|) ≤
        ∑ time ∈ Finset.range block.horizon,
          2 * M * block.stageHazardCharge time := by
      apply Finset.sum_le_sum
      intro time htime
      have htimeLt : time < block.horizon := Finset.mem_range.mp htime
      have hstep :=
        abs_quittingRootSuccessorPayoff_sub_tail_le_two_mul_absorptionMass
          reward (block.state (time + 1)).1 (block.root time) player M
          hreward (hstate (time + 1) htimeLt player)
      rw [← congrFun (block.value_eq_successor htimeLt) player] at hstep
      exact hstep.trans (mul_le_mul_of_nonneg_left
        (quittingRootAbsorptionMass_le_sum_quitProbability (block.root time))
        (mul_nonneg (by norm_num) hM))
    _ = 2 * M * block.hazardCharge := by
      simp [QuittingFiniteExactNashBellmanBlock.hazardCharge,
        QuittingFiniteExactNashBellmanBlock.stageHazardCharge,
        QuittingFiniteExactNashBellmanBlock.marginalQuitHazard,
        Finset.mul_sum]

/-- A moat-separated absorbing block beginning on the plateau pays at least
the moat divided by twice the common payoff bound in literal hazard charge. -/
theorem moat_div_two_mul_bound_le_hazardCharge
    (block : QuittingFiniteExactNashBellmanBlock reward carrier)
    (anchor : Payoff ι) (rho M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hstate : ∀ time, time ≤ block.horizon → ∀ player,
      |(block.state time).1 player| ≤ M)
    (hstart : (block.state 0).1 = anchor)
    (hseparation : rho ≤ dist (block.state block.horizon).1 anchor) :
    rho / (2 * M) ≤ block.hazardCharge := by
  rw [← hstart] at hseparation
  apply (div_le_iff₀ (mul_pos (by norm_num) hM)).2
  simpa [mul_comm] using hseparation.trans
    (block.dist_terminal_start_le_two_mul_bound_mul_hazardCharge
      M hreward hstate)

/-- Summable aggregate block hazards permit only finitely many positively
absorbing restart blocks whose literal initial values lie on the compact
plateau. -/
theorem finite_positiveAbsorptionBlocks_of_summable_hazardCharge
    (plateau basin : Set (Payoff ι)) (hplateau : IsCompact plateau)
    (hbasin : IsOpen basin) (hsubset : plateau ⊆ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootEndpointNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (block : ℕ → QuittingFiniteExactNashBellmanBlock reward carrier)
    (M : ℝ) (hM : 0 < M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hstate : ∀ index time, time ≤ (block index).horizon → ∀ player,
      |((block index).state time).1 player| ≤ M)
    (hstart : ∀ index, ((block index).state 0).1 ∈ plateau)
    (hsummable : Summable (fun index ↦ (block index).hazardCharge)) :
    Set.Finite {index | ∃ stage, stage < (block index).horizon ∧
      0 < quittingRootAbsorptionMass ((block index).root stage)} := by
  obtain ⟨rho, hrho, hseparation⟩ :=
    exists_uniform_terminal_separation_of_positiveAbsorption
      plateau basin hplateau hbasin hsubset hunique
  apply finite_markedIndices_of_summable_moat
    (fun index ↦ (block index).hazardCharge)
    (fun index ↦ ∃ stage, stage < (block index).horizon ∧
      0 < quittingRootAbsorptionMass ((block index).root stage))
    (rho := rho / (2 * M))
    (div_pos hrho (mul_pos (by norm_num) hM)) hsummable
  intro index hmarked
  obtain ⟨stage, hstage, habsorption⟩ := hmarked
  apply (block index).moat_div_two_mul_bound_le_hazardCharge
    ((block index).state 0).1 rho M hM hreward (hstate index) rfl
  exact hseparation carrier ((block index).state 0).1 (hstart index)
    (block index) stage hstage habsorption

end QuittingFiniteExactNashBellmanBlock

open QuittingFiniteExactNashBellmanBlock

namespace IsCanonicalExactQuittingNashBellmanSpine

/-- Summability of every literal marginal Quit-hazard series makes the whole
bounded exact Nash--Bellman value spine converge. -/
theorem exists_tendsto_value_of_summable_marginalQuitHazards
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (hsummable : ∀ player,
      Summable (fun time ↦ (roots time player true).toReal)) :
    ∃ limit : Payoff ι, Tendsto value atTop (nhds limit) := by
  have hcoordinate (player : ι) :
      ∃ limit : ℝ, Tendsto (fun time ↦ value time player)
        atTop (nhds limit) := by
    apply hspine.exists_tendsto_value_of_summableClock
      reward value roots player
    exact (summable_quittingOpponentClockCharge_iff roots player).2
      fun owner _ ↦ hsummable owner
  choose limit hlimit using hcoordinate
  exact ⟨limit, tendsto_pi_nhds.mpr hlimit⟩

/-- An all-marginal-summable bounded exact spine is either the literal
constant all-Continue spine, or its limit lies outside the exact
all-Continue basin and remains uniformly separated from the compact plateau. -/
theorem eq_constantAllContinue_or_limit_uniformlySeparated
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {value : ℕ → Payoff ι} {roots : ℕ → ι → PMF Bool}
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots)
    (plateau basin : Set (Payoff ι)) (hplateau : IsCompact plateau)
    (hbasin : IsOpen basin) (hsubset : plateau ⊆ basin)
    (hunique : ∀ tail ∈ basin, ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool))
    (hsummable : ∀ player,
      Summable (fun time ↦ (roots time player true).toReal)) :
    ∃ (rho : ℝ) (limit : Payoff ι),
      0 < rho ∧ Tendsto value atTop (nhds limit) ∧
      ((∀ time, value time = limit ∧
          roots time = (quittingAllContinueRoot : ι → PMF Bool)) ∨
        (limit ∉ basin ∧ ∀ anchor ∈ plateau,
          rho ≤ dist limit anchor)) := by
  obtain ⟨rho, hrho, _hthick, hseparation⟩ :=
    exists_uniformMoat_of_isCompact_subset_isOpen
      plateau basin hplateau hbasin hsubset
  obtain ⟨limit, hlimit⟩ :=
    hspine.exists_tendsto_value_of_summable_marginalQuitHazards hsummable
  refine ⟨rho, limit, hrho, hlimit, ?_⟩
  by_cases hlimitMem : limit ∈ basin
  · left
    apply exactNashBellmanPath_eq_anchor_of_tendsto_unique_allContinue
      reward basin hbasin limit hlimitMem
    · intro tail htail root hnash
      exact hunique tail htail root
        ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
          reward tail root).1 hnash)
    · exact hspine.2.1
    · intro time
      exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (value (time + 1)) (roots time)).2 (hspine.2.2 time)
    · exact hlimit
  · exact Or.inr ⟨hlimitMem, fun anchor hanchor ↦
      hseparation anchor hanchor limit hlimitMem⟩

end IsCanonicalExactQuittingNashBellmanSpine

end GameTheory
