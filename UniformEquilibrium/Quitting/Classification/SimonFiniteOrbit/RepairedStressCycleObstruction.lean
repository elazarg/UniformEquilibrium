/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.UniformPayoffExamples
import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence

/-!
# The repaired stress circulation obstructs strict Simon potentials

The repaired four-player stress table has an exact four-phase singleton
circulation.  Subdividing every phase geometrically embeds that circulation
into the full production `F_epsilon` correspondence.  Every microedge has
positive Euclidean cost, so the closed cycle excludes every global potential
with a positive cost-decrease coefficient.  Consequently it also excludes
every positive-coefficient finite-cell Lyapunov certificate.

This is a candidate-level negative result for the Simon Lyapunov search.  The
same table independently has a uniform-equilibrium payoff; no equilibrium
nonexistence conclusion is drawn here.
-/

noncomputable section

namespace GameTheory
namespace RepairedFourPlayerStress

open Finset StochasticGame Math.PMFProduct
open Math.Topology SimonViability
open scoped BigOperators

/-- The quitting reward associated with the repaired stress weight. -/
abbrev stressReward := rewardOfWeight stressWeight

/-- Convex weights expressing each stress vertex as a mixture of the four
singleton terminal rewards. -/
def stressVertexWeight (phase : ZMod 4) : Player → ℝ :=
  if phase = 0 then ![8 / 15, 4 / 15, 2 / 15, 1 / 15]
  else if phase = 1 then ![4 / 15, 2 / 15, 1 / 15, 8 / 15]
  else if phase = 2 then ![2 / 15, 1 / 15, 8 / 15, 4 / 15]
  else ![1 / 15, 8 / 15, 4 / 15, 2 / 15]

theorem stressVertexWeight_nonneg (phase : ZMod 4) (owner : Player) :
    0 ≤ stressVertexWeight phase owner := by
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl <;>
    fin_cases owner <;> simp +decide [stressVertexWeight] <;> norm_num

theorem sum_stressVertexWeight (phase : ZMod 4) :
    ∑ owner, stressVertexWeight phase owner = 1 := by
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl <;>
    simp +decide [stressVertexWeight, Fin.sum_univ_succ] <;> norm_num

theorem stressVertex_eq_weighted_singletons (phase : ZMod 4) :
    stressVertex phase =
      ∑ owner, stressVertexWeight phase owner • stressWeight {owner} := by
  funext who
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl <;>
    fin_cases who <;>
    simp +decide [stressVertexWeight, stressVertex, Fin.sum_univ_succ,
      stressWeight] <;> norm_num

/-- Every ideal stress vertex is exactly feasible for the production Simon
carrier. -/
theorem stressVertex_feasible (phase : ZMod 4) :
    QuittingSimonFeasiblePayoff stressReward (stressVertex phase) := by
  refine mem_convexHull_of_exists_fintype
    (s := Set.range stressReward ∪ {0})
    (ι := Player) (stressVertexWeight phase)
    (fun owner ↦ stressReward ⟨{owner}, singleton_nonempty owner⟩)
    (stressVertexWeight_nonneg phase) (sum_stressVertexWeight phase) ?_ ?_
  · intro owner
    exact Set.mem_union_left _ ⟨⟨{owner}, singleton_nonempty owner⟩, rfl⟩
  · rw [stressVertex_eq_weighted_singletons]
    rfl

/-- Data for one geometric subdivision of every stress phase. -/
structure StressSimonSubdivision (epsilon : ℝ) where
  /-- Number of microedges in each phase. -/
  length : ℕ
  /-- Every phase has at least one microedge. -/
  length_pos : 0 < length
  /-- Per-microedge Continue probability. -/
  beta : ℝ
  /-- The Continue probability is positive. -/
  beta_pos : 0 < beta
  /-- The Continue probability is strictly below one. -/
  beta_lt_one : beta < 1
  /-- A whole phase contracts by one half. -/
  beta_pow : beta ^ length = 1 / 2
  /-- The passive endpoint error fits the production tolerance. -/
  hazard_le : 1 - beta ≤ epsilon

namespace StressSimonSubdivision

variable {epsilon : ℝ} (data : StressSimonSubdivision epsilon)

/-- The payoff state after `step` microedges of a phase. -/
def state (phase : ZMod 4) (step : ℕ) : Payoff Player :=
  segmentPoint (stressVertex phase)
    (stressWeight {stressOwner phase}) (data.beta ^ step)

/-- The singleton hazard row used throughout one phase. -/
def row (phase : ZMod 4) : Player → ℝ :=
  singletonRow (1 - data.beta) (stressOwner phase)

theorem beta_nonneg : 0 ≤ data.beta := data.beta_pos.le

theorem beta_le_one : data.beta ≤ 1 := data.beta_lt_one.le

theorem state_parameter_lower {step : ℕ} (hstep : step ≤ data.length) :
    1 / 2 ≤ data.beta ^ step := by
  rw [← data.beta_pow]
  exact pow_le_pow_of_le_one data.beta_nonneg data.beta_le_one hstep

theorem state_parameter_upper (step : ℕ) : data.beta ^ step ≤ 1 :=
  pow_le_one₀ data.beta_nonneg data.beta_le_one

@[simp] theorem state_zero (phase : ZMod 4) :
    data.state phase 0 = stressVertex phase := by
  simp [state]

theorem state_end (phase : ZMod 4) :
    data.state phase data.length = stressVertex (phase + 1) := by
  funext who
  rw [state, data.beta_pow]
  simpa [segmentPoint] using (stressVertex_step phase who).symm

theorem state_succ (phase : ZMod 4) (step : ℕ) :
    data.state phase (step + 1) =
      oneStageNext stressWeight (data.row phase) (data.state phase step) := by
  funext who
  simp only [state, row, oneStageNext_singletonRow_segmentPoint, pow_succ]

/-- Every subdivided state remains exactly feasible. -/
theorem state_feasible (phase : ZMod 4) {step : ℕ}
    (_hstep : step ≤ data.length) :
    QuittingSimonFeasiblePayoff stressReward (data.state phase step) := by
  have hvertex := stressVertex_feasible phase
  have hsolo : stressWeight {stressOwner phase} ∈
      convexHull ℝ (Set.range stressReward ∪ {0}) := by
    apply subset_convexHull ℝ
    exact Set.mem_union_left _
      ⟨⟨{stressOwner phase}, singleton_nonempty _⟩, rfl⟩
  have hmu0 : 0 ≤ data.beta ^ step := pow_nonneg data.beta_nonneg _
  have hmu1 : 0 ≤ 1 - data.beta ^ step := by
    linarith [data.state_parameter_upper step]
  have hsum : data.beta ^ step + (1 - data.beta ^ step) = 1 := by ring
  have hcombo := (convex_iff_add_mem.mp
    (convex_convexHull ℝ (Set.range stressReward ∪ {0})))
      hvertex hsolo hmu0 hmu1 hsum
  change data.state phase step ∈
    convexHull ℝ (Set.range stressReward ∪ {0})
  have heq : data.state phase step =
      data.beta ^ step • stressVertex phase +
        (1 - data.beta ^ step) • stressWeight {stressOwner phase} := by
    funext who
    rfl
  rw [heq]
  exact hcombo

/-- Every subdivided state satisfies exact individual rationality. -/
theorem state_rational (phase : ZMod 4) {step : ℕ}
    (hstep : step ≤ data.length) :
    QuittingSimonRationalPayoffAt stressReward epsilon
      (data.state phase step) := by
  intro who
  have hfloor := segmentPoint_ge_floor
    (stressVertex phase) (stressWeight {stressOwner phase}) stressFloor
    (1 / 2) (data.beta ^ step) (by norm_num)
    (data.state_parameter_lower hstep) (data.state_parameter_upper step)
    (stressVertex_ge_floor phase)
    (fun player ↦ by
      rw [← stressVertex_step]
      exact stressVertex_ge_floor (phase + 1) player)
    who
  have hpunish := quittingPunishmentValue_le_stressFloor who
  have hepsilon : 0 ≤ epsilon := le_trans (sub_nonneg.mpr data.beta_le_one)
    data.hazard_le
  have hfloor' : stressFloor who ≤ data.state phase step who := by
    simpa only [state] using hfloor
  dsimp [stressReward]
  linarith

/-- Every subdivided state belongs to the full production carrier. -/
def carrierState (phase : ZMod 4) (step : Fin (data.length + 1)) :
    QuittingSimonFiniteOrbitCarrier stressReward epsilon :=
  ⟨data.state phase step,
    data.state_rational phase (Nat.le_of_lt_succ step.isLt),
    data.state phase step,
    data.state_feasible phase (Nat.le_of_lt_succ step.isLt),
    by
      have hepsilon : 0 ≤ epsilon := le_trans
        (sub_nonneg.mpr data.beta_le_one) data.hazard_le
      simpa [euclideanDist, euclideanNorm] using hepsilon⟩

theorem gain_owner (phase : ZMod 4) (step : ℕ) :
    gainValue stressWeight (data.row phase) (stressOwner phase)
      (data.state phase step (stressOwner phase)) = 0 := by
  rw [row, gainValue_singletonRow_self, state,
    segmentPoint_pinned stressWeight]
  · ring
  · exact stressVertex_owner_pinned phase

/-- The repaired table's exact passive-row estimate.  The coarse generic
reward bound would lose a factor six; this sharp estimate is what makes the
unsubdivided four-edge cycle valid already at tolerance `1/2`. -/
theorem gain_le_hazard (phase : ZMod 4) {step : ℕ}
    (hstep : step < data.length) (who : Player) :
    gainValue stressWeight (data.row phase) who
      (data.state phase step who) ≤ 1 - data.beta := by
  have hhalf : (1 / 2 : ℝ) ≤ data.beta ^ (step + 1) :=
    data.state_parameter_lower (Nat.succ_le_iff.mpr hstep)
  have hbpow0 : 0 < data.beta ^ step := pow_pos data.beta_pos _
  have hbpow1 : data.beta ^ step ≤ 1 := data.state_parameter_upper step
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl <;>
    fin_cases who <;>
    simp +decide [row, state, stressVertex, stressOwner,
      gainValue_singletonRow_self, gainValue_singletonRow_of_ne,
      stressWeight, segmentPoint] <;>
    nlinarith [data.beta_pos, data.beta_lt_one,
      pow_succ data.beta step]

theorem row_supportPerfect (phase : ZMod 4) {step : ℕ}
    (hstep : step < data.length) :
    IsSupportPerfectRow stressWeight (data.row phase)
      (data.state phase step) epsilon := by
  intro who
  constructor
  · intro hused
    have howner : who = stressOwner phase := by
      by_contra hne
      rw [row, singletonRow_of_ne _ hne] at hused
      exact (lt_irrefl 0) hused
    subst who
    rw [data.gain_owner]
    have hepsilon : 0 ≤ epsilon := le_trans
      (sub_nonneg.mpr data.beta_le_one) data.hazard_le
    linarith
  · intro _
    exact (data.gain_le_hazard phase hstep who).trans data.hazard_le

theorem row_nonneg (phase : ZMod 4) (who : Player) :
    0 ≤ data.row phase who := by
  exact (singletonRow_mem_unitInterval (1 - data.beta)
    (sub_nonneg.mpr data.beta_le_one) (by linarith [data.beta_pos])
    (stressOwner phase) who).1

theorem row_le_one (phase : ZMod 4) (who : Player) :
    data.row phase who ≤ 1 := by
  exact (singletonRow_mem_unitInterval (1 - data.beta)
    (sub_nonneg.mpr data.beta_le_one) (by linarith [data.beta_pos])
    (stressOwner phase) who).2

/-- Every microstep is an edge of the full production correspondence. -/
theorem fEdge (phase : ZMod 4) (step : Fin data.length) :
    QuittingSimonFEdgeAt stressReward epsilon
      (data.state phase step) (data.state phase (step + 1)) := by
  let root := rootOfHazard (data.row phase) (data.row_nonneg phase)
    (data.row_le_one phase)
  refine ⟨root, ?_, ?_⟩
  · exact isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow
      stressWeight (data.row phase) (data.row_nonneg phase)
      (data.row_le_one phase) (data.state phase step) epsilon
      (data.row_supportPerfect phase step.isLt)
  · rw [quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext]
    exact (data.state_succ phase step).symm

private theorem euclideanDist_pos_of_ne {first second : Payoff Player}
    (hne : first ≠ second) : 0 < euclideanDist first second := by
  rw [euclideanDist, euclideanNorm]
  obtain ⟨who, hwho⟩ : ∃ who, first who - second who ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun who ↦ sub_eq_zero.mp (hall who))
  apply Real.sqrt_pos_of_pos
  refine Finset.sum_pos' (fun who _ ↦ sq_nonneg (first who - second who)) ?_
  exact ⟨who, Finset.mem_univ who, sq_pos_of_ne_zero hwho⟩

theorem state_succ_ne (phase : ZMod 4) (step : ℕ) :
    data.state phase (step + 1) ≠ data.state phase step := by
  intro heq
  have hbpow : 0 < data.beta ^ step := pow_pos data.beta_pos _
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl
  · have h := congrFun heq 0
    simp +decide [state, stressVertex, stressWeight, segmentPoint,
      pow_succ] at h
    nlinarith [data.beta_lt_one]
  · have h := congrFun heq 1
    simp +decide [state, stressVertex, stressWeight, segmentPoint,
      pow_succ] at h
    nlinarith [data.beta_lt_one]
  · have h := congrFun heq 0
    simp +decide [state, stressVertex, stressWeight, segmentPoint,
      pow_succ] at h
    nlinarith [data.beta_lt_one]
  · have h := congrFun heq 1
    simp +decide [state, stressVertex, stressWeight, segmentPoint,
      pow_succ] at h
    nlinarith [data.beta_lt_one]

/-- Every microedge has strictly positive Euclidean variation. -/
theorem microCost_pos (phase : ZMod 4) (step : Fin data.length) :
    0 < euclideanDist (data.state phase (step + 1))
      (data.state phase step) :=
  euclideanDist_pos_of_ne (data.state_succ_ne phase step)

/-- The four geometrically subdivided phases form a literal positive-cost
cycle in the production carrier. -/
structure PositiveCycle where
  /-- Carrier states along every phase, including both endpoints. -/
  point : ZMod 4 → Fin (data.length + 1) →
    QuittingSimonFiniteOrbitCarrier stressReward epsilon
  /-- Every consecutive pair is a production edge. -/
  edge : ∀ phase (step : Fin data.length),
    (point phase step.castSucc, point phase step.succ) ∈
      QuittingSimonFiniteOrbitGraphAt stressReward epsilon
  /-- Phase endpoints glue cyclically. -/
  glue : ∀ phase, point phase (Fin.last data.length) =
    point (phase + 1) 0
  /-- Every microedge has positive cost. -/
  cost_pos : ∀ phase (step : Fin data.length),
    0 < QuittingSimonFiniteOrbitCost
      (point phase step.castSucc) (point phase step.succ)

/-- Package the actual full-correspondence positive cycle. -/
def positiveCycle : data.PositiveCycle where
  point := data.carrierState
  edge := by
    intro phase step
    exact data.fEdge phase step
  glue := by
    intro phase
    apply Subtype.ext
    change data.state phase data.length = data.state (phase + 1) 0
    rw [data.state_end, data.state_zero]
  cost_pos := by
    intro phase step
    change 0 < euclideanDist (data.state phase (step + 1))
      (data.state phase step)
    exact data.microCost_pos phase step

end StressSimonSubdivision

/-- Every positive tolerance admits a finite geometric subdivision of the
stress circulation inside the full production correspondence. -/
theorem exists_stressSimonSubdivision (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Nonempty (StressSimonSubdivision epsilon) := by
  obtain ⟨length, beta, hlength, hbeta0, hbeta1, hpow, hhazard⟩ :=
    exists_pow_eq_and_one_sub_le (1 / 2) (by norm_num) (by norm_num)
      epsilon hepsilon
  have hbetaPos : 0 < beta := by
    apply lt_of_le_of_ne hbeta0
    intro hzero
    have hzero' : beta = 0 := hzero.symm
    rw [hzero', zero_pow (Nat.ne_of_gt hlength)] at hpow
    norm_num at hpow
  exact ⟨⟨length, hlength, beta, hbetaPos, hbeta1, hpow, hhazard⟩⟩

/-- At tolerance `1/2`, the subdivision has exactly one edge per phase and
all data are rational. -/
def stressSimonHalfSubdivision : StressSimonSubdivision (1 / 2) where
  length := 1
  length_pos := by norm_num
  beta := 1 / 2
  beta_pos := by norm_num
  beta_lt_one := by norm_num
  beta_pow := by norm_num
  hazard_le := by norm_num

/-- Every edge of the unsubdivided rational cycle at tolerance `1/2` has
Euclidean cost exactly `sqrt 2`. -/
theorem stressSimonHalfSubdivision_microCost
    (phase : ZMod 4) (step : Fin stressSimonHalfSubdivision.length) :
    QuittingSimonFiniteOrbitCost
      (stressSimonHalfSubdivision.positiveCycle.point phase step.castSucc)
      (stressSimonHalfSubdivision.positiveCycle.point phase step.succ) =
        Real.sqrt 2 := by
  fin_cases step
  rcases zmod_four_cases phase with rfl | rfl | rfl | rfl <;>
    simp +decide [StressSimonSubdivision.positiveCycle,
      StressSimonSubdivision.carrierState, QuittingSimonFiniteOrbitCost,
      StressSimonSubdivision.state, stressSimonHalfSubdivision,
      euclideanDist, euclideanNorm, segmentPoint, stressVertex,
      stressWeight, Fin.sum_univ_succ] <;> norm_num

/-- A positive-cost finite cycle excludes every positive-coefficient global
potential on the full stress correspondence. -/
theorem not_exists_stressSimonStrictPotential
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ¬ ∃ (potential : QuittingSimonFiniteOrbitCarrier stressReward epsilon → ℝ)
        (constant : ℝ),
      0 < constant ∧
        ∀ first next,
          (first, next) ∈ QuittingSimonFiniteOrbitGraphAt stressReward epsilon →
            potential next ≤ potential first - constant *
              QuittingSimonFiniteOrbitCost first next := by
  obtain ⟨data⟩ := exists_stressSimonSubdivision epsilon hepsilon
  rintro ⟨potential, constant, hconstant, hdecrease⟩
  let cycle := data.positiveCycle
  have hstep (phase : ZMod 4) (step : Fin data.length) :
      potential (cycle.point phase step.succ) <
        potential (cycle.point phase step.castSucc) := by
    have hle := hdecrease _ _ (cycle.edge phase step)
    have hcost := cycle.cost_pos phase step
    nlinarith
  have hphase (phase : ZMod 4) :
      potential (cycle.point phase (Fin.last data.length)) <
        potential (cycle.point phase 0) := by
    have hwalk (step : ℕ) (hstepLt : step < data.length) :
        potential (cycle.point phase
          ⟨step + 1, Nat.succ_lt_succ hstepLt⟩) <
        potential (cycle.point phase
          ⟨step, Nat.lt_succ_of_lt hstepLt⟩) := by
      simpa using hstep phase ⟨step, hstepLt⟩
    have hchain : ∀ (step : ℕ) (hstepLt : step < data.length),
        potential (cycle.point phase
          ⟨step + 1, Nat.succ_lt_succ hstepLt⟩) <
        potential (cycle.point phase 0) := by
      intro step hstepLt
      induction step with
      | zero => simpa using hwalk 0 hstepLt
      | succ step ih =>
          have hprevious : step < data.length := by omega
          exact (hwalk (step + 1) hstepLt).trans (ih hprevious)
    have hlength := data.length_pos
    have hlast : data.length - 1 < data.length := by omega
    have hsucc : data.length - 1 + 1 = data.length := by omega
    let lastIndex : Fin (data.length + 1) :=
      ⟨data.length - 1 + 1, Nat.succ_lt_succ hlast⟩
    have hlastIndex : lastIndex = Fin.last data.length := by
      apply Fin.ext
      exact hsucc
    rw [← hlastIndex]
    exact hchain (data.length - 1) hlast
  have h0 := hphase (0 : ZMod 4)
  have h1 := hphase (1 : ZMod 4)
  have h2 := hphase (2 : ZMod 4)
  have h3 := hphase (3 : ZMod 4)
  rw [cycle.glue] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  exact (lt_trans h3 (lt_trans h2 (lt_trans h1 h0))).false

/-- The repaired stress table has no positive-coefficient finite-cell Simon
Lyapunov certificate at any positive tolerance. -/
theorem not_hasQuittingSimonFiniteCellLyapunovCertificate_stressWeight
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {Cell : Type*} [Fintype Cell]
    (cell : Cell → Set (QuittingSimonFiniteOrbitCarrier stressReward epsilon))
    (localPotential : Cell →
      QuittingSimonFiniteOrbitCarrier stressReward epsilon → ℝ)
    (constant lower upper : ℝ) (hconstant : 0 < constant) :
    ¬ HasQuittingSimonFiniteCellLyapunovCertificate stressReward epsilon
      cell localPotential constant lower upper := by
  intro hcertificate
  obtain ⟨potential, _, _, hdecrease⟩ :=
    Math.Topology.HasFiniteCellLyapunovCertificate.exists_globalPotential
      hcertificate
  exact not_exists_stressSimonStrictPotential epsilon hepsilon
    ⟨potential, constant, hconstant, fun first next hedge ↦
      hdecrease first next hedge⟩

end RepairedFourPlayerStress
end GameTheory
