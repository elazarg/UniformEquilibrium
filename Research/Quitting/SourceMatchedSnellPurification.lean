/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SparseVanishingSchedule
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Conditioned.Diffuse.FixedOutsider

/-!
# The source-matched Snell-purification interface

The positive diffuse branch supplies a fixed-outsider endpoint gap.  The
coupled construction must impose the outsider's scalar Snell contact set while
retaining the vector conditioned chronology.  This file states the exact
input/output contract for that construction.

`SourceMatchedSnellPurification` is a proposition, not a theorem.  Its
enlargement output is a fully certified candidate with a strictly larger
source face.  The finite-face consumer applies when an implementation supplies
the whole interface for every candidate it creates.

**Caveat: the interface as stated admits regime-free candidates, and its
enlargement branch is free.**  `selected_support` bounds activity *above* by
`face`; no field forces a face member to be active.  So enlargement is mere
padding, and the finite-face induction carries content only at
`face = Finset.univ.erase owner`.  Moreover a fully certified candidate with a
schedule assembles on the Solan--Vieille boundary table from a single solo
quitter and one strict preemption edge, with no counterexample regime, seam,
minmax, or debt input, and with an unbounded phantom `boundary`.  Both facts
are checked in `Research/Quitting/SourceMatchedSnellPurificationCollapse.lean`.
Nothing below is changed by that module, and neither
it nor this caveat refutes the proposition; they record that satisfying the
interface cannot be powered by regime data reaching it through a candidate.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A complete conditioned-tail datum to which the source-matched construction
must be applied.  The `endpointGap` is the literal endpoint difference, not
merely a positive rescaled-Quit defect. -/
structure SourceMatchedSnellCandidate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) where
  roots : ℕ → ι → PMF Bool
  value : ℕ → Payoff ι
  boundary : Payoff ι
  face : Finset ι
  owner : ι
  owner_not_mem_face : owner ∉ face
  positive : ∀ time, 0 < quittingTailEventualAbsorption roots time
  mesh_tendsto : Tendsto
    (quittingTailConditionedAbsorptionWeight roots) atTop (nhds 0)
  policy : ∀ time, value time =
    quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)
  endpoint_nash : ∀ time,
    IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time)
  conditioned_bound : ∀ time player,
    |quittingTailConditionedValue roots value boundary time player| ≤
      quittingRewardBound reward

/-- The schedule evidence consumed by a source-matched implementation. -/
structure SourceMatchedSnellSchedule (c : SourceMatchedSnellCandidate reward) where
  time : ℕ → ℕ
  theta : ℕ → ℝ
  strictMono : StrictMono time
  theta_pos : ∀ n, 0 < theta n
  theta_le_one : ∀ n, theta n ≤ 1
  theta_tendsto_zero : Tendsto theta atTop (nhds 0)
  theta_not_summable : ¬Summable theta
  selected_mesh_bound : ∀ n,
    quittingTailConditionedAbsorptionWeight c.roots (time n) ≤
      (1 / 2 : ℝ) ^ n
  endpoint_eta : ℝ
  endpoint_eta_pos : 0 < endpoint_eta
  selected_endpoint_gap : ∀ n,
    endpoint_eta / 2 ≤ quittingRootEndpointDifference reward
      (quittingTailConditionedValue c.roots c.value c.boundary (time n + 1))
        (quittingTailDiffuseRescaledRoot c.roots (time n)
          (c.positive (time n))) c.owner
  selected_support : ∀ n player,
    c.roots (time n) player ≠ PMF.pure false → player ∈ c.face

namespace SourceMatchedSnellSchedule

variable {c : SourceMatchedSnellCandidate (ι := ι) reward}

/-- Source support containment forces the selected outsider to Continue. -/
theorem owner_inactive (schedule : SourceMatchedSnellSchedule c) (n : ℕ) :
    c.roots (schedule.time n) c.owner = PMF.pure false := by
  by_contra hactive
  exact c.owner_not_mem_face (schedule.selected_support n c.owner hactive)

/-- The selected mesh bound and unit clock make the collision costs summable. -/
theorem collision_summable (schedule : SourceMatchedSnellSchedule c) :
    Summable (fun n => schedule.theta n *
      quittingTailConditionedAbsorptionWeight c.roots (schedule.time n)) := by
  have hnonneg : ∀ n, 0 ≤ schedule.theta n *
      quittingTailConditionedAbsorptionWeight c.roots (schedule.time n) := by
    intro n
    exact mul_nonneg (schedule.theta_pos n).le
      (quittingTailConditionedAbsorptionWeight_nonneg c.roots _ (c.positive _))
  have hbound : ∀ n, schedule.theta n *
      quittingTailConditionedAbsorptionWeight c.roots (schedule.time n) ≤
        (1 / 2 : ℝ) ^ n := by
    intro n
    exact (mul_le_of_le_one_left
      (quittingTailConditionedAbsorptionWeight_nonneg c.roots _ (c.positive _))
      (schedule.theta_le_one n)).trans (schedule.selected_mesh_bound n)
  exact Summable.of_nonneg_of_le hnonneg hbound
    (summable_geometric_of_norm_lt_one (by norm_num))

end SourceMatchedSnellSchedule

/-- The two honest outputs of the missing source-matched construction. -/
def SourceMatchedSnellStep (c : SourceMatchedSnellCandidate reward) : Prop :=
  (∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
    ∃ next : SourceMatchedSnellCandidate reward,
      Nonempty (SourceMatchedSnellSchedule next) ∧ c.face ⊂ next.face

/-- The source-matched Snell-purification proposition.  It is open: no field
asserts that the scalar contact set has already been coupled to the vector
recursion. -/
def SourceMatchedSnellPurification : Prop :=
  ∀ c : SourceMatchedSnellCandidate reward,
    Nonempty (SourceMatchedSnellSchedule c) →
      SourceMatchedSnellStep c

/-! ## Checked assembly of the positive diffuse input -/

theorem exists_sourceMatchedSnellCandidate_of_diffuse
    {regime : QuittingCounterexampleRegime reward}
    (seam : QuittingCounterexampleDynamicTailWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ c : SourceMatchedSnellCandidate reward,
      Nonempty (SourceMatchedSnellSchedule c) ∧
        c.roots = quittingDynamicDebtTailRoots seam.tail := by
  letI : Nonempty ι := regime.nonempty_players
  let roots := quittingDynamicDebtTailRoots seam.tail
  let value : ℕ → Payoff ι := fun time => (seam.tail time).1.1
  obtain ⟨owner, eta, heta, hdates⟩ :=
    seam.exists_cofinal_fixed_inactive_rescaledEndpointGap_of_diffuse
      hpositive hmesh
  let face : Finset ι := Finset.univ.erase owner
  let P : ℕ → Prop := fun time =>
    eta / 2 ≤ quittingRootEndpointDifference reward
      (quittingTailConditionedValue roots value seam.limit.value (time + 1))
      (quittingTailDiffuseRescaledRoot roots time (hpositive time)) owner ∧
    ∀ player, roots time player ≠ PMF.pure false → player ∈ face
  have hP : ∀ start, ∃ time, start ≤ time ∧ P time := by
    intro start
    obtain ⟨time, htime, hinactive, _, _, hendpoint⟩ := hdates start
    refine ⟨time, htime, hendpoint, ?_⟩
    intro player hplayer
    simp only [face, Finset.mem_erase, Finset.mem_univ]
    constructor
    · intro heq
      subst player
      exact (hplayer hinactive).elim
    · trivial
  have hsched : ∃ time : ℕ → ℕ, ∃ theta : ℕ → ℝ,
      (∀ n, P (time n)) ∧ StrictMono time ∧
      (∀ n, quittingTailConditionedAbsorptionWeight roots (time n) ≤
        (1 / 2 : ℝ) ^ n) ∧
      (∀ n, 0 < theta n) ∧ (∀ n, theta n ≤ 1) ∧
      Tendsto theta atTop (nhds 0) ∧
      ¬Summable theta ∧ Summable (fun n => theta n *
        quittingTailConditionedAbsorptionWeight roots (time n)) := by
    simpa [P] using
      Math.exists_sparse_vanishing_nonsummable_schedule_of_cofinal P hP
        (fun time => quittingTailConditionedAbsorptionWeight roots time)
        (fun time => quittingTailConditionedAbsorptionWeight_nonneg roots time
          (hpositive time)) hmesh
  have hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
    intro time
    exact (seam.tail_edge time).1.1
  have hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time) := by
    intro time
    simpa only [value, roots, quittingDynamicDebtTailRoots] using
      (seam.tail_edge time).1.2
  have hbound : ∀ time player,
      |quittingTailConditionedValue roots value seam.limit.value time player| ≤
        quittingRewardBound reward := by
    intro time player
    exact abs_quittingTailConditionedValue_le roots value seam.limit.value
      hpolicy (abs_reward_le_quittingRewardBound reward) seam.value_tendsto time
      (hpositive time) player
  obtain ⟨time, theta, hPtime, htime, hselectedMesh, hthetaPos, hthetaLe,
      hthetaZero, hthetaNonsummable, _⟩ := hsched
  let c : SourceMatchedSnellCandidate reward := by
    refine ⟨roots, value, seam.limit.value, face, owner, ?_, hpositive, hmesh,
      hpolicy, hnash, hbound⟩
    simp [face]
  have hselected : ∀ n, eta / 2 ≤ quittingRootEndpointDifference reward
        (quittingTailConditionedValue c.roots c.value c.boundary (time n + 1))
        (quittingTailDiffuseRescaledRoot c.roots (time n)
          (c.positive (time n))) c.owner := by
    intro n
    simpa only [c, P] using (hPtime n).1
  have hselectedSupport : ∀ n player,
      c.roots (time n) player ≠ PMF.pure false → player ∈ c.face := by
    intro n player hplayer
    have hsupport := (hPtime n).2
    exact hsupport player hplayer
  let sched : SourceMatchedSnellSchedule c := by
    exact ⟨time, theta, htime, hthetaPos, hthetaLe, hthetaZero,
      hthetaNonsummable, hselectedMesh, eta, heta, hselected, hselectedSupport⟩
  exact ⟨c, ⟨⟨sched⟩, rfl⟩⟩

/-! ## Finite-face consumption, conditional on the open interface -/

/-- Finite face enlargement turns a complete source-matched interface into an
actual uniform-equilibrium payoff for every certified starting candidate. -/
theorem exists_uniformPayoff_of_sourceMatchedSnellCandidate
    (hinterface : SourceMatchedSnellPurification (reward := reward))
    (c : SourceMatchedSnellCandidate reward)
    (hc : Nonempty (SourceMatchedSnellSchedule c)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  let remaining : SourceMatchedSnellCandidate reward → ℕ := fun d =>
    Fintype.card ι - d.face.card
  have hsolve : ∀ n : ℕ, ∀ d : SourceMatchedSnellCandidate reward,
      remaining d = n → Nonempty (SourceMatchedSnellSchedule d) →
        ∃ payoff : Payoff ι,
          (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hrem hd
      rcases hinterface d hd with ⟨hpayoff⟩ | ⟨d', hd', hsubset⟩
      · exact hpayoff
      · have hcard : d.face.card < d'.face.card := Finset.card_lt_card hsubset
        have hle : d'.face.card ≤ Fintype.card ι := by
          exact Finset.card_le_univ d'.face
        have hnext : remaining d' < n := by
          dsimp [remaining] at hrem ⊢
          omega
        exact ih (remaining d') hnext d' rfl hd'
  exact hsolve (remaining c) c rfl hc

/-- Under the positive-diffuse hypotheses, a source-matched implementation for
every certified candidate reaches a uniform-equilibrium payoff. -/
theorem exists_uniformPayoff_of_sourceMatchedSnellPurification
    {regime : QuittingCounterexampleRegime reward}
    (hinterface : SourceMatchedSnellPurification (reward := reward))
    (seam : QuittingCounterexampleDynamicTailWitness regime)
    (hpositive : ∀ time, 0 < quittingTailEventualAbsorption
      (quittingDynamicDebtTailRoots seam.tail) time)
    (hmesh : Tendsto (quittingTailConditionedAbsorptionWeight
      (quittingDynamicDebtTailRoots seam.tail)) atTop (nhds 0)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨c, hc, _⟩ := exists_sourceMatchedSnellCandidate_of_diffuse
    seam hpositive hmesh
  exact exists_uniformPayoff_of_sourceMatchedSnellCandidate hinterface c hc

end GameTheory
