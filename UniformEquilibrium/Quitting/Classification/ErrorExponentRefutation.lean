/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.LocalGlobalCounterexample
import UniformEquilibrium.Quitting.Classification.Existence.PerfectSequenceExtraction

/-!
# The unqualified error-exponent claim is false

Ashkenazi-Golan, Krasikov, Rainer and Solan, *Absorption paths and equilibria
in quitting games*, Mathematical Programming 203 (2024), Theorem 3.5, state that
for every sufficiently small `ε > 0` an absorbing profile at which every player
is sequentially `ε`-perfect is an `ε ^ (1 / 6)`-equilibrium.  The theorem the
statement is attributed to, Solan and Vieille, *Quitting games*, Math. Oper.
Res. 26 (2001), Proposition 2.4, restated there as Proposition 2.6, concludes a
disjunction instead: either the absorbing sequentially perfect profile is
globally approximately optimal, or the game has a stationary approximate
equilibrium.

`QuittingSequentialPerfectionErrorExponent` states the journal form over the
repository's quitting semantics, and
`not_quittingSequentialPerfectionErrorExponent` proves its negation.  The
witness is the two-player game of
`UniformEquilibrium/Quitting/Boundary/Repair/LocalGlobalCounterexample.lean`,
packaged here as the constant root sequence
`localGlobalCounterexampleRoots`: it absorbs at its first stage, every row is
exactly `0`-perfect against the sequence's own continuation vector, and the
generated profile has terminal regret exactly one.

The faithful every-tail disjunction from 2001 is checked in
`exists_quittingSubgamePerfectOrStationary_of_unitSoloExit_of_terminatingTails`.
It assumes unit solo-exit payoffs and termination after every restart.  The
counterexample satisfies its stationary disjunct, by
`quittingStationaryεEquilibriumExistence_localGlobalCounterexampleReward`, so
the disjunction is not refuted by the same witness.

The error exponent `1 / 6` plays no role in the refutation: any exponent
sending small positive errors to values below one fails on this witness,
because the witness is exactly `0`-perfect and has regret one.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter
open scoped Topology

/-! ## The counterexample as an absorbing root sequence -/

/-- The counterexample's constant root sequence: player one quits and player
two continues at every stage. -/
def localGlobalCounterexampleRoots : ℕ → Bool → PMF Bool :=
  fun _ => localGlobalCounterexampleRoot

/-- The root sequence generates the counterexample's stationary profile from
every starting stage. -/
theorem quittingRootSequenceProfile_localGlobalCounterexampleRoots
    (start : ℕ) :
    quittingRootSequenceProfile localGlobalCounterexampleReward
        localGlobalCounterexampleRoots start =
      localGlobalCounterexampleProfile := by
  rw [localGlobalCounterexampleProfile_eq_stationary]
  rfl

/-- Each row of the sequence absorbs surely, so no play survives one stage. -/
@[simp] theorem quittingStationaryContinueMass_localGlobalCounterexampleRoot :
    quittingStationaryContinueMass localGlobalCounterexampleRoot = 0 := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  refine Finset.prod_eq_zero (Finset.mem_univ false) ?_
  simp [localGlobalCounterexampleRoot, localGlobalCounterexampleAction]

/-- The root sequence is completely absorbing: its survival prefix is `0` from
the first stage on. -/
theorem isCompletelyAbsorbing_localGlobalCounterexampleRoots :
    IsCompletelyAbsorbing localGlobalCounterexampleRoots := by
  refine Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ℝ))
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [quittingSurvivalPrefix]
  refine (Finset.prod_eq_zero (Finset.mem_range.2 hN) ?_).symm
  exact quittingStationaryContinueMass_localGlobalCounterexampleRoot

/-- The sequence's continuation vector at every stage is the counterexample's
declared continuation `(-1, 0)`. -/
@[simp] theorem quittingRootSequenceTailVector_localGlobalCounterexampleRoots
    (start : ℕ) :
    quittingRootSequenceTailVector localGlobalCounterexampleReward
        localGlobalCounterexampleRoots start =
      localGlobalCounterexampleContinuation := by
  funext who
  rw [quittingRootSequenceTailVector, quittingRootSequenceTerminalValue,
    quittingRootSequenceProfile_localGlobalCounterexampleRoots]
  exact congrFun quittingTerminalPayoff_localGlobalCounterexampleProfile_eq who

/-- Every row of the sequence is exactly `0`-perfect against the sequence's
own continuation vector: at `(-1, 0)` both of each player's pure actions pay
that player its prescribed value. -/
theorem quittingRowεPerfect_localGlobalCounterexampleRoots
    {ε : ℝ} (hε : 0 ≤ ε) (time : ℕ) :
    QuittingRowεPerfect localGlobalCounterexampleReward
      (quittingRootSequenceTailVector localGlobalCounterexampleReward
        localGlobalCounterexampleRoots (time + 1))
      (localGlobalCounterexampleRoots time) ε := by
  rw [quittingRootSequenceTailVector_localGlobalCounterexampleRoots]
  intro who
  have hquit :
      quittingRootQuitPayoff localGlobalCounterexampleReward
          localGlobalCounterexampleContinuation
          localGlobalCounterexampleRoot who =
        quittingRootSuccessorPayoff localGlobalCounterexampleReward
          localGlobalCounterexampleContinuation
          localGlobalCounterexampleRoot who :=
    quittingRootExpectedPayoff_localGlobalCounterexample_pureDeviation who true
  have hcontinue :
      quittingRootContinuePayoff localGlobalCounterexampleReward
          localGlobalCounterexampleContinuation
          localGlobalCounterexampleRoot who =
        quittingRootSuccessorPayoff localGlobalCounterexampleReward
          localGlobalCounterexampleContinuation
          localGlobalCounterexampleRoot who :=
    quittingRootExpectedPayoff_localGlobalCounterexample_pureDeviation who false
  simp only [localGlobalCounterexampleRoots]
  refine ⟨by rw [hquit]; linarith, by rw [hcontinue]; linarith,
    fun _ => by rw [hquit]; linarith, fun _ => by rw [hcontinue]; linarith⟩

/-- The local-to-global separation in one literal theorem: the displayed
root sequence is completely absorbing and exactly row-perfect against all of
its restarted tail values, while its generated profile has terminal regret
exactly one and is not even a terminal zero-equilibrium. -/
theorem localGlobalCounterexample_rowwiseZeroPerfect_but_terminalRegretOne :
    IsCompletelyAbsorbing localGlobalCounterexampleRoots ∧
      (∀ time : ℕ, QuittingRowεPerfect localGlobalCounterexampleReward
        (quittingRootSequenceTailVector localGlobalCounterexampleReward
          localGlobalCounterexampleRoots (time + 1))
        (localGlobalCounterexampleRoots time) 0) ∧
      quittingTerminalPayoff localGlobalCounterexampleReward
          (Function.update localGlobalCounterexampleProfile false
            (quittingAlwaysContinueStrategy
              localGlobalCounterexampleReward false)) false -
        quittingTerminalPayoff localGlobalCounterexampleReward
          localGlobalCounterexampleProfile false = 1 ∧
      ¬(quittingGame localGlobalCounterexampleReward).IsεAsymptoticNash
        (quittingTerminalPayoff localGlobalCounterexampleReward) 0
        localGlobalCounterexampleProfile := by
  refine ⟨isCompletelyAbsorbing_localGlobalCounterexampleRoots, ?_,
    localGlobalCounterexample_terminalRegret_eq_one,
    not_isεAsymptoticNash_localGlobalCounterexampleProfile (by norm_num)⟩
  intro time
  exact quittingRowεPerfect_localGlobalCounterexampleRoots le_rfl time

/-! ## The printed claim and its negation -/

/-- **Theorem 3.5 as printed**, over the repository's quitting semantics: in
every finite quitting game there is a positive threshold below which every
completely absorbing root sequence with `ε`-perfect rows generates a terminal
`ε ^ (1 / 6)`-equilibrium.

`QuittingRowεPerfect` is the paper's one-stage test and
`quittingRootSequenceTailVector` is the sequence's own continuation vector, so
the hypothesis is sequential `ε`-perfectness of every player at the generated
profile. -/
def QuittingSequentialPerfectionErrorExponent : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (reward : {S : Finset ι // S.Nonempty} → Payoff ι),
    ∃ bound : ℝ, 0 < bound ∧
      ∀ ε : ℝ, 0 < ε → ε < bound →
        ∀ roots : ℕ → ι → PMF Bool, IsCompletelyAbsorbing roots →
          (∀ time : ℕ, QuittingRowεPerfect reward
              (quittingRootSequenceTailVector reward roots (time + 1))
              (roots time) ε) →
            (quittingGame reward).IsεAsymptoticNash
              (quittingTerminalPayoff reward) (ε ^ ((1 : ℝ) / 6))
              (quittingRootSequenceProfile reward roots 0)

/-- **The printed error-exponent claim is false.**  In the two-player game of
`localGlobalCounterexampleReward` the constant sequence
`localGlobalCounterexampleRoots` absorbs surely at its first stage and is
exactly `0`-perfect at every stage, yet the profile it generates lets player
one continue forever and gain exactly one, by
`localGlobalCounterexample_terminalRegret_eq_one`.  For every positive `ε`
below one the promised error `ε ^ (1 / 6)` is below one, so no threshold
works. -/
theorem not_quittingSequentialPerfectionErrorExponent :
    ¬ QuittingSequentialPerfectionErrorExponent := by
  intro hclaim
  obtain ⟨bound, hbound, hsmall⟩ := hclaim Bool localGlobalCounterexampleReward
  set ε : ℝ := min bound 1 / 2 with hεdef
  have hone : (0 : ℝ) < min bound 1 := lt_min hbound one_pos
  have hε0 : 0 < ε := by positivity
  have hεbound : ε < bound := by
    have := min_le_left bound (1 : ℝ)
    simp only [hεdef]
    linarith
  have hε1 : ε < 1 := by
    have := min_le_right bound (1 : ℝ)
    simp only [hεdef]
    linarith
  have hnash := hsmall ε hε0 hεbound localGlobalCounterexampleRoots
    isCompletelyAbsorbing_localGlobalCounterexampleRoots
    (quittingRowεPerfect_localGlobalCounterexampleRoots hε0.le)
  rw [quittingRootSequenceProfile_localGlobalCounterexampleRoots] at hnash
  exact not_isεAsymptoticNash_localGlobalCounterexampleProfile
    (Real.rpow_lt_one hε0.le hε1 (by norm_num)) hnash

/-! ## The faithful every-tail disjunction -/

/-- **Solan--Vieille Proposition 2.4, in production semantics.**  Under unit
solo-exit payoffs, a sufficiently accurate root sequence that terminates after
every restart and is row-perfect against its actual restarted tail values is
either a terminal approximate equilibrium after every restart or yields a
stationary approximate equilibrium.

The every-tail hypothesis is strictly stronger than initial
`IsCompletelyAbsorbing` after a sure-absorption row.  This theorem therefore
does not supply the missing reverse implication for the literal S.3 branch of
AKRS Theorem 3.4. -/
theorem exists_quittingSubgamePerfectOrStationary_of_unitSoloExit_of_terminatingTails
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (hunit : QuittingUnitSoloExit reward) :
    ∃ bound : ℝ, 0 < bound ∧
      ∀ (roots : ℕ → ι → PMF Bool) (ε : ℝ),
        0 < ε → ε < bound →
        (∀ start, Tendsto (quittingJointSurvivalWeight roots start)
          atTop (nhds 0)) →
        (∀ time : ℕ, QuittingRowεPerfect reward
          (quittingRootSequenceTailVector reward roots (time + 1))
          (roots time) ε) →
        (∀ start, (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) (ε ^ ((1 : ℝ) / 6))
          (quittingRootSequenceProfile reward roots start)) ∨
        ∃ root : ι → PMF Bool,
          (quittingGame reward).IsεAsymptoticNash
            (quittingTerminalPayoff reward) (ε ^ ((1 : ℝ) / 6))
            (quittingStationaryProfile reward root) :=
  exists_quittingPerfectSequenceSubgameDichotomy_of_soloExitPreference hunit

/-- **The counterexample satisfies the stationary disjunct exactly.**  The
all-continue profile is a terminal `0`-equilibrium of
`localGlobalCounterexampleReward`, by
`isAsymptoticNash_quittingAlwaysContinue_localGlobalCounterexample`, hence a
terminal `ε`-equilibrium at every positive tolerance. -/
theorem quittingStationaryεEquilibriumExistence_localGlobalCounterexampleReward :
    QuittingStationaryεEquilibriumExistence localGlobalCounterexampleReward := by
  intro ε hε
  refine ⟨quittingAllContinueRoot, ?_⟩
  have hcontinue :
      quittingStationaryProfile localGlobalCounterexampleReward
          quittingAllContinueRoot =
        quittingAlwaysContinueProfile localGlobalCounterexampleReward := rfl
  rw [hcontinue]
  exact isAsymptoticNash_quittingAlwaysContinue_localGlobalCounterexample.mono
    hε.le

end GameTheory
