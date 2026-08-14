/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import UniformEquilibrium.Quitting.Debt.Dynamic.PositiveDynamicDebtProvenance
import UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Owner-solo certification, or a universal joining obstruction

The positive branch of the exact dynamic-debt split supplies a debt owner
with a strictly positive singleton reward, and the Q129 provenance theorem
identifies the owner's optimal deviation as Continue-through-prefix plus a
terminal solo Quit.  This experiment certifies that deviation as prescribed
play: the owner's solo stationary root at any rate `p ∈ (0,1]` is an exact
terminal Nash equilibrium precisely when every opponent's exact inactive
inequality

  `(1-p) * r_other({other}) + p * r_other({owner,other}) ≤ r_other({owner})`

holds.  The certified payoff vector is `quittingSoloReward reward owner` —
exactly the value of the deviation whose exploitability the debt measured.

Consequently the positive-debt exceptional object splits further: either
some rate certifies, and the game has a uniform-equilibrium payoff through
the landed terminal-to-uniform bridge, or **every** rate has a strict joiner
or preemptor.  The two-player vanishing counterexample
(`QuittingExactDynamicDebtVanishingCounterexample`, table `QC ↦ (1,0)`,
`CQ ↦ (3,-1)`, `QQ ↦ (2,1)`) sits in the first branch: its stationary
equilibrium `(1,0)` is the owner-solo certificate at rate `1/2`, and its
value appears in no zero-boundary chain, so this producer genuinely leaves
the chain geometry.
-/


noncomputable section

namespace GameTheory
namespace OwnerSoloCertificationResearch

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Exact owner-solo certification -/

/-- **Exact owner-solo certification criterion.**  If the owner's singleton
reward is nonnegative and every opponent's inactive-Quit mixture is bounded
by that opponent's payoff under the owner's solo absorption, then the solo
stationary root is an exact terminal Nash equilibrium. -/
theorem isεAsymptoticNash_soloStationary_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard)) := by
  intro who deviation
  rw [quittingTerminalPayoff_soloStationary reward owner who hazard
    hpositive, add_zero]
  by_cases hwho : who = owner
  · subst who
    exact (quittingTerminalPayoff_update_solo_owner_le
      reward owner hazard deviation).trans (max_le howner le_rfl)
  · refine (quittingTerminalPayoff_update_stationary_le_unilateralCap
      reward (quittingSoloStationaryRoot owner hazard) who deviation
      (quittingStationaryFixedOpponentsContinueMass_solo_other_lt_one
        hwho hazard hpositive)).trans ?_
    rw [quittingStationaryUnilateralCap_solo_other reward hwho hazard
        hpositive,
      quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
        reward hwho hazard]
    exact max_le (hinactive who hwho) le_rfl

/-! ## Exact terminal Nash delivers its own terminal payoff uniformly -/

/-- An exact terminal Nash profile's own terminal payoff is a
uniform-equilibrium payoff.  This is the generic form of the delivery
argument used for the concrete two-player counterexample. -/
theorem quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) 0 profile) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingTerminalPayoff reward profile) := by
  intro ε hε
  obtain ⟨nashThreshold, hnashThreshold⟩ :=
    quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hε hnash
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in Filter.atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
        quittingTerminalPayoff reward profile who| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro who
    have hball :=
      (tendsto_finiteAveragePayoff_quittingGame reward profile who).eventually
        (Metric.ball_mem_nhds
          (quittingTerminalPayoff reward profile who) hε)
    filter_upwards [hball] with horizon hhorizon
    simpa [Metric.mem_ball, Real.dist_eq] using hhorizon.le
  obtain ⟨deliveryThreshold, hdeliveryThreshold⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon ↦ ⟨?_, ?_⟩⟩
  · exact hnashThreshold horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)
  · exact hdeliveryThreshold horizon
      (le_trans (Nat.le_max_right _ _) hhorizon)

/-- The certified owner-solo payoff vector is a uniform-equilibrium
payoff. -/
theorem isUniformEquilibriumPayoff_soloReward_of_inactive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (howner : 0 ≤ quittingSoloReward reward owner owner)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner) := by
  have hpayoff := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    reward _ (isεAsymptoticNash_soloStationary_exact
      reward owner hazard hpositive howner hinactive)
  have heq : quittingTerminalPayoff reward
      (quittingStationaryProfile reward
        (quittingSoloStationaryRoot owner hazard)) =
      quittingSoloReward reward owner :=
    funext fun who ↦
      quittingTerminalPayoff_soloStationary reward owner who hazard hpositive
  rwa [heq] at hpayoff

/-! ## The rate dichotomy -/

/-- Some opponent strictly prefers quitting against the owner's solo rate
`p` to receiving the owner's solo absorption payoff. -/
def QuittingSoloJoiningObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) : Prop :=
  ∃ other, other ≠ owner ∧
    quittingSoloReward reward owner other <
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other

omit [Fintype ι] in
/-- Either some rate in `(0,1]` satisfies every opponent's inactive
inequality, or every rate has a strict joiner/preemptor. -/
theorem soloCertification_or_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ other, other ≠ owner →
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other) ∨
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p := by
  by_cases hfeasible : ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ other, other ≠ owner →
      (1 - p) * quittingSoloReward reward other other +
        p * quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other
  · exact Or.inl hfeasible
  · right
    intro p hp0 hp1
    push Not at hfeasible
    obtain ⟨other, hne, hgt⟩ := hfeasible p hp0 hp1
    exact ⟨other, hne, hgt⟩

omit [Fintype ι] in
/-- Extracting the vanishing-rate witness: some opponent weakly prefers its
own solo exit to the owner's solo absorption payoff.  The proof is a finite
minimum-gap argument, not a limit: if every opponent strictly preferred the
owner's absorption payoff, a sufficiently small rate would satisfy every
inactive inequality strictly and contradict the obstruction there. -/
theorem exists_weak_preemptor_of_universalJoining
    [Finite ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other ≤
        quittingSoloReward reward other other := by
  letI := Fintype.ofFinite ι
  by_contra hnot
  push Not at hnot
  obtain ⟨witness, hwitnessNe, _⟩ := hobstruction 1 one_pos le_rfl
  have hwitnessMem : witness ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hwitnessNe, Finset.mem_univ witness⟩
  have hopponents : (Finset.univ.erase owner).Nonempty := ⟨witness, hwitnessMem⟩
  obtain ⟨gapArg, hgapMem, hgapMin⟩ := Finset.exists_min_image
    (Finset.univ.erase owner)
    (fun other ↦ quittingSoloReward reward owner other -
      quittingSoloReward reward other other) hopponents
  obtain ⟨spreadArg, _, hspreadMax⟩ := Finset.exists_max_image
    (Finset.univ.erase owner)
    (fun other ↦ |quittingSingletonCollisionReward reward owner other -
      quittingSoloReward reward other other|) hopponents
  set δ := quittingSoloReward reward owner gapArg -
    quittingSoloReward reward gapArg gapArg with hδdef
  set spread := |quittingSingletonCollisionReward reward owner spreadArg -
    quittingSoloReward reward spreadArg spreadArg| with hspreaddef
  have hδ : 0 < δ := by
    have := hnot gapArg (Finset.mem_erase.mp hgapMem).1
    rw [hδdef]
    linarith
  have hspread0 : 0 ≤ spread := abs_nonneg _
  set p := δ / (spread + δ) with hpdef
  have hdenominator : 0 < spread + δ := by linarith
  have hp0 : 0 < p := div_pos hδ hdenominator
  have hp1 : p ≤ 1 := (div_le_one hdenominator).mpr (by linarith)
  obtain ⟨other, hotherNe, hgt⟩ := hobstruction p hp0 hp1
  have hotherMem : other ∈ Finset.univ.erase owner :=
    Finset.mem_erase.mpr ⟨hotherNe, Finset.mem_univ other⟩
  have hspreadBound :
      quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward other other ≤ spread :=
    le_trans (le_abs_self _) (hspreadMax other hotherMem)
  have hgapBound : δ ≤ quittingSoloReward reward owner other -
      quittingSoloReward reward other other :=
    hgapMin other hotherMem
  have hsmall : p * spread < δ := by
    rw [hpdef, div_mul_eq_mul_div, div_lt_iff₀ hdenominator]
    nlinarith
  have hmix : (1 - p) * quittingSoloReward reward other other +
      p * quittingSingletonCollisionReward reward owner other =
      quittingSoloReward reward other other +
        p * (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward other other) := by
    ring
  nlinarith [mul_le_mul_of_nonneg_left hspreadBound (le_of_lt hp0)]

omit [Fintype ι] in
/-- Specializing the obstruction to `p = 1`: some opponent strictly gains by
joining the owner's sure quit. -/
theorem exists_sure_joiner_of_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other <
        quittingSingletonCollisionReward reward owner other := by
  obtain ⟨other, hne, hlt⟩ := hobstruction 1 one_pos le_rfl
  refine ⟨other, hne, ?_⟩
  simpa using hlt

/-! ## The positive-debt refinement -/

/-- **Positive-debt owner-solo refinement.**  A positive exact dynamic debt
either produces the owner-solo uniform-equilibrium payoff — the value of the
very deviation the debt measured — or every solo rate of the debt owner has
a strict joiner/preemptor.  The second branch is the refined exceptional
object left for the relative-boundary producer. -/
theorem uniformPayoff_or_universalJoining_of_positiveDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (owner : ι) (start : ℕ) (hstart : start ≤ cutoff)
    (hdebt : 0 < quittingFiniteNashBellmanPathDynamicDebt
      reward cutoff path owner start) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner) ∨
      ∀ p : ℝ, 0 < p → p ≤ 1 →
        QuittingSoloJoiningObstruction reward owner p := by
  have hsolo : 0 < quittingSoloReward reward owner owner := by
    have hsingleton := positiveSingletonReward_of_finiteDynamicDebt_pos_at
      reward cutoff path hpath owner start hstart hdebt
    simpa [quittingSoloReward, quittingSingletonTerminal] using hsingleton
  rcases soloCertification_or_universalJoining reward owner with
    ⟨p, hp0, hp1, hinactive⟩ | hobstruction
  · left
    refine isUniformEquilibriumPayoff_soloReward_of_inactive
      reward owner (quittingHazardCoin p (le_of_lt hp0) hp1) ?_
        (le_of_lt hsolo) ?_
    · rw [quittingHazardCoin_true_toReal p (le_of_lt hp0) hp1]
      exact hp0
    · intro other hne
      rw [quittingHazardCoin_true_toReal p (le_of_lt hp0) hp1,
        quittingHazardCoin_false_toReal p (le_of_lt hp0) hp1]
      exact hinactive other hne
  · exact Or.inr hobstruction

/-! ## Ownerwise assembly and the stagewise transfer kernel -/

/-- Ownerwise assembly (SR2).  With finitely many players, either some
player's solo payoff vector is a uniform-equilibrium payoff, or every
player carrying positive exact dynamic debt at any live date of any
admissible zero-boundary chain has the universal joining obstruction at
every rate. -/
theorem exists_soloUniformPayoff_or_forall_positiveDebt_owners_obstructed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ owner, (quittingGame reward).IsUniformEquilibriumPayoff none
      (quittingSoloReward reward owner)) ∨
    ∀ (owner : ι) (cutoff : ℕ)
      (path : QuittingFiniteNashBellmanPath ι cutoff),
      path ∈ quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff →
      ∀ start, start ≤ cutoff →
        0 < quittingFiniteNashBellmanPathDynamicDebt reward cutoff path
          owner start →
        ∀ p : ℝ, 0 < p → p ≤ 1 →
          QuittingSoloJoiningObstruction reward owner p := by
  by_cases hexists : ∃ owner,
      (quittingGame reward).IsUniformEquilibriumPayoff none
        (quittingSoloReward reward owner)
  · exact Or.inl hexists
  · right
    intro owner cutoff path hpath start hstart hdebt
    rcases uniformPayoff_or_universalJoining_of_positiveDebt reward cutoff
      path hpath owner start hstart hdebt with hpayoff | hobstruction
    · exact absurd ⟨owner, hpayoff⟩ hexists
    · exact hobstruction

omit [Fintype ι] in
/-- Stagewise transfer kernel (SR3a).  Under the universal constant-rate
joining obstruction, every hazard sequence has, at each stage with positive
hazard, a strict stagewise joiner.  The obstruction is therefore not
specific to constant rates. -/
theorem stagewise_obstruction_of_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι)
    (hobstruction : ∀ p : ℝ, 0 < p → p ≤ 1 →
      QuittingSoloJoiningObstruction reward owner p)
    (hazardSeq : ℕ → ℝ) (hrange : ∀ t, 0 ≤ hazardSeq t ∧ hazardSeq t ≤ 1)
    (time : ℕ) (hlive : 0 < hazardSeq time) :
    ∃ other, other ≠ owner ∧
      quittingSoloReward reward owner other <
        (1 - hazardSeq time) * quittingSoloReward reward other other +
          hazardSeq time *
            quittingSingletonCollisionReward reward owner other :=
  hobstruction (hazardSeq time) hlive (hrange time).2


end OwnerSoloCertificationResearch
end GameTheory
