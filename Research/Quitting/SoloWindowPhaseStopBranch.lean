/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.SoloTailStoppingVerification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration

/-!
# The phase-stop branch on a solo seam tail

`Research/Quitting/DiffuseTailSoloStructure.lean` reduces the stabilized
obstruction of a seam's canonical periodic windows to a phase stop, given two
hypotheses about the windows: that every root is solo at a fixed `owner`, and
that the windows deliver `owner` at least `-terminalGap / 2`.  This module
supplies both from the tail.

* **Window rotation** (`canonicalPeriodicTailWindowFamily_roots_eq`): the root
  of window `window` at date `time` is the tail root at date
  `window + time % (window + 1)`, so tail-level soloness transfers verbatim
  (`isQuittingSoloRoot_canonicalPeriodicTailWindowFamily`).
* **Terminal concentration on a solo sequence**
  (`quittingAbsorbedMassLimit_eq_zero_of_soloRoots`): no coalition other than
  the owner's singleton ever absorbs, so the terminal payoff is the owner's
  singleton mass times its singleton row
  (`quittingRootSequenceTerminalValue_eq_of_soloRoots`).  Nonnegativity of
  that row therefore floors the delivery
  (`quittingRootSequenceTerminalValue_nonneg_of_soloRoots`), with no
  absorption hypothesis: the never-absorbed boundary contributes nothing.
* **Assembly** (`exists_phaseStopObstruction_of_tailSolo`): a seam whose tail
  roots are solo at an `owner` with nonnegative singleton reward has a
  coordinate whose phase stops obstruct infinitely many canonical windows.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Terminal concentration on a solo root sequence -/

/-- **Only the owner's singleton absorbs.**  Along a root sequence at which
`owner` is the only possible quitter, every other terminal coalition carries
zero absorbed mass: each stage atom of the time disintegration vanishes. -/
theorem quittingAbsorbedMassLimit_eq_zero_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner)
    {terminal : {S : Finset ι // S.Nonempty}}
    (hterminal : terminal ≠ quittingSingletonTerminal owner) :
    quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots 0) terminal = 0 := by
  have hne : terminal.val ≠ {owner} := fun hval => hterminal (Subtype.ext hval)
  have hzero : ∀ time, quittingStageCoalitionMass reward
      (quittingRootSequenceProfile reward roots 0) time terminal = 0 := by
    intro time
    rw [quittingStageCoalitionMass_eq_liveMass_mul_rootCoalitionMass,
      quittingProfileLiveRoot_quittingRootSequenceProfile_zero]
    have hmass : quittingRootCoalitionMass (roots time) terminal.val = 0 := by
      conv_lhs => rw [(hsolo time).eq_soloStationaryRoot]
      rw [quittingRootCoalitionMass_solo_of_nonempty owner (roots time owner)
        terminal.val terminal.2, if_neg hne]
    rw [hmass, mul_zero]
  rw [← tsum_quittingStageCoalitionMass reward
    (quittingRootSequenceProfile reward roots 0) terminal]
  simp [hzero]

/-- **Closed form of the terminal value on a solo root sequence.**  The
terminal payoff is the owner's singleton absorbed mass times the owner's
singleton row. -/
theorem quittingRootSequenceTerminalValue_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner) (who : ι) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingAbsorbedMassLimit reward
          (quittingRootSequenceProfile reward roots 0)
          (quittingSingletonTerminal owner) *
        quittingSoloReward reward owner who := by
  rw [quittingRootSequenceTerminalValue, quittingTerminalPayoff]
  refine Finset.sum_eq_single (quittingSingletonTerminal owner) ?_ ?_
  · intro terminal _ hterminal
    rw [quittingAbsorbedMassLimit_eq_zero_of_soloRoots reward roots owner hsolo
      hterminal, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **The delivery of a solo root sequence inherits the owner's sign.**  No
absorption hypothesis is needed: the never-absorbed boundary contributes
nothing to a terminal payoff. -/
theorem quittingRootSequenceTerminalValue_nonneg_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner) {who : ι}
    (hnonneg : 0 ≤ quittingSoloReward reward owner who) :
    0 ≤ quittingRootSequenceTerminalValue reward roots who 0 := by
  rw [quittingRootSequenceTerminalValue_eq_of_soloRoots reward roots owner hsolo
    who]
  exact mul_nonneg (quittingAbsorbedMassLimit_nonneg reward _ _) hnonneg

/-! ## Fixed-opponent coefficients of a spectator on a solo root sequence -/

/-- At a solo root the survival mass seen by a spectator is the owner's
continue probability. -/
theorem quittingFixedOpponentsContinueMass_eq_of_soloRoot
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) owner) (hne : other ≠ owner) :
    quittingFixedOpponentsContinueMass roots other time =
      (roots time owner false).toReal := by
  have hupdate : Function.update (roots time) other (PMF.pure false) =
      roots time := by
    rw [← hsolo other hne]
    exact Function.update_eq_self other (roots time)
  rw [quittingFixedOpponentsContinueMass, hupdate]
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingStationaryContinueMass_solo owner (roots time owner)

/-- At a solo root a spectator's continue reward is the owner's hazard times
the owner's singleton row. -/
theorem quittingFixedOpponentsContinueReward_eq_of_soloRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) owner) (hne : other ≠ owner) :
    quittingFixedOpponentsContinueReward reward roots other time =
      (roots time owner true).toReal * quittingSoloReward reward owner other := by
  have hupdate : Function.update (roots time) other (PMF.pure false) =
      roots time := by
    rw [← hsolo other hne]
    exact Function.update_eq_self other (roots time)
  rw [quittingFixedOpponentsContinueReward, hupdate]
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootAbsorbingContribution_solo reward owner other
    (roots time owner)

/-- At a solo root a spectator's quit-now value mixes exiting alone with
colliding with the owner. -/
theorem quittingFixedOpponentsQuitValue_eq_of_soloRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} {time : ℕ}
    (hsolo : IsQuittingSoloRoot (roots time) owner) (hne : other ≠ owner) :
    quittingFixedOpponentsQuitValue reward roots other time =
      (roots time owner false).toReal * quittingSoloReward reward other other +
        (roots time owner true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  have hstationary : quittingFixedOpponentsQuitValue reward roots other time =
      quittingStationaryFixedOpponentsQuitValue reward (roots time) other := rfl
  rw [hstationary]
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix reward hne
    (roots time owner)

/-! ## Closed form of a spectator's stopping values -/

/-- **Ledger telescope on a solo sequence.**  Everything a spectator collects
before stopping is the owner's singleton row weighted by the mass already
absorbed. -/
theorem quittingLiveLedgerAccum_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} (hne : other ≠ owner)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner) (fuel : ℕ) :
    quittingLiveLedgerAccum reward roots other 0 fuel =
      (1 - quittingOpponentSurvivalWeight roots other 0 fuel) *
        quittingSoloReward reward owner other := by
  induction fuel with
  | zero => simp [quittingLiveLedgerAccum, quittingOpponentSurvivalWeight]
  | succ fuel ih =>
      have hmass := quittingFixedOpponentsContinueMass_eq_of_soloRoot roots
        (hsolo (0 + fuel)) hne
      have hreward := quittingFixedOpponentsContinueReward_eq_of_soloRoot reward
        roots (hsolo (0 + fuel)) hne
      have hsum := quittingRoot_continueProbability_add_quitProbability
        (roots (0 + fuel)) owner
      rw [quittingLiveLedgerAccum, Finset.sum_range_succ,
        ← quittingLiveLedgerAccum, ih, quittingOpponentSurvivalWeight_succ,
        hmass, hreward]
      linear_combination (quittingSoloReward reward owner other *
        quittingOpponentSurvivalWeight roots other 0 fuel) * hsum

/-- **A spectator's deterministic stop, in closed form.**  Before the stop the
spectator receives the owner's singleton row on the absorbed mass; at the stop
it exits alone or collides with the owner. -/
theorem quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} (hne : other ≠ owner)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner) (phase : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots other
        (some phase) 0 =
      (1 - quittingOpponentSurvivalWeight roots other 0 phase) *
          quittingSoloReward reward owner other +
        quittingOpponentSurvivalWeight roots other 0 phase *
          ((roots phase owner false).toReal *
              quittingSoloReward reward other other +
            (roots phase owner true).toReal *
              quittingSingletonCollisionReward reward owner other) := by
  have hsome := quittingRootSequencePureTimeTerminalValue_some_add reward roots
    other 0 phase
  rw [Nat.zero_add] at hsome
  rw [hsome, quittingLiveLedgerAccum_eq_of_soloRoots reward roots hne hsolo
    phase, quittingFixedOpponentsQuitValue_eq_of_soloRoot reward roots
    (hsolo phase) hne]

/-- **The delivery of a solo sequence that absorbs almost surely.**  With no
surviving mass the whole delivery is the owner's singleton row. -/
theorem quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0) (who : ι) :
    quittingRootSequenceTerminalValue reward roots who 0 =
      quittingSoloReward reward owner who := by
  have hconservation := quittingLiveMassLimit_add_sum_absorbedMassLimit reward
    (quittingRootSequenceProfile reward roots 0)
  have hconcentrate : ∑ terminal, quittingAbsorbedMassLimit reward
      (quittingRootSequenceProfile reward roots 0) terminal =
      quittingAbsorbedMassLimit reward
        (quittingRootSequenceProfile reward roots 0)
        (quittingSingletonTerminal owner) := by
    refine Finset.sum_eq_single (quittingSingletonTerminal owner) ?_ ?_
    · intro terminal _ hterminal
      exact quittingAbsorbedMassLimit_eq_zero_of_soloRoots reward roots owner
        hsolo hterminal
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [hconcentrate, habsorb, zero_add] at hconservation
  rw [quittingRootSequenceTerminalValue_eq_of_soloRoots reward roots owner hsolo
    who, hconservation, one_mul]

/-! ## The owner cannot obstruct its own solo sequence -/

/-- **The owner's deterministic stop pays its singleton row.**  On a solo
sequence nobody else can absorb, so whenever the owner stops it exits alone. -/
theorem quittingRootSequencePureTimeTerminalValue_some_owner_eq_of_soloRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner) (phase : ℕ) :
    quittingRootSequencePureTimeTerminalValue reward roots owner
        (some phase) 0 = quittingSoloReward reward owner owner := by
  have hmass : ∀ time,
      quittingFixedOpponentsContinueMass roots owner time = 1 := fun time =>
    quittingFixedOpponentsContinueMass_eq_one_of_soloRoot roots (hsolo time)
  have hreward : ∀ time,
      quittingFixedOpponentsContinueReward reward roots owner time = 0 :=
    fun time =>
      quittingFixedOpponentsContinueReward_eq_zero_of_soloRoot reward roots
        (hsolo time)
  have hsurvival : quittingOpponentSurvivalWeight roots owner 0 phase = 1 :=
    Finset.prod_eq_one fun offset _ => hmass (0 + offset)
  have hledger : quittingLiveLedgerAccum reward roots owner 0 phase = 0 :=
    Finset.sum_eq_zero fun offset _ => by rw [hreward (0 + offset), mul_zero]
  have hquit : quittingFixedOpponentsQuitValue reward roots owner phase =
      quittingSoloReward reward owner owner := by
    have hstationary : quittingFixedOpponentsQuitValue reward roots owner phase =
        quittingStationaryFixedOpponentsQuitValue reward (roots phase) owner :=
      rfl
    rw [hstationary]
    conv_lhs => rw [(hsolo phase).eq_soloStationaryRoot]
    exact quittingStationaryFixedOpponentsQuitValue_solo_owner reward owner
      (roots phase owner)
  have hsome := quittingRootSequencePureTimeTerminalValue_some_add reward roots
    owner 0 phase
  rw [Nat.zero_add] at hsome
  rw [hsome, hledger, hsurvival, hquit, zero_add, one_mul]

/-! ## A spectator's profitable stop is a preemption edge -/

/-- **A phase stop that beats an absorbing solo delivery exposes a preemption
edge.**  On a solo root sequence that absorbs almost surely, a coordinate whose
deterministic stop beats the delivery by `margin` is strictly preempted by the
owner at half that margin, once the owner's hazard at the stopping date is
small enough that the collision term cannot carry the gap.

The two ways to beat the delivery are exiting alone and colliding with the
owner; the collision is weighted by the owner's hazard, so a small hazard
leaves only the solo exit, which is exactly a preemption edge. -/
theorem quittingSoloPreempts_of_phaseStop_gap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) {owner other : ι} (hne : other ≠ owner)
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) owner)
    (habsorb : quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward roots 0) = 0)
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    {margin : ℝ} (hmargin : 0 < margin) {phase : ℕ}
    (hsmall : (roots phase owner true).toReal * (2 * bound) ≤ margin / 2)
    (hgap : margin <
      quittingRootSequencePureTimeTerminalValue reward roots other
          (some phase) 0 -
        quittingRootSequenceTerminalValue reward roots other 0) :
    QuittingSoloPreempts reward (margin / 2) owner other := by
  have hstop := quittingRootSequencePureTimeTerminalValue_some_eq_of_soloRoots
    reward roots hne hsolo phase
  have hdelivery := quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing
    reward roots owner hsolo habsorb other
  rw [hstop, hdelivery] at hgap
  set survival := quittingOpponentSurvivalWeight roots other 0 phase
    with hsurvivalDef
  set continueMass := (roots phase owner false).toReal with hcontinueDef
  set hazard := (roots phase owner true).toReal with hhazardDef
  set ownerRow := quittingSoloReward reward owner other with hownerDef
  set soloRow := quittingSoloReward reward other other with hsoloDef
  set collisionRow := quittingSingletonCollisionReward reward owner other
    with hcollisionDef
  have hmasses : continueMass + hazard = 1 :=
    quittingRoot_continueProbability_add_quitProbability (roots phase) owner
  have hsurvival0 : 0 ≤ survival :=
    quittingOpponentSurvivalWeight_nonneg roots other 0 phase
  have hsurvival1 : survival ≤ 1 :=
    quittingOpponentSurvivalWeight_le_one roots other 0 phase
  have hcontinue0 : 0 ≤ continueMass := ENNReal.toReal_nonneg
  have hhazard0 : 0 ≤ hazard := ENNReal.toReal_nonneg
  have hidentity : (1 - survival) * ownerRow +
        survival * (continueMass * soloRow + hazard * collisionRow) -
          ownerRow =
      survival * continueMass * (soloRow - ownerRow) +
        survival * hazard * (collisionRow - ownerRow) := by
    linear_combination (survival * ownerRow) * hmasses
  rw [hidentity] at hgap
  have hcollisionRowBound : |collisionRow| ≤ bound := hreward _ other
  have hownerRowBound : |ownerRow| ≤ bound := hreward _ other
  have hcollisionAbs : -(2 * bound) ≤ collisionRow - ownerRow ∧
      collisionRow - ownerRow ≤ 2 * bound := by
    have hleft := abs_le.1 hcollisionRowBound
    have hright := abs_le.1 hownerRowBound
    constructor <;> linarith [hleft.1, hleft.2, hright.1, hright.2]
  have hproduct0 : 0 ≤ survival * continueMass :=
    mul_nonneg hsurvival0 hcontinue0
  have hproduct1 : survival * continueMass ≤ 1 := by nlinarith
  have hhazardProduct : survival * hazard ≤ hazard := by nlinarith
  have hhazardProduct0 : 0 ≤ survival * hazard := mul_nonneg hsurvival0 hhazard0
  have hsecond : survival * hazard * (collisionRow - ownerRow) ≤
      margin / 2 := by nlinarith [hcollisionAbs.1, hcollisionAbs.2]
  refine ⟨hne, ?_⟩
  by_contra hcontra
  push Not at hcontra
  have hfirst : survival * continueMass * (soloRow - ownerRow) < margin / 2 := by
    rcases le_or_gt (soloRow - ownerRow) 0 with hsign | hsign
    · nlinarith
    · nlinarith
  linarith

/-! ## A periodic sequence with one absorbing date absorbs almost surely -/

omit [Fintype ι] [DecidableEq ι] in
/-- A periodic root sequence repeats after any multiple of its period. -/
private theorem roots_add_mul_period
    {roots : ℕ → ι → PMF Bool} {period : ℕ}
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (multiple time : ℕ) : roots (multiple * period + time) = roots time := by
  induction multiple with
  | zero => simp
  | succ multiple ih =>
      rw [show (multiple + 1) * period + time = (multiple * period + time) +
        period from by ring, hperiodic, ih]

omit [DecidableEq ι] in
/-- Over a periodic sequence the survival weight of `multiple` whole periods
is the one-period weight raised to that power. -/
private theorem quittingJointSurvivalWeight_mul_period
    {roots : ℕ → ι → PMF Bool} {period : ℕ}
    (hperiodic : ∀ time, roots (time + period) = roots time) (multiple : ℕ) :
    quittingJointSurvivalWeight roots 0 (multiple * period) =
      quittingJointSurvivalWeight roots 0 period ^ multiple := by
  induction multiple with
  | zero => simp [quittingJointSurvivalWeight_eq_prod]
  | succ multiple ih =>
      have hshift : quittingJointSurvivalWeight roots (0 + multiple * period)
          period = quittingJointSurvivalWeight roots 0 period := by
        rw [quittingJointSurvivalWeight_eq_prod,
          quittingJointSurvivalWeight_eq_prod]
        refine Finset.prod_congr rfl fun offset _ => ?_
        rw [show 0 + multiple * period + offset =
          multiple * period + (0 + offset) from by ring,
          roots_add_mul_period hperiodic]
      rw [show (multiple + 1) * period = multiple * period + period from by ring,
        quittingJointSurvivalWeight_add, ih, hshift, pow_succ]

omit [DecidableEq ι] in
/-- **A periodic sequence with one absorbing date absorbs almost surely.**  The
survival weight of a single period is below one, so its powers vanish and the
joint survival limit is zero. -/
theorem quittingJointSurvivalLimit_eq_zero_of_periodic
    (roots : ℕ → ι → PMF Bool) {period date : ℕ}
    (hperiodic : ∀ time, roots (time + period) = roots time)
    (hdate : date < period)
    (habsorbing : quittingStationaryContinueMass (roots date) < 1) :
    quittingJointSurvivalLimit roots 0 = 0 := by
  have hmem : date ∈ Finset.range period := Finset.mem_range.2 hdate
  have hfactor0 : ∀ offset,
      0 ≤ quittingStationaryContinueMass (roots (0 + offset)) := fun offset =>
    quittingStationaryContinueMass_nonneg (roots (0 + offset))
  have hperiodWeight0 : 0 ≤ quittingJointSurvivalWeight roots 0 period :=
    quittingJointSurvivalWeight_nonneg roots 0 period
  have hperiodWeight1 : quittingJointSurvivalWeight roots 0 period < 1 := by
    rw [quittingJointSurvivalWeight_eq_prod]
    have hsplit := Finset.mul_prod_erase (Finset.range period)
      (fun offset => quittingStationaryContinueMass (roots (0 + offset))) hmem
    have hrest : (∏ offset ∈ (Finset.range period).erase date,
        quittingStationaryContinueMass (roots (0 + offset))) ≤ 1 :=
      Finset.prod_le_one (fun offset _ => hfactor0 offset)
        (fun offset _ => quittingStationaryContinueMass_le_one (roots (0 + offset)))
    have hrest0 : 0 ≤ (∏ offset ∈ (Finset.range period).erase date,
        quittingStationaryContinueMass (roots (0 + offset))) :=
      Finset.prod_nonneg fun offset _ => hfactor0 offset
    have hhead : quittingStationaryContinueMass (roots (0 + date)) < 1 := by
      rwa [Nat.zero_add]
    have hhead0 : 0 ≤ quittingStationaryContinueMass (roots (0 + date)) :=
      hfactor0 date
    nlinarith [hsplit, hrest, hrest0, hhead, hhead0]
  have hpow : Tendsto
      (fun multiple => quittingJointSurvivalWeight roots 0 period ^ multiple)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hperiodWeight0 hperiodWeight1
  have hbdd : BddBelow (Set.range fun fuel =>
      quittingJointSurvivalWeight roots 0 fuel) := by
    refine ⟨0, ?_⟩
    rintro value ⟨fuel, rfl⟩
    exact quittingJointSurvivalWeight_nonneg roots 0 fuel
  have hle : ∀ multiple, quittingJointSurvivalLimit roots 0 ≤
      quittingJointSurvivalWeight roots 0 period ^ multiple := by
    intro multiple
    rw [← quittingJointSurvivalWeight_mul_period hperiodic multiple]
    exact ciInf_le hbdd (multiple * period)
  refine le_antisymm ?_ (quittingJointSurvivalLimit_nonneg roots 0)
  exact ge_of_tendsto' hpow hle

namespace QuittingCounterexampleSeamWitness

variable {regime : QuittingCounterexampleRegime reward}

/-! ## Rotating the tail into the canonical windows -/

/-- The canonical window `window` reads the tail at date
`window + time % (window + 1)`: it restarts the block of `window + 1` tail
dates beginning at `window`. -/
theorem canonicalPeriodicTailWindowFamily_roots_eq
    (seam : QuittingCounterexampleSeamWitness regime) (window time : ℕ) :
    seam.canonicalPeriodicTailWindowFamily.roots window time =
      quittingDynamicDebtTailRoots seam.tail
        (window + time % (window + 1)) := by
  show quittingDynamicDebtTailRoots seam.tail
      (window + (quittingCyclicOrbit
        (quittingPeriodicWindowInitialPhase window) time).1) = _
  congr 2
  simp [quittingCyclicOrbit, quittingPeriodicWindowInitialPhase]

/-- Tail-level soloness transfers to every canonical periodic window. -/
theorem isQuittingSoloRoot_canonicalPeriodicTailWindowFamily
    (seam : QuittingCounterexampleSeamWitness regime) {owner : ι}
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    (window time : ℕ) :
    IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner := by
  rw [seam.canonicalPeriodicTailWindowFamily_roots_eq window time]
  exact hsolo _

/-! ## The phase-stop branch from tail-level hypotheses -/

/-- **T4(a), phase-stop branch from the tail.**  On a seam whose tail roots
are solo at `owner`, with `owner`'s singleton reward nonnegative, the
stabilized obstruction of `exists_infinite_fixedPlayer_fixedBranch` is a phase
stop: every other coordinate's refusal reproduces the window's delivery, and
`owner`'s own refusal stops all absorption and pays zero, while the delivery
to `owner` is nonnegative. -/
theorem exists_phaseStopObstruction_of_tailSolo
    (seam : QuittingCounterexampleSeamWitness regime) (owner : ι)
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    (hnonneg : 0 ≤ quittingSoloReward reward owner owner) :
    ∃ other, Set.Infinite {window : ℕ |
      ∃ phase : Fin (window + 1),
        regime.terminalGap / 2 <
          quittingPeriodicWindowPhaseStopValue reward
            (seam.canonicalPeriodicTailWindowFamily.roots window) other phase -
            seam.canonicalPeriodicTailWindowFamily.delivery window other} := by
  have hwindowSolo : ∀ window time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner :=
    seam.isQuittingSoloRoot_canonicalPeriodicTailWindowFamily hsolo
  refine seam.exists_phaseStopObstruction_of_soloWindows owner hwindowSolo
    fun window => ?_
  have hdelivery : seam.canonicalPeriodicTailWindowFamily.delivery window owner =
      quittingRootSequenceTerminalValue reward
        (seam.canonicalPeriodicTailWindowFamily.roots window) owner 0 := rfl
  have hzero : 0 ≤ seam.canonicalPeriodicTailWindowFamily.delivery window owner := by
    rw [hdelivery]
    exact quittingRootSequenceTerminalValue_nonneg_of_soloRoots reward
      (seam.canonicalPeriodicTailWindowFamily.roots window) owner
      (hwindowSolo window) hnonneg
  linarith [regime.terminalGap_pos]

/-- **T4(a), proved.**  On a seam whose tail roots are solo at an `owner` with
nonnegative singleton reward, and whose canonical windows absorb almost
surely, the stabilized obstruction is a phase stop whose obstructing
coordinate is strictly preempted by `owner` at a quarter of the terminal gap.

The obstructing coordinate cannot be `owner` itself: on a solo sequence the
owner's own stop pays exactly its singleton row, which is also the delivery.
At a late window the owner's hazard is small, so the profitable stop of the
obstructing coordinate is its solo exit rather than a collision, and that is a
preemption edge. -/
theorem quittingSoloWindowPhaseStopBranch_of_tailSolo
    (seam : QuittingCounterexampleSeamWitness regime) (owner : ι)
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    (hnonneg : 0 ≤ quittingSoloReward reward owner owner)
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (habsorb : ∀ window, quittingLiveMassLimit reward
      (quittingRootSequenceProfile reward
        (seam.canonicalPeriodicTailWindowFamily.roots window) 0) = 0) :
    QuittingSoloWindowPhaseStopBranch seam owner (regime.terminalGap / 4) := by
  obtain ⟨other, hinfinite⟩ :=
    seam.exists_phaseStopObstruction_of_tailSolo owner hsolo hnonneg
  have hwindowSolo : ∀ window time, IsQuittingSoloRoot
      (seam.canonicalPeriodicTailWindowFamily.roots window time) owner :=
    seam.isQuittingSoloRoot_canonicalPeriodicTailWindowFamily hsolo
  have hgapPos := regime.terminalGap_pos
  have hne : other ≠ owner := by
    intro heq
    subst other
    obtain ⟨window, hwindow⟩ := Set.Infinite.nonempty hinfinite
    obtain ⟨phase, hphase⟩ := hwindow
    rw [quittingPeriodicWindowPhaseStopValue,
      quittingRootSequencePureTimeTerminalValue_some_owner_eq_of_soloRoots reward
        (seam.canonicalPeriodicTailWindowFamily.roots window) owner
        (hwindowSolo window) phase.val] at hphase
    have hdelivery :
        seam.canonicalPeriodicTailWindowFamily.delivery window owner =
          quittingSoloReward reward owner owner :=
      quittingRootSequenceTerminalValue_eq_soloReward_of_absorbing reward
        (seam.canonicalPeriodicTailWindowFamily.roots window) owner
        (hwindowSolo window) (habsorb window) owner
    rw [hdelivery] at hphase
    linarith
  have hvanish : Tendsto (fun time =>
      (quittingDynamicDebtTailRoots seam.tail time owner true).toReal *
        (2 * bound)) atTop (nhds 0) := by
    simpa using (seam.quitProbability_tendsto_zero owner).mul
      (tendsto_const_nhds (x := 2 * bound) (f := atTop (α := ℕ)))
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1
    ((tendsto_order.1 hvanish).2 (regime.terminalGap / 4) (by linarith))
  obtain ⟨window, hwindow, hlarge⟩ :=
    Set.Infinite.exists_gt hinfinite threshold
  obtain ⟨phase, hphase⟩ := hwindow
  refine ⟨other, ?_, hinfinite⟩
  have hsmall : (seam.canonicalPeriodicTailWindowFamily.roots window phase.val
      owner true).toReal * (2 * bound) ≤ regime.terminalGap / 2 / 2 := by
    rw [seam.canonicalPeriodicTailWindowFamily_roots_eq window phase.val]
    have hdate : threshold ≤ window + phase.val % (window + 1) := by omega
    have hlate := hthreshold _ hdate
    linarith
  have hpreempt := quittingSoloPreempts_of_phaseStop_gap reward
    (seam.canonicalPeriodicTailWindowFamily.roots window) hne
    (hwindowSolo window) (habsorb window) hreward
    (by linarith : (0 : ℝ) < regime.terminalGap / 2) hsmall hphase
  have hquarter : regime.terminalGap / 2 / 2 = regime.terminalGap / 4 := by ring
  rwa [hquarter] at hpreempt

/-- The canonical window absorbs almost surely as soon as `owner` is active at
one date of the block it restarts: the window is periodic, so a single
absorbing date drives its survival to zero. -/
theorem quittingLiveMassLimit_canonicalWindow_eq_zero
    (seam : QuittingCounterexampleSeamWitness regime) {owner : ι}
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    {window date : ℕ} (hdate : date < window + 1)
    (hactive : 0 <
      (quittingDynamicDebtTailRoots seam.tail (window + date) owner true).toReal) :
    quittingLiveMassLimit reward (quittingRootSequenceProfile reward
      (seam.canonicalPeriodicTailWindowFamily.roots window) 0) = 0 := by
  rw [quittingLiveMassLimit_rootSequence_eq_jointSurvivalLimit]
  refine quittingJointSurvivalLimit_eq_zero_of_periodic
    (seam.canonicalPeriodicTailWindowFamily.roots window)
    (period := window + 1) (date := date) (fun time => ?_) hdate ?_
  · rw [seam.canonicalPeriodicTailWindowFamily_roots_eq,
      seam.canonicalPeriodicTailWindowFamily_roots_eq, Nat.add_mod_right]
  · have hroot : seam.canonicalPeriodicTailWindowFamily.roots window date =
        quittingDynamicDebtTailRoots seam.tail (window + date) := by
      rw [seam.canonicalPeriodicTailWindowFamily_roots_eq,
        Nat.mod_eq_of_lt hdate]
    have hsum := quittingRoot_continueProbability_add_quitProbability
      (quittingDynamicDebtTailRoots seam.tail (window + date)) owner
    rw [hroot]
    conv_lhs => rw [(hsolo (window + date)).eq_soloStationaryRoot]
    rw [quittingStationaryContinueMass_solo]
    linarith

/-- **T4(a) from tail-level hypotheses only.**  A seam whose tail roots are
solo at an `owner` with nonnegative singleton reward, and whose `owner` is
active at one date of every restarted block, realizes the phase-stop branch at
a quarter of the terminal gap. -/
theorem quittingSoloWindowPhaseStopBranch_of_tailSolo_of_blockActive
    (seam : QuittingCounterexampleSeamWitness regime) (owner : ι)
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    (hnonneg : 0 ≤ quittingSoloReward reward owner owner)
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hactive : ∀ window, ∃ date, date < window + 1 ∧
      0 < (quittingDynamicDebtTailRoots seam.tail (window + date) owner
        true).toReal) :
    QuittingSoloWindowPhaseStopBranch seam owner (regime.terminalGap / 4) := by
  refine seam.quittingSoloWindowPhaseStopBranch_of_tailSolo owner hsolo hnonneg
    hreward fun window => ?_
  obtain ⟨date, hdate, hdateActive⟩ := hactive window
  exact seam.quittingLiveMassLimit_canonicalWindow_eq_zero hsolo hdate
    hdateActive

/-- **T4(a) for a tail whose owner is active at every date.**  This is the
shape a diffuse tail with vanishing but positive hazards presents. -/
theorem quittingSoloWindowPhaseStopBranch_of_tailSolo_of_active
    (seam : QuittingCounterexampleSeamWitness regime) (owner : ι)
    (hsolo : ∀ time,
      IsQuittingSoloRoot (quittingDynamicDebtTailRoots seam.tail time) owner)
    (hnonneg : 0 ≤ quittingSoloReward reward owner owner)
    {bound : ℝ} (hreward : ∀ terminal player, |reward terminal player| ≤ bound)
    (hactive : ∀ time,
      0 < (quittingDynamicDebtTailRoots seam.tail time owner true).toReal) :
    QuittingSoloWindowPhaseStopBranch seam owner (regime.terminalGap / 4) :=
  seam.quittingSoloWindowPhaseStopBranch_of_tailSolo_of_blockActive owner hsolo
    hnonneg hreward fun window => ⟨0, Nat.succ_pos window, hactive _⟩

end QuittingCounterexampleSeamWitness

end GameTheory
