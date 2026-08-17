/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Toggles
import UniformEquilibrium.Quitting.Boundary.Repair.CollisionCertificateRepair

/-!
# Collision-repair screens in a counterexample regime

A collision-repair mechanism produces terminal approximate equilibria at
every positive tolerance.  A counterexample regime excludes every terminal
approximate equilibrium below its fixed exploitability gap.  Therefore no
collision-repair mechanism works in a counterexample regime, at any legal
rate and for any ordered pair of players.

For distinct players, the exact repair characterization turns this exclusion
into a three-condition screen: owner endpoint optimality, spectator no-join,
and blocker-floor balance cannot all hold simultaneously.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- No collision-repair mechanism works under a counterexample regime. -/
theorem not_quittingCollisionRepairWorks
    (regime : QuittingCounterexampleRegime reward)
    (owner blocker : ι) (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 := by
  intro hworks
  have hhalf : 0 < regime.terminalGap / 2 := half_pos regime.terminalGap_pos
  obtain ⟨profile, _hshape, hnash⟩ :=
    hworks (regime.terminalGap / 2) hhalf
  exact regime.not_isεAsymptoticNash_of_lt_terminalGap profile
    (by linarith [regime.terminalGap_pos]) hnash

/-- For a distinct owner and blocker, at least one exact repair condition
fails at every legal rate. -/
theorem collisionRepair_condition_failure
    (regime : QuittingCounterexampleRegime reward)
    {owner blocker : ι} (hne : owner ≠ blocker)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionOwnerOptimal reward owner blocker rate ∨
      ¬ QuittingCollisionSpectatorNoJoin reward owner blocker rate ∨
        ¬ QuittingCollisionBlockerBalance reward owner blocker rate := by
  have hnot := regime.not_quittingCollisionRepairWorks
    owner blocker rate hrate0 hrate1
  rw [quittingCollisionRepairWorks_iff reward hne hrate0 hrate1] at hnot
  tauto

/-- If the collider's punishment value lies below its solo payoff, blocker
balance is automatic and every legal repair rate fails through owner endpoint
optimality or through a spectator's profitable join. -/
theorem collisionRepair_owner_or_spectator_failure_of_punishmentValue_le_solo
    (regime : QuittingCounterexampleRegime reward)
    (certificate : QuittingImmediateSingletonCollision reward
      regime.terminalGap)
    (hpunishment : quittingPunishmentValue reward certificate.collider ≤
      quittingSoloReward reward certificate.collider certificate.collider)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionOwnerOptimal reward certificate.owner
        certificate.collider rate ∨
      ¬ QuittingCollisionSpectatorNoJoin reward certificate.owner
        certificate.collider rate := by
  have hfailure := regime.collisionRepair_condition_failure
    (Ne.symm certificate.collider_ne_owner) hrate0 hrate1
  have hbalance := certificate.blockerBalance_of_punishmentValue_le_solo
    regime.terminalGap_pos.le hpunishment hrate0 hrate1
  tauto

end QuittingCounterexampleRegime

end GameTheory
