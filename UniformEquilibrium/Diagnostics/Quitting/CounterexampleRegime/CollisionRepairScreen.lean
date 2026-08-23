/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.TerminalExploitabilityToggles
import UniformEquilibrium.Quitting.Boundary.Repair.CollisionCertificateRepair

/-!
# Collision-repair screens in a terminal exploitability witness

A collision-repair mechanism produces terminal approximate equilibria at
every positive tolerance.  A terminal exploitability witness excludes every terminal
approximate equilibrium below its fixed exploitability gap.  Therefore no
collision-repair mechanism works in a terminal exploitability witness, at any legal
rate and for any ordered pair of players.

For distinct players, the exact repair characterization turns this exclusion
into a three-condition screen: owner endpoint optimality, spectator no-join,
and blocker-floor balance cannot all hold simultaneously.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- No collision-repair mechanism works under a terminal exploitability witness. -/
theorem not_quittingCollisionRepairWorks
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner blocker : ι) (rate : ℝ) (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionRepairWorks reward owner blocker rate hrate0 hrate1 := by
  intro hworks
  have hhalf : 0 < witness.terminalGap / 2 := half_pos witness.terminalGap_pos
  obtain ⟨profile, _hshape, hnash⟩ :=
    hworks (witness.terminalGap / 2) hhalf
  exact witness.not_isεAsymptoticNash_of_lt_terminalGap profile
    (by linarith [witness.terminalGap_pos]) hnash

/-- For a distinct owner and blocker, at least one exact repair condition
fails at every legal rate. -/
theorem collisionRepair_condition_failure
    (witness : QuittingTerminalExploitabilityWitness reward)
    {owner blocker : ι} (hne : owner ≠ blocker)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionOwnerOptimal reward owner blocker rate ∨
      ¬ QuittingCollisionSpectatorNoJoin reward owner blocker rate ∨
        ¬ QuittingCollisionBlockerBalance reward owner blocker rate := by
  have hnot := witness.not_quittingCollisionRepairWorks
    owner blocker rate hrate0 hrate1
  rw [quittingCollisionRepairWorks_iff reward hne hrate0 hrate1] at hnot
  tauto

/-- If the collider's punishment value lies below its solo payoff, blocker
balance is automatic and every legal repair rate fails through owner endpoint
optimality or through a spectator's profitable join. -/
theorem collisionRepair_owner_or_spectator_failure_of_punishmentValue_le_solo
    (witness : QuittingTerminalExploitabilityWitness reward)
    (certificate : QuittingImmediateSingletonCollision reward
      witness.terminalGap)
    (hpunishment : quittingPunishmentValue reward certificate.collider ≤
      quittingSoloReward reward certificate.collider certificate.collider)
    {rate : ℝ} (hrate0 : 0 ≤ rate) (hrate1 : rate ≤ 1) :
    ¬ QuittingCollisionOwnerOptimal reward certificate.owner
        certificate.collider rate ∨
      ¬ QuittingCollisionSpectatorNoJoin reward certificate.owner
        certificate.collider rate := by
  have hfailure := witness.collisionRepair_condition_failure
    (Ne.symm certificate.collider_ne_owner) hrate0 hrate1
  have hbalance := certificate.blockerBalance_of_punishmentValue_le_solo
    witness.terminalGap_pos.le hpunishment hrate0 hrate1
  tauto

end QuittingTerminalExploitabilityWitness

end GameTheory
