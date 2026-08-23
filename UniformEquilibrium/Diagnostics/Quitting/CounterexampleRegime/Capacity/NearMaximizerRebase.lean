/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Terminal.TerminalExploitabilityWitness
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefixAdmissiblePath
import UniformEquilibrium.Quitting.Debt.Dynamic.ReachableCarryTelescope

/-!
# Near-maximal admissible capacity and the rebasing seam

The counterexample prefix-charge bound makes the canonical admissible
budget-to-go finite.  Literal exact-prefix sources approach its least global
capacity, so at every positive scale one such source forbids any incoming
admissible path carrying that much absorption charge.

This does not choose a zero-boundary calibrated exact-D anchor at the same
state.  The conclusion is a capacity obstruction, not a chronological splice.
-/

noncomputable section

namespace GameTheory

open Math.ChargedPathBudget
open Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private abbrev AdmissibleRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :=
  quittingPunishmentFloorAdmissibleChargedRelation reward

/-! ## Near-maximal global admissible capacity -/

/-- The charge of a finite exact prefix is already available from the
budget-to-go at its literal source state. -/
theorem finitePrefix_charge_le_admissiblePotential_source
    (witness : QuittingTerminalExploitabilityWitness reward)
    (cert : QuittingPunishmentFloorFinitePrefix reward) :
    cert.charge ≤ quittingPunishmentFloorAdmissiblePotential reward
      (quittingFinitePrefixAdmissibleState cert 0 (by omega)) := by
  rw [← chargeSum_quittingFinitePrefixAdmissiblePath_horizon cert]
  exact (AdmissibleRelation reward).chargeSum_le_value
    (quittingPunishmentFloorAdmissible_hasFiniteBudget_of_finitePrefixChargeBound
      witness.prefixCharge_le)
    (quittingFinitePrefixAdmissiblePath cert cert.horizon (by omega))

/-- Every positive tolerance is beaten by an exact prefix whose charge is
within that tolerance of the least prefix-charge bound. -/
theorem exists_finitePrefix_charge_gt_prefixChargeBound_sub
    (witness : QuittingTerminalExploitabilityWitness reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      quittingPunishmentFloorPrefixChargeBound reward - ε < cert.charge := by
  classical
  by_cases htarget : 0 ≤ quittingPunishmentFloorPrefixChargeBound reward - ε
  · by_contra hno
    have hall : ∀ cert : QuittingPunishmentFloorFinitePrefix reward,
        cert.charge ≤ quittingPunishmentFloorPrefixChargeBound reward - ε := by
      intro cert
      exact le_of_not_gt fun hgt ↦ hno ⟨cert, hgt⟩
    have hleast :=
      (punishmentFloorPrefixChargeCapacity_toReal_le_iff
        witness.prefixChargeCapacity_ne_top htarget).2 hall
    linarith
  · refine ⟨quittingPunishmentFloorForwardFinitePrefix reward 0, ?_⟩
    have hnegative : quittingPunishmentFloorPrefixChargeBound reward - ε < 0 :=
      lt_of_not_ge htarget
    change quittingPunishmentFloorPrefixChargeBound reward - ε < 0
    exact hnegative

/-- Literal prefix sources approach the global least capacity from below.
This is an existence statement about admissible states, not about calibrated
zero-boundary minimizers at those same states. -/
theorem exists_finitePrefix_source_remainingCapacity_lt
    (witness : QuittingTerminalExploitabilityWitness reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      0 ≤ quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) ∧
      quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) < ε := by
  obtain ⟨cert, hcharge⟩ :=
    exists_finitePrefix_charge_gt_prefixChargeBound_sub witness hε
  refine ⟨cert, ?_, ?_⟩
  · unfold quittingPunishmentFloorAdmissibleRemainingCapacity
    exact sub_nonneg.mpr
      (QuittingFiniteDynamicDebtAdmissibleChronology.admissiblePotential_le_prefixChargeBound
        witness.prefixCharge_le _)
  · unfold quittingPunishmentFloorAdmissibleRemainingCapacity
    have hlower := finitePrefix_charge_le_admissiblePotential_source witness cert
    linarith

/-- Any literal incoming path must fit in the remaining capacity of its
target.  This is the quantitative least-capacity obstruction to attaching a
fixed positive-charge terminal funding path at a near-maximal state. -/
theorem admissiblePath_chargeSum_le_target_remainingCapacity
    (witness : QuittingTerminalExploitabilityWitness reward)
    {source target : QuittingPunishmentFloorAdmissibleState reward}
    (path : (AdmissibleRelation reward).Path source target) :
    path.chargeSum ≤
      quittingPunishmentFloorAdmissibleRemainingCapacity reward target := by
  have hdrop :=
    (quittingPunishmentFloorAdmissiblePotential_isBoundedPotential
      witness.prefixCharge_le).isPotential.chargeSum_le path
  have hsource :=
    QuittingFiniteDynamicDebtAdmissibleChronology.admissiblePotential_le_prefixChargeBound
      witness.prefixCharge_le source
  unfold quittingPunishmentFloorAdmissibleRemainingCapacity
  linarith

/-- At every scale there is a literal exact-prefix source which cannot be the
target of any admissible incoming path carrying that scale of charge. -/
theorem exists_finitePrefix_source_forbids_incoming_charge
    (witness : QuittingTerminalExploitabilityWitness reward)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ cert : QuittingPunishmentFloorFinitePrefix reward,
      0 ≤ quittingPunishmentFloorAdmissibleRemainingCapacity reward
          (quittingFinitePrefixAdmissibleState cert 0 (by omega)) ∧
      ∀ (source : QuittingPunishmentFloorAdmissibleState reward)
        (path : (AdmissibleRelation reward).Path source
          (quittingFinitePrefixAdmissibleState cert 0 (by omega))),
        path.chargeSum < ε := by
  obtain ⟨cert, hnonneg, hsmall⟩ :=
    exists_finitePrefix_source_remainingCapacity_lt witness hε
  refine ⟨cert, hnonneg, ?_⟩
  intro source path
  exact lt_of_le_of_lt
    (admissiblePath_chargeSum_le_target_remainingCapacity witness path) hsmall

end GameTheory
