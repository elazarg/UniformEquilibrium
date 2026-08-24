/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import MathUE.PMFProduct.SmallHazardExpectation
import UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.Support
import UniformEquilibrium.Quitting.Classification.AbnormalSingletonConsequences
import UniformEquilibrium.Quitting.Classification.SingletonPacketSupport
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# Quantitative layer for the normal terminal-gap full-support lift

This module records the exact fractional-linear regret identity, the uniform
hazard normalization estimate, and the final normalized singleton-packet
constructor.  The remaining producer is the constrained stationary fixed
point and its compact small-hazard limit.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Repeated-row terminal payoff when the selected player quits with rate
`p`, its opponents survive with probability `beta`, and `A` is the
unnormalized Continue-row absorbing payoff. -/
def constrainedStationaryValue
    (p quitValue continueAbsorbing beta : ℝ) : ℝ :=
  (p * quitValue + (1 - p) * continueAbsorbing) /
    ((1 - beta) + p * beta)

/-- Exact lower-bound regret formula.  The denominator is left explicit so
the theorem can be reused before substituting `delta = 1 - beta`. -/
theorem neverValue_sub_constrainedStationaryValue_eq
    (epsilon quitValue continueAbsorbing delta beta : ℝ)
    (hdelta : delta ≠ 0)
    (hdenominator : delta + epsilon * beta ≠ 0)
    (hpartition : delta + beta = 1) :
    continueAbsorbing / delta -
        (epsilon * quitValue + (1 - epsilon) * continueAbsorbing) /
          (delta + epsilon * beta) =
      epsilon * (continueAbsorbing / delta - quitValue) /
        (delta + epsilon * beta) := by
  field_simp [hdelta, hdenominator]
  linear_combination epsilon * continueAbsorbing * hpartition

/-- Version in the literal `constrainedStationaryValue` coordinates. -/
theorem neverValue_sub_constrainedStationaryValue_eq_one_sub
    (epsilon quitValue continueAbsorbing beta : ℝ)
    (hdelta : 1 - beta ≠ 0)
    (hdenominator : 1 - beta + epsilon * beta ≠ 0) :
    continueAbsorbing / (1 - beta) -
        constrainedStationaryValue epsilon quitValue continueAbsorbing beta =
      epsilon * (continueAbsorbing / (1 - beta) - quitValue) /
        (1 - beta + epsilon * beta) := by
  unfold constrainedStationaryValue
  apply neverValue_sub_constrainedStationaryValue_eq
    epsilon quitValue continueAbsorbing (1 - beta) beta
      hdelta hdenominator
  ring

/-- A terminal gain bounded by a payoff range forces the lower-bound row's
absorption denominator to be of order `epsilon`. -/
theorem denominator_le_two_mul_bound_mul_epsilon_div_gap
    {epsilon gap bound neverValue quitValue denominator : ℝ}
    (hepsilon : 0 < epsilon) (hgap : 0 < gap) (hdenominator : 0 < denominator)
    (hgain : gap ≤ epsilon * (neverValue - quitValue) / denominator)
    (hrange : neverValue - quitValue ≤ 2 * bound) :
    denominator ≤ 2 * bound * epsilon / gap := by
  have hscaled : gap * denominator ≤
      epsilon * (neverValue - quitValue) := by
    exact (le_div_iff₀ hdenominator).mp hgain
  have hupper : epsilon * (neverValue - quitValue) ≤ epsilon * (2 * bound) :=
    mul_le_mul_of_nonneg_left hrange hepsilon.le
  have := hscaled.trans hupper
  exact (le_div_iff₀ hgap).mpr (by nlinarith)

/-- If one selected hazard is `epsilon` and every other hazard is at most
`K epsilon`, the total hazard has the displayed finite-cardinality bound. -/
theorem sum_hazard_le_of_selected_eq_and_opponents_le
    (hazard : ι → ℝ) (selected : ι) (epsilon K : ℝ)
    (hselected : hazard selected = epsilon)
    (hopponents : ∀ who, who ≠ selected → hazard who ≤ K * epsilon) :
    ∑ who, hazard who ≤
      (1 + K * (Fintype.card ι - 1)) * epsilon := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ selected), hselected]
  calc
    ∑ who ∈ Finset.univ.erase selected, hazard who + epsilon ≤
        ∑ _who ∈ Finset.univ.erase selected, K * epsilon + epsilon := by
      gcongr with who hwho
      exact hopponents who (Finset.ne_of_mem_erase hwho)
    _ = (1 + K * (Fintype.card ι - 1)) * epsilon := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem
        (Finset.mem_univ selected), Finset.card_univ]
      have hcard : 1 ≤ Fintype.card ι :=
        Fintype.card_pos_iff.mpr ⟨selected⟩
      rw [Nat.cast_sub hcard]
      push_cast
      ring

omit [DecidableEq ι] in
/-- Normalizing hazards with a common positive lower bound and an upper bound
on their sum gives a coordinatewise full-support floor. -/
theorem normalized_hazard_ge_inv
    (hazard : ι → ℝ) (epsilon totalBound : ℝ)
    (hepsilon : 0 < epsilon) (htotalBound : 0 < totalBound)
    (hlower : ∀ who, epsilon ≤ hazard who)
    (hsum : ∑ who, hazard who ≤ totalBound * epsilon) (who : ι) :
    1 / totalBound ≤ hazard who / ∑ player, hazard player := by
  have hsumPos : 0 < ∑ player, hazard player := by
    have hwho := hlower who
    have hnonneg : ∀ player, 0 ≤ hazard player := fun player =>
      hepsilon.le.trans (hlower player)
    have hle := Finset.single_le_sum (fun player _ => hnonneg player)
      (Finset.mem_univ who)
    exact lt_of_lt_of_le hepsilon (hwho.trans hle)
  apply (div_le_div_iff₀ htotalBound hsumPos).mpr
  have hwho := hlower who
  have hscaled : ∑ player, hazard player ≤ totalBound * hazard who :=
    hsum.trans (mul_le_mul_of_nonneg_left hwho htotalBound.le)
  simpa [one_mul, mul_comm] using hscaled

/-- The last static step of the lift: a full-support probability vector whose
singleton mixture dominates every solo payoff produces the literal normalized
singleton source packet at the solo target. -/
def normalFullSupportSingletonPacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ)
    (hmassNonneg : ∀ owner, 0 ≤ mass owner)
    (hmassSum : ∑ owner, mass owner = 1)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hmixture : ∀ who,
      reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward mass who) :
    QuittingNormalizedSingletonSourcePacket reward where
  mass := mass
  target := fun who => reward (quittingSingletonTerminal who) who
  mass_nonneg := hmassNonneg
  mass_sum := hmassSum
  mix_ge_target := hmixture
  solo_le_target := fun _ => le_rfl
  punishment_le_target := hnormal
  positive_mass_pins_target := fun _ _ => rfl

/-- The constructed packet has literal full support. -/
theorem normalFullSupportSingletonPacket_support_eq_univ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ)
    (hmassNonneg : ∀ owner, 0 ≤ mass owner)
    (hmassSum : ∑ owner, mass owner = 1)
    (hmassPos : ∀ owner, 0 < mass owner)
    (hnormal : ∀ who, quittingPunishmentValue reward who ≤
      reward (quittingSingletonTerminal who) who)
    (hmixture : ∀ who,
      reward (quittingSingletonTerminal who) who ≤
        quittingSingletonMixture reward mass who) :
    (normalFullSupportSingletonPacket reward mass hmassNonneg hmassSum
      hnormal hmixture).support = Finset.univ := by
  ext owner
  simp [QuittingNormalizedSingletonSourcePacket.support,
    normalFullSupportSingletonPacket, hmassPos]

/-- In the crossed support-two chamber on four players, terminal-gap failure
forces every player to be punishment-normal.  The supported owners are normal
by positive packet mass.  If an outsider were abnormal, the abnormal-player
singleton floor would contradict the strict crossed row which identifies that
outsider. -/
theorem QuittingTerminalExploitabilityWitness.all_normal_of_finFour_support_eq_pair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    {first second : Fin 4} (hne : first ≠ second)
    (hsupport : packet.support = {first, second}) :
    ∀ who, IsQuittingNormalPlayer reward who := by
  obtain ⟨left, right, houtside, _hlr, hleftBad, _hleftHelped,
      hrightBad, _hrightHelped⟩ :=
    witness.exists_crossedSpectators_of_finFour_support_eq_pair
      packet hne hsupport
  have hfirstMem : first ∈ packet.support := by
    rw [hsupport]
    simp
  have hsecondMem : second ∈ packet.support := by
    rw [hsupport]
    simp
  intro who
  by_cases hwho : who ∈ packet.support
  · exact packet.isQuittingNormalPlayer_of_mass_pos who
      ((packet.mem_support_iff who).mp hwho)
  have hwhoOutside : who ∈ packet.supportᶜ := Finset.mem_compl.mpr hwho
  rw [houtside] at hwhoOutside
  simp only [Finset.mem_insert, Finset.mem_singleton] at hwhoOutside
  rcases hwhoOutside with hwhoLeft | hwhoRight
  · subst who
    by_contra hnotNormal
    have habnormal : IsQuittingAbnormalPlayer reward left := by
      exact lt_of_not_ge hnotNormal
    have hleftNe : left ≠ first := by
      intro heq
      subst left
      exact hwho hfirstMem
    obtain ⟨hsoloFloor, hownerFloor⟩ :=
      abnormal_singletonFloor_chain reward habnormal hleftNe
    have hleftBad' : quittingSoloReward reward first left <
        quittingSoloReward reward left left := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using hleftBad
    linarith
  · subst who
    by_contra hnotNormal
    have habnormal : IsQuittingAbnormalPlayer reward right := by
      exact lt_of_not_ge hnotNormal
    have hrightNe : right ≠ second := by
      intro heq
      subst right
      exact hwho hsecondMem
    obtain ⟨hsoloFloor, hownerFloor⟩ :=
      abnormal_singletonFloor_chain reward habnormal hrightNe
    have hrightBad' : quittingSoloReward reward second right <
        quittingSoloReward reward right right := by
      simpa [quittingSoloReward, quittingSingletonTerminal] using hrightBad
    linarith

end GameTheory
