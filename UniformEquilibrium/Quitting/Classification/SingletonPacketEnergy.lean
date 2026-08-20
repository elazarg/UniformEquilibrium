/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SingletonPacketDefect
import UniformEquilibrium.Quitting.Classification.SingletonPacketRefusal

/-!
# Energy and reciprocal effects of a singleton source packet

A normalized singleton source packet has mass `mu`, target `z`, and singleton
delivery `y`.  Subtracting each receiver's own singleton payoff defines the
solo-effect matrix

`M i j = r_i({j}) - r_i({i})`.

Packet pinning and normalization identify the weighted source surplus with
the quadratic form

`sum_i mu_i (y_i - z_i) = sum_i,j mu_i mu_j M_i,j`.

The skew part of `M` vanishes in this quadratic form; only reciprocal pair
sums contribute. Conditional refusal has the same aggregate energy, and the
maximum packet defect is bounded by that energy. This gives a solved class:
if every reciprocal pair sum is nonpositive, the packet is complementary and
the existing singleton-circulation compiler supplies a uniform-equilibrium
payoff.

These are packet-local identities.  They do not identify a source packet with
a chronological occupation law or turn its energy into an exact charged
path.
-/

noncomputable section

namespace GameTheory

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Receiver `who`'s payoff effect when singleton owner `owner` replaces the
receiver's own singleton exit. -/
def quittingSingletonSoloEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  reward (quittingSingletonTerminal owner) who -
    reward (quittingSingletonTerminal who) who

omit [Fintype ι] [DecidableEq ι] in
/-- The diagonal solo effect vanishes. -/
@[simp]
theorem quittingSingletonSoloEffect_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingSingletonSoloEffect reward who who = 0 := by
  simp [quittingSingletonSoloEffect]

/-- Symmetric reciprocal-synergy part of the singleton solo-effect matrix. -/
def quittingSingletonSoloSymmetricEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  (quittingSingletonSoloEffect reward who owner +
    quittingSingletonSoloEffect reward owner who) / 2

/-- Skew circulation part of the singleton solo-effect matrix. -/
def quittingSingletonSoloSkewEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) : ℝ :=
  (quittingSingletonSoloEffect reward who owner -
    quittingSingletonSoloEffect reward owner who) / 2

omit [Fintype ι] [DecidableEq ι] in
/-- Pointwise symmetric/skew decomposition of the solo-effect matrix. -/
theorem quittingSingletonSoloEffect_eq_symmetric_add_skew
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    quittingSingletonSoloEffect reward who owner =
      quittingSingletonSoloSymmetricEffect reward who owner +
        quittingSingletonSoloSkewEffect reward who owner := by
  unfold quittingSingletonSoloSymmetricEffect
    quittingSingletonSoloSkewEffect
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The reciprocal part is symmetric. -/
theorem quittingSingletonSoloSymmetricEffect_comm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    quittingSingletonSoloSymmetricEffect reward who owner =
      quittingSingletonSoloSymmetricEffect reward owner who := by
  unfold quittingSingletonSoloSymmetricEffect
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The circulation part is skew-symmetric. -/
theorem quittingSingletonSoloSkewEffect_swap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    quittingSingletonSoloSkewEffect reward owner who =
      -quittingSingletonSoloSkewEffect reward who owner := by
  unfold quittingSingletonSoloSkewEffect
  ring

/-- Quadratic solo-effect energy of a mass vector. -/
def quittingSingletonPacketQuadraticEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) : ℝ :=
  ∑ who, mass who * ∑ owner,
    mass owner * quittingSingletonSoloEffect reward who owner

/-- Quadratic energy formed from the symmetric reciprocal-synergy part. -/
def quittingSingletonPacketSymmetricEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) : ℝ :=
  ∑ who, mass who * ∑ owner,
    mass owner * quittingSingletonSoloSymmetricEffect reward who owner

/-- Quadratic energy formed from the skew circulation part. -/
def quittingSingletonPacketSkewEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) : ℝ :=
  ∑ who, mass who * ∑ owner,
    mass owner * quittingSingletonSoloSkewEffect reward who owner

omit [DecidableEq ι] in
/-- The skew part contributes zero to every quadratic packet energy. -/
theorem quittingSingletonPacketSkewEnergy_eq_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) :
    quittingSingletonPacketSkewEnergy reward mass = 0 := by
  classical
  have hswap :
      (∑ who, ∑ owner,
          mass who * mass owner *
            quittingSingletonSoloSkewEffect reward who owner) =
        -(∑ who, ∑ owner,
          mass who * mass owner *
            quittingSingletonSoloSkewEffect reward who owner) := by
    calc
      (∑ who, ∑ owner,
          mass who * mass owner *
            quittingSingletonSoloSkewEffect reward who owner) =
          ∑ owner, ∑ who,
            mass who * mass owner *
              quittingSingletonSoloSkewEffect reward who owner := by
        rw [sum_comm]
      _ = -(∑ who, ∑ owner,
          mass who * mass owner *
            quittingSingletonSoloSkewEffect reward who owner) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro who _
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro owner _
        rw [quittingSingletonSoloSkewEffect_swap]
        ring
  have hzero :
      (∑ who, ∑ owner,
          mass who * mass owner *
            quittingSingletonSoloSkewEffect reward who owner) = 0 := by
    linarith
  unfold quittingSingletonPacketSkewEnergy
  simpa only [Finset.mul_sum, mul_assoc] using hzero

omit [DecidableEq ι] in
/-- The packet quadratic form sees only the symmetric reciprocal-synergy
channel. -/
theorem quittingSingletonPacketQuadraticEnergy_eq_symmetricEnergy
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) :
    quittingSingletonPacketQuadraticEnergy reward mass =
      quittingSingletonPacketSymmetricEnergy reward mass := by
  classical
  have hdecompose :
      quittingSingletonPacketQuadraticEnergy reward mass =
        quittingSingletonPacketSymmetricEnergy reward mass +
          quittingSingletonPacketSkewEnergy reward mass := by
    unfold quittingSingletonPacketQuadraticEnergy
      quittingSingletonPacketSymmetricEnergy
      quittingSingletonPacketSkewEnergy
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro who _
    rw [← mul_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro owner _
    rw [← mul_add]
    congr 1
    exact quittingSingletonSoloEffect_eq_symmetric_add_skew
      reward who owner
  rw [hdecompose, quittingSingletonPacketSkewEnergy_eq_zero, add_zero]

omit [DecidableEq ι] in
/-- The singleton-effect average is delivery minus the receiver's own solo
payoff whenever the masses sum to one. -/
theorem sum_mass_mul_quittingSingletonSoloEffect_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) (hmassSum : ∑ owner, mass owner = 1) (who : ι) :
    (∑ owner, mass owner * quittingSingletonSoloEffect reward who owner) =
      quittingSingletonMixture reward mass who -
        reward (quittingSingletonTerminal who) who := by
  classical
  unfold quittingSingletonSoloEffect quittingSingletonMixture
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hmassSum, one_mul]

namespace QuittingNormalizedSingletonSourcePacket

/-- Packet complementarity in closed product form. -/
theorem mass_mul_target_sub_solo_eq_zero
    (packet : QuittingNormalizedSingletonSourcePacket reward) (who : ι) :
    packet.mass who *
      (packet.target who -
        reward (quittingSingletonTerminal who) who) = 0 := by
  by_cases hzero : packet.mass who = 0
  · simp [hzero]
  · have hpos : 0 < packet.mass who :=
      lt_of_le_of_ne (packet.mass_nonneg who) (Ne.symm hzero)
    rw [packet.positive_mass_pins_target who hpos, sub_self, mul_zero]

/-- Coordinate form of the packet energy identity. -/
theorem mass_mul_surplus_eq_soloEffect
    (packet : QuittingNormalizedSingletonSourcePacket reward) (who : ι) :
    packet.mass who *
        (quittingSingletonMixture reward packet.mass who -
          packet.target who) =
      packet.mass who * ∑ owner,
        packet.mass owner * quittingSingletonSoloEffect reward who owner := by
  have hmatrix := sum_mass_mul_quittingSingletonSoloEffect_eq
    reward packet.mass packet.mass_sum who
  have hcomplement := packet.mass_mul_target_sub_solo_eq_zero who
  rw [hmatrix]
  linarith

end QuittingNormalizedSingletonSourcePacket

/-- Mass-weighted delivery surplus of a normalized singleton packet. -/
def quittingPacketWeightedSurplus
    (packet : QuittingNormalizedSingletonSourcePacket reward) : ℝ :=
  ∑ who, packet.mass who *
    (quittingSingletonMixture reward packet.mass who - packet.target who)

/-- **Packet energy identity.**  Weighted delivery surplus is exactly the
quadratic form of the normalized solo-effect matrix. -/
theorem quittingPacketWeightedSurplus_eq_quadraticForm
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    quittingPacketWeightedSurplus packet =
      quittingSingletonPacketQuadraticEnergy reward packet.mass := by
  classical
  unfold quittingPacketWeightedSurplus
    quittingSingletonPacketQuadraticEnergy
  apply Finset.sum_congr rfl
  intro who _
  exact packet.mass_mul_surplus_eq_soloEffect who

/-- Every weighted coordinate surplus of a feasible packet is nonnegative. -/
theorem QuittingNormalizedSingletonSourcePacket.mass_mul_surplus_nonneg
    (packet : QuittingNormalizedSingletonSourcePacket reward) (who : ι) :
    0 ≤ packet.mass who *
      (quittingSingletonMixture reward packet.mass who -
        packet.target who) :=
  mul_nonneg (packet.mass_nonneg who)
    (sub_nonneg.mpr (packet.mix_ge_target who))

/-- The total packet surplus is nonnegative. -/
theorem quittingPacketWeightedSurplus_nonneg
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    0 ≤ quittingPacketWeightedSurplus packet := by
  classical
  unfold quittingPacketWeightedSurplus
  exact Finset.sum_nonneg fun who _ => packet.mass_mul_surplus_nonneg who

/-- Mass-weighted gain from conditioning each owner out of the singleton
delivery. Its energy identity applies when every packet atom has mass below
one. -/
def quittingPacketWeightedRefusalSurplus
    (packet : QuittingNormalizedSingletonSourcePacket reward) : ℝ :=
  ∑ owner, (1 - packet.mass owner) *
    (quittingSingletonRefusalValue reward packet.mass owner owner -
      quittingSingletonMixture reward packet.mass owner)

namespace QuittingNormalizedSingletonSourcePacket

/-- On a proper atom, the weighted refusal gain is exactly the weighted
packet surplus. Zero-mass atoms are included; only a full-mass denominator
is excluded. -/
theorem one_sub_mass_mul_refusal_sub_mixture_eq_mass_mul_surplus
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (owner : ι) (hmass : packet.mass owner < 1) :
    (1 - packet.mass owner) *
        (quittingSingletonRefusalValue reward packet.mass owner owner -
          quittingSingletonMixture reward packet.mass owner) =
      packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by
  have hsplit := packet.singletonMixture_eq_mass_mul_add_refusal hmass owner
  have hcomplement := packet.mass_mul_target_sub_solo_eq_zero owner
  have hfirst :
      (1 - packet.mass owner) *
          (quittingSingletonRefusalValue reward packet.mass owner owner -
            quittingSingletonMixture reward packet.mass owner) =
        packet.mass owner *
          (quittingSingletonMixture reward packet.mass owner -
            reward (quittingSingletonTerminal owner) owner) := by
    rw [hsplit]
    ring
  have htargetSolo :
      packet.mass owner * packet.target owner =
        packet.mass owner *
          reward (quittingSingletonTerminal owner) owner := by
    rw [mul_sub] at hcomplement
    linarith
  rw [hfirst]
  calc
    packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          reward (quittingSingletonTerminal owner) owner) =
      packet.mass owner *
          quittingSingletonMixture reward packet.mass owner -
        packet.mass owner *
          reward (quittingSingletonTerminal owner) owner := by ring
    _ = packet.mass owner *
          quittingSingletonMixture reward packet.mass owner -
        packet.mass owner * packet.target owner := by rw [htargetSolo]
    _ = packet.mass owner *
        (quittingSingletonMixture reward packet.mass owner -
          packet.target owner) := by ring

end QuittingNormalizedSingletonSourcePacket

/-- **Aggregate refusal-energy identity.** If every packet atom is proper,
the total weighted refusal surplus is the solo-effect quadratic form. -/
theorem quittingPacketWeightedRefusal_eq_quadraticForm
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hmass : ∀ owner, packet.mass owner < 1) :
    quittingPacketWeightedRefusalSurplus packet =
      quittingSingletonPacketQuadraticEnergy reward packet.mass := by
  classical
  calc
    quittingPacketWeightedRefusalSurplus packet =
        quittingPacketWeightedSurplus packet := by
      unfold quittingPacketWeightedRefusalSurplus
        quittingPacketWeightedSurplus
      apply Finset.sum_congr rfl
      intro owner _
      exact packet.one_sub_mass_mul_refusal_sub_mixture_eq_mass_mul_surplus
        owner (hmass owner)
    _ = quittingSingletonPacketQuadraticEnergy reward packet.mass :=
      quittingPacketWeightedSurplus_eq_quadraticForm packet

/-- The maximum coordinate packet defect is at most the sum of all weighted
coordinate surpluses. -/
theorem quittingNormalizedSingletonPacketDefect_le_weightedSurplus
    [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward) :
    quittingNormalizedSingletonPacketDefect reward
        (packet.mass, packet.target) ≤
      quittingPacketWeightedSurplus packet := by
  classical
  obtain ⟨owner, _, howner⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who => packet.mass who *
      (quittingSingletonMixture reward packet.mass who - packet.target who))
  rw [quittingNormalizedSingletonPacketDefect, howner]
  unfold quittingPacketWeightedSurplus
  exact Finset.single_le_sum
    (fun who _ => packet.mass_mul_surplus_nonneg who)
    (Finset.mem_univ owner)

omit [DecidableEq ι] in
/-- Pairwise nonpositive reciprocal solo effects make every nonnegative mass
vector's symmetric packet energy nonpositive. -/
theorem quittingSingletonPacketQuadraticEnergy_nonpos_of_pairwise_reciprocal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) (hmass : ∀ who, 0 ≤ mass who)
    (hpair : ∀ who owner, who ≠ owner →
      quittingSingletonSoloEffect reward who owner +
        quittingSingletonSoloEffect reward owner who ≤ 0) :
    quittingSingletonPacketQuadraticEnergy reward mass ≤ 0 := by
  rw [quittingSingletonPacketQuadraticEnergy_eq_symmetricEnergy]
  unfold quittingSingletonPacketSymmetricEnergy
  apply Finset.sum_nonpos
  intro who _
  apply mul_nonpos_of_nonneg_of_nonpos (hmass who)
  apply Finset.sum_nonpos
  intro owner _
  apply mul_nonpos_of_nonneg_of_nonpos (hmass owner)
  unfold quittingSingletonSoloSymmetricEffect
  by_cases heq : who = owner
  · subst owner
    simp
  · exact div_nonpos_of_nonpos_of_nonneg (hpair who owner heq) (by norm_num)

omit [DecidableEq ι] in
/-- Positive packet energy forces a positive reciprocal-synergy pair inside
the positive support of the mass vector. -/
theorem exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (mass : ι → ℝ) (hmass : ∀ who, 0 ≤ mass who)
    (henergy : 0 < quittingSingletonPacketQuadraticEnergy reward mass) :
    ∃ who owner, 0 < mass who ∧ 0 < mass owner ∧ who ≠ owner ∧
      0 < quittingSingletonSoloEffect reward who owner +
        quittingSingletonSoloEffect reward owner who := by
  by_contra hno
  push Not at hno
  have henergyNonpos :
      quittingSingletonPacketQuadraticEnergy reward mass ≤ 0 := by
    rw [quittingSingletonPacketQuadraticEnergy_eq_symmetricEnergy]
    unfold quittingSingletonPacketSymmetricEnergy
    apply Finset.sum_nonpos
    intro who _
    by_cases hwho : 0 < mass who
    · apply mul_nonpos_of_nonneg_of_nonpos (hmass who)
      apply Finset.sum_nonpos
      intro owner _
      by_cases howner : 0 < mass owner
      · apply mul_nonpos_of_nonneg_of_nonpos (hmass owner)
        unfold quittingSingletonSoloSymmetricEffect
        by_cases heq : who = owner
        · subst owner
          simp
        · exact div_nonpos_of_nonpos_of_nonneg
            (hno who owner hwho howner heq) (by norm_num)
      · have hownerZero : mass owner = 0 :=
          le_antisymm (le_of_not_gt howner) (hmass owner)
        simp [hownerZero]
    · have hwhoZero : mass who = 0 :=
        le_antisymm (le_of_not_gt hwho) (hmass who)
      simp [hwhoZero]
  exact (not_lt_of_ge henergyNonpos) henergy

/-- A positive normalized packet defect forces a positive reciprocal-synergy
pair in the positive support of that packet. -/
theorem exists_supported_pair_pos_reciprocalSoloEffect_of_packetDefect_pos
    [Nonempty ι]
    (packet : QuittingNormalizedSingletonSourcePacket reward)
    (hdefect : 0 < quittingNormalizedSingletonPacketDefect reward
      (packet.mass, packet.target)) :
    ∃ who owner,
      0 < packet.mass who ∧ 0 < packet.mass owner ∧ who ≠ owner ∧
        0 < quittingSingletonSoloEffect reward who owner +
          quittingSingletonSoloEffect reward owner who := by
  have hsurplus : 0 < quittingPacketWeightedSurplus packet :=
    hdefect.trans_le
      (quittingNormalizedSingletonPacketDefect_le_weightedSurplus packet)
  have henergy :
      0 < quittingSingletonPacketQuadraticEnergy reward packet.mass := by
    rwa [quittingPacketWeightedSurplus_eq_quadraticForm] at hsurplus
  exact exists_supported_pair_pos_reciprocalSoloEffect_of_energy_pos
    reward packet.mass packet.mass_nonneg henergy

/-- **Reciprocal-solo solved class.**  If every distinct player pair has
nonpositive reciprocal solo effect, the finite quitting game has an ordinary
uniform-equilibrium payoff. -/
theorem exists_uniformEquilibriumPayoff_of_pairwise_reciprocalSolo_nonpos
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hpair : ∀ who owner, who ≠ owner →
      quittingSingletonSoloEffect reward who owner +
        quittingSingletonSoloEffect reward owner who ≤ 0) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  rcases quittingGame_uniformPayoff_or_normalizedSingletonSourcePacket reward with
    hpayoff | hpacket
  · exact hpayoff
  · obtain ⟨packet⟩ := hpacket
    have henergyNonpos :=
      quittingSingletonPacketQuadraticEnergy_nonpos_of_pairwise_reciprocal
        reward packet.mass packet.mass_nonneg hpair
    have hsurplusNonpos : quittingPacketWeightedSurplus packet ≤ 0 := by
      rw [quittingPacketWeightedSurplus_eq_quadraticForm]
      exact henergyNonpos
    have hsurplusZero : quittingPacketWeightedSurplus packet = 0 :=
      le_antisymm hsurplusNonpos (quittingPacketWeightedSurplus_nonneg packet)
    have hactive : ∀ owner, 0 < packet.mass owner →
        quittingSingletonMixture reward packet.mass owner =
          reward (quittingSingletonTerminal owner) owner := by
      intro owner howner
      have hterm : packet.mass owner *
          (quittingSingletonMixture reward packet.mass owner -
            packet.target owner) = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun who _ => packet.mass_mul_surplus_nonneg who)).1
        · exact hsurplusZero
        · exact Finset.mem_univ owner
      have hmixTarget :
          quittingSingletonMixture reward packet.mass owner =
            packet.target owner := by
        rcases mul_eq_zero.mp hterm with hmassZero | hgap
        · exact (howner.ne' hmassZero).elim
        · linarith
      rw [hmixTarget, packet.positive_mass_pins_target owner howner]
    exact exists_uniformEquilibriumPayoff_of_complementarySingletonMixture
      reward packet.mass packet.target packet.mass_nonneg packet.mass_sum
        packet.mix_ge_target hactive packet.solo_le_target
        packet.punishment_le_target

end GameTheory
