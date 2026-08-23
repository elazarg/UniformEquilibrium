/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.PowersetBernoulliWeight
import Research.Quitting.CirculantColliderBonusFamily
import UniformEquilibrium.Diagnostics.Quitting.Chronology.PeriodicBlockProfile
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# The stationary all-quitter block of a raised-collider table

Every player quitting at every stage with one common probability `1 - u` is a
period-one block profile in the sense of
`UniformEquilibrium/Quitting/Cycles/BlockPeriodicProfile.lean`.  Its two
endpoint values at a player `who` read the raised-collider table of
`Research/Quitting/CirculantColliderBonusFamily.lean` in closed form.

* Quitting now, `who` is joined by whichever opponents quit.  It is alone with
  probability `u⁴`, worth its solo self value; it is joined by exactly its
  predecessor with probability `(1 - u) u³`, the collider row, worth
  `s + bonus`; and every other joint exit pays it the joint value.  So the
  quit endpoint is `low + (s - low) u⁴ + (s + bonus - low) (1 - u) u³`.
* Continuing, `who` is an outsider.  A single opponent quitting pays it that
  opponent's circulant singleton row and any larger coalition pays it zero, so
  the continue endpoint is `(1 - u) u³ (4 s + σ) + u⁴ V`, with `σ` the margin
  sum and `V` the displayed value.

Equating both endpoints to `V` determines `V` from the continue equation and
then `bonus` from the quit equation, giving `stationaryValue` and
`stationaryBonus`.  So the all-quitter block is an exact equilibrium of the
raised-collider table at exactly one bonus per rate, and the region it closes
is the range of `stationaryBonus` on the open unit interval.

## Main definitions

* `uniformHazard` — the period-one all-quitter schedule
* `stationaryValue`, `stationaryBonus` — the value and the bonus a rate forces

## Main results

* `sigmaValue_eq_add_sum` — a quit endpoint measured from a reference value
* `sigmaValue_colliderBonusReward` — the quit endpoint
* `excludedValue_colliderBonusReward` and `continueMassExcl_uniform` — the
  continue endpoint
* `stationaryValue_spec`, `stationaryBonus_spec` — the two indifference
  equations the definitions solve
* `isQuittingBlockCertificate_uniform` — the certificate at the forced bonus
* `exists_uniformEquilibriumPayoff_colliderBonusReward_stationary` and
  `isEmpty_terminalExploitabilityWitness_colliderBonusReward_stationary` — the closure
-/

noncomputable section

namespace GameTheory
namespace CirculantColliderBonus

open Math.Probability Math.PMFProduct CirculantConstantStepCycle
open CirculantColliderCompletion

/-! ## Coalition weights among the opponents of one player -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The probability that exactly the opponents in `J` quit and every other
opponent of `who` continues: the relative Bernoulli weight of
`MathUE/Finset/PowersetBernoulliWeight.lean` over the coordinates other than
`who`. -/
abbrev oppWeight (x : ι → ℝ) (who : ι) (J : Finset ι) : ℝ :=
  Math.Finset.bernoulliWeight x (Finset.univ.erase who) J

theorem sum_oppWeight (x : ι → ℝ) (who : ι) :
    ∑ J ∈ (Finset.univ.erase who).powerset, oppWeight x who J = 1 :=
  Math.Finset.sum_bernoulliWeight x _

/-- A quit endpoint measured from a reference value. -/
theorem sigmaValue_eq_add_sum (r : Finset ι → ι → ℝ) (x : ι → ℝ) (who : ι) (c : ℝ) :
    sigmaValue r x who =
      c + ∑ J ∈ (Finset.univ.erase who).powerset,
        oppWeight x who J * (r (insert who J) who - c) := by
  rw [sigmaValue]
  have hsplit : ∀ J ∈ (Finset.univ.erase who).powerset,
      (∏ j ∈ J, x j) * (∏ j ∈ Finset.univ.erase who \ J, (1 - x j)) *
          r (insert who J) who =
        oppWeight x who J * c + oppWeight x who J * (r (insert who J) who - c) := by
    intro J _
    rw [oppWeight, Math.Finset.bernoulliWeight]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_oppWeight, one_mul]

/-! ## The two endpoints of the all-quitter block -/

/-- The all-quitter hazard row of a common rate. -/
def uniformHazard (p : ℝ) : Fin 1 → ZMod 5 → ℝ := fun _ _ ↦ p

theorem uniformHazard_nonneg {p : ℝ} (h0 : 0 ≤ p) : ∀ k who, 0 ≤ uniformHazard p k who :=
  fun _ _ ↦ h0

theorem uniformHazard_le_one {p : ℝ} (h1 : p ≤ 1) : ∀ k who, uniformHazard p k who ≤ 1 :=
  fun _ _ ↦ h1

variable (s low bonus : ℝ) (m : ZMod 5 → ℝ)

/-! ### Which coalitions the quit endpoint reads -/

theorem card_erase_univ (who : ZMod 5) : (Finset.univ.erase who).card = 4 := by
  revert who
  decide

theorem notMem_of_mem_powerset_erase {who : ZMod 5} {J : Finset (ZMod 5)}
    (hJ : J ∈ (Finset.univ.erase who).powerset) : who ∉ J := by
  intro hmem
  exact (Finset.mem_erase.mp (Finset.mem_powerset.mp hJ hmem)).1 rfl

theorem erase_collider_pair (who : ZMod 5) :
    ({who - 1, who} : Finset (ZMod 5)).erase who = {who - 1} := by
  revert who
  decide

/-- Away from the two exceptional coalitions the quit endpoint pays the joint
value. -/
theorem colliderBonusReward_insert_eq
    {who : ZMod 5} {J : Finset (ZMod 5)} (hJ : J ∈ (Finset.univ.erase who).powerset)
    (hne : J ≠ ∅) (hcol : J ≠ {who - 1}) :
    weightOfReward (colliderBonusReward s low bonus m) (insert who J) who = low := by
  have hwho : who ∉ J := notMem_of_mem_powerset_erase hJ
  have hnonempty : (insert who J).Nonempty := Finset.insert_nonempty who J
  have hcard : (insert who J).card ≠ 1 := by
    rw [Finset.card_insert_of_notMem hwho]
    have : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have := Finset.card_pos.mpr this
    omega
  have hnotcollider : insert who J ≠ ({who - 1, who} : Finset (ZMod 5)) := by
    intro hcontra
    apply hcol
    have herase : (insert who J).erase who = J := Finset.erase_insert hwho
    rw [hcontra, erase_collider_pair] at herase
    exact herase.symm
  rw [weightOfReward, dif_pos hnonempty, colliderBonusReward,
    colliderReward_of_mem s low m ⟨insert who J, hnonempty⟩ hcard who
      (Finset.mem_insert_self who J) hnotcollider,
    if_neg hnotcollider, add_zero]

theorem colliderBonusReward_insert_empty (hm0 : m 0 = 0) (who : ZMod 5) :
    weightOfReward (colliderBonusReward s low bonus m) (insert who ∅) who = s := by
  have hnonempty : (insert who (∅ : Finset (ZMod 5))).Nonempty :=
    Finset.insert_nonempty who ∅
  rw [weightOfReward, dif_pos hnonempty]
  have hset : (⟨insert who (∅ : Finset (ZMod 5)), hnonempty⟩ :
      {S : Finset (ZMod 5) // S.Nonempty}) = quittingSingletonTerminal who :=
    Subtype.ext (by simp [quittingSingletonTerminal])
  rw [hset, colliderBonusReward_singleton, sub_self, hm0, add_zero]

theorem colliderBonusReward_insert_collider (who : ZMod 5) :
    weightOfReward (colliderBonusReward s low bonus m) (insert who {who - 1}) who =
      s + bonus := by
  have hnonempty : (insert who ({who - 1} : Finset (ZMod 5))).Nonempty :=
    Finset.insert_nonempty who _
  have hset : insert who ({who - 1} : Finset (ZMod 5)) = {who - 1, who} := by
    revert who
    decide
  rw [weightOfReward, dif_pos hnonempty]
  have hsub : (⟨insert who ({who - 1} : Finset (ZMod 5)), hnonempty⟩ :
      {S : Finset (ZMod 5) // S.Nonempty}) =
      ⟨{who - 1, who}, Finset.insert_nonempty (who - 1) {who}⟩ := Subtype.ext hset
  rw [hsub, colliderBonusReward, colliderReward_collider,
    if_pos (rfl : ({who - 1, who} : Finset (ZMod 5)) = {who - 1, who})]

/-! ### The support of the two endpoint sums -/

theorem oppWeight_empty {p : ℝ} (who : ZMod 5) :
    oppWeight (fun _ : ZMod 5 ↦ p) who ∅ = (1 - p) ^ 4 := by
  rw [oppWeight, Math.Finset.bernoulliWeight_empty_const, card_erase_univ]

theorem oppWeight_singleton {p : ℝ} {who j : ZMod 5} (hj : j ≠ who) :
    oppWeight (fun _ : ZMod 5 ↦ p) who {j} = p * (1 - p) ^ 3 := by
  rw [oppWeight, Math.Finset.bernoulliWeight_singleton_const p
    (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩), card_erase_univ]

/-! ### The quit endpoint -/

theorem pair_subset_powerset (who : ZMod 5) :
    ({∅, {who - 1}} : Finset (Finset (ZMod 5))) ⊆ (Finset.univ.erase who).powerset := by
  revert who
  decide

theorem empty_ne_singleton_pred (who : ZMod 5) :
    (∅ : Finset (ZMod 5)) ≠ {who - 1} := by
  revert who
  decide

theorem pred_ne_self (who : ZMod 5) : who - 1 ≠ who := by
  revert who
  decide

/-- **The quit endpoint of the all-quitter block.**  A player quitting now is
alone with probability `(1 - p)⁴`, joined by exactly its predecessor with
probability `p (1 - p)³`, and paid the joint value otherwise. -/
theorem sigmaValue_colliderBonusReward (hm0 : m 0 = 0) (p : ℝ) (who : ZMod 5) :
    sigmaValue (weightOfReward (colliderBonusReward s low bonus m))
        (fun _ ↦ p) who =
      low + (s - low) * (1 - p) ^ 4 + (s + bonus - low) * (p * (1 - p) ^ 3) := by
  rw [sigmaValue_eq_add_sum _ _ _ low]
  have hzero : ∀ J ∈ (Finset.univ.erase who).powerset,
      J ∉ ({∅, {who - 1}} : Finset (Finset (ZMod 5))) →
      oppWeight (fun _ : ZMod 5 ↦ p) who J *
        (weightOfReward (colliderBonusReward s low bonus m) (insert who J) who - low) = 0 := by
    intro J hJ hJ'
    have hne : J ≠ ∅ := fun h ↦ hJ' (by rw [h]; exact Finset.mem_insert_self _ _)
    have hcol : J ≠ {who - 1} := fun h ↦ hJ' (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [colliderBonusReward_insert_eq s low bonus m hJ hne hcol, sub_self, mul_zero]
  rw [← Finset.sum_subset (pair_subset_powerset who) hzero,
    Finset.sum_pair (empty_ne_singleton_pred who),
    colliderBonusReward_insert_empty s low bonus m hm0 who,
    colliderBonusReward_insert_collider s low bonus m who,
    oppWeight_empty who, oppWeight_singleton (pred_ne_self who)]
  ring

/-! ### The continue endpoint -/

/-- An outsider of a joint exit of at least two members is paid zero. -/
theorem colliderBonusReward_outsider {who : ZMod 5} {J : Finset (ZMod 5)}
    (hne : J.Nonempty) (hcard : J.card ≠ 1) (hwho : who ∉ J) :
    weightOfReward (colliderBonusReward s low bonus m) J who = 0 := by
  have hnotcollider : J ≠ ({who - 1, who} : Finset (ZMod 5)) := by
    intro hcontra
    exact hwho (by rw [hcontra]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [weightOfReward, dif_pos hne, colliderBonusReward,
    colliderReward_of_notMem s low m ⟨J, hne⟩ hcard who hwho, if_neg hnotcollider, add_zero]

/-- A single opponent quitting pays a spectator that opponent's circulant
singleton row. -/
theorem colliderBonusReward_singleton_weight (j who : ZMod 5) :
    weightOfReward (colliderBonusReward s low bonus m) {j} who = s + m (j - who) := by
  have hne : ({j} : Finset (ZMod 5)).Nonempty := Finset.singleton_nonempty j
  rw [weightOfReward, dif_pos hne]
  have hsub : (⟨({j} : Finset (ZMod 5)), hne⟩ : {S : Finset (ZMod 5) // S.Nonempty}) =
      quittingSingletonTerminal j := Subtype.ext rfl
  rw [hsub, colliderBonusReward_singleton]

theorem sum_margin_erase (hm0 : m 0 = 0) (who : ZMod 5) :
    ∑ j ∈ Finset.univ.erase who, (s + m (j - who)) = 4 * s + ∑ d, m d := by
  have hshift : (∑ j : ZMod 5, m (j - who)) = ∑ d, m d :=
    Fintype.sum_equiv (Equiv.subRight who) (fun j ↦ m (j - who)) m (fun _ ↦ rfl)
  have hfull : ∑ j : ZMod 5, (s + m (j - who)) = 5 * s + ∑ d, m d := by
    rw [Finset.sum_add_distrib, Finset.sum_const, hshift]
    have : (Finset.univ : Finset (ZMod 5)).card = 5 := by decide
    rw [this, nsmul_eq_mul]
    norm_num
  have herase := Finset.add_sum_erase Finset.univ (fun j : ZMod 5 ↦ s + m (j - who))
    (Finset.mem_univ who)
  rw [sub_self, hm0, add_zero, hfull] at herase
  linarith

/-- **The continue endpoint of the all-quitter block.**  A spectator collects
a singleton row when exactly one opponent quits and nothing when more do. -/
theorem excludedValue_colliderBonusReward (hm0 : m 0 = 0) (p : ℝ) (who : ZMod 5) :
    excludedValue (weightOfReward (colliderBonusReward s low bonus m))
        (fun _ ↦ p) who =
      p * (1 - p) ^ 3 * (4 * s + ∑ d, m d) := by
  have hsub : (Finset.univ.erase who).image (fun j ↦ ({j} : Finset (ZMod 5))) ⊆
      ((Finset.univ.erase who).powerset).erase ∅ := by
    revert who
    decide
  have hzero : ∀ J ∈ ((Finset.univ.erase who).powerset).erase ∅,
      J ∉ (Finset.univ.erase who).image (fun j ↦ ({j} : Finset (ZMod 5))) →
      (∏ j ∈ J, (fun _ : ZMod 5 ↦ p) j) *
          (∏ j ∈ Finset.univ.erase who \ J, (1 - (fun _ : ZMod 5 ↦ p) j)) *
          weightOfReward (colliderBonusReward s low bonus m) J who = 0 := by
    intro J hJ hJ'
    have hmem := Finset.mem_erase.mp hJ
    have hne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hmem.1
    have hpow := Finset.mem_powerset.mp hmem.2
    have hwho : who ∉ J := fun hcontra ↦ (Finset.mem_erase.mp (hpow hcontra)).1 rfl
    have hcard : J.card ≠ 1 := by
      intro hone
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
      refine hJ' (Finset.mem_image.mpr ⟨j, ?_, hj.symm⟩)
      exact hpow (by rw [hj]; exact Finset.mem_singleton_self j)
    rw [colliderBonusReward_outsider s low bonus m hne hcard hwho, mul_zero]
  rw [excludedValue, ← Finset.sum_subset hsub hzero,
    Finset.sum_image (fun a _ b _ h ↦ Finset.singleton_injective h)]
  have hterm : ∀ j ∈ Finset.univ.erase who,
      (∏ i ∈ ({j} : Finset (ZMod 5)), (fun _ : ZMod 5 ↦ p) i) *
          (∏ i ∈ Finset.univ.erase who \ {j}, (1 - (fun _ : ZMod 5 ↦ p) i)) *
          weightOfReward (colliderBonusReward s low bonus m) {j} who =
        p * (1 - p) ^ 3 * (s + m (j - who)) := by
    intro j hj
    have hjne : j ≠ who := (Finset.mem_erase.mp hj).1
    have hw := oppWeight_singleton (p := p) hjne
    rw [oppWeight, Math.Finset.bernoulliWeight] at hw
    rw [colliderBonusReward_singleton_weight, hw]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_margin_erase s m hm0 who]

theorem continueMassExcl_uniform (p : ℝ) (who : ZMod 5) :
    continueMassExcl (fun _ : ZMod 5 ↦ p) who = (1 - p) ^ 4 := by
  rw [continueMassExcl, Finset.prod_const, card_erase_univ]

/-! ## The value and the bonus a rate forces -/

/-- The displayed value of the all-quitter block at continuation rate `u`.  It
solves the spectator equation `V = (1 - u) u³ (4 s + σ) + u⁴ V`. -/
def stationaryValue (s σ u : ℝ) : ℝ := (1 - u) * u ^ 3 * (4 * s + σ) / (1 - u ^ 4)

/-- The collider bonus at which the all-quitter block of continuation rate `u`
is exactly indifferent.  It solves the quitter equation
`V = low + (s - low) u⁴ + (s + bonus - low) (1 - u) u³`. -/
def stationaryBonus (s low σ u : ℝ) : ℝ :=
  (stationaryValue s σ u - low - (s - low) * u ^ 3) / ((1 - u) * u ^ 3)

theorem stationaryValue_spec (s σ : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (1 - u) * u ^ 3 * (4 * s + σ) + u ^ 4 * stationaryValue s σ u =
      stationaryValue s σ u := by
  have hden : (1 : ℝ) - u ^ 4 ≠ 0 := by nlinarith [pow_lt_one₀ hu0.le hu1 (by norm_num : 4 ≠ 0)]
  rw [stationaryValue]
  field_simp
  ring

theorem stationaryBonus_spec (s low σ : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    low + (s - low) * u ^ 4 +
        (s + stationaryBonus s low σ u - low) * ((1 - u) * u ^ 3) =
      stationaryValue s σ u := by
  have hnum : (1 - u) * u ^ 3 ≠ 0 :=
    ne_of_gt (mul_pos (by linarith) (pow_pos hu0 3))
  have hkey : stationaryBonus s low σ u * ((1 - u) * u ^ 3) =
      stationaryValue s σ u - low - (s - low) * u ^ 3 := by
    rw [stationaryBonus, div_mul_cancel₀ _ hnum]
  linear_combination hkey

/-! ## The reward box -/

theorem colliderBonusReward_collider (who : ZMod 5) :
    colliderBonusReward s low bonus m
        ⟨{who - 1, who}, Finset.insert_nonempty (who - 1) {who}⟩ who = s + bonus := by
  rw [colliderBonusReward, colliderReward_collider,
    if_pos (rfl : ({who - 1, who} : Finset (ZMod 5)) = {who - 1, who})]

theorem abs_self_le_bound (hm0 : m 0 = 0) :
    |s| ≤ quittingRewardBound (colliderBonusReward s low bonus m) := by
  have hentry := abs_reward_le_quittingRewardBound (colliderBonusReward s low bonus m)
    (quittingSingletonTerminal 0) 0
  rwa [colliderBonusReward_singleton, sub_self, hm0, add_zero] at hentry

theorem abs_collider_le_bound :
    |s + bonus| ≤ quittingRewardBound (colliderBonusReward s low bonus m) := by
  have hentry := abs_reward_le_quittingRewardBound (colliderBonusReward s low bonus m)
    ⟨{(0 : ZMod 5) - 1, 0}, Finset.insert_nonempty ((0 : ZMod 5) - 1) {0}⟩ 0
  rwa [colliderBonusReward_collider] at hentry

theorem nonempty_triple : ({0, 1, 2} : Finset (ZMod 5)).Nonempty := by decide

theorem card_triple : ({0, 1, 2} : Finset (ZMod 5)).card ≠ 1 := by decide

theorem mem_triple : (0 : ZMod 5) ∈ ({0, 1, 2} : Finset (ZMod 5)) := by decide

theorem triple_ne_collider :
    ({0, 1, 2} : Finset (ZMod 5)) ≠ {(0 : ZMod 5) - 1, (0 : ZMod 5)} := by decide

theorem abs_low_le_bound :
    |low| ≤ quittingRewardBound (colliderBonusReward s low bonus m) := by
  have hentry := abs_reward_le_quittingRewardBound (colliderBonusReward s low bonus m)
    ⟨{0, 1, 2}, nonempty_triple⟩ 0
  have hval : colliderBonusReward s low bonus m ⟨{0, 1, 2}, nonempty_triple⟩ 0 = low := by
    rw [colliderBonusReward,
      colliderReward_of_mem s low m ⟨{0, 1, 2}, nonempty_triple⟩ card_triple 0 mem_triple
        triple_ne_collider,
      if_neg triple_ne_collider, add_zero]
  rwa [hval] at hentry

/-! ## The certificate -/

variable {s low m}

/-- **The all-quitter block certificate.**  At continuation rate `u` in the
open unit interval, and at the bonus the rate forces, every player is exactly
indifferent between quitting and continuing, so the constant displayed value
is a period-one block certificate. -/
theorem isQuittingBlockCertificate_uniform (hm0 : m 0 = 0) (hs : 0 ≤ s)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    IsQuittingBlockCertificate
      (colliderBonusReward s low (stationaryBonus s low (∑ d, m d) u) m)
      (uniformHazard (1 - u))
      (fun _ _ ↦ stationaryValue s (∑ d, m d) u) := by
  have hp0 : (0 : ℝ) ≤ 1 - u := by linarith
  have hp1 : (1 : ℝ) - u ≤ 1 := by linarith
  have hbonus := stationaryBonus_spec s low (∑ d, m d) hu0 hu1
  have hvalue := stationaryValue_spec s (∑ d, m d) hu0 hu1
  have hsimp : (1 : ℝ) - (1 - u) = u := by ring
  have hquit : ∀ who : ZMod 5,
      sigmaValue (weightOfReward (colliderBonusReward s low
          (stationaryBonus s low (∑ d, m d) u) m)) (fun _ ↦ 1 - u) who =
        stationaryValue s (∑ d, m d) u := by
    intro who
    rw [sigmaValue_colliderBonusReward s low _ m hm0 (1 - u) who, hsimp]
    linarith [hbonus]
  have hcont : ∀ who : ZMod 5,
      gammaValue (weightOfReward (colliderBonusReward s low
          (stationaryBonus s low (∑ d, m d) u) m)) (fun _ ↦ 1 - u) who
          (stationaryValue s (∑ d, m d) u) =
        stationaryValue s (∑ d, m d) u := by
    intro who
    rw [gammaValue, excludedValue_colliderBonusReward s low _ m hm0 (1 - u) who,
      continueMassExcl_uniform (1 - u) who, hsimp]
    linarith [hvalue]
  refine isQuittingBlockCertificate_of_root (uniformHazard_nonneg hp0)
    (uniformHazard_le_one hp1) ?_ rfl ?_ ?_ ?_ ?_
  · intro _ _
    set bonus := stationaryBonus s low (∑ d, m d) u with hbdef
    set B := quittingRewardBound (colliderBonusReward s low bonus m) with hBdef
    have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0.le hu1.le
    have hw1 : (0 : ℝ) ≤ 1 - u ^ 3 := by linarith
    have hw2 : (0 : ℝ) ≤ u ^ 4 := by positivity
    have hw3 : (0 : ℝ) ≤ (1 - u) * u ^ 3 := by positivity
    have hconvex : stationaryValue s (∑ d, m d) u =
        (1 - u ^ 3) * low + u ^ 4 * s + (1 - u) * u ^ 3 * (s + bonus) := by
      linear_combination -hbonus
    have h1 := abs_low_le_bound s low bonus m
    have h2 := abs_self_le_bound s low bonus m hm0
    have h3 := abs_collider_le_bound s low bonus m
    rw [← hBdef] at h1 h2 h3
    have hstep : |(1 - u ^ 3) * low + u ^ 4 * s + (1 - u) * u ^ 3 * (s + bonus)| ≤
        (1 - u ^ 3) * |low| + u ^ 4 * |s| + (1 - u) * u ^ 3 * |s + bonus| := by
      calc |(1 - u ^ 3) * low + u ^ 4 * s + (1 - u) * u ^ 3 * (s + bonus)|
          ≤ |(1 - u ^ 3) * low + u ^ 4 * s| + |(1 - u) * u ^ 3 * (s + bonus)| :=
            abs_add_le _ _
        _ ≤ |(1 - u ^ 3) * low| + |u ^ 4 * s| + |(1 - u) * u ^ 3 * (s + bonus)| := by
            gcongr
            exact abs_add_le _ _
        _ = (1 - u ^ 3) * |low| + u ^ 4 * |s| + (1 - u) * u ^ 3 * |s + bonus| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2,
              abs_of_nonneg hw3]
    have hcollapse : (1 - u ^ 3) * B + u ^ 4 * B + (1 - u) * u ^ 3 * B = B := by ring
    rw [hconvex]
    linarith [mul_le_mul_of_nonneg_left h1 hw1, mul_le_mul_of_nonneg_left h2 hw2,
      mul_le_mul_of_nonneg_left h3 hw3, hstep]
  · intro k
    funext who
    have huni : uniformHazard (1 - u) k = (fun _ : ZMod 5 ↦ 1 - u) := rfl
    rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
      quittingRootContinuePayoff_eq_gammaValue, hazardOfRoot_quittingBlockCycle,
      huni, hquit who, hcont who, quittingBlockCycle_true, quittingBlockCycle_false]
    show stationaryValue s (∑ d, m d) u =
      uniformHazard (1 - u) k who * stationaryValue s (∑ d, m d) u +
        (1 - uniformHazard (1 - u) k who) * stationaryValue s (∑ d, m d) u
    rw [uniformHazard]
    ring
  · intro k who
    have huni : uniformHazard (1 - u) k = (fun _ : ZMod 5 ↦ 1 - u) := rfl
    have hdiff : quittingRootEndpointDifference (colliderBonusReward s low
        (stationaryBonus s low (∑ d, m d) u) m)
        (fun _ ↦ stationaryValue s (∑ d, m d) u)
        (quittingBlockCycle (uniformHazard (1 - u)) (uniformHazard_nonneg hp0)
          (uniformHazard_le_one hp1) k) who = 0 := by
      rw [quittingRootEndpointDifference_eq_gainValue, gainValue,
        hazardOfRoot_quittingBlockCycle, huni, hquit who, hcont who, sub_self]
    rw [hdiff]
    constructor
    · rw [mul_zero]
    · rw [mul_zero, neg_zero]
  · refine ⟨0, continueMass_lt_one_of_pos (uniformHazard_nonneg hp0 0)
      (uniformHazard_le_one hp1 0) (i₀ := 0) ?_⟩
    show (0 : ℝ) < 1 - u
    linarith
  · intro who
    refine Or.inr ?_
    rw [colliderBonusReward_singleton, sub_self, hm0, add_zero]
    exact hs

/-- **The all-quitter block closes the raised-collider table at the bonus its
rate forces.** -/
theorem exists_uniformEquilibriumPayoff_colliderBonusReward_stationary
    (hm0 : m 0 = 0) (hs : 0 ≤ s) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ payoff : Payoff (ZMod 5),
      (quittingGame (colliderBonusReward s low (stationaryBonus s low (∑ d, m d) u) m)
        ).IsUniformEquilibriumPayoff none payoff :=
  ⟨_, isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
    (isQuittingBlockCertificate_uniform hm0 hs hu0 hu1)⟩

/-- The same closure, as emptiness of the terminal exploitability witness. -/
theorem isEmpty_terminalExploitabilityWitness_colliderBonusReward_stationary
    (hm0 : m 0 = 0) (hs : 0 ≤ s) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    IsEmpty (QuittingTerminalExploitabilityWitness
      (colliderBonusReward s low (stationaryBonus s low (∑ d, m d) u) m)) :=
  isEmpty_quittingTerminalExploitabilityWitness_of_exists_uniformEquilibriumPayoff _
    ⟨_, isUniformEquilibriumPayoff_of_isQuittingBlockCertificate
      (isQuittingBlockCertificate_uniform hm0 hs hu0 hu1)⟩

end CirculantColliderBonus
end GameTheory
