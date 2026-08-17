/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.DiffuseTailEffectiveCharge

/-!
# A three-player cyclic solo tail

This module builds one explicit three-player quitting table together with an
explicit exact tail over it: at date `time` the only coordinate that may quit
is `time % 3`, and it quits with probability `1 / (2 ^ time + 2)`.

The table is zero-free: its normalized solo matrix pays `1` on the successor
entry and `-2` on the predecessor entry of the three-cycle.  The hazards are
chosen so that the exact gap-return balance of each coordinate closes across
the two dates it sits out, which is what makes the tail exactly Nash at every
date at accuracy zero rather than merely approximately.

Every coordinate is persistently active, and no two coordinates are ever
active at the same date.  So the dates owned by the third coordinate break
late strict alternation for any pair, while the absence of simultaneous
activity leaves no co-activity floor: the pair dichotomy
`QuittingTailPairSoloDichotomy` fails
(`not_quittingTailPairSoloDichotomy`), and so does the eventually-solo
conclusion `QuittingTailPersistentlySolo`
(`not_quittingTailPersistentlySolo`).

No pair carries a fenced solo window family either
(`quittingNoFencedSoloWindowFamily`), because each coordinate's active dates
are isolated in the cycle.

`pairSoloDichotomy_fails_under_consumer_hypotheses` collects the exact value
recursion, exact endpoint Nash at accuracy zero, interior hazards, zero-freeness
and vanishing one-stage absorption together with those failures.
-/

noncomputable section

namespace GameTheory

namespace QuittingCyclicTripleSoloTail

open QuittingLCPClassification

/-- The three coordinates of the cycle. -/
abbrev Player := Fin 3

/-- The reward table: a solo exit pays its owner `1`, the owner's successor
in the cycle `-1`, and the owner's predecessor `2`.  Every collision pays
`-1` to everybody. -/
def reward (quitters : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  if quitters.1 = {0} then ![1, -1, 2]
  else if quitters.1 = {1} then ![2, 1, -1]
  else if quitters.1 = {2} then ![-1, 2, 1]
  else fun _ => -1

/-- The coordinate that may quit at `time`. -/
def owner (time : ℕ) : Player := ⟨time % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The quit probability at `time`. -/
def hazardValue (time : ℕ) : ℝ := 1 / (2 ^ time + 2)

theorem hazardValue_pos (time : ℕ) : 0 < hazardValue time := by
  have hpow : (0 : ℝ) < 2 ^ time := by positivity
  rw [hazardValue]
  positivity

theorem hazardValue_nonneg (time : ℕ) : 0 ≤ hazardValue time :=
  (hazardValue_pos time).le

theorem hazardValue_lt_one (time : ℕ) : hazardValue time < 1 := by
  have hpow : (0 : ℝ) < 2 ^ time := by positivity
  rw [hazardValue, div_lt_one (by linarith)]
  linarith

theorem hazardValue_le_one (time : ℕ) : hazardValue time ≤ 1 :=
  (hazardValue_lt_one time).le

/-- **The exact gap-return balance of the cycle.**  The successor entry `1`
and the predecessor entry `-2` of the normalized solo matrix balance across
the two dates a coordinate sits out exactly when the hazards obey this
recursion, and `1 / (2 ^ time + 2)` is the solution that vanishes. -/
theorem hazardValue_recursion (time : ℕ) :
    2 * hazardValue (time + 1) * (1 - hazardValue time) = hazardValue time := by
  have hpow : (0 : ℝ) < 2 ^ time := by positivity
  have hone : (2 : ℝ) ^ time + 2 ≠ 0 := by positivity
  have htwo : (2 : ℝ) ^ (time + 1) + 2 ≠ 0 := by positivity
  rw [hazardValue, hazardValue, pow_succ]
  field_simp
  ring

theorem tendsto_hazardValue :
    Filter.Tendsto hazardValue Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun time : ℕ => (2 : ℝ) ^ time + 2) Filter.atTop
      Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 2
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  refine Filter.Tendsto.congr (fun time => ?_) hpow.inv_tendsto_atTop
  simp [hazardValue]

/-- The Boolean law of the quitting coordinate at `time`. -/
def hazard (time : ℕ) : PMF Bool :=
  quittingHazardCoin (hazardValue time) (hazardValue_nonneg time)
    (hazardValue_le_one time)

@[simp] theorem hazard_true (time : ℕ) :
    (hazard time true).toReal = hazardValue time :=
  quittingHazardCoin_true_toReal _ _ _

@[simp] theorem hazard_false (time : ℕ) :
    (hazard time false).toReal = 1 - hazardValue time :=
  quittingHazardCoin_false_toReal _ _ _

/-- The root sequence: at `time` only `owner time` may quit. -/
def roots (time : ℕ) : Player → PMF Bool :=
  quittingSoloStationaryRoot (owner time) (hazard time)

theorem isQuittingSoloRoot_roots (time : ℕ) :
    IsQuittingSoloRoot (roots time) (owner time) := fun _player hplayer =>
  quittingSoloStationaryRoot_apply_other hplayer (hazard time)

/-- The prescribed value: every coordinate is worth `1` except the next
coordinate to quit, which is worth `1 - 2 * hazardValue time`. -/
def value (time : ℕ) : Payoff Player :=
  fun who => if who = owner (time + 1) then 1 - 2 * hazardValue time else 1

/-! ## Arithmetic of the three-cycle -/

theorem owner_val (time : ℕ) : (owner time).val = time % 3 := rfl

/-- The three coordinates visited at `time`, `time + 1` and `time + 2` are
the three coordinates of the cycle, in one of three rotations. -/
theorem owner_rotation (time : ℕ) :
    (owner time = 0 ∧ owner (time + 1) = 1 ∧ owner (time + 2) = 2) ∨
      (owner time = 1 ∧ owner (time + 1) = 2 ∧ owner (time + 2) = 0) ∨
      (owner time = 2 ∧ owner (time + 1) = 0 ∧ owner (time + 2) = 1) := by
  have hmod : time % 3 = 0 ∨ time % 3 = 1 ∨ time % 3 = 2 := by omega
  rcases hmod with hmod | hmod | hmod
  · exact Or.inl ⟨Fin.ext (by simp [owner_val, hmod]),
      Fin.ext (by simp [owner_val]; omega), Fin.ext (by simp [owner_val]; omega)⟩
  · exact Or.inr (Or.inl ⟨Fin.ext (by simp [owner_val, hmod]),
      Fin.ext (by simp [owner_val]; omega), Fin.ext (by simp [owner_val]; omega)⟩)
  · exact Or.inr (Or.inr ⟨Fin.ext (by simp [owner_val, hmod]),
      Fin.ext (by simp [owner_val]; omega), Fin.ext (by simp [owner_val]; omega)⟩)

theorem owner_succ_ne (time : ℕ) : owner (time + 1) ≠ owner time := by
  rcases owner_rotation time with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ <;>
    rw [h0, h1] <;> decide

theorem owner_add_two_ne (time : ℕ) : owner (time + 2) ≠ owner time := by
  rcases owner_rotation time with ⟨h0, -, h2⟩ | ⟨h0, -, h2⟩ | ⟨h0, -, h2⟩ <;>
    rw [h0, h2] <;> decide

theorem owner_add_three (time : ℕ) : owner (time + 3) = owner time :=
  Fin.ext (by simp only [owner_val]; omega)

theorem player_cases (time : ℕ) (who : Player) :
    who = owner time ∨ who = owner (time + 1) ∨ who = owner (time + 2) := by
  rcases owner_rotation time with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
    rw [h0, h1, h2] <;> fin_cases who <;> decide

theorem exists_owner_eq (who : Player) (start : ℕ) :
    ∃ time, start ≤ time ∧ owner time = who := by
  have hlt := who.isLt
  refine ⟨3 * start + who.val, by omega, Fin.ext ?_⟩
  simp only [owner_val]
  omega

/-! ## The reward table in closed form -/

@[simp] theorem soloReward_zero_zero : quittingSoloReward reward 0 0 = 1 := rfl
@[simp] theorem soloReward_zero_one : quittingSoloReward reward 0 1 = -1 := rfl
@[simp] theorem soloReward_zero_two : quittingSoloReward reward 0 2 = 2 := rfl
@[simp] theorem soloReward_one_zero : quittingSoloReward reward 1 0 = 2 := rfl
@[simp] theorem soloReward_one_one : quittingSoloReward reward 1 1 = 1 := rfl
@[simp] theorem soloReward_one_two : quittingSoloReward reward 1 2 = -1 := rfl
@[simp] theorem soloReward_two_zero : quittingSoloReward reward 2 0 = -1 := rfl
@[simp] theorem soloReward_two_one : quittingSoloReward reward 2 1 = 2 := rfl
@[simp] theorem soloReward_two_two : quittingSoloReward reward 2 2 = 1 := rfl

/-- Every collision pays `-1`. -/
theorem collisionReward_eval {first second : Player} (hne : second ≠ first) :
    quittingSingletonCollisionReward reward first second = -1 := by
  fin_cases first <;> fin_cases second <;>
    first
      | exact absurd rfl hne
      | rfl

/-- **The table is zero-free.**  Off the diagonal the normalized solo matrix
takes the value `1` on the successor entry and `-2` on the predecessor entry. -/
theorem zeroFree : QuittingZeroFreeSoloMatrix reward := by
  intro who ownerIndex hne
  rw [normalizedSoloMatrix_eq_soloReward_sub]
  fin_cases who <;> fin_cases ownerIndex <;>
    first
      | exact absurd rfl hne
      | norm_num [quittingSoloReward, reward, Finset.singleton_inj, Fin.ext_iff]

theorem soloReward_self (time : ℕ) :
    quittingSoloReward reward (owner time) (owner time) = 1 := by
  rcases owner_rotation time with ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ <;>
    rw [h0] <;> norm_num

theorem soloReward_next (time : ℕ) :
    quittingSoloReward reward (owner time) (owner (time + 1)) = -1 := by
  rcases owner_rotation time with ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ | ⟨h0, h1, -⟩ <;>
    rw [h0, h1] <;> norm_num

theorem soloReward_prev (time : ℕ) :
    quittingSoloReward reward (owner time) (owner (time + 2)) = 2 := by
  rcases owner_rotation time with ⟨h0, -, h2⟩ | ⟨h0, -, h2⟩ | ⟨h0, -, h2⟩ <;>
    rw [h0, h2] <;> norm_num

/-! ## The prescribed value -/

theorem value_self (time : ℕ) : value time (owner time) = 1 := by
  rw [value, if_neg (Ne.symm (owner_succ_ne time))]

theorem value_next (time : ℕ) :
    value time (owner (time + 1)) = 1 - 2 * hazardValue time := by
  rw [value, if_pos rfl]

theorem value_prev (time : ℕ) : value time (owner (time + 2)) = 1 := by
  rw [value, if_neg (owner_succ_ne (time + 1))]

theorem value_succ_of_owner (time : ℕ) : value (time + 1) (owner time) = 1 := by
  have howner : owner time = owner (time + 1 + 2) := by
    rw [show time + 1 + 2 = time + 3 from by omega, owner_add_three]
  rw [howner]
  exact value_prev (time + 1)

theorem value_succ_of_owner_add_two (time : ℕ) :
    value (time + 1) (owner (time + 2)) = 1 - 2 * hazardValue (time + 1) := by
  have hnext := value_next (time + 1)
  rwa [show time + 1 + 1 = time + 2 from by omega] at hnext

/-! ## The tail is an exact solo tail -/

/-- The prescribed value obeys the exact one-stage recursion of the root
sequence. -/
theorem hpolicy (time : ℕ) :
    value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time) := by
  funext who
  rw [roots, congrFun (quittingRootSuccessorPayoff_solo reward (owner time)
    (hazard time) (value (time + 1))) who, hazard_true, hazard_false]
  rcases player_cases time who with hwho | hwho | hwho <;> subst hwho
  · rw [value_self, soloReward_self, value_succ_of_owner]
    ring
  · rw [value_next, soloReward_next, value_self (time + 1)]
    ring
  · rw [value_prev, soloReward_prev, value_succ_of_owner_add_two]
    linear_combination hazardValue_recursion time

/-- Every root of the sequence is an exact endpoint-Nash root against the
prescribed continuation, at accuracy zero. -/
theorem hnash (time : ℕ) :
    IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time) := by
  have hsolo := isQuittingSoloRoot_roots time
  have hownerRoot : roots time (owner time) = hazard time :=
    quittingSoloStationaryRoot_apply_owner (owner time) (hazard time)
  intro who
  by_cases hwho : who = owner time
  · subst who
    have hdiff : quittingRootEndpointDifference reward (value (time + 1))
        (roots time) (owner time) = 0 := by
      rw [quittingRootEndpointDifference,
        hsolo.quitPayoff_owner reward (value (time + 1)),
        hsolo.continuePayoff_owner reward (value (time + 1)), soloReward_self,
        value_succ_of_owner]
      ring
    rw [hdiff]
    constructor <;> simp
  · have hpure : roots time who = PMF.pure false := hsolo who hwho
    have hfalse : (roots time who false).toReal = 1 := by rw [hpure]; simp
    have htrue : (roots time who true).toReal = 0 := by rw [hpure]; simp
    have hdiff : quittingRootEndpointDifference reward (value (time + 1))
        (roots time) who ≤ 0 := by
      rw [quittingRootEndpointDifference,
        hsolo.quitPayoff_other reward hwho (value (time + 1)),
        hsolo.continuePayoff_other reward hwho (value (time + 1)), hownerRoot,
        hazard_true, hazard_false, collisionReward_eval hwho]
      rcases player_cases time who with hcase | hcase | hcase
      · exact absurd hcase hwho
      · subst who
        rw [soloReward_self (time + 1), soloReward_next, value_self (time + 1)]
        ring_nf
        exact le_refl 0
      · subst who
        rw [soloReward_self (time + 2), soloReward_prev,
          value_succ_of_owner_add_two]
        have hrec := hazardValue_recursion time
        have hpos := hazardValue_pos time
        nlinarith [hrec, hpos]
    refine ⟨?_, ?_⟩
    · rw [hfalse, one_mul]
      exact hdiff
    · rw [htrue, zero_mul]
      norm_num

/-! ## Regularity of the tail -/

theorem hinterior (time : ℕ) (who : Player) :
    0 < (roots time who false).toReal := by
  by_cases hwho : who = owner time
  · subst who
    rw [roots, quittingSoloStationaryRoot_apply_owner, hazard_false]
    linarith [hazardValue_lt_one time]
  · rw [(isQuittingSoloRoot_roots time) who hwho]
    simp

theorem quittingRootAbsorptionMass_roots (time : ℕ) :
    quittingRootAbsorptionMass (roots time) = hazardValue time := by
  rw [roots, quittingRootAbsorptionMass_soloStationaryRoot, hazard_true]

/-- The one-stage absorption mass of the tail vanishes. -/
theorem tendsto_absorptionMass :
    Filter.Tendsto (fun time => quittingRootAbsorptionMass (roots time))
      Filter.atTop (nhds 0) :=
  Filter.Tendsto.congr
    (fun time => (quittingRootAbsorptionMass_roots time).symm) tendsto_hazardValue

/-! ## Every coordinate is persistently active, and no two ever together -/

theorem persistentlyActive (who : Player) :
    QuittingTailPersistentlyActive roots who := by
  intro start
  obtain ⟨time, hle, howner⟩ := exists_owner_eq who start
  refine ⟨time, hle, ?_⟩
  rw [roots, ← howner, quittingSoloStationaryRoot_apply_owner, hazard_true]
  exact hazardValue_pos time

theorem quitProbability_eq_zero_of_ne (time : ℕ) {who : Player}
    (hne : who ≠ owner time) : (roots time who true).toReal = 0 := by
  rw [(isQuittingSoloRoot_roots time) who hne]
  simp

/-- **The pair dichotomy fails on this tail.**  Coordinates `0` and `1` are
both persistently active, yet the dates owned by `2` break late strict
alternation, and no two coordinates are ever active at the same date, so there
is no co-activity floor either. -/
theorem not_quittingTailPairSoloDichotomy :
    ¬ QuittingTailPairSoloDichotomy roots := by
  intro hdichotomy
  rcases hdichotomy 0 1 (by decide) (persistentlyActive 0)
    (persistentlyActive 1) with ⟨base, halternating⟩ | ⟨charge, hcharge, hfloor⟩
  · obtain ⟨time, hle, howner⟩ := exists_owner_eq 2 base
    have hzeroFirst : (roots time 0 true).toReal = 0 :=
      quitProbability_eq_zero_of_ne time (by rw [howner]; decide)
    have hzeroSecond : (roots time 1 true).toReal = 0 :=
      quitProbability_eq_zero_of_ne time (by rw [howner]; decide)
    rcases halternating time hle with ⟨-, hactive⟩ | ⟨-, hactive⟩
    · rw [hzeroFirst] at hactive
      exact absurd hactive (lt_irrefl 0)
    · rw [hzeroSecond] at hactive
      exact absurd hactive (lt_irrefl 0)
  · obtain ⟨time, -, hfirst, hsecond⟩ := hfloor 0
    by_cases howner : owner time = 0
    · have hzeroSecond : (roots time 1 true).toReal = 0 :=
        quitProbability_eq_zero_of_ne time (by rw [howner]; decide)
      rw [hzeroSecond] at hsecond
      linarith
    · have hzeroFirst : (roots time 0 true).toReal = 0 :=
        quitProbability_eq_zero_of_ne time fun heq => howner heq.symm
      rw [hzeroFirst] at hfirst
      linarith

/-- **The eventually-solo conclusion fails on this tail.**  All three
coordinates are persistently active. -/
theorem not_quittingTailPersistentlySolo :
    ¬ QuittingTailPersistentlySolo roots := fun hsolo =>
  absurd (hsolo 0 1 (persistentlyActive 0) (persistentlyActive 1)) (by decide)

/-! ## No fenced solo window family -/

theorem eq_owner_of_active {time : ℕ} {who : Player}
    (hactive : 0 < (roots time who true).toReal) : who = owner time := by
  by_contra hne
  rw [quitProbability_eq_zero_of_ne time hne] at hactive
  exact absurd hactive (lt_irrefl 0)

/-- **No distinct pair carries a fenced solo window family.**  A window's
interior is a run of consecutive dates owned by one coordinate, and in the
three-cycle each coordinate's dates are isolated, so the run has length one;
its closing date is then owned by the third coordinate rather than by the
spectator, which the fence condition forbids.  Distinctness of the pair is not
needed: the fence and the closing date are two dates apart, and no coordinate
owns both. -/
theorem isEmpty_quittingFencedSoloWindowFamily (spectator ownerIndex : Player) :
    IsEmpty (QuittingFencedSoloWindowFamily roots spectator ownerIndex) := by
  refine ⟨fun family => ?_⟩
  have hlength := family.length_pos 0
  have hspectator : spectator = owner (family.fence 0) :=
    eq_owner_of_active (family.fence_active 0)
  have hownerIndex : ownerIndex = owner (family.fence 0 + 1) := by
    have hactive := family.window_active 0 0 hlength
    rw [Nat.add_zero] at hactive
    exact eq_owner_of_active hactive
  have hlengthOne : family.length 0 = 1 := by
    by_contra hlengthNe
    have htwo : 1 < family.length 0 := by omega
    have hsecond : ownerIndex = owner (family.fence 0 + 1 + 1) :=
      eq_owner_of_active (family.window_active 0 1 htwo)
    have hval := congrArg Fin.val (hownerIndex.symm.trans hsecond)
    simp only [owner_val] at hval
    omega
  have hreturn : spectator = owner (family.fence 0 + 1 + family.length 0) :=
    eq_owner_of_active (family.return_active 0)
  rw [hlengthOne] at hreturn
  have hval := congrArg Fin.val (hspectator.symm.trans hreturn)
  simp only [owner_val] at hval
  omega

/-- **The no-family residual holds on this tail.**  Together with
`not_quittingTailPersistentlySolo` this exhibits an exact zero-free tail with
vanishing one-stage absorption on which no distinct pair carries a fenced solo
window family and yet every coordinate is persistently active. -/
theorem quittingNoFencedSoloWindowFamily :
    QuittingNoFencedSoloWindowFamily roots := fun spectator ownerIndex _ =>
  isEmpty_quittingFencedSoloWindowFamily spectator ownerIndex

/-! ## The assembled witness -/

/-- **The pair dichotomy fails under the hypotheses it is consumed with.**
This tail obeys the exact value recursion, is exact endpoint-Nash at accuracy
zero at every date, has interior hazards and a vanishing one-stage absorption
mass, and lives over a zero-free table -- every hypothesis of
`quittingTailPersistentlySolo_of_zeroFree_of_dichotomy` except the pair
dichotomy itself -- and it carries no fenced solo window family for any pair.
Both the dichotomy and the eventually-solo conclusion fail here, so neither the
dichotomy nor the absence of fenced solo window families follows from those
hypotheses, and neither supplies the conclusion on its own. -/
theorem pairSoloDichotomy_fails_under_consumer_hypotheses :
    (∀ time, value time =
        quittingRootSuccessorPayoff reward (value (time + 1)) (roots time)) ∧
      (∀ time, IsεQuittingRootEndpointNash reward (value (time + 1)) 0
        (roots time)) ∧
      (∀ time who, 0 < (roots time who false).toReal) ∧
      QuittingZeroFreeSoloMatrix reward ∧
      Filter.Tendsto (fun time => quittingRootAbsorptionMass (roots time))
          Filter.atTop (nhds 0) ∧
      QuittingNoFencedSoloWindowFamily roots ∧
      ¬ QuittingTailPairSoloDichotomy roots ∧
      ¬ QuittingTailPersistentlySolo roots :=
  ⟨hpolicy, hnash, hinterior, zeroFree, tendsto_absorptionMass,
    quittingNoFencedSoloWindowFamily, not_quittingTailPairSoloDichotomy,
    not_quittingTailPersistentlySolo⟩

end QuittingCyclicTripleSoloTail

end GameTheory
