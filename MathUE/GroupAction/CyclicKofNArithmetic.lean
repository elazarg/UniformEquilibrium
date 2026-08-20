/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Arithmetic and cyclic structure of `K/N` activation schedules

This file isolates the combinatorics behind schedules in which exactly `K`
of `N` players are active at a phase.  The first invariant is a double count:
if a finite schedule has constant phase load `K` and every player has the
same load `r`, then

`K * numberOfPhases = N * r`.

Consequently the reduced denominator `N / gcd K N` divides the number of
phases.  This is the exact arithmetic obstruction suggested by the phrase
"`K` out of `N`".  It is independent of payoffs and therefore applies to any
balanced quitting-support schedule.

The second part constructs the canonical translation schedule of a block in
a finite additive group.  Every translate has the same size and every player
occurs equally often.  Thus the arithmetic lower bound is attained by the
full cyclic translation schedule (and can sometimes be shortened precisely
when the block has translation symmetry).
-/

namespace Math

namespace CyclicKofNArithmetic

open scoped BigOperators Pointwise

noncomputable section

section Incidence

variable {Phase Player : Type*}
variable [Fintype Phase] [Fintype Player] [DecidableEq Player]

/-- Number of active players at one phase. -/
def phaseLoad (active : Phase → Finset Player) (t : Phase) : ℕ :=
  (active t).card

/-- Number of phases at which one player is active. -/
def playerLoad (active : Phase → Finset Player) (i : Player) : ℕ :=
  (Finset.univ.filter fun t => i ∈ active t).card

/-- A `K/N` schedule is balanced when every phase has load `K` and every
player has one common appearance count `r`. -/
def IsBalanced (active : Phase → Finset Player) (K r : ℕ) : Prop :=
  (∀ t, phaseLoad active t = K) ∧
    ∀ i, playerLoad active i = r

/-- Double-count the phase-player incidence relation. -/
theorem sum_phaseLoad_eq_sum_playerLoad (active : Phase → Finset Player) :
    (∑ t, phaseLoad active t) = ∑ i, playerLoad active i := by
  calc
    (∑ t, phaseLoad active t) =
        ∑ t, ∑ i : Player, if i ∈ active t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      simp [phaseLoad]
    _ = ∑ i, ∑ t, if i ∈ active t then 1 else 0 := Finset.sum_comm
    _ = ∑ i, playerLoad active i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [playerLoad]

/-- The fundamental balance equation for a finite `K/N` schedule. -/
theorem IsBalanced.incidenceEquation {active : Phase → Finset Player} {K r : ℕ}
    (h : IsBalanced active K r) :
    K * Fintype.card Phase = Fintype.card Player * r := by
  calc
    K * Fintype.card Phase = ∑ _t : Phase, K := by simp [mul_comm]
    _ = ∑ t, phaseLoad active t := by
      apply Finset.sum_congr rfl
      intro t _
      exact (h.1 t).symm
    _ = ∑ i, playerLoad active i := sum_phaseLoad_eq_sum_playerLoad active
    _ = ∑ _i : Player, r := by
      apply Finset.sum_congr rfl
      intro i _
      exact h.2 i
    _ = Fintype.card Player * r := by simp

end Incidence

section Arithmetic

/-- Remove the common divisor from an exact `K * L = N * r` balance
equation. -/
theorem reduced_incidenceEquation {K N L r : ℕ} (hN : 0 < N)
    (h : K * L = N * r) :
    (K / K.gcd N) * L = (N / K.gcd N) * r := by
  have hd : 0 < K.gcd N := Nat.gcd_pos_of_pos_right K hN
  have hK : K.gcd N * (K / K.gcd N) = K :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left K N)
  have hN' : K.gcd N * (N / K.gcd N) = N :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right K N)
  have hscaled :
      K.gcd N * ((K / K.gcd N) * L) =
        K.gcd N * ((N / K.gcd N) * r) := by
    calc
      K.gcd N * ((K / K.gcd N) * L) =
          (K.gcd N * (K / K.gcd N)) * L := by rw [mul_assoc]
      _ = K * L := by rw [hK]
      _ = N * r := h
      _ = (K.gcd N * (N / K.gcd N)) * r := by rw [hN']
      _ = K.gcd N * ((N / K.gcd N) * r) := by rw [mul_assoc]
  exact Nat.mul_left_cancel hd hscaled

/-- **Reduced-denominator law.**  Any exact balanced `K/N` schedule has a
number of phases divisible by `N / gcd K N`. -/
theorem reducedPopulation_dvd_period {K N L r : ℕ} (hN : 0 < N)
    (h : K * L = N * r) :
    N / K.gcd N ∣ L := by
  have hred := reduced_incidenceEquation hN h
  have hdvd : N / K.gcd N ∣ (K / K.gcd N) * L :=
    ⟨r, hred⟩
  have hcoprime : Nat.Coprime (K / K.gcd N) (N / K.gcd N) :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right K hN)
  exact hcoprime.symm.dvd_of_dvd_mul_left hdvd

/-- Coprime `K` and `N` force a full multiple of `N` phases. -/
theorem population_dvd_period_of_coprime {K N L r : ℕ}
    (hcoprime : Nat.Coprime K N) (h : K * L = N * r) :
    N ∣ L := by
  have hdvd : N ∣ K * L := ⟨r, h⟩
  exact hcoprime.symm.dvd_of_dvd_mul_left hdvd

/-- The balance equation also determines the common number of appearances. -/
theorem reducedActive_dvd_appearances {K N L r : ℕ} (hN : 0 < N)
    (h : K * L = N * r) :
    K / K.gcd N ∣ r := by
  have hred := reduced_incidenceEquation hN h
  have hdvd : K / K.gcd N ∣ (N / K.gcd N) * r :=
    ⟨L, by simpa [mul_comm] using hred.symm⟩
  have hcoprime : Nat.Coprime (K / K.gcd N) (N / K.gcd N) :=
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right K hN)
  exact hcoprime.dvd_of_dvd_mul_left hdvd

/-- Package the reduced-denominator law directly for balanced schedules. -/
theorem IsBalanced.reducedPopulation_dvd_card
    {Phase Player : Type*} [Fintype Phase] [Fintype Player]
    [DecidableEq Player]
    {active : Phase → Finset Player} {K r : ℕ}
    (hPlayer : 0 < Fintype.card Player)
    (h : IsBalanced active K r) :
    Fintype.card Player / K.gcd (Fintype.card Player) ∣ Fintype.card Phase :=
  reducedPopulation_dvd_period hPlayer h.incidenceEquation

/-- If `K` is coprime to the population, a balanced schedule contains at
least `N` phases unless the phase type is empty. -/
theorem IsBalanced.population_le_card_phase_of_coprime
    {Phase Player : Type*} [Fintype Phase] [Fintype Player]
    [DecidableEq Player]
    {active : Phase → Finset Player} {K r : ℕ}
    (hPhase : 0 < Fintype.card Phase)
    (hcoprime : Nat.Coprime K (Fintype.card Player))
    (h : IsBalanced active K r) :
    Fintype.card Player ≤ Fintype.card Phase := by
  exact Nat.le_of_dvd hPhase
    (population_dvd_period_of_coprime hcoprime h.incidenceEquation)

end Arithmetic

section TranslationOrbit

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]

/-- The phases of the cyclic block schedule are the distinct translates of
one base block.  Repeated translates are identified automatically. -/
abbrev TranslationPhase (A : Finset G) : Type _ :=
  AddAction.orbit G A

instance translationPhaseFintype (A : Finset G) :
    Fintype (TranslationPhase A) :=
  Fintype.ofFinite (TranslationPhase A)

instance translationPhaseNonempty (A : Finset G) :
    Nonempty (TranslationPhase A) :=
  Set.nonempty_coe_sort.mpr (AddAction.nonempty_orbit A)

/-- At an orbit phase, the active set is the corresponding translate of the
base block. -/
def orbitSchedule (A : Finset G) : TranslationPhase A → Finset G :=
  fun B => B.1

omit [Fintype G] in
/-- Every distinct translate has the cardinality of the base block. -/
theorem orbitSchedule_phaseLoad (A : Finset G) (B : TranslationPhase A) :
    phaseLoad (orbitSchedule A) B = A.card := by
  rcases B.2 with ⟨g, hg⟩
  change B.1.card = A.card
  rw [← hg]
  exact Finset.card_vadd_finset g A

/-- Translating all orbit phases by `y - x` bijects the phases containing
`x` with the phases containing `y`. -/
theorem orbitSchedule_playerLoad_eq (A : Finset G) (x y : G) :
    playerLoad (orbitSchedule A) x = playerLoad (orbitSchedule A) y := by
  unfold playerLoad
  let e : TranslationPhase A ≃ TranslationPhase A :=
    AddAction.toPerm (β := TranslationPhase A) (y - x)
  apply Finset.card_equiv e
  intro B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  dsimp [e]
  change x ∈ B.1 ↔ y ∈ ((y - x) +ᵥ B).1
  change x ∈ B.1 ↔ y ∈ (y - x) +ᵥ B.1
  simpa only [vadd_eq_add, sub_add_cancel] using
    (Finset.vadd_mem_vadd_finset_iff (s := B.1) (b := x) (y - x)).symm

/-- The schedule of distinct translates is balanced.  This remains true
when the block has a nontrivial period and hence fewer than `|G|` distinct
translates. -/
theorem orbitSchedule_isBalanced (A : Finset G) :
    IsBalanced (orbitSchedule A) A.card
      (playerLoad (orbitSchedule A) 0) := by
  constructor
  · exact orbitSchedule_phaseLoad A
  · intro x
    exact orbitSchedule_playerLoad_eq A x 0

/-- The reduced population divides the number of *distinct* translates, not
merely the length of the unreduced full translation list. -/
theorem reducedPopulation_dvd_card_translationPhase (A : Finset G) :
    Fintype.card G / A.card.gcd (Fintype.card G) ∣
      Fintype.card (TranslationPhase A) := by
  exact (orbitSchedule_isBalanced A).reducedPopulation_dvd_card
    (Fintype.card_pos_iff.mpr inferInstance)

/-- Orbit-stabilizer for a block under translation. -/
theorem translationOrbit_mul_stabilizer (A : Finset G) :
    Fintype.card (TranslationPhase A) *
        Fintype.card (AddAction.stabilizer G A) =
      Fintype.card G :=
  AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup G A

/-- Exact orbit length: the number of distinct translates is the population
divided by the translation-stabilizer size. -/
theorem card_translationPhase_eq_div_stabilizer (A : Finset G) :
    Fintype.card (TranslationPhase A) =
      Fintype.card G / Fintype.card (AddAction.stabilizer G A) := by
  have hd : 0 < Fintype.card (AddAction.stabilizer G A) :=
    Fintype.card_pos_iff.mpr inferInstance
  calc
    Fintype.card (TranslationPhase A) =
        (Fintype.card (AddAction.stabilizer G A) *
          Fintype.card (TranslationPhase A)) /
            Fintype.card (AddAction.stabilizer G A) :=
      (Nat.mul_div_right _ hd).symm
    _ = (Fintype.card (TranslationPhase A) *
          Fintype.card (AddAction.stabilizer G A)) /
            Fintype.card (AddAction.stabilizer G A) := by
      rw [mul_comm]
    _ = Fintype.card G /
          Fintype.card (AddAction.stabilizer G A) := by
      rw [translationOrbit_mul_stabilizer]

/-- The size of the translation stabilizer divides the block size.  Together
with orbit-stabilizer this says that every possible cyclic collapse is
controlled by a divisor of `gcd(K,N)`. -/
theorem card_translationStabilizer_dvd_card_block (A : Finset G) :
    Fintype.card (AddAction.stabilizer G A) ∣ A.card := by
  let L := Fintype.card (TranslationPhase A)
  let d := Fintype.card (AddAction.stabilizer G A)
  let r := playerLoad (orbitSchedule A) 0
  have hL : 0 < L := Fintype.card_pos_iff.mpr inferInstance
  have hinc : A.card * L = Fintype.card G * r :=
    (orbitSchedule_isBalanced A).incidenceEquation
  have horbit : L * d = Fintype.card G := translationOrbit_mul_stabilizer A
  have hscaled : L * A.card = L * (d * r) := by
    calc
      L * A.card = A.card * L := by rw [mul_comm]
      _ = Fintype.card G * r := hinc
      _ = (L * d) * r := by rw [horbit]
      _ = L * (d * r) := by rw [mul_assoc]
  have hp : A.card = d * r := Nat.mul_left_cancel hL hscaled
  exact ⟨r, hp⟩

/-- Exact gcd restriction on cyclic symmetry: stabilizer size divides both
the block size and the population size. -/
theorem card_translationStabilizer_dvd_gcd (A : Finset G) :
    Fintype.card (AddAction.stabilizer G A) ∣
      A.card.gcd (Fintype.card G) := by
  apply Nat.dvd_gcd (card_translationStabilizer_dvd_card_block A)
  refine ⟨Fintype.card (TranslationPhase A), ?_⟩
  simpa [mul_comm] using (translationOrbit_mul_stabilizer A).symm

/-- Intrinsic period classification for a translated block: its number of
distinct phases is `|G| / d` for a positive divisor `d` of both the block
size and the population size. The canonical factor is the translation
stabilizer cardinality. -/
theorem exists_positive_commonDivisor_card_translationPhase_eq_div
    (A : Finset G) :
    ∃ d : ℕ,
      0 < d ∧ d ∣ A.card.gcd (Fintype.card G) ∧
        Fintype.card (TranslationPhase A) = Fintype.card G / d := by
  refine ⟨Fintype.card (AddAction.stabilizer G A), ?_,
    card_translationStabilizer_dvd_gcd A, ?_⟩
  · exact Fintype.card_pos_iff.mpr inferInstance
  · exact card_translationPhase_eq_div_stabilizer A

/-- If the block size and population are coprime, no cyclic collapse is
possible: all `|G|` translates are distinct. -/
theorem card_translationPhase_eq_card_of_coprime (A : Finset G)
    (hcoprime : Nat.Coprime A.card (Fintype.card G)) :
    Fintype.card (TranslationPhase A) = Fintype.card G := by
  have hdvd : Fintype.card (AddAction.stabilizer G A) ∣ 1 := by
    simpa [hcoprime.gcd_eq_one] using card_translationStabilizer_dvd_gcd A
  have hstabilizer : Fintype.card (AddAction.stabilizer G A) = 1 :=
    Nat.eq_one_of_dvd_one hdvd
  have horbit := translationOrbit_mul_stabilizer A
  rw [hstabilizer, mul_one] at horbit
  exact horbit

/-- One-at-a-time cyclic activation never collapses: a singleton block has
one distinct phase for every player. -/
theorem card_translationPhase_eq_card_of_singleton (A : Finset G)
    (hA : A.card = 1) :
    Fintype.card (TranslationPhase A) = Fintype.card G := by
  apply card_translationPhase_eq_card_of_coprime A
  simp [hA]

/-- Nor does the co-singleton schedule collapse: activating everybody except
one player also requires all population phases. -/
theorem card_translationPhase_eq_card_of_cosingleton (A : Finset G)
    (hA : A.card + 1 = Fintype.card G) :
    Fintype.card (TranslationPhase A) = Fintype.card G := by
  apply card_translationPhase_eq_card_of_coprime A
  rw [← hA]
  simp

/-- For prime population size, every nontrivial `K`-block has a full orbit.
This is the cleanest prime-size version of the `K/N` structure theorem. -/
theorem card_translationPhase_eq_card_of_prime
    (A : Finset G) (hprime : Nat.Prime (Fintype.card G))
    (hnonempty : 0 < A.card) (hproper : A.card < Fintype.card G) :
    Fintype.card (TranslationPhase A) = Fintype.card G := by
  apply card_translationPhase_eq_card_of_coprime A
  have hnotdvd : ¬Fintype.card G ∣ A.card := by
    intro hdvd
    exact (Nat.not_le_of_lt hproper) (Nat.le_of_dvd hnonempty hdvd)
  exact (hprime.coprime_iff_not_dvd.mpr hnotdvd).symm

/-! ## Prime and four-active collapse classifications -/

/-- If the block size itself is prime, the only stabilizer sizes are `1` and
the whole block size. -/
theorem card_translationStabilizer_eq_one_or_eq_card_of_prime
    (A : Finset G) (hprime : Nat.Prime A.card) :
    Fintype.card (AddAction.stabilizer G A) = 1 ∨
      Fintype.card (AddAction.stabilizer G A) = A.card :=
  (Nat.dvd_prime hprime).mp (card_translationStabilizer_dvd_card_block A)

/-- For prime `K`, a cyclic `K/N` schedule has either the full `N` phases or
the maximally collapsed `N/K` phases.  There is no intermediate collapse. -/
theorem card_translationPhase_eq_card_or_div_card_of_prime
    (A : Finset G) (hprime : Nat.Prime A.card) :
    Fintype.card (TranslationPhase A) = Fintype.card G ∨
      Fintype.card (TranslationPhase A) = Fintype.card G / A.card := by
  rcases card_translationStabilizer_eq_one_or_eq_card_of_prime A hprime with
      hstabilizer | hstabilizer
  · left
    rw [card_translationPhase_eq_div_stabilizer, hstabilizer, Nat.div_one]
  · right
    rw [card_translationPhase_eq_div_stabilizer, hstabilizer]

/-- Elementary divisor classification used by the `4/N` corollary. -/
theorem eq_one_or_two_or_four_of_dvd_four {d : ℕ} (hd : d ∣ 4) :
    d = 1 ∨ d = 2 ∨ d = 4 := by
  have hdle : d ≤ 4 := Nat.le_of_dvd (by decide) hd
  interval_cases d
  · norm_num at hd
  · simp
  · simp
  · norm_num at hd
  · simp

/-- **Complete `4/N` cyclic classification.**  Four-active translated blocks
can only have period `N`, `N/2`, or `N/4`. -/
theorem card_translationPhase_eq_card_or_half_or_quarter
    (A : Finset G) (hA : A.card = 4) :
    Fintype.card (TranslationPhase A) = Fintype.card G ∨
      Fintype.card (TranslationPhase A) = Fintype.card G / 2 ∨
        Fintype.card (TranslationPhase A) = Fintype.card G / 4 := by
  have hdvd : Fintype.card (AddAction.stabilizer G A) ∣ 4 := by
    simpa [hA] using card_translationStabilizer_dvd_card_block A
  rcases eq_one_or_two_or_four_of_dvd_four hdvd with hstabilizer |
      hstabilizer | hstabilizer
  · left
    rw [card_translationPhase_eq_div_stabilizer, hstabilizer, Nat.div_one]
  · right; left
    rw [card_translationPhase_eq_div_stabilizer, hstabilizer]
  · right; right
    rw [card_translationPhase_eq_div_stabilizer, hstabilizer]

/-! ## Complement duality -/

/-- Translation commutes with finite-set complement because translation is a
permutation of the population. -/
theorem vadd_finset_compl (g : G) (A : Finset G) :
    g +ᵥ Aᶜ = (g +ᵥ A)ᶜ := by
  ext x
  simp only [Finset.mem_compl]
  rw [← Finset.neg_vadd_mem_iff, ← Finset.neg_vadd_mem_iff]
  simp

/-- A block and its complement have exactly the same translation
stabilizer. -/
theorem translationStabilizer_compl (A : Finset G) :
    AddAction.stabilizer G Aᶜ = AddAction.stabilizer G A := by
  ext g
  change (g +ᵥ Aᶜ = Aᶜ) ↔ (g +ᵥ A = A)
  rw [vadd_finset_compl]
  constructor
  · intro h
    have hc := congrArg (fun B : Finset G => Bᶜ) h
    simpa using hc
  · intro h
    rw [h]

/-- **Complement duality.**  A `K/N` translated block and its
`(N-K)/N` complement have the same number of distinct phases. -/
theorem card_translationPhase_compl (A : Finset G) :
    Fintype.card (TranslationPhase Aᶜ) =
      Fintype.card (TranslationPhase A) := by
  have hcompl := translationOrbit_mul_stabilizer Aᶜ
  have hstabCard :
      Fintype.card (AddAction.stabilizer G Aᶜ) =
        Fintype.card (AddAction.stabilizer G A) := by
    simpa only [Nat.card_eq_fintype_card] using
      congrArg (fun H : AddSubgroup G => Nat.card H)
        (translationStabilizer_compl A)
  rw [hstabCard] at hcompl
  have hbase := translationOrbit_mul_stabilizer A
  have hd : 0 < Fintype.card (AddAction.stabilizer G A) :=
    Fintype.card_pos_iff.mpr inferInstance
  exact Nat.mul_right_cancel hd (hcompl.trans hbase.symm)

end TranslationOrbit

end

end CyclicKofNArithmetic

end Math
