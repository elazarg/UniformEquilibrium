/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Examples.SolanVieilleBoundaryTable
import UniformEquilibrium.Quitting.Cycles.BlockPeriodicProfile

/-!
# The finite-prefix ledger of a solo-hazard schedule

This file isolates the exact algebra used when at most one player can quit at
each live date of the Solan--Vieille boundary game.  It deliberately stops at
finite prefixes.  Passing from these identities to a uniform lower bound over
all infinite schedules additionally requires either a quantitative discrete
argument or compactness of a suitable path space.

The main identity is `boundarySoloBudgetIdentity`.  It says that the initial
deviation allowance is exactly the sum of own-clock friction, the final
deflated gap, and the unabsorbed mass.  The statement is independent of any
choice of a terminal tail and is therefore reusable in either infinite-path
proof route.
-/

noncomputable section

namespace GameTheory
namespace SolanVieilleBoundary
namespace SoloHazardLedger

open Math.Probability

abbrev Player := Fin 4

/-- The partner in the pairing `{0,1}`, `{2,3}`. -/
def partner : Player → Player := ![1, 0, 3, 2]

@[simp] theorem partner_partner (who : Player) : partner (partner who) = who := by
  fin_cases who <;> rfl

@[simp] theorem partner_ne (who : Player) : partner who ≠ who := by
  fin_cases who <;> decide

/-- Singleton mass prescribed to each possible owner. -/
def prescribedPayoff (mass : Player → ℝ) (who : Player) : ℝ :=
  mass who + 4 * mass (partner who)

/-- Total singleton absorption mass. -/
def totalMass (mass : Player → ℝ) : ℝ := ∑ owner, mass owner

/-- Singleton mass owned by the pair opposite `who`. -/
def oppositeMass (mass : Player → ℝ) (who : Player) : ℝ :=
  totalMass mass - mass who - mass (partner who)

/-- The elementary mass identity behind the deflated-gap budget. -/
theorem oppositeMass_sub_three_partner
    (mass : Player → ℝ) (who : Player) :
    oppositeMass mass who - 3 * mass (partner who) =
      totalMass mass - prescribedPayoff mass who := by
  simp [oppositeMass, prescribedPayoff]
  ring

/-- An atom records its owner, hazard, and on-path first-exit mass.  The
relation between hazard and mass is intentionally external: the ledger
identity itself only needs the two numbers appearing in its update. -/
structure Atom where
  owner : Player
  hazard : ℝ
  mass : ℝ

/-- One deflated-gap update.  Partner mass spends three units, opposite-pair
mass replenishes one unit, and an own atom deflates by its survival factor. -/
def gapStep (who : Player) (atom : Atom) (gap : ℝ) : ℝ :=
  if atom.owner = who then (1 - atom.hazard) * gap
  else if atom.owner = partner who then gap - 3 * atom.mass
  else gap + atom.mass

/-- Friction paid at an own atom. -/
def frictionStep (who : Player) (atom : Atom) (gap : ℝ) : ℝ :=
  if atom.owner = who then gap * atom.hazard else 0

/-- The signed mass contribution to a player's gap. -/
def signedMassStep (who : Player) (atom : Atom) : ℝ :=
  if atom.owner = who then 0
  else if atom.owner = partner who then -3 * atom.mass
  else atom.mass

/-- Adding own-clock friction restores a purely additive mass update. -/
theorem gapStep_add_frictionStep
    (who : Player) (atom : Atom) (gap : ℝ) :
    gapStep who atom gap + frictionStep who atom gap =
      gap + signedMassStep who atom := by
  unfold gapStep frictionStep signedMassStep
  split_ifs <;> ring

/-- Gap after a finite atom word. -/
def gapAfter (who : Player) : List Atom → ℝ → ℝ
  | [], gap => gap
  | atom :: atoms, gap => gapAfter who atoms (gapStep who atom gap)

/-- Accumulated own-clock friction along a finite atom word. -/
def friction (who : Player) : List Atom → ℝ → ℝ
  | [], _ => 0
  | atom :: atoms, gap =>
      frictionStep who atom gap + friction who atoms (gapStep who atom gap)

/-- Accumulated signed mass contribution along a finite atom word. -/
def signedMass (who : Player) (atoms : List Atom) : ℝ :=
  (atoms.map (signedMassStep who)).sum

/-- Every prefix gap, including the empty prefix, is nonnegative. -/
def PrefixGapsNonnegative
    (who : Player) (atoms : List Atom) (initial : ℝ) : Prop :=
  ∀ xs, xs <+: atoms → 0 ≤ gapAfter who xs initial

/-- Prefix nonnegativity descends to the tail after one update. -/
theorem PrefixGapsNonnegative.tail
    {who : Player} {atom : Atom} {atoms : List Atom} {initial : ℝ}
    (h : PrefixGapsNonnegative who (atom :: atoms) initial) :
    PrefixGapsNonnegative who atoms (gapStep who atom initial) := by
  intro xs hxs
  have hcons : atom :: xs <+: atom :: atoms :=
    List.cons_prefix_cons.mpr ⟨rfl, hxs⟩
  simpa [gapAfter] using h (atom :: xs) hcons

/-- Nonnegative hazards and prefix gaps make accumulated friction
nonnegative. -/
theorem friction_nonneg
    (who : Player) (atoms : List Atom) (initial : ℝ)
    (hhazard : ∀ atom ∈ atoms, 0 ≤ atom.hazard)
    (hgaps : PrefixGapsNonnegative who atoms initial) :
    0 ≤ friction who atoms initial := by
  induction atoms generalizing initial with
  | nil => simp [friction]
  | cons atom atoms ih =>
      rw [friction]
      have hinitial : 0 ≤ initial := hgaps [] (by simp)
      have hstep : 0 ≤ frictionStep who atom initial := by
        unfold frictionStep
        split
        · exact mul_nonneg hinitial (hhazard atom (by simp))
        · exact le_rfl
      have htail := ih (gapStep who atom initial)
        (fun later hlater => hhazard later (by simp [hlater])) hgaps.tail
      linarith

/-- The finite-prefix telescoping identity. -/
theorem gapAfter_add_friction
    (who : Player) (atoms : List Atom) (initial : ℝ) :
    gapAfter who atoms initial + friction who atoms initial =
      initial + signedMass who atoms := by
  induction atoms generalizing initial with
  | nil => simp [gapAfter, friction, signedMass]
  | cons atom atoms ih =>
      rw [gapAfter, friction]
      have htail := ih (gapStep who atom initial)
      have hstep := gapStep_add_frictionStep who atom initial
      simp only [signedMass, List.map_cons, List.sum_cons]
      simp only [signedMass] at htail
      linarith

/-- Owner-class mass carried by a finite atom word. -/
def ownerMass (atoms : List Atom) (owner : Player) : ℝ :=
  (atoms.map fun atom => if atom.owner = owner then atom.mass else 0).sum

@[simp] theorem ownerMass_nil (owner : Player) : ownerMass [] owner = 0 := rfl

@[simp] theorem ownerMass_cons (atom : Atom) (atoms : List Atom) (owner : Player) :
    ownerMass (atom :: atoms) owner =
      (if atom.owner = owner then atom.mass else 0) + ownerMass atoms owner := by
  simp [ownerMass]

/-- Total mass is the sum of the atom masses. -/
theorem totalMass_ownerMass (atoms : List Atom) :
    totalMass (ownerMass atoms) = (atoms.map Atom.mass).sum := by
  induction atoms with
  | nil => simp [totalMass]
  | cons atom atoms ih =>
      rcases atom with ⟨owner, hazard, mass⟩
      simp [totalMass, Fin.sum_univ_four] at ih
      simp only [totalMass, Fin.sum_univ_four, ownerMass_cons,
        List.map_cons, List.sum_cons]
      fin_cases owner <;> simp at ih ⊢ <;> linarith

/-- The signed list contribution is exactly opposite mass minus three times
partner mass. -/
theorem signedMass_eq (who : Player) (atoms : List Atom) :
    signedMass who atoms =
      oppositeMass (ownerMass atoms) who - 3 * ownerMass atoms (partner who) := by
  induction atoms with
  | nil =>
      simp [signedMass, oppositeMass, totalMass, ownerMass]
  | cons atom atoms ih =>
      rcases atom with ⟨owner, hazard, mass⟩
      simp only [signedMass, List.map_cons, List.sum_cons, ownerMass_cons]
      change signedMassStep who ⟨owner, hazard, mass⟩ + signedMass who atoms = _
      rw [ih]
      unfold signedMassStep oppositeMass totalMass
      simp only [Fin.sum_univ_four]
      fin_cases who <;> fin_cases owner <;>
        simp [partner] <;> ring

/-- **Finite-prefix deflated-gap budget.**  If the initial gap is the
prescribed singleton slack plus an allowance `epsilon`, then the allowance
splits exactly into own-clock friction, the final gap, and unabsorbed mass. -/
theorem boundarySoloBudgetIdentity
    (who : Player) (atoms : List Atom) (epsilon : ℝ) :
    epsilon =
      friction who atoms
          (prescribedPayoff (ownerMass atoms) who - 1 + epsilon) +
        gapAfter who atoms
          (prescribedPayoff (ownerMass atoms) who - 1 + epsilon) +
        (1 - totalMass (ownerMass atoms)) := by
  have htelescope := gapAfter_add_friction who atoms
    (prescribedPayoff (ownerMass atoms) who - 1 + epsilon)
  rw [signedMass_eq, oppositeMass_sub_three_partner] at htelescope
  linarith

/-- Nonnegative final gap and friction force the unabsorbed-mass estimate. -/
theorem one_sub_totalMass_le_epsilon
    (who : Player) (atoms : List Atom) (epsilon : ℝ)
    (hfriction : 0 ≤ friction who atoms
      (prescribedPayoff (ownerMass atoms) who - 1 + epsilon))
    (hgap : 0 ≤ gapAfter who atoms
      (prescribedPayoff (ownerMass atoms) who - 1 + epsilon)) :
    1 - totalMass (ownerMass atoms) ≤ epsilon := by
  rw [boundarySoloBudgetIdentity who atoms epsilon]
  linarith

/-- Under the same hypotheses, own-clock friction is bounded by the entire
deviation allowance whenever unabsorbed mass is nonnegative. -/
theorem friction_le_epsilon
    (who : Player) (atoms : List Atom) (epsilon : ℝ)
    (hgap : 0 ≤ gapAfter who atoms
      (prescribedPayoff (ownerMass atoms) who - 1 + epsilon))
    (hmass : totalMass (ownerMass atoms) ≤ 1) :
    friction who atoms
        (prescribedPayoff (ownerMass atoms) who - 1 + epsilon) ≤ epsilon := by
  have hid := boundarySoloBudgetIdentity who atoms epsilon
  linarith

/-- Inversion of the two singleton payoff equations within each partner
pair. -/
theorem ownerMass_eq_of_slack
    (mass slack : Player → ℝ)
    (hslack : ∀ who, slack who = prescribedPayoff mass who - 1)
    (who : Player) :
    mass who = (3 + 4 * slack (partner who) - slack who) / 15 := by
  have hwho := hslack who
  have hpartner := hslack (partner who)
  fin_cases who <;> simp [prescribedPayoff, partner] at hwho hpartner ⊢ <;>
    linarith

/-- Every singleton absorption row has total social payoff `5`. -/
theorem sum_prescribedPayoff (mass : Player → ℝ) :
    ∑ who, prescribedPayoff mass who = 5 * totalMass mass := by
  simp only [Fin.sum_univ_four, prescribedPayoff, totalMass]
  simp [partner]
  ring

/-- The four payoff slacks sum to five times absorbed singleton mass minus
the four unit quit-now floors. -/
theorem sum_slack_eq_five_mul_totalMass_sub_four
    (mass slack : Player → ℝ)
    (hslack : ∀ who, slack who = prescribedPayoff mass who - 1) :
    ∑ who, slack who = 5 * totalMass mass - 4 := by
  calc
    ∑ who, slack who = ∑ who, (prescribedPayoff mass who - 1) := by
      apply Finset.sum_congr rfl
      intro who _
      exact hslack who
    _ = (∑ who, prescribedPayoff mass who) - 4 := by
      simp only [Fin.sum_univ_four]
      ring
    _ = 5 * totalMass mass - 4 := by rw [sum_prescribedPayoff]

/-- At full singleton absorption the four payoff slacks sum to one. -/
theorem sum_slack_eq_one_of_totalMass_eq_one
    (mass slack : Player → ℝ)
    (hslack : ∀ who, slack who = prescribedPayoff mass who - 1)
    (hfull : totalMass mass = 1) :
    ∑ who, slack who = 1 := by
  rw [sum_slack_eq_five_mul_totalMass_sub_four mass slack hslack, hfull]
  norm_num

/-- At an exact fully absorbed floor, every owner carries at least `2/15`
singleton mass. -/
theorem two_fifteenths_le_ownerMass_of_exact_floor
    (mass slack : Player → ℝ)
    (hslack : ∀ who, slack who = prescribedPayoff mass who - 1)
    (hnonneg : ∀ who, 0 ≤ slack who)
    (hsum : ∑ who, slack who = 1)
    (who : Player) :
    (2 : ℝ) / 15 ≤ mass who := by
  rw [ownerMass_eq_of_slack mass slack hslack who]
  have hle : slack who ≤ 1 := by
    have h0 := hnonneg 0
    have h1 := hnonneg 1
    have h2 := hnonneg 2
    have h3 := hnonneg 3
    rw [Fin.sum_univ_four] at hsum
    fin_cases who
    · change slack 0 ≤ 1
      linarith
    · change slack 1 ≤ 1
      linarith
    · change slack 2 ≤ 1
      linarith
    · change slack 3 ≤ 1
      linarith
  have hp := hnonneg (partner who)
  linarith

/-- Full absorption and the four unit payoff floors directly force the
`2/15` lower bound on every singleton owner mass. -/
theorem two_fifteenths_le_ownerMass_of_full_absorption
    (mass : Player → ℝ)
    (hfull : totalMass mass = 1)
    (hfloor : ∀ who, 1 ≤ prescribedPayoff mass who)
    (who : Player) :
    (2 : ℝ) / 15 ≤ mass who := by
  let slack : Player → ℝ := fun player => prescribedPayoff mass player - 1
  have hslack : ∀ player, slack player = prescribedPayoff mass player - 1 :=
    fun _ => rfl
  have hnonneg : ∀ player, 0 ≤ slack player := by
    intro player
    dsimp [slack]
    linarith [hfloor player]
  exact two_fifteenths_le_ownerMass_of_exact_floor mass slack hslack hnonneg
    (sum_slack_eq_one_of_totalMass_eq_one mass slack hslack hfull) who

/-- The same `2/15` conclusion fed directly by a fully absorbed finite atom
word and its four prescribed payoff floors. -/
theorem two_fifteenths_le_finite_ownerMass_of_full_absorption
    (atoms : List Atom)
    (hfull : totalMass (ownerMass atoms) = 1)
    (hfloor : ∀ who, 1 ≤ prescribedPayoff (ownerMass atoms) who)
    (who : Player) :
    (2 : ℝ) / 15 ≤ ownerMass atoms who :=
  two_fifteenths_le_ownerMass_of_full_absorption
    (ownerMass atoms) hfull hfloor who

/-! ## Canonical semantic schedule -/

/-- A semantic solo-hazard schedule: one owner and one scalar hazard at each
date, with the scalar constrained to `[0,1]`. -/
structure Schedule where
  owner : ℕ → Player
  hazard : ℕ → ℝ
  hazard_nonneg : ∀ time, 0 ≤ hazard time
  hazard_le_one : ∀ time, hazard time ≤ 1

/-- The literal product root induced by a solo-hazard schedule. -/
def Schedule.roots (schedule : Schedule) (time : ℕ) : Player → PMF Bool :=
  quittingSoloStationaryRoot (schedule.owner time)
    (quittingHazardCoin (schedule.hazard time)
      (schedule.hazard_nonneg time) (schedule.hazard_le_one time))

@[simp] theorem Schedule.roots_owner_true_toReal
    (schedule : Schedule) (time : ℕ) :
    (schedule.roots time (schedule.owner time) true).toReal =
      schedule.hazard time := by
  simp [Schedule.roots, quittingHazardCoin_true_toReal]

theorem Schedule.roots_other
    (schedule : Schedule) (time : ℕ) (other : Player)
    (hother : other ≠ schedule.owner time) :
    schedule.roots time other = PMF.pure false := by
  exact quittingSoloStationaryRoot_apply_other hother _

/-- Thus the definition represents exactly an at-most-one-owner row at every
date; no periodicity or positivity assumption is present. -/
theorem Schedule.roots_isolated
    (schedule : Schedule) (time : ℕ) :
    ∀ other, other ≠ schedule.owner time →
      schedule.roots time other = PMF.pure false :=
  schedule.roots_other time

end SoloHazardLedger
end SolanVieilleBoundary
end GameTheory
