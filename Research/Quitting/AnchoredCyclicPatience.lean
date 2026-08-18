/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.Normalization

/-!
# Patience along an anchored cyclic single-quitter schedule

A cyclic single-quitter schedule designates one quitter per phase and lets the
cycle survive each phase with a probability strictly below one.  Its phase
values solve the one-step renewal recursion

`Φ^k y = (1 - β_k) * r_y({w_k}) + β_k * Φ^{k+1} y`.

Two side conditions are imposed on top of the recursion.  The *anchor* at phase
`k` says that the designated quitter `w_k` is exactly indifferent one phase
later, `Φ^{k+1} (w_k) = r_{w_k}({w_k})`; *patience* says that no player's phase
value ever falls below its own solo payoff.  This file bundles the recursion,
the anchors and patience as a structure and reads three consequences off it,
each valid for every period, every schedule — repetitions allowed — and every
nonuniform survival vector.

## Scope of the patience condition

The two side conditions differ in kind.  The anchor is an exact equality at the
given survivals: the phase's own quitter compares its solo self payoff with the
next phase's value, and since every other player continues with certainty at
that phase no hazard enters the comparison.  It is the equality that the
fixed-hazard exactness condition `IsExactAnchoredSoloPeriodic`
(`UniformEquilibrium/Quitting/Cycles/AnchoredSoloPeriodic.lean`) yields at each
phase, through `anchor_of_isExactAnchoredSoloPeriodic`.  Patience is not the
spectator half of that condition: fixed-hazard exactness bounds a spectator
against `spectatorQuitNowValue`, while patience compares against the solo self
payoff itself.

Patience is the vanishing-hazard reading of a player's incentive not to quit,
and it is a hypothesis of the structure, not a derived fact.  At a phase where
the designated quitter `w_k` quits with probability `p`, the value to a
spectator `y` of quitting at that phase is the mixture
`(1 - p) * r_y({y}) + p * r_y({y, w_k})`, which is the solo self payoff
`r_y({y})` only in the limit `p → 0` or when the pair row `r_y({y, w_k})`
equals it.  When pair rows pay their members strictly less than their solo self
payoffs, that mixture is strictly below `r_y({y})`, so patience is a strictly
stronger requirement than the fixed-hazard comparison
(`spectatorQuitNowValue_lt_solo_of_pair_lt`); when pair rows pay their members
exactly their solo self payoffs the two coincide
(`spectatorQuitNowValue_eq_solo_of_pair_eq`).

Consequently the results below constrain solutions of this structure, and only
of this structure.  Infeasibility of the structure over a table says nothing on
its own about which behaviour profiles that table admits.

The central algebraic fact is an identity.  Applying the recursion at phase
`k + 1` to the quitter `w_k` and subtracting that quitter's solo payoff
throughout expresses the patience slack two phases on as the slack one phase on
minus the discounted margin `M[w_k][w_{k+1}]`.  At the anchor the first slack
vanishes, so the anchor equation alone prices the successor margin into the
deepest patience slot, and where the intervening survival does not vanish the
identity may be divided through:

`Φ^{k+2} (w_k) - r_{w_k}({w_k}) = -((1 - β_{k+1}) / β_{k+1}) * M[w_k][w_{k+1}]`.

Nonnegativity of the left-hand side is then exactly a sign condition on the
margin, and that sign condition needs no division.  Along a schedule of
constant step in a rotation-symmetric table with a
uniform survival factor, that sign condition is the positivity of the backward
partial sum of the step's anchor polynomial at a root of the polynomial.

## Main definitions

* `spectatorQuitNowValue` — the fixed-hazard value of quitting at a phase
* `QuittingAnchoredCyclicPatienceSystem` — schedule, survivals and phase values
  together with the recursion, the anchors, and patience

## Main results

* `QuittingAnchoredCyclicPatienceSystem.survival_mul_successor_defect` and
  `QuittingAnchoredCyclicPatienceSystem.successor_defect_eq` — the identity
  above, in its cleared and its divided form
* `QuittingAnchoredCyclicPatienceSystem.successor_margin_nonpos` — successor
  patience: `M[w_k][w_{k+1}] ≤ 0`
* `QuittingAnchoredCyclicPatienceSystem.predecessor_margin_nonneg` —
  predecessor patience: `M[w_{k+1}][w_k] ≥ 0`
* `QuittingAnchoredCyclicPatienceSystem.exists_margin_nonneg` — every player,
  scheduled or not, has a nonnegative margin against the quitter of some phase
* `QuittingAnchoredCyclicPatienceSystem.spectatorQuitNowValue_le_phaseValue` —
  where pair rows do not exceed solo self payoffs, patience implies the
  fixed-hazard comparison
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normalized solo matrix written with singleton terminal payoffs: row
`receiver`, column `quitter`, measured from the receiver's own solo payoff. -/
theorem normalizedSoloMatrix_eq_singleton_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (receiver quitter : ι) :
    normalizedSoloMatrix reward receiver quitter =
      reward (quittingProjectiveSingletonTerminal quitter) receiver -
        reward (quittingProjectiveSingletonTerminal receiver) receiver := by
  simp [normalizedSoloMatrix, QuittingPayoffTable.singletonMatrix,
    normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable, quittingSoloBaseline,
    quittingProjectiveSingletonTerminal, sub_eq_add_neg]

/-! ## The fixed-hazard value of quitting -/

/-- The value to a spectator `y` of quitting at a phase whose designated
quitter `quitter` quits with probability `p`: with probability `p` both quit
and the pair row applies, and otherwise `y` quits alone. -/
def spectatorQuitNowValue (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (p : ℝ) (quitter y : ι) : ℝ :=
  p * reward ⟨{y, quitter}, Finset.insert_nonempty y {quitter}⟩ y +
    (1 - p) * reward (quittingProjectiveSingletonTerminal y) y

omit [Fintype ι] in
/-- A pair row paying its member exactly the member's solo self payoff makes
the fixed-hazard value of quitting that solo self payoff, at every hazard. -/
theorem spectatorQuitNowValue_eq_solo_of_pair_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (p : ℝ) (quitter y : ι)
    (hpair : reward ⟨{y, quitter}, Finset.insert_nonempty y {quitter}⟩ y =
      reward (quittingProjectiveSingletonTerminal y) y) :
    spectatorQuitNowValue reward p quitter y =
      reward (quittingProjectiveSingletonTerminal y) y := by
  rw [spectatorQuitNowValue, hpair]
  ring

omit [Fintype ι] in
/-- A pair row paying its member strictly less than the member's solo self
payoff puts the fixed-hazard value of quitting strictly below that solo self
payoff, at every positive hazard. -/
theorem spectatorQuitNowValue_lt_solo_of_pair_lt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {p : ℝ} (hp : 0 < p)
    (quitter y : ι)
    (hpair : reward ⟨{y, quitter}, Finset.insert_nonempty y {quitter}⟩ y <
      reward (quittingProjectiveSingletonTerminal y) y) :
    spectatorQuitNowValue reward p quitter y <
      reward (quittingProjectiveSingletonTerminal y) y := by
  rw [spectatorQuitNowValue]
  nlinarith [mul_pos hp (sub_pos.mpr hpair)]

omit [Fintype ι] in
/-- A pair row not exceeding its member's solo self payoff keeps the
fixed-hazard value of quitting at or below that solo self payoff, at every
hazard in the unit interval. -/
theorem spectatorQuitNowValue_le_solo_of_pair_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {p : ℝ} (hp : 0 ≤ p)
    (quitter y : ι)
    (hpair : reward ⟨{y, quitter}, Finset.insert_nonempty y {quitter}⟩ y ≤
      reward (quittingProjectiveSingletonTerminal y) y) :
    spectatorQuitNowValue reward p quitter y ≤
      reward (quittingProjectiveSingletonTerminal y) y := by
  rw [spectatorQuitNowValue]
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hpair)]

/-- An anchored cyclic single-quitter schedule together with its phase values:
per-phase survival in `[0, 1)`, the one-step renewal recursion, an anchor
making each phase's quitter indifferent one phase later, and patience keeping
every player's phase value at or above its solo payoff. -/
structure QuittingAnchoredCyclicPatienceSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (m : ℕ) [NeZero m] where
  /-- The designated quitter of each phase. -/
  order : Fin m → ι
  /-- The probability that the cycle survives a phase. -/
  survival : Fin m → ℝ
  /-- The payoff vector the schedule delivers when read from a phase. -/
  phaseValue : Fin m → Payoff ι
  /-- Survival is nonnegative at every phase. -/
  survival_nonneg : ∀ k, 0 ≤ survival k
  /-- Survival is strictly below one at every phase. -/
  survival_lt_one : ∀ k, survival k < 1
  /-- One-step renewal around the cycle. -/
  recursion : ∀ k y, phaseValue k y =
    (1 - survival k) * reward (quittingProjectiveSingletonTerminal (order k)) y +
      survival k * phaseValue (k + 1) y
  /-- Each phase's quitter is indifferent one phase later. -/
  anchor : ∀ k, phaseValue (k + 1) (order k) =
    reward (quittingProjectiveSingletonTerminal (order k)) (order k)
  /-- No player's phase value falls below its own solo payoff. -/
  patience : ∀ k y, reward (quittingProjectiveSingletonTerminal y) y ≤ phaseValue k y

namespace QuittingAnchoredCyclicPatienceSystem

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {m : ℕ} [NeZero m]
  (system : QuittingAnchoredCyclicPatienceSystem reward m)

omit [Fintype ι] [DecidableEq ι] in
/-- A phase's quitter is already indifferent at its own phase: the anchor one
phase later propagates back through the recursion. -/
theorem phaseValue_order_self (k : Fin m) :
    system.phaseValue k (system.order k) =
      reward (quittingProjectiveSingletonTerminal (system.order k)) (system.order k) := by
  have hrec := system.recursion k (system.order k)
  rw [system.anchor k] at hrec
  rw [hrec]
  ring

/-- **The one-phase transfer of patience slack.**  A player's patience slack
two phases on, discounted by the intervening survival, is its slack one phase
on minus the discounted margin against that phase's quitter. -/
theorem survival_mul_defect (k : Fin m) (y : ι) :
    system.survival (k + 1) *
        (system.phaseValue (k + 1 + 1) y -
          reward (quittingProjectiveSingletonTerminal y) y) =
      (system.phaseValue (k + 1) y - reward (quittingProjectiveSingletonTerminal y) y) -
        (1 - system.survival (k + 1)) *
          normalizedSoloMatrix reward y (system.order (k + 1)) := by
  have hrec := system.recursion (k + 1) y
  rw [normalizedSoloMatrix_eq_singleton_sub, hrec]
  ring

/-- **The anchor prices the successor margin.**  At the quitter of phase `k`
the slack one phase on vanishes, so the discounted slack two phases on is the
negated discounted margin against the quitter of phase `k + 1`. -/
theorem survival_mul_successor_defect (k : Fin m) :
    system.survival (k + 1) *
        (system.phaseValue (k + 1 + 1) (system.order k) -
          reward (quittingProjectiveSingletonTerminal (system.order k)) (system.order k)) =
      -((1 - system.survival (k + 1)) *
        normalizedSoloMatrix reward (system.order k) (system.order (k + 1))) := by
  have h := system.survival_mul_defect k (system.order k)
  rw [system.anchor k] at h
  rw [h]
  ring

/-- The same identity solved for the patience slack two phases on, at a phase
whose survival does not vanish. -/
theorem successor_defect_eq (k : Fin m) (hsurvival : system.survival (k + 1) ≠ 0) :
    system.phaseValue (k + 1 + 1) (system.order k) -
        reward (quittingProjectiveSingletonTerminal (system.order k)) (system.order k) =
      -((1 - system.survival (k + 1)) / system.survival (k + 1)) *
        normalizedSoloMatrix reward (system.order k) (system.order (k + 1)) := by
  have h := system.survival_mul_successor_defect k
  field_simp
  linarith [h]

/-- **Successor patience.**  The quitter of a phase has a nonpositive margin
against the quitter of the next phase. -/
theorem successor_margin_nonpos (k : Fin m) :
    normalizedSoloMatrix reward (system.order k) (system.order (k + 1)) ≤ 0 := by
  have hnonneg := system.survival_nonneg (k + 1)
  have hlt := system.survival_lt_one (k + 1)
  have hslack : 0 ≤ system.phaseValue (k + 1 + 1) (system.order k) -
      reward (quittingProjectiveSingletonTerminal (system.order k)) (system.order k) :=
    sub_nonneg.mpr (system.patience (k + 1 + 1) (system.order k))
  have hprod := mul_nonneg hnonneg hslack
  rw [system.survival_mul_successor_defect k] at hprod
  by_contra hpositive
  have hmargin : 0 < normalizedSoloMatrix reward (system.order k)
      (system.order (k + 1)) := lt_of_not_ge hpositive
  nlinarith [mul_pos (show (0 : ℝ) < 1 - system.survival (k + 1) by linarith) hmargin]

/-- **Predecessor patience.**  The quitter of a phase has a nonnegative margin
against the quitter of the previous phase. -/
theorem predecessor_margin_nonneg (k : Fin m) :
    0 ≤ normalizedSoloMatrix reward (system.order (k + 1)) (system.order k) := by
  have hlt := system.survival_lt_one k
  have hrec := system.recursion k (system.order (k + 1))
  rw [system.phaseValue_order_self (k + 1)] at hrec
  have hpat := system.patience k (system.order (k + 1))
  rw [normalizedSoloMatrix_eq_singleton_sub]
  by_contra hnegative
  have hgap : reward (quittingProjectiveSingletonTerminal (system.order k))
        (system.order (k + 1)) -
      reward (quittingProjectiveSingletonTerminal (system.order (k + 1)))
        (system.order (k + 1)) < 0 := lt_of_not_ge hnegative
  nlinarith [mul_pos (show (0 : ℝ) < 1 - system.survival k by linarith)
    (show (0 : ℝ) < -(reward (quittingProjectiveSingletonTerminal (system.order k))
        (system.order (k + 1)) -
      reward (quittingProjectiveSingletonTerminal (system.order (k + 1)))
        (system.order (k + 1))) by linarith)]

/-- **Every player tolerates some scheduled quitter.**  At a phase where a
player's patience slack is largest, the recursion forces that slack below the
player's margin against that phase's quitter, and the slack is nonnegative. -/
theorem exists_margin_nonneg (z : ι) :
    ∃ k : Fin m, 0 ≤ normalizedSoloMatrix reward z (system.order k) := by
  classical
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty (α := Fin m)
  obtain ⟨top, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ
      (fun k => system.phaseValue k z - reward (quittingProjectiveSingletonTerminal z) z) hne
  refine ⟨top, ?_⟩
  have hnonneg := system.survival_nonneg top
  have hlt := system.survival_lt_one top
  have hslack : 0 ≤ system.phaseValue top z -
      reward (quittingProjectiveSingletonTerminal z) z :=
    sub_nonneg.mpr (system.patience top z)
  have hle := hmax (top + 1) (Finset.mem_univ _)
  have hmul : system.survival top *
      (system.phaseValue (top + 1) z - reward (quittingProjectiveSingletonTerminal z) z) ≤
        system.survival top *
          (system.phaseValue top z - reward (quittingProjectiveSingletonTerminal z) z) :=
    mul_le_mul_of_nonneg_left hle hnonneg
  have hrec := system.recursion top z
  rw [normalizedSoloMatrix_eq_singleton_sub]
  by_contra hnegative
  have hmargin : reward (quittingProjectiveSingletonTerminal (system.order top)) z -
      reward (quittingProjectiveSingletonTerminal z) z < 0 := lt_of_not_ge hnegative
  nlinarith [mul_pos (show (0 : ℝ) < 1 - system.survival top by linarith)
    (show (0 : ℝ) < -(reward (quittingProjectiveSingletonTerminal (system.order top)) z -
      reward (quittingProjectiveSingletonTerminal z) z) by linarith)]

omit [Fintype ι] in
/-- **Where patience is the fixed-hazard comparison.**  On a table whose pair
rows do not exceed their members' solo self payoffs, the patience field bounds
the fixed-hazard value of quitting at every phase, hazard, and quitter. -/
theorem spectatorQuitNowValue_le_phaseValue {p : ℝ} (hp : 0 ≤ p) (quitter y : ι)
    (hpair : reward ⟨{y, quitter}, Finset.insert_nonempty y {quitter}⟩ y ≤
      reward (quittingProjectiveSingletonTerminal y) y) (k : Fin m) :
    spectatorQuitNowValue reward p quitter y ≤ system.phaseValue k y :=
  (spectatorQuitNowValue_le_solo_of_pair_le reward hp quitter y hpair).trans
    (system.patience k y)

end QuittingAnchoredCyclicPatienceSystem

end GameTheory
