/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Attractive and repulsive orientations of a positive terminal atom

A positive terminal payoff-difference atom is a product of exactly two
signed quantities:

* the change in probability of one terminal outcome; and
* that outcome's reward to the observer.

Consequently there are exactly two, and not four, positive orientations.
An **attractive** atom has positive reward and gains probability at the
first endpoint.  A **repulsive** atom has negative reward and loses
probability there.  The second branch stores the useful terminal mass at the
source endpoint, so it cannot be replaced by the first branch in an argument
which also needs a property known only at the target endpoint.

This is an algebraic polarity theorem, not a strategic equivalence of games.
Reversing both signs preserves the scalar product, but negating a player's
reward table reverses that player's optimization order.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive-reward terminal event whose probability is larger under the
first profile. -/
def IsQuittingAttractiveTerminalAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) : Prop :=
  0 < reward terminal observer ∧
    quittingTerminalOutcomeMass reward second (some terminal) <
      quittingTerminalOutcomeMass reward first (some terminal)

/-- A negative-reward terminal event whose probability is smaller under the
first profile.  Its useful mass is therefore stored at the second profile. -/
def IsQuittingRepulsiveTerminalAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) : Prop :=
  reward terminal observer < 0 ∧
    quittingTerminalOutcomeMass reward first (some terminal) <
      quittingTerminalOutcomeMass reward second (some terminal)

omit [DecidableEq ι] in
/-- A positive absorbing terminal atom has exactly one of the two strict
orientations: attractive or repulsive. -/
theorem positive_quittingTerminalPayoffDifferenceAtom_iff_polarity
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty}) :
    0 < quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal) ↔
      IsQuittingAttractiveTerminalAtom reward first second observer terminal ∨
        IsQuittingRepulsiveTerminalAtom reward first second observer terminal := by
  unfold quittingTerminalPayoffDifferenceAtom
  simp only [quittingTerminalOutcomeReward]
  rw [mul_pos_iff]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨h.2, sub_pos.mp h.1⟩
    · exact Or.inr ⟨h.2, sub_neg.mp h.1⟩
  · intro h
    rcases h with h | h
    · exact Or.inl ⟨sub_pos.mpr h.2, h.1⟩
    · exact Or.inr ⟨sub_neg.mpr h.2, h.1⟩

omit [DecidableEq ι] in
/-- The two positive orientations are disjoint. -/
theorem attractive_not_repulsive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty})
    (hattractive : IsQuittingAttractiveTerminalAtom reward first second observer
      terminal) :
    ¬ IsQuittingRepulsiveTerminalAtom reward first second observer terminal := by
  intro hrepulsive
  exact (not_lt_of_ge hattractive.1.le) hrepulsive.1

omit [DecidableEq ι] in
/-- Attractive atoms have positive mass at the first endpoint; repulsive
atoms have positive mass at the second endpoint.  This is the exact endpoint
asymmetry hidden by the weaker statement that one of the two masses is
positive. -/
theorem positive_terminalMass_at_polarity_endpoint
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty})
    (hatom : 0 < quittingTerminalPayoffDifferenceAtom reward first second
      observer (some terminal)) :
    (IsQuittingAttractiveTerminalAtom reward first second observer terminal ∧
        0 < quittingTerminalOutcomeMass reward first (some terminal)) ∨
      (IsQuittingRepulsiveTerminalAtom reward first second observer terminal ∧
        0 < quittingTerminalOutcomeMass reward second (some terminal)) := by
  have hfirstNonneg : 0 ≤ quittingTerminalOutcomeMass reward first
      (some terminal) :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward first).1 (some terminal)
  have hsecondNonneg : 0 ≤ quittingTerminalOutcomeMass reward second
      (some terminal) :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward second).1 (some terminal)
  rw [positive_quittingTerminalPayoffDifferenceAtom_iff_polarity] at hatom
  rcases hatom with hattractive | hrepulsive
  · exact Or.inl ⟨hattractive, hsecondNonneg.trans_lt hattractive.2⟩
  · exact Or.inr ⟨hrepulsive, hfirstNonneg.trans_lt hrepulsive.2⟩

omit [DecidableEq ι] in
/-- Quantitative polarity.  A positive atom charge and a uniform absolute
reward bound force a probability gap at the correct endpoint.  The formula
avoids division and remains meaningful when used under limits. -/
theorem terminalAtom_charge_le_orientedMassGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty})
    (charge scale bound : ℝ) (hscale : 0 ≤ scale)
    (hrewardBound : |reward terminal observer| ≤ bound)
    (hcharge : charge ≤ scale *
      quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal))
    (hchargePositive : 0 < charge) :
    (IsQuittingAttractiveTerminalAtom reward first second observer terminal ∧
        charge ≤ scale * bound *
          (quittingTerminalOutcomeMass reward first (some terminal) -
            quittingTerminalOutcomeMass reward second (some terminal))) ∨
      (IsQuittingRepulsiveTerminalAtom reward first second observer terminal ∧
        charge ≤ scale * bound *
          (quittingTerminalOutcomeMass reward second (some terminal) -
            quittingTerminalOutcomeMass reward first (some terminal))) := by
  have hatom : 0 < quittingTerminalPayoffDifferenceAtom reward first second
      observer (some terminal) := by
    by_contra hnot
    have hnonpos : quittingTerminalPayoffDifferenceAtom reward first second
        observer (some terminal) ≤ 0 := le_of_not_gt hnot
    have : scale * quittingTerminalPayoffDifferenceAtom reward first second
        observer (some terminal) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hscale hnonpos
    linarith
  rw [positive_quittingTerminalPayoffDifferenceAtom_iff_polarity] at hatom
  rcases hatom with hattractive | hrepulsive
  · left
    refine ⟨hattractive, hcharge.trans ?_⟩
    unfold quittingTerminalPayoffDifferenceAtom
    simp only [quittingTerminalOutcomeReward]
    have hrewardLe : reward terminal observer ≤ bound :=
      (le_abs_self (reward terminal observer)).trans hrewardBound
    have hgap : 0 ≤ quittingTerminalOutcomeMass reward first (some terminal) -
        quittingTerminalOutcomeMass reward second (some terminal) :=
      (sub_pos.mpr hattractive.2).le
    calc
      scale *
          ((quittingTerminalOutcomeMass reward first (some terminal) -
              quittingTerminalOutcomeMass reward second (some terminal)) *
            reward terminal observer) ≤
          scale *
            ((quittingTerminalOutcomeMass reward first (some terminal) -
                quittingTerminalOutcomeMass reward second (some terminal)) *
              bound) := by gcongr
      _ = scale * bound *
          (quittingTerminalOutcomeMass reward first (some terminal) -
            quittingTerminalOutcomeMass reward second (some terminal)) := by ring
  · right
    refine ⟨hrepulsive, hcharge.trans ?_⟩
    unfold quittingTerminalPayoffDifferenceAtom
    simp only [quittingTerminalOutcomeReward]
    have hnegativeRewardLe : -reward terminal observer ≤ bound := by
      rw [← abs_of_neg hrepulsive.1]
      exact hrewardBound
    have hgap : 0 ≤ quittingTerminalOutcomeMass reward second (some terminal) -
        quittingTerminalOutcomeMass reward first (some terminal) :=
      (sub_pos.mpr hrepulsive.2).le
    calc
      scale *
          ((quittingTerminalOutcomeMass reward first (some terminal) -
              quittingTerminalOutcomeMass reward second (some terminal)) *
            reward terminal observer) =
          scale *
            ((quittingTerminalOutcomeMass reward second (some terminal) -
                quittingTerminalOutcomeMass reward first (some terminal)) *
              (-reward terminal observer)) := by ring
      _ ≤ scale *
            ((quittingTerminalOutcomeMass reward second (some terminal) -
                quittingTerminalOutcomeMass reward first (some terminal)) *
              bound) := by gcongr
      _ = scale * bound *
          (quittingTerminalOutcomeMass reward second (some terminal) -
            quittingTerminalOutcomeMass reward first (some terminal)) := by ring

omit [DecidableEq ι] in
/-- Specialization to the canonical quitting-game reward bound. -/
theorem terminalAtom_charge_le_orientedMassGap_rewardBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (terminal : {S : Finset ι // S.Nonempty})
    (charge scale : ℝ) (hscale : 0 ≤ scale)
    (hcharge : charge ≤ scale *
      quittingTerminalPayoffDifferenceAtom reward first second observer
        (some terminal))
    (hchargePositive : 0 < charge) :
    (IsQuittingAttractiveTerminalAtom reward first second observer terminal ∧
        charge ≤ scale * quittingRewardBound reward *
          (quittingTerminalOutcomeMass reward first (some terminal) -
            quittingTerminalOutcomeMass reward second (some terminal))) ∨
      (IsQuittingRepulsiveTerminalAtom reward first second observer terminal ∧
        charge ≤ scale * quittingRewardBound reward *
          (quittingTerminalOutcomeMass reward second (some terminal) -
            quittingTerminalOutcomeMass reward first (some terminal))) := by
  exact terminalAtom_charge_le_orientedMassGap reward first second observer
    terminal charge scale (quittingRewardBound reward) hscale
      (abs_reward_le_quittingRewardBound reward terminal observer) hcharge
      hchargePositive

/-! ## The exact scalar duality -/

/-- The signed atom scalar is invariant under simultaneous reversal of its
mass direction and reward sign.  This is the exact `Z/2` duality behind the
attractive/repulsive split. -/
theorem terminalAtomScalar_neg_neg (massDifference terminalReward : ℝ) :
    (-massDifference) * (-terminalReward) =
      massDifference * terminalReward := by
  ring

omit [DecidableEq ι] in
/-- Reversing only the endpoint order negates every terminal atom. -/
theorem quittingTerminalPayoffDifferenceAtom_swap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (outcome : QuittingTerminalOutcome ι) :
    quittingTerminalPayoffDifferenceAtom reward second first observer outcome =
      -quittingTerminalPayoffDifferenceAtom reward first second observer
        outcome := by
  unfold quittingTerminalPayoffDifferenceAtom
  ring

end GameTheory
