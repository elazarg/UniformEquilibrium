/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom

/-!
# Two-outcome passports for profitable terminal-law comparisons

For two literal terminal laws `p` and `q`, the payoff difference is the
expectation of `reward high - reward low` under the independent coupling
`p × q`.  Hence every positive comparison is witnessed by one outcome of the
first law and one lower-reward outcome of the second law, both with positive
mass.  The only quantitative loss is the square of the finite outcome count.

This representation is invariant under the arbitrary choice of the zero
reward assigned to `Never`.  The familiar positive-reward mass creation and
negative-reward mass deletion atoms are the two cases obtained when one end
of the passport is compared with that origin.

For two absorbing coalition outcomes, every player has one of the four
membership signatures in `Bool × Bool`.  This is a canonical four-role
quotient of the passport.  No claim is made here that players in one fiber
can be strategically merged: their payoff coordinates and conditional
behavior laws may still differ.
-/

noncomputable section

namespace GameTheory

open Set StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Independent-coupling contribution of one high/low terminal-outcome pair
to the payoff difference between two literal profiles. -/
def quittingTerminalCrossLawAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι)
    (high low : QuittingTerminalOutcome ι) : ℝ :=
  quittingTerminalOutcomeMass reward first high *
    quittingTerminalOutcomeMass reward second low *
      (quittingTerminalOutcomeReward reward high observer -
        quittingTerminalOutcomeReward reward low observer)

omit [DecidableEq ι] in
/-- **Independent-coupling identity.**  The cross-law atoms sum exactly to
the terminal payoff difference. -/
theorem sum_quittingTerminalCrossLawAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) :
    (∑ high : QuittingTerminalOutcome ι,
      ∑ low : QuittingTerminalOutcome ι,
        quittingTerminalCrossLawAtom reward first second observer high low) =
      quittingTerminalPayoff reward first observer -
        quittingTerminalPayoff reward second observer := by
  let p := quittingTerminalOutcomeMass reward first
  let q := quittingTerminalOutcomeMass reward second
  let r := fun outcome : QuittingTerminalOutcome ι =>
    quittingTerminalOutcomeReward reward outcome observer
  have hp : ∑ outcome, p outcome = 1 :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward first).2
  have hq : ∑ outcome, q outcome = 1 :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward second).2
  rw [← quittingTerminalRewardMoment_outcomeMass reward first,
    ← quittingTerminalRewardMoment_outcomeMass reward second]
  change (∑ high, ∑ low, p high * q low * (r high - r low)) =
    (∑ high, p high * r high) - ∑ low, q low * r low
  calc
    (∑ high, ∑ low, p high * q low * (r high - r low)) =
        (∑ high, p high * r high) * (∑ low, q low) -
          (∑ high, p high) * (∑ low, q low * r low) := by
            simp_rw [mul_sub, Finset.sum_sub_distrib]
            congr 1
            · calc
                (∑ high, ∑ low, p high * q low * r high) =
                    ∑ high, (p high * r high) * ∑ low, q low := by
                      apply Finset.sum_congr rfl
                      intro high _
                      calc
                        (∑ low, p high * q low * r high) =
                            ∑ low, (p high * r high) * q low := by
                              apply Finset.sum_congr rfl
                              intro low _
                              ring
                        _ = (p high * r high) * ∑ low, q low := by
                              rw [Finset.mul_sum]
                _ = (∑ high, p high * r high) * ∑ low, q low := by
                      rw [Finset.sum_mul]
            · calc
                (∑ high, ∑ low, p high * q low * r low) =
                    ∑ high, p high * ∑ low, q low * r low := by
                      apply Finset.sum_congr rfl
                      intro high _
                      calc
                        (∑ low, p high * q low * r low) =
                            ∑ low, p high * (q low * r low) := by
                              apply Finset.sum_congr rfl
                              intro low _
                              ring
                        _ = p high * ∑ low, q low * r low := by
                              rw [Finset.mul_sum]
                _ = (∑ high, p high) * ∑ low, q low * r low := by
                      rw [Finset.sum_mul]
    _ = (∑ high, p high * r high) -
          ∑ low, q low * r low := by rw [hp, hq]; ring

omit [DecidableEq ι] in
/-- A positive terminal payoff difference exposes one literal high/low pair.
The factor is exactly the cardinality of the product outcome space. -/
theorem exists_terminalCrossLawAtom
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ)
    (hcharge : charge ≤ quittingTerminalPayoff reward first observer -
      quittingTerminalPayoff reward second observer) :
    ∃ high low : QuittingTerminalOutcome ι,
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward first second observer high low := by
  let X := QuittingTerminalOutcome ι × QuittingTerminalOutcome ι
  let atom : X → ℝ := fun pair =>
    quittingTerminalCrossLawAtom reward first second observer pair.1 pair.2
  let carrier := (Finset.univ : Finset X)
  have hcarrier : carrier.Nonempty := Finset.univ_nonempty
  obtain ⟨pair, _hpair, hmax⟩ :=
    Finset.exists_max_image carrier atom hcarrier
  refine ⟨pair.1, pair.2, hcharge.trans ?_⟩
  rw [← sum_quittingTerminalCrossLawAtom reward first second observer]
  have hsum := carrier.sum_le_card_nsmul atom (atom pair)
    (fun other hother => hmax other hother)
  have hcard : (carrier.card : ℝ) =
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 := by
    simp [carrier, X, pow_two]
  change (∑ high, ∑ low, atom (high, low)) ≤ _
  rw [← Fintype.sum_prod_type]
  calc
    (∑ pair : X, atom pair) ≤ (carrier.card : ℝ) * atom pair := by
      simpa only [carrier, nsmul_eq_mul, Nat.cast_ofNat] using hsum
    _ = (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward first second observer pair.1
          pair.2 := by rw [hcard]

omit [DecidableEq ι] in
/-- Positivity of one cross-law atom gives positive mass at both literal
endpoints and a strict reward ascent. -/
theorem positive_quittingTerminalCrossLawAtom_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (high low : QuittingTerminalOutcome ι) :
    0 < quittingTerminalCrossLawAtom reward first second observer high low ↔
      0 < quittingTerminalOutcomeMass reward first high ∧
      0 < quittingTerminalOutcomeMass reward second low ∧
      quittingTerminalOutcomeReward reward low observer <
        quittingTerminalOutcomeReward reward high observer := by
  unfold quittingTerminalCrossLawAtom
  rw [mul_pos_iff]
  constructor
  · intro h
    have hp : 0 ≤ quittingTerminalOutcomeMass reward first high :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward first).1 high
    have hq : 0 ≤ quittingTerminalOutcomeMass reward second low :=
      (quittingTerminalOutcomeMass_mem_stdSimplex reward second).1 low
    rcases h with h | h
    · exact ⟨pos_of_mul_pos_left h.1 hq, pos_of_mul_pos_right h.1 hp,
        sub_pos.mp h.2⟩
    · have hpq : 0 ≤ quittingTerminalOutcomeMass reward first high *
          quittingTerminalOutcomeMass reward second low := mul_nonneg hp hq
      exact False.elim ((not_lt_of_ge hpq) h.1)
  · rintro ⟨hp, hq, hr⟩
    exact Or.inl ⟨mul_pos hp hq, sub_pos.mpr hr⟩

omit [DecidableEq ι] in
/-- Quantitative two-outcome passport.  A positive payoff charge produces
one high outcome in the first law and one lower outcome in the second law,
both with positive probability. -/
theorem exists_positive_terminalCrossLawPassport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ) (hchargePositive : 0 < charge)
    (hcharge : charge ≤ quittingTerminalPayoff reward first observer -
      quittingTerminalPayoff reward second observer) :
    ∃ high low : QuittingTerminalOutcome ι,
      charge ≤ (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
        quittingTerminalCrossLawAtom reward first second observer high low ∧
      0 < quittingTerminalOutcomeMass reward first high ∧
      0 < quittingTerminalOutcomeMass reward second low ∧
      quittingTerminalOutcomeReward reward low observer <
        quittingTerminalOutcomeReward reward high observer := by
  obtain ⟨high, low, hatomBound⟩ :=
    exists_terminalCrossLawAtom reward first second observer charge hcharge
  have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 := by
    positivity
  have hatom : 0 <
      quittingTerminalCrossLawAtom reward first second observer high low := by
    nlinarith
  have hpassport :=
    (positive_quittingTerminalCrossLawAtom_iff reward first second observer
      high low).1 hatom
  exact ⟨high, low, hatomBound, hpassport.1, hpassport.2.1, hpassport.2.2⟩

omit [DecidableEq ι] in
/-- A terminal cross-law atom is bounded by twice the reward bound times its
literal product-coupling mass. -/
theorem quittingTerminalCrossLawAtom_le_two_mul_rewardBound_mul_mass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (high low : QuittingTerminalOutcome ι) :
    quittingTerminalCrossLawAtom reward first second observer high low ≤
      2 * quittingRewardBound reward *
        (quittingTerminalOutcomeMass reward first high *
          quittingTerminalOutcomeMass reward second low) := by
  let p := quittingTerminalOutcomeMass reward first high
  let q := quittingTerminalOutcomeMass reward second low
  let highReward := quittingTerminalOutcomeReward reward high observer
  let lowReward := quittingTerminalOutcomeReward reward low observer
  have hp : 0 ≤ p :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward first).1 high
  have hq : 0 ≤ q :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward second).1 low
  have hM : 0 ≤ quittingRewardBound reward :=
    quittingRewardBound_nonneg reward
  have hhigh : highReward ≤ quittingRewardBound reward := by
    cases high with
    | none => simp [highReward, quittingTerminalOutcomeReward, hM]
    | some terminal =>
        exact (le_abs_self _).trans
          (abs_reward_le_quittingRewardBound reward terminal observer)
  have hlow : -quittingRewardBound reward ≤ lowReward := by
    cases low with
    | none => simp [lowReward, quittingTerminalOutcomeReward, hM]
    | some terminal =>
        exact (neg_le_of_abs_le
          (abs_reward_le_quittingRewardBound reward terminal observer))
  have hgap : highReward - lowReward ≤ 2 * quittingRewardBound reward := by
    linarith
  unfold quittingTerminalCrossLawAtom
  change p * q * (highReward - lowReward) ≤
    2 * quittingRewardBound reward * (p * q)
  have hpq : 0 ≤ p * q := mul_nonneg hp hq
  nlinarith

omit [DecidableEq ι] in
/-- Quantitative passport stated directly as a lower bound on the joint mass
of its two endpoint outcomes. -/
theorem exists_terminalCrossLawPassport_massProductBound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (first second : (quittingGame reward).BehaviorProfile)
    (observer : ι) (charge : ℝ) (hchargePositive : 0 < charge)
    (hcharge : charge ≤ quittingTerminalPayoff reward first observer -
      quittingTerminalPayoff reward second observer) :
    ∃ high low : QuittingTerminalOutcome ι,
      charge ≤
        (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 *
          (2 * quittingRewardBound reward) *
          (quittingTerminalOutcomeMass reward first high *
            quittingTerminalOutcomeMass reward second low) ∧
      quittingTerminalOutcomeReward reward low observer <
        quittingTerminalOutcomeReward reward high observer := by
  obtain ⟨high, low, hatom, _hhigh, _hlow, hreward⟩ :=
    exists_positive_terminalCrossLawPassport reward first second observer
      charge hchargePositive hcharge
  refine ⟨high, low, hatom.trans ?_, hreward⟩
  have hscale : 0 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) ^ 2 := by positivity
  have h := quittingTerminalCrossLawAtom_le_two_mul_rewardBound_mul_mass
    reward first second observer high low
  nlinarith

/-! ## The canonical four-role quotient of two coalition outcomes -/

/-- Membership signature of a player in an ordered pair of coalitions. -/
def quittingTwoCoalitionRole
    (low high : Finset ι) (who : ι) : Bool × Bool :=
  (decide (who ∈ low), decide (who ∈ high))

omit [Fintype ι] in
/-- The four role fibers are an exact partition: equality of roles is exactly
agreement on membership in both coalitions. -/
theorem quittingTwoCoalitionRole_eq_iff
    (low high : Finset ι) (first second : ι) :
    quittingTwoCoalitionRole low high first =
        quittingTwoCoalitionRole low high second ↔
      (first ∈ low ↔ second ∈ low) ∧
        (first ∈ high ↔ second ∈ high) := by
  simp [quittingTwoCoalitionRole]

/-- At most four role signatures occur, independently of the ambient number
of players. -/
theorem card_image_quittingTwoCoalitionRole_le_four
    (low high : Finset ι) :
    (Finset.univ.image (quittingTwoCoalitionRole low high)).card ≤ 4 := by
  calc
    (Finset.univ.image (quittingTwoCoalitionRole low high)).card ≤
        Fintype.card (Bool × Bool) := Finset.card_le_univ _
    _ = 4 := by decide

omit [Fintype ι] in
/-- Swapping the two coalition outcomes transposes the two role bits. -/
theorem quittingTwoCoalitionRole_swap
    (low high : Finset ι) (who : ι) :
    quittingTwoCoalitionRole high low who =
      (quittingTwoCoalitionRole low high who).swap := by
  rfl

end GameTheory
