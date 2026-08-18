/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.DiscreteHazardStopping
import Research.Quitting.DiffuseTailSoloStructure
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# Exact per-date structure of solo quitting roots

A *solo root* is a product root at which a single designated `owner` may quit
(`IsQuittingSoloRoot`, `Research/Quitting/DiffuseTailSoloStructure.lean`).
This file records the exact one-date consequences of pairing such a root with
an endpoint-Nash certificate at accuracy zero, and telescopes them across a
window of consecutive solo dates.

The per-date facts are exact identities and exact inequalities: no `O(q)`
collision allowance is used anywhere, because at a solo root the owner's pure
Quit meets no collision and an inactive player's pure Quit meets only the
owner.

* **Endpoint formulas** (`IsQuittingSoloRoot.quitPayoff_owner` and its
  companions): the pure endpoint payoffs at a solo root in closed form,
  together with the prescribed value (`IsQuittingSoloRoot.successorPayoff_any`),
  which mixes the owner's singleton row with the declared continuation at every
  coordinate, the owner's own included.
* **Active indifference**
  (`IsQuittingSoloRoot.tail_owner_eq_soloReward_of_interior`): at an exact
  endpoint-Nash solo root whose owner mixes strictly, the declared
  continuation already pays the owner its own singleton reward, and the
  owner's prescribed value is unchanged across the date
  (`IsQuittingSoloRoot.successorPayoff_owner_eq_tail_of_interior`).
* **Approximate pin** (`IsQuittingSoloRoot.tail_owner_le_successorPayoff_add`):
  at Nash slack `ε` the owner's value falls by at most `ε` across the date,
  with no interiority hypothesis.
* **Pure-Quit floor** (`IsQuittingSoloRoot.quitMix_floor` and
  `IsQuittingSoloRoot.tail_displacement_floor`): a player's mixture of
  quitting alone and colliding with the owner is at most its prescribed
  value, exactly.
* **Window telescope**
  (`quittingSoloTailValue_sub_eq_windowFlow_add_survival`): across a window of
  solo dates, every player's prescribed value decomposes into the discounted
  hazard-weighted singleton rows received inside the window plus the surviving
  endpoint term, around an arbitrary base point.
* **Exact gap-return identity**
  (`quittingSoloTailMatrixFlow_eq_zero_of_fencedActiveDates`): between two
  consecutive dates at which a player is the strictly mixing soloist, that
  player's discounted normalized-solo-matrix flow across the intervening
  window is exactly zero.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification Math.Probability.DiscreteHazard

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Endpoint payoffs at a solo root -/

omit [Fintype ι] in
/-- A player colliding with itself receives its own singleton reward: the
absorbing set `{who, who}` is the singleton `{who}`. -/
theorem quittingSingletonCollisionReward_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingSingletonCollisionReward reward who who =
      quittingSoloReward reward who who := by
  have hset : (⟨{who, who}, by simp⟩ : {S : Finset ι // S.Nonempty}) =
      ⟨{who}, Finset.singleton_nonempty who⟩ :=
    Subtype.ext (Finset.pair_eq_singleton who)
  rw [quittingSingletonCollisionReward, quittingSoloReward, hset]

namespace IsQuittingSoloRoot

/-- The owner's pure-Quit endpoint at its own solo root is its singleton
reward, whatever the declared continuation. -/
theorem quitPayoff_owner (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} (hsolo : IsQuittingSoloRoot root owner)
    (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail root owner =
      quittingSoloReward reward owner owner := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootQuitPayoff_soloStationaryRoot_owner reward owner
    (root owner) tail

/-- The owner's pure-Continue endpoint at its own solo root is the declared
continuation: no opponent can absorb. -/
theorem continuePayoff_owner (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} (hsolo : IsQuittingSoloRoot root owner)
    (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail root owner = tail owner := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootContinuePayoff_soloStationaryRoot_owner reward owner
    (root owner) tail

/-- Any player's pure-Quit endpoint at a solo root mixes quitting alone with
colliding with the owner, and does not see the continuation.  At the owner's
own coordinate the two branches coincide, so the formula needs no case
distinction. -/
theorem quitPayoff_any (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} (hsolo : IsQuittingSoloRoot root owner)
    (who : ι) (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail root who =
      (root owner false).toReal * quittingSoloReward reward who who +
        (root owner true).toReal *
          quittingSingletonCollisionReward reward owner who := by
  by_cases hne : who = owner
  · subst hne
    have hmass := quittingRoot_continueProbability_add_quitProbability root who
    rw [hsolo.quitPayoff_owner reward tail,
      quittingSingletonCollisionReward_self reward who]
    linear_combination quittingSoloReward reward who who * hmass.symm
  · conv_lhs => rw [hsolo.eq_soloStationaryRoot]
    exact quittingRootQuitPayoff_soloStationaryRoot_other reward hne
      (root owner) tail

/-- An inactive player's pure-Continue endpoint at a solo root mixes the
owner's singleton row with the declared continuation. -/
theorem continuePayoff_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner other : ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner)
    (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail root other =
      (root owner true).toReal * quittingSoloReward reward owner other +
        (root owner false).toReal * tail other := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
  exact quittingRootContinuePayoff_soloStationaryRoot_other reward hne
    (root owner) tail

/-- **Uniform one-date recursion.**  Every player's prescribed value at a solo
root splits along the owner's hazard into the owner's singleton row and the
declared continuation.  An inactive player sees this because it continues
surely and its pure-Continue endpoint already has that shape; the owner sees
the same formula because its own pure-Quit endpoint is its singleton reward and
its pure-Continue endpoint is the continuation. -/
theorem successorPayoff_any
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} (hsolo : IsQuittingSoloRoot root owner)
    (who : ι) (tail : Payoff ι) :
    quittingRootSuccessorPayoff reward tail root who =
      (root owner true).toReal * quittingSoloReward reward owner who +
        (root owner false).toReal * tail who := by
  by_cases hne : who = owner
  · subst hne
    rw [quittingRootSuccessorPayoff_eq_endpointMix,
      hsolo.quitPayoff_owner reward tail,
      hsolo.continuePayoff_owner reward tail]
  · have hpure : root who = PMF.pure false := hsolo who hne
    have hquitMass : (root who true).toReal = 0 := by rw [hpure]; simp
    have hcontinueMass : (root who false).toReal = 1 := by rw [hpure]; simp
    rw [quittingRootSuccessorPayoff_eq_endpointMix, hquitMass, hcontinueMass,
      zero_mul, one_mul, zero_add,
      hsolo.continuePayoff_other reward hne tail]

/-! ## Active indifference -/

/-- **Exact active indifference.**  At a solo root that is exact endpoint-Nash
and whose owner mixes strictly, the declared continuation already pays the
owner its own singleton reward.  The owner's pure Quit meets no collision, so
the indifference is exact rather than accurate to first order in the
hazard. -/
theorem tail_owner_eq_soloReward_of_interior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root owner true).toReal)
    (hcontinue : 0 < (root owner false).toReal) :
    tail owner = quittingSoloReward reward owner owner := by
  have hzero := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail root owner hnash hcontinue hquit
  rw [quittingRootEndpointDifference, hsolo.quitPayoff_owner reward tail,
    hsolo.continuePayoff_owner reward tail] at hzero
  linarith

/-- **The active player's value is pinned.**  At a strictly mixing exact
endpoint-Nash solo root the owner's prescribed value equals its declared
continuation, hence also its own singleton reward. -/
theorem successorPayoff_owner_eq_tail_of_interior
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root)
    (hquit : 0 < (root owner true).toReal)
    (hcontinue : 0 < (root owner false).toReal) :
    quittingRootSuccessorPayoff reward tail root owner = tail owner := by
  have hpin := hsolo.tail_owner_eq_soloReward_of_interior reward hnash hquit
    hcontinue
  have hmass := quittingRoot_continueProbability_add_quitProbability root owner
  rw [quittingRootSuccessorPayoff_eq_endpointMix,
    hsolo.quitPayoff_owner reward tail, hsolo.continuePayoff_owner reward tail,
    ← hpin]
  linear_combination tail owner * hmass

/-- **Approximate pin.**  At Nash slack `ε` the owner's prescribed value at a
solo root falls short of its declared continuation by at most `ε`.  Neither
strict mixing nor exactness is needed: the owner's pure-Continue endpoint is
the continuation itself, so the whole displacement is the Nash residual. -/
theorem tail_owner_le_successorPayoff_add
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} {tail : Payoff ι} {ε : ℝ}
    (hsolo : IsQuittingSoloRoot root owner)
    (hnash : IsεQuittingRootEndpointNash reward tail ε root) :
    tail owner ≤ quittingRootSuccessorPayoff reward tail root owner + ε := by
  have hresidual := quittingRootContinuePayoff_sub_successorPayoff reward tail
    root owner
  rw [hsolo.continuePayoff_owner reward tail] at hresidual
  have hendpoint := (hnash owner).2
  linarith

/-! ## The pure-Quit floor -/

/-- **Exact pure-Quit floor.**  At an exact endpoint-Nash solo root a player's
mixture of quitting alone and colliding with the owner is at most its
prescribed value. -/
theorem quitMix_floor (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root owner false).toReal * quittingSoloReward reward who who +
        (root owner true).toReal *
          quittingSingletonCollisionReward reward owner who ≤
      quittingRootSuccessorPayoff reward tail root who := by
  have hbound := quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail
    root who
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward tail 0
      root).1 hnash)
  rwa [hsolo.quitPayoff_any reward who tail] at hbound

/-- **Rearranged pure-Quit floor.**  The continuation's displacement above a
player's own singleton reward, weighted by the survival mass, dominates the
hazard-weighted collision deficit.  Dividing by the survival mass is the
`O(hazard)` floor with the collision increment as its constant. -/
theorem tail_displacement_floor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner) (who : ι)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root owner true).toReal *
        (quittingSingletonCollisionReward reward owner who -
          quittingSoloReward reward owner who) ≤
      (root owner false).toReal *
        (tail who - quittingSoloReward reward who who) := by
  have hfloor := hsolo.quitMix_floor reward who hnash
  rw [hsolo.successorPayoff_any reward who tail] at hfloor
  nlinarith [hfloor]

end IsQuittingSoloRoot

/-! ## Hazards and survival across a window of solo dates -/

/-- The scalar hazard of a schedule of designated soloists: at each date, the
quit probability of that date's owner. -/
def quittingSoloTailHazard (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) :
    ScalarHazard :=
  BooleanHazard.toScalar fun time => roots time (owner time)

omit [Fintype ι] [DecidableEq ι] in
/-- The complement of a date's soloist hazard is that soloist's continuation
mass. -/
theorem one_sub_quittingSoloTailHazard_stop (roots : ℕ → ι → PMF Bool)
    (owner : ℕ → ι) (time : ℕ) :
    1 - (quittingSoloTailHazard roots owner).stop time =
      (roots time (owner time) false).toReal := by
  have hmass := continue_add_stop (fun time => roots time (owner time)) time
  simp only [continueProbability, stopProbability] at hmass
  show 1 - (roots time (owner time) true).toReal = _
  linarith

/-- Discounted hazard weight of the date `start + offset` inside the window
beginning at `start`: the probability that the window's first absorption
happens exactly then.  At `start = 0` this is
`Math.Probability.DiscreteHazard.ScalarHazard.stopMass`. -/
def quittingSoloTailWindowWeight (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (start offset : ℕ) : ℝ :=
  (quittingSoloTailHazard roots owner).survival start offset *
    (quittingSoloTailHazard roots owner).stop (start + offset)

omit [Fintype ι] [DecidableEq ι] in
/-- The window weights and the window survival together exhaust the unit
mass: the exact hazard telescope. -/
theorem sum_quittingSoloTailWindowWeight_add_survival
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start length : ℕ) :
    (∑ offset ∈ Finset.range length,
        quittingSoloTailWindowWeight roots owner start offset) +
      (quittingSoloTailHazard roots owner).survival start length = 1 := by
  have htelescope :=
    (quittingSoloTailHazard roots owner).sum_survival_mul_stop start length
  simp only [quittingSoloTailWindowWeight]
  linarith

/-! ## Transporting a value across a window -/

/-- **Window telescope.**  On a window of solo dates, `who`'s prescribed value
decomposes, around an arbitrary base point `base`, into the discounted
singleton rows it receives inside the window plus the surviving endpoint
displacement.  This is exact and holds at every coordinate, the dates' own
soloists included: only the value recursion and the solo shape of each root are
used, and no endpoint-Nash input enters. -/
theorem quittingSoloTailValue_sub_eq_windowFlow_add_survival
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (base : ℝ) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset))) :
    value start who - base =
      (∑ offset ∈ Finset.range length,
          quittingSoloTailWindowWeight roots owner start offset *
            (quittingSoloReward reward (owner (start + offset)) who - base)) +
        (quittingSoloTailHazard roots owner).survival start length *
          (value (start + length) who - base) := by
  induction length generalizing start with
  | zero => simp [ScalarHazard.survival]
  | succ length ih =>
      have hsolo0 : IsQuittingSoloRoot (roots start) (owner start) := by
        simpa using hsolo 0 (Nat.succ_pos length)
      have hsoloTail : ∀ offset, offset < length →
          IsQuittingSoloRoot (roots (start + 1 + offset))
            (owner (start + 1 + offset)) := by
        intro offset hoffset
        have hshift := hsolo (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hstep : value start who =
          (quittingSoloTailHazard roots owner).stop start *
              quittingSoloReward reward (owner start) who +
            (1 - (quittingSoloTailHazard roots owner).stop start) *
              value (start + 1) who := by
        rw [one_sub_quittingSoloTailHazard_stop]
        conv_lhs => rw [hpolicy start]
        exact hsolo0.successorPayoff_any reward who (value (start + 1))
      have hIH := ih (start + 1) hsoloTail
      have hsum :
          (∑ offset ∈ Finset.range (length + 1),
              quittingSoloTailWindowWeight roots owner start offset *
                (quittingSoloReward reward (owner (start + offset)) who -
                  base)) =
            (quittingSoloTailHazard roots owner).stop start *
                (quittingSoloReward reward (owner start) who - base) +
              (1 - (quittingSoloTailHazard roots owner).stop start) *
                ∑ offset ∈ Finset.range length,
                  quittingSoloTailWindowWeight roots owner (start + 1) offset *
                    (quittingSoloReward reward
                      (owner (start + 1 + offset)) who - base) := by
        have hshift : ∀ offset ∈ Finset.range length,
            quittingSoloTailWindowWeight roots owner start (offset + 1) *
                (quittingSoloReward reward
                  (owner (start + (offset + 1))) who - base) =
              (1 - (quittingSoloTailHazard roots owner).stop start) *
                (quittingSoloTailWindowWeight roots owner (start + 1) offset *
                  (quittingSoloReward reward
                    (owner (start + 1 + offset)) who - base)) := by
          intro offset _
          unfold quittingSoloTailWindowWeight
          rw [ScalarHazard.survival_succ_left,
            show start + (offset + 1) = start + 1 + offset from by omega]
          ring
        rw [Finset.sum_range_succ', Finset.sum_congr rfl hshift,
          ← Finset.mul_sum]
        have hfirst : quittingSoloTailWindowWeight roots owner start 0 *
            (quittingSoloReward reward (owner (start + 0)) who - base) =
              (quittingSoloTailHazard roots owner).stop start *
                (quittingSoloReward reward (owner start) who - base) := by
          simp [quittingSoloTailWindowWeight, ScalarHazard.survival]
        rw [hfirst, add_comm]
      rw [hsum, show start + (length + 1) = start + 1 + length from by omega,
        ScalarHazard.survival_succ_left, hstep]
      linear_combination
        (1 - (quittingSoloTailHazard roots owner).stop start) * hIH

/-! ## The exact gap-return identity -/

/-- Discounted normalized-solo-matrix flow of `who` across the window of
`length` dates beginning at `start`. -/
def quittingSoloTailMatrixFlow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (who : ι)
    (start length : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range length,
    quittingSoloTailWindowWeight roots owner start offset *
      normalizedSoloMatrix reward who (owner (start + offset))

/-- The window telescope written in normalized-solo-matrix coordinates: a
player's displacement from its own singleton reward is its discounted matrix
flow plus the surviving endpoint displacement.  The dates at which the player
is itself the soloist contribute nothing, their matrix entries being
diagonal. -/
theorem quittingSoloTailValue_sub_soloReward_eq_matrixFlow_add_survival
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset))) :
    value start who - quittingSoloReward reward who who =
      quittingSoloTailMatrixFlow reward roots owner who start length +
        (quittingSoloTailHazard roots owner).survival start length *
          (value (start + length) who - quittingSoloReward reward who who) := by
  have hbase := quittingSoloTailValue_sub_eq_windowFlow_add_survival roots value
    owner hpolicy who (quittingSoloReward reward who who) start length hsolo
  rw [hbase, quittingSoloTailMatrixFlow]
  refine congrArg (· + _) (Finset.sum_congr rfl fun offset _ => ?_)
  rw [normalizedSoloMatrix_eq_soloReward_sub]

/-- **Pinned-end form.**  A window across which a player's prescribed value
returns to its own singleton reward carries exactly zero discounted matrix
flow. -/
theorem quittingSoloTailMatrixFlow_eq_zero_of_pinnedEnds
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hstart : value start who = quittingSoloReward reward who who)
    (hend : value (start + length) who = quittingSoloReward reward who who) :
    quittingSoloTailMatrixFlow reward roots owner who start length = 0 := by
  have hidentity :=
    quittingSoloTailValue_sub_soloReward_eq_matrixFlow_add_survival roots value
      owner hpolicy who start length hsolo
  rw [hstart, hend] at hidentity
  simp only [sub_self, mul_zero, add_zero] at hidentity
  linarith

/-- At a strictly mixing date on which `who` is the exact-Nash soloist, both
`who`'s prescribed value at that date and its declared continuation are its
own singleton reward.  Only the one date's value recursion, Nash certificate
and solo shape enter. -/
theorem quittingSoloTailValue_eq_soloReward_of_activeInterior
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (who : ι) (time : ℕ)
    (hpolicy : value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash :
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hsolo : IsQuittingSoloRoot (roots time) who)
    (hquit : 0 < (roots time who true).toReal)
    (hcontinue : 0 < (roots time who false).toReal) :
    value time who = quittingSoloReward reward who who ∧
      value (time + 1) who = quittingSoloReward reward who who := by
  have hpin := hsolo.tail_owner_eq_soloReward_of_interior reward hnash hquit
    hcontinue
  refine ⟨?_, hpin⟩
  have hstep := hsolo.successorPayoff_owner_eq_tail_of_interior reward hnash
    hquit hcontinue
  rw [hpolicy]
  exact hstep.trans hpin

/-- **Exact gap-return identity.**  Let `who` be the strictly mixing
exact-Nash soloist at two dates `fence` and `fence + 1 + length`.  Then `who`'s
discounted normalized-solo-matrix flow across the intervening window is exactly
zero: every recurrent player's discounted flow over each of its gaps balances
with no error term.  Whether `who` is itself the soloist at some intervening
date is immaterial, such a date contributing a diagonal matrix entry. -/
theorem quittingSoloTailMatrixFlow_eq_zero_of_fencedActiveDates
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    (who : ι) (fence length : ℕ)
    (hopen : owner fence = who)
    (hopenQuit : 0 < (roots fence who true).toReal)
    (hopenContinue : 0 < (roots fence who false).toReal)
    (hclose : owner (fence + 1 + length) = who)
    (hcloseQuit : 0 < (roots (fence + 1 + length) who true).toReal)
    (hcloseContinue : 0 < (roots (fence + 1 + length) who false).toReal) :
    quittingSoloTailMatrixFlow reward roots owner who (fence + 1) length = 0 := by
  have hstart := (quittingSoloTailValue_eq_soloReward_of_activeInterior roots
    value who fence (hpolicy fence) (hnash fence) (hopen ▸ hsolo fence)
    hopenQuit hopenContinue).2
  have hend := (quittingSoloTailValue_eq_soloReward_of_activeInterior roots
    value who (fence + 1 + length) (hpolicy (fence + 1 + length))
    (hnash (fence + 1 + length)) (hclose ▸ hsolo (fence + 1 + length))
    hcloseQuit hcloseContinue).1
  exact quittingSoloTailMatrixFlow_eq_zero_of_pinnedEnds roots value owner
    hpolicy who (fence + 1) length (fun offset _ => hsolo _) hstart hend

/-! ## Constant-soloist windows and the phantom mismatch -/

/-- **Constant-soloist window.**  When every date of the window is solo at one
fixed coordinate, the window's absorbed mass is the complement of its survival
and the whole absorbed mass delivers that coordinate's singleton row. -/
theorem quittingSoloTailValue_sub_eq_absorbedMass_mul_of_constantOwner
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who fixedOwner : ι) (base : ℝ) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hconstant : ∀ offset, offset < length → owner (start + offset) = fixedOwner) :
    value start who - base =
      (1 - (quittingSoloTailHazard roots owner).survival start length) *
          (quittingSoloReward reward fixedOwner who - base) +
        (quittingSoloTailHazard roots owner).survival start length *
          (value (start + length) who - base) := by
  have hbase := quittingSoloTailValue_sub_eq_windowFlow_add_survival roots value
    owner hpolicy who base start length hsolo
  have hflow :
      (∑ offset ∈ Finset.range length,
          quittingSoloTailWindowWeight roots owner start offset *
            (quittingSoloReward reward (owner (start + offset)) who - base)) =
        (∑ offset ∈ Finset.range length,
            quittingSoloTailWindowWeight roots owner start offset) *
          (quittingSoloReward reward fixedOwner who - base) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun offset hoffset => ?_
    rw [hconstant offset (Finset.mem_range.1 hoffset)]
  have htelescope := sum_quittingSoloTailWindowWeight_add_survival roots owner
    start length
  rw [hbase, hflow]
  have hmass : (∑ offset ∈ Finset.range length,
      quittingSoloTailWindowWeight roots owner start offset) =
      1 - (quittingSoloTailHazard roots owner).survival start length := by
    linarith
  rw [hmass]

omit [Fintype ι] [DecidableEq ι] in
/-- **Phantom mismatch along a preemption out-edge.**  Suppose every date of
the window is solo at a fixed coordinate that strictly preempts `who` by
`margin`, and suppose the base point dominates `who`'s own singleton reward --
which is what the spectator floor supplies in the limit.  Then the window's
absorbed conditional delivery to `who` falls below the base point by at least
`margin`, so no amount of window survival can make the two agree. -/
theorem quittingSoloTailWindowDelivery_sub_base_le_neg_margin
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {who fixedOwner : ι} {margin base : ℝ}
    (hpreempt : QuittingSoloPreempts reward margin fixedOwner who)
    (hfloor : quittingSoloReward reward who who ≤ base) :
    quittingSoloReward reward fixedOwner who - base ≤ -margin := by
  obtain ⟨_, hedge⟩ := hpreempt
  linarith

/-- **Endpoint form of the mismatch.**  On a constant-soloist window along a
strict preemption out-edge, the prescribed value at the window's start falls
below a base point dominating `who`'s own singleton reward by at least the
absorbed mass times the margin, minus the surviving endpoint displacement. -/
theorem quittingSoloTailValue_sub_le_of_constantOwner_preemption
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    {who fixedOwner : ι} {margin base : ℝ}
    (hpreempt : QuittingSoloPreempts reward margin fixedOwner who)
    (hfloor : quittingSoloReward reward who who ≤ base)
    (start length : ℕ)
    (hconstant : ∀ offset, offset < length →
      owner (start + offset) = fixedOwner) :
    value start who - base ≤
      -((1 - (quittingSoloTailHazard roots owner).survival start length) *
          margin) +
        (quittingSoloTailHazard roots owner).survival start length *
          (value (start + length) who - base) := by
  have hidentity := quittingSoloTailValue_sub_eq_absorbedMass_mul_of_constantOwner
    roots value owner hpolicy who fixedOwner base start length
    (fun offset _ => hsolo _) hconstant
  have hmismatch := quittingSoloTailWindowDelivery_sub_base_le_neg_margin reward
    hpreempt hfloor
  have hsurvival :=
    (quittingSoloTailHazard roots owner).survival_le_one start length
  nlinarith [hidentity, hmismatch, hsurvival]

end GameTheory
