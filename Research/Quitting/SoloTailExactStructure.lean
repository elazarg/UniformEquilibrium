/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.SurvivalProduct
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

* **Endpoint formulas** (`IsQuittingSoloRoot.quitPayoff_owner` and the three
  companions): the four pure endpoint payoffs at a solo root in closed form.
* **Active indifference**
  (`IsQuittingSoloRoot.tail_owner_eq_soloReward_of_interior`): at an exact
  endpoint-Nash solo root whose owner mixes strictly, the declared
  continuation already pays the owner its own singleton reward, and the
  owner's prescribed value is unchanged across the date
  (`IsQuittingSoloRoot.successorPayoff_owner_eq_tail_of_interior`).
* **Approximate pin** (`IsQuittingSoloRoot.tail_owner_le_successorPayoff_add`):
  at Nash slack `ε` the owner's value falls by at most `ε` across the date,
  with no interiority hypothesis.
* **Spectator floor** (`IsQuittingSoloRoot.spectator_floor` and
  `IsQuittingSoloRoot.tail_other_floor`): an inactive player's mixture of
  quitting alone and colliding with the owner is at most its prescribed
  value, exactly.
* **Window telescope**
  (`quittingSoloTailValue_sub_eq_windowFlow_add_survival`): across a window on
  which a fixed spectator is inactive, its prescribed value decomposes into
  the discounted hazard-weighted singleton rows received inside the window
  plus the surviving endpoint term, around an arbitrary base point.
* **Exact gap-return identity**
  (`quittingSoloTailMatrixFlow_eq_zero_of_fencedActiveDates`): between two
  consecutive dates at which a player is the strictly mixing soloist, that
  player's discounted normalized-solo-matrix flow across the intervening
  window is exactly zero.
-/

noncomputable section

namespace GameTheory

open QuittingLCPClassification

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-! ## Endpoint payoffs at a solo root -/

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

/-- An inactive player's pure-Quit endpoint at a solo root mixes quitting
alone with colliding with the owner, and does not see the continuation. -/
theorem quitPayoff_other (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner other : ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner)
    (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail root other =
      (root owner false).toReal * quittingSoloReward reward other other +
        (root owner true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  conv_lhs => rw [hsolo.eq_soloStationaryRoot]
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

/-- An inactive player's prescribed value at a solo root is its pure-Continue
endpoint: it already continues surely. -/
theorem successorPayoff_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner other : ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner)
    (tail : Payoff ι) :
    quittingRootSuccessorPayoff reward tail root other =
      (root owner true).toReal * quittingSoloReward reward owner other +
        (root owner false).toReal * tail other := by
  have hpure : root other = PMF.pure false := hsolo other hne
  have hquitMass : (root other true).toReal = 0 := by rw [hpure]; simp
  have hcontinueMass : (root other false).toReal = 1 := by rw [hpure]; simp
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

/-! ## The spectator floor -/

/-- **Exact spectator floor.**  At an exact endpoint-Nash solo root an
inactive player's mixture of quitting alone and colliding with the owner is
at most its prescribed value. -/
theorem spectator_floor (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner other : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root owner false).toReal * quittingSoloReward reward other other +
        (root owner true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
      quittingRootSuccessorPayoff reward tail root other := by
  have hbound := quittingRootQuitPayoff_le_successor_of_isZeroNash reward tail
    root other
    ((isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward tail 0
      root).1 hnash)
  rwa [hsolo.quitPayoff_other reward hne tail] at hbound

/-- **Rearranged spectator floor.**  The continuation's displacement above the
inactive player's own singleton reward, weighted by the survival mass,
dominates the hazard-weighted collision deficit.  Dividing by the survival
mass is the `O(hazard)` floor with the collision increment as its
constant. -/
theorem tail_other_floor (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {owner other : ι} {tail : Payoff ι}
    (hsolo : IsQuittingSoloRoot root owner) (hne : other ≠ owner)
    (hnash : IsεQuittingRootEndpointNash reward tail 0 root) :
    (root owner true).toReal *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) ≤
      (root owner false).toReal *
        (tail other - quittingSoloReward reward other other) := by
  have hfloor := hsolo.spectator_floor reward hne hnash
  rw [hsolo.successorPayoff_other reward hne tail] at hfloor
  nlinarith [hfloor]

end IsQuittingSoloRoot

/-! ## Hazards and survival across a window of solo dates -/

/-- The quit probability of the date's designated soloist. -/
def quittingSoloTailHazard (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (time : ℕ) : ℝ :=
  (roots time (owner time) true).toReal

/-- Survival mass of the date's designated soloist. -/
def quittingSoloTailContinueMass (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (time : ℕ) : ℝ :=
  (roots time (owner time) false).toReal

omit [Fintype ι] [DecidableEq ι] in
/-- The two masses of a date's designated soloist sum to one. -/
theorem quittingSoloTailContinueMass_add_hazard
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (time : ℕ) :
    quittingSoloTailContinueMass roots owner time +
        quittingSoloTailHazard roots owner time = 1 :=
  quittingRoot_continueProbability_add_quitProbability (roots time) (owner time)

/-- Survival across the window of `length` solo dates beginning at `start`. -/
def quittingSoloTailSurvival (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (start length : ℕ) : ℝ :=
  Math.survivalProduct (quittingSoloTailContinueMass roots owner) start length

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSoloTailSurvival_zero
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start : ℕ) :
    quittingSoloTailSurvival roots owner start 0 = 1 :=
  Math.survivalProduct_zero _ start

omit [Fintype ι] [DecidableEq ι] in
/-- Appending one date multiplies the window survival by that date's survival
mass. -/
theorem quittingSoloTailSurvival_succ
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start length : ℕ) :
    quittingSoloTailSurvival roots owner start (length + 1) =
      quittingSoloTailSurvival roots owner start length *
        quittingSoloTailContinueMass roots owner (start + length) :=
  Math.survivalProduct_succ _ start length

omit [Fintype ι] [DecidableEq ι] in
/-- The window survival peels its first factor. -/
theorem quittingSoloTailSurvival_succ_left
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start length : ℕ) :
    quittingSoloTailSurvival roots owner start (length + 1) =
      quittingSoloTailContinueMass roots owner start *
        quittingSoloTailSurvival roots owner (start + 1) length := by
  unfold quittingSoloTailSurvival
  rw [show length + 1 = 1 + length from by omega,
    Math.survivalProduct_add]
  congr 1
  simpa using Math.survivalProduct_succ
    (quittingSoloTailContinueMass roots owner) start 0

omit [Fintype ι] [DecidableEq ι] in
/-- Every window survival lies in the unit interval. -/
theorem quittingSoloTailSurvival_mem_unitInterval
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start length : ℕ) :
    0 ≤ quittingSoloTailSurvival roots owner start length ∧
      quittingSoloTailSurvival roots owner start length ≤ 1 := by
  have hmass : ∀ time,
      0 ≤ quittingSoloTailContinueMass roots owner time ∧
        quittingSoloTailContinueMass roots owner time ≤ 1 := by
    intro time
    have hsum := quittingSoloTailContinueMass_add_hazard roots owner time
    have hhazard : 0 ≤ quittingSoloTailHazard roots owner time :=
      ENNReal.toReal_nonneg
    exact ⟨ENNReal.toReal_nonneg, by linarith⟩
  exact ⟨Math.survivalProduct_nonneg _ (fun time => (hmass time).1) start length,
    Math.survivalProduct_le_one _ (fun time => (hmass time).1)
      (fun time => (hmass time).2) start length⟩

/-- Discounted hazard weight of the date `start + offset` inside the window
beginning at `start`: the probability that the window's first absorption
happens exactly then. -/
def quittingSoloTailWindowWeight (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι)
    (start offset : ℕ) : ℝ :=
  quittingSoloTailSurvival roots owner start offset *
    quittingSoloTailHazard roots owner (start + offset)

omit [Fintype ι] [DecidableEq ι] in
/-- The window weights and the window survival together exhaust the unit
mass: the exact hazard telescope. -/
theorem sum_quittingSoloTailWindowWeight_add_survival
    (roots : ℕ → ι → PMF Bool) (owner : ℕ → ι) (start length : ℕ) :
    (∑ offset ∈ Finset.range length,
        quittingSoloTailWindowWeight roots owner start offset) +
      quittingSoloTailSurvival roots owner start length = 1 := by
  induction length with
  | zero => simp
  | succ length ih =>
      have hmass := quittingSoloTailContinueMass_add_hazard roots owner
        (start + length)
      rw [Finset.sum_range_succ, quittingSoloTailSurvival_succ,
        quittingSoloTailWindowWeight]
      linear_combination ih +
        quittingSoloTailSurvival roots owner start length * hmass

/-! ## Transporting a spectator's value across a window -/

/-- **Window telescope.**  On a window of solo dates at which `who` is never
the designated soloist, `who`'s prescribed value decomposes, around an
arbitrary base point `base`, into the discounted singleton rows it receives
inside the window plus the surviving endpoint displacement.  This is exact:
only the value recursion and the solo shape of each root are used, and no
endpoint-Nash input enters. -/
theorem quittingSoloTailValue_sub_eq_windowFlow_add_survival
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (base : ℝ) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hspectator : ∀ offset, offset < length → who ≠ owner (start + offset)) :
    value start who - base =
      (∑ offset ∈ Finset.range length,
          quittingSoloTailWindowWeight roots owner start offset *
            (quittingSoloReward reward (owner (start + offset)) who - base)) +
        quittingSoloTailSurvival roots owner start length *
          (value (start + length) who - base) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
      have hspectator0 : who ≠ owner start := by
        simpa using hspectator 0 (Nat.succ_pos length)
      have hsolo0 : IsQuittingSoloRoot (roots start) (owner start) := by
        simpa using hsolo 0 (Nat.succ_pos length)
      have hspectatorTail : ∀ offset, offset < length →
          who ≠ owner (start + 1 + offset) := by
        intro offset hoffset
        have hshift := hspectator (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hsoloTail : ∀ offset, offset < length →
          IsQuittingSoloRoot (roots (start + 1 + offset))
            (owner (start + 1 + offset)) := by
        intro offset hoffset
        have hshift := hsolo (offset + 1) (by omega)
        rwa [show start + (offset + 1) = start + 1 + offset from by omega]
          at hshift
      have hstep : value start who =
          quittingSoloTailHazard roots owner start *
              quittingSoloReward reward (owner start) who +
            quittingSoloTailContinueMass roots owner start *
              value (start + 1) who := by
        conv_lhs => rw [hpolicy start]
        exact hsolo0.successorPayoff_other reward hspectator0
          (value (start + 1))
      have hIH := ih (start + 1) hsoloTail hspectatorTail
      have hmass := quittingSoloTailContinueMass_add_hazard roots owner start
      have hsum :
          (∑ offset ∈ Finset.range (length + 1),
              quittingSoloTailWindowWeight roots owner start offset *
                (quittingSoloReward reward (owner (start + offset)) who -
                  base)) =
            quittingSoloTailHazard roots owner start *
                (quittingSoloReward reward (owner start) who - base) +
              quittingSoloTailContinueMass roots owner start *
                ∑ offset ∈ Finset.range length,
                  quittingSoloTailWindowWeight roots owner (start + 1) offset *
                    (quittingSoloReward reward
                      (owner (start + 1 + offset)) who - base) := by
        have hshift : ∀ offset ∈ Finset.range length,
            quittingSoloTailWindowWeight roots owner start (offset + 1) *
                (quittingSoloReward reward
                  (owner (start + (offset + 1))) who - base) =
              quittingSoloTailContinueMass roots owner start *
                (quittingSoloTailWindowWeight roots owner (start + 1) offset *
                  (quittingSoloReward reward
                    (owner (start + 1 + offset)) who - base)) := by
          intro offset _
          unfold quittingSoloTailWindowWeight
          rw [quittingSoloTailSurvival_succ_left,
            show start + (offset + 1) = start + 1 + offset from by omega]
          ring
        rw [Finset.sum_range_succ', Finset.sum_congr rfl hshift,
          ← Finset.mul_sum]
        have hfirst : quittingSoloTailWindowWeight roots owner start 0 *
            (quittingSoloReward reward (owner (start + 0)) who - base) =
              quittingSoloTailHazard roots owner start *
                (quittingSoloReward reward (owner start) who - base) := by
          simp [quittingSoloTailWindowWeight]
        rw [hfirst, add_comm]
      rw [hsum, show start + (length + 1) = start + 1 + length from by omega,
        quittingSoloTailSurvival_succ_left, hstep]
      linear_combination quittingSoloTailContinueMass roots owner start * hIH +
        base * hmass

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
spectator's displacement from its own singleton reward is its discounted
matrix flow plus the surviving endpoint displacement. -/
theorem quittingSoloTailValue_sub_soloReward_eq_matrixFlow_add_survival
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hspectator : ∀ offset, offset < length → who ≠ owner (start + offset)) :
    value start who - quittingSoloReward reward who who =
      quittingSoloTailMatrixFlow reward roots owner who start length +
        quittingSoloTailSurvival roots owner start length *
          (value (start + length) who - quittingSoloReward reward who who) := by
  have hbase := quittingSoloTailValue_sub_eq_windowFlow_add_survival roots value
    owner hpolicy who (quittingSoloReward reward who who) start length hsolo
    hspectator
  rw [hbase, quittingSoloTailMatrixFlow]
  refine congrArg (· + _) (Finset.sum_congr rfl fun offset _ => ?_)
  rw [normalizedSoloMatrix_eq_soloReward_sub]

/-- **Pinned-end form.**  A window across which a spectator's prescribed value
returns to its own singleton reward carries exactly zero discounted matrix
flow. -/
theorem quittingSoloTailMatrixFlow_eq_zero_of_pinnedEnds
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who : ι) (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hspectator : ∀ offset, offset < length → who ≠ owner (start + offset))
    (hstart : value start who = quittingSoloReward reward who who)
    (hend : value (start + length) who = quittingSoloReward reward who who) :
    quittingSoloTailMatrixFlow reward roots owner who start length = 0 := by
  have hidentity :=
    quittingSoloTailValue_sub_soloReward_eq_matrixFlow_add_survival roots value
      owner hpolicy who start length hsolo hspectator
  rw [hstart, hend] at hidentity
  simp only [sub_self, mul_zero, add_zero] at hidentity
  linarith

/-- At a strictly mixing date on which `who` is the exact-Nash soloist, both
`who`'s prescribed value at that date and its declared continuation are its
own singleton reward. -/
theorem quittingSoloTailValue_eq_soloReward_of_activeInterior
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (hsolo : ∀ time, IsQuittingSoloRoot (roots time) (owner time))
    (who : ι) (time : ℕ) (hactive : owner time = who)
    (hquit : 0 < (roots time who true).toReal)
    (hcontinue : 0 < (roots time who false).toReal) :
    value time who = quittingSoloReward reward who who ∧
      value (time + 1) who = quittingSoloReward reward who who := by
  have hsoloTime : IsQuittingSoloRoot (roots time) who := by
    rw [← hactive]; exact hsolo time
  have hpin := hsoloTime.tail_owner_eq_soloReward_of_interior reward
    (hnash time) hquit hcontinue
  refine ⟨?_, hpin⟩
  have hstep := hsoloTime.successorPayoff_owner_eq_tail_of_interior reward
    (hnash time) hquit hcontinue
  rw [hpolicy time]
  exact hstep.trans hpin

/-- **Exact gap-return identity.**  Let `who` be the strictly mixing
exact-Nash soloist at two dates `fence` and `fence + 1 + length`, and let it
be a spectator at every date in between.  Then `who`'s discounted
normalized-solo-matrix flow across the intervening window is exactly zero:
every recurrent player's discounted flow over each of its gaps balances with
no error term. -/
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
    (hcloseContinue : 0 < (roots (fence + 1 + length) who false).toReal)
    (hspectator : ∀ offset, offset < length →
      who ≠ owner (fence + 1 + offset)) :
    quittingSoloTailMatrixFlow reward roots owner who (fence + 1) length = 0 := by
  have hstart := (quittingSoloTailValue_eq_soloReward_of_activeInterior roots
    value owner hpolicy hnash hsolo who fence hopen hopenQuit hopenContinue).2
  have hend := (quittingSoloTailValue_eq_soloReward_of_activeInterior roots
    value owner hpolicy hnash hsolo who (fence + 1 + length) hclose hcloseQuit
    hcloseContinue).1
  exact quittingSoloTailMatrixFlow_eq_zero_of_pinnedEnds roots value owner
    hpolicy who (fence + 1) length (fun offset _ => hsolo _) hspectator hstart
    hend

/-! ## Constant-soloist windows and the phantom mismatch -/

/-- **Constant-soloist window.**  When every date of the window is solo at one
fixed coordinate, the window's absorbed mass is the complement of its survival
and the whole absorbed mass delivers that coordinate's singleton row. -/
theorem quittingSoloTailValue_sub_eq_absorbedMass_mul_of_constantOwner
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι) (owner : ℕ → ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (who fixedOwner : ι) (hne : who ≠ fixedOwner) (base : ℝ)
    (start length : ℕ)
    (hsolo : ∀ offset, offset < length →
      IsQuittingSoloRoot (roots (start + offset)) (owner (start + offset)))
    (hconstant : ∀ offset, offset < length → owner (start + offset) = fixedOwner) :
    value start who - base =
      (1 - quittingSoloTailSurvival roots owner start length) *
          (quittingSoloReward reward fixedOwner who - base) +
        quittingSoloTailSurvival roots owner start length *
          (value (start + length) who - base) := by
  have hspectator : ∀ offset, offset < length → who ≠ owner (start + offset) := by
    intro offset hoffset
    rw [hconstant offset hoffset]
    exact hne
  have hbase := quittingSoloTailValue_sub_eq_windowFlow_add_survival roots value
    owner hpolicy who base start length hsolo hspectator
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
      1 - quittingSoloTailSurvival roots owner start length := by linarith
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
      -((1 - quittingSoloTailSurvival roots owner start length) * margin) +
        quittingSoloTailSurvival roots owner start length *
          (value (start + length) who - base) := by
  have hidentity := quittingSoloTailValue_sub_eq_absorbedMass_mul_of_constantOwner
    roots value owner hpolicy who fixedOwner hpreempt.1 base start length
    (fun offset _ => hsolo _) hconstant
  have hmismatch := quittingSoloTailWindowDelivery_sub_base_le_neg_margin reward
    hpreempt hfloor
  have hsurvival :=
    quittingSoloTailSurvival_mem_unitInterval roots owner start length
  nlinarith [hidentity, hmismatch, hsurvival.2]

end GameTheory
