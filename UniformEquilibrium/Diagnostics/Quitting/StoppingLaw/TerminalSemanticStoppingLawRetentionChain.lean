/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Finset.MonotoneChainChangeBudget
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.TerminalSemanticStoppingLawGlobalRetention
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

/-!
# Retention along stopping-law reset chains

If each edge in a finite interval retains a fixed chronological atom by a
common nonnegative factor `a`, then `m` composable edges retain `a^m` of that
atom. The premise is pointwise in its terminal and time. Global all-atom
retention supplies it by specialization, while support results quantify only
over the singleton atoms they actually use.

These bounds specialize to `2⁻ᵐ` for half resets. Combined with finite live
support, they give saturated-support rigidity, a finite support-change budget,
and one-active owner locking.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct
open Math.Finset.MonotoneChainChangeBudget

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Uniform pointwise retention of every chronological coalition atom. -/
def RetainsAllQuittingStageAtoms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (factor : ℝ)
    (source target : (quittingGame reward).BehaviorProfile) : Prop :=
  ∀ terminal time,
    factor * quittingStageCoalitionMass reward source time terminal ≤
      quittingStageCoalitionMass reward target time terminal

/-- Retention of one fixed chronological atom on exactly the finite interval
of edges starting at `start`. The edge at offset `k` runs from `start + k` to
`start + k + 1`. -/
def RetainsQuittingStageAtomOnInterval
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (factor : ℝ)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (start steps : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ) : Prop :=
  ∀ offset, offset < steps →
    factor * quittingStageCoalitionMass reward
        (profiles (start + offset)) time terminal ≤
      quittingStageCoalitionMass reward
        (profiles (start + offset + 1)) time terminal

/-- Retention on a finite interval restricts to any shorter prefix. -/
theorem RetainsQuittingStageAtomOnInterval.mono_steps
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (factor : ℝ)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (start : ℕ) {short long : ℕ}
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hretain : RetainsQuittingStageAtomOnInterval
      reward factor profiles start long terminal time)
    (hle : short ≤ long) :
    RetainsQuittingStageAtomOnInterval
      reward factor profiles start short terminal time := by
  intro offset hoffset
  exact hretain offset (hoffset.trans_le hle)

/-- Retention factors multiply under composition. -/
theorem RetainsAllQuittingStageAtoms.comp
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {firstFactor secondFactor : ℝ}
    {first second third : (quittingGame reward).BehaviorProfile}
    (hsecondFactor : 0 ≤ secondFactor)
    (hfirst : RetainsAllQuittingStageAtoms reward firstFactor first second)
    (hsecond : RetainsAllQuittingStageAtoms reward secondFactor second third) :
    RetainsAllQuittingStageAtoms reward
      (secondFactor * firstFactor) first third := by
  intro terminal time
  calc
    (secondFactor * firstFactor) *
          quittingStageCoalitionMass reward first time terminal =
        secondFactor *
          (firstFactor *
            quittingStageCoalitionMass reward first time terminal) := by ring
    _ ≤ secondFactor *
          quittingStageCoalitionMass reward second time terminal :=
      mul_le_mul_of_nonneg_left (hfirst terminal time) hsecondFactor
    _ ≤ quittingStageCoalitionMass reward third time terminal :=
      hsecond terminal time

/-- **Arbitrary finite retention-chain bound.**  If every consecutive edge
retains a common nonnegative factor, an interval of `steps` edges retains its
`steps`-th power simultaneously for every terminal and time. -/
theorem factorPow_mul_stageCoalitionMass_le_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 ≤ factor)
    (start steps : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hstep : RetainsQuittingStageAtomOnInterval
      reward factor profiles start steps terminal time) :
    factor ^ steps *
        quittingStageCoalitionMass reward (profiles start) time terminal ≤
      quittingStageCoalitionMass reward (profiles (start + steps)) time terminal := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : RetainsQuittingStageAtomOnInterval
          reward factor profiles start steps terminal time :=
        RetainsQuittingStageAtomOnInterval.mono_steps
          reward factor profiles start terminal time hstep (Nat.le_succ steps)
      have hscaled :
          factor *
              (factor ^ steps *
                quittingStageCoalitionMass reward (profiles start) time terminal) ≤
            factor *
              quittingStageCoalitionMass reward (profiles (start + steps))
                time terminal :=
        mul_le_mul_of_nonneg_left (ih hprefix) hfactor
      calc
        factor ^ (steps + 1) *
              quittingStageCoalitionMass reward (profiles start) time terminal =
            factor *
              (factor ^ steps *
                quittingStageCoalitionMass reward (profiles start) time terminal) := by
          rw [pow_succ]
          ring
        _ ≤ factor *
              quittingStageCoalitionMass reward (profiles (start + steps))
                time terminal := hscaled
        _ ≤ quittingStageCoalitionMass reward
              (profiles ((start + steps) + 1)) time terminal :=
          hstep steps (Nat.lt_succ_self steps)
        _ = quittingStageCoalitionMass reward
              (profiles (start + (steps + 1))) time terminal := by
          rw [Nat.add_assoc]

/-- Every positive chronological atom remains positive along a finite chain
whose common retention factor is positive. -/
theorem stageCoalitionMass_pos_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (start steps : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hstep : RetainsQuittingStageAtomOnInterval
      reward factor profiles start steps terminal time)
    (hpositive : 0 <
      quittingStageCoalitionMass reward (profiles start) time terminal) :
    0 < quittingStageCoalitionMass reward
      (profiles (start + steps)) time terminal := by
  have hretained := factorPow_mul_stageCoalitionMass_le_of_resetChain
    reward profiles factor hfactor.le start steps terminal time hstep
  have hscaled : 0 < factor ^ steps *
      quittingStageCoalitionMass reward (profiles start) time terminal :=
    mul_pos (pow_pos hfactor steps) hpositive
  exact hscaled.trans_le hretained

/-- Positive singleton incidence support is monotone across one edge with a
positive retention factor. -/
theorem quittingPositiveSingletonStageSupport_mono_of_retention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor) (time : ℕ)
    (hretain : ∀ owner,
      factor * quittingStageCoalitionMass reward source time
          (quittingSingletonTerminal owner) ≤
        quittingStageCoalitionMass reward target time
          (quittingSingletonTerminal owner)) :
    quittingPositiveSingletonStageSupport reward source time ⊆
      quittingPositiveSingletonStageSupport reward target time := by
  intro owner howner
  have hsource : 0 < quittingStageCoalitionMass reward source time
      (quittingSingletonTerminal owner) := by
    simpa [quittingPositiveSingletonStageSupport] using howner
  have htarget : 0 < quittingStageCoalitionMass reward target time
      (quittingSingletonTerminal owner) :=
    (mul_pos hfactor hsource).trans_le
      (hretain owner)
  simpa [quittingPositiveSingletonStageSupport] using htarget

/-- Singleton incidence support is monotone along an arbitrary finite
positive-retention interval, not just across one edge. -/
theorem quittingPositiveSingletonStageSupport_mono_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (start steps : ℕ)
    (time : ℕ)
    (hstep : ∀ owner, RetainsQuittingStageAtomOnInterval
      reward factor profiles start steps
        (quittingSingletonTerminal owner) time) :
    quittingPositiveSingletonStageSupport reward (profiles start) time ⊆
      quittingPositiveSingletonStageSupport reward
        (profiles (start + steps)) time := by
  intro owner howner
  have hpositive : 0 < quittingStageCoalitionMass reward
      (profiles start) time (quittingSingletonTerminal owner) := by
    simpa [quittingPositiveSingletonStageSupport] using howner
  have htarget := stageCoalitionMass_pos_of_resetChain
    reward profiles factor hfactor start steps
      (quittingSingletonTerminal owner) time (hstep owner) hpositive
  simpa [quittingPositiveSingletonStageSupport] using htarget

/-! ## Bridge to stage-action `K/N` support -/

/-- Positive singleton terminal mass at a stage forces the singleton owner
to have positive Quit hazard in that stage's live product root. -/
theorem quittingPositiveSingletonStageSupport_subset_positiveHazardSupport
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ) :
    quittingPositiveSingletonStageSupport reward profile time ⊆
      quittingPositiveHazardSupport
        (quittingProfileLiveRoot reward profile time) := by
  intro owner howner
  have hstage : 0 < quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal owner) := by
    simpa [quittingPositiveSingletonStageSupport] using howner
  have hquit := positive_profileLiveRoot_quit_of_positive_stageCoalitionMass
    reward profile time (quittingSingletonTerminal owner) owner
      (by simp [quittingSingletonTerminal]) hstage
  simpa [quittingPositiveHazardSupport, hazardOfRoot] using hquit

/-- A `K`-active live root bounds the number of positive singleton terminal
atoms at that chronological stage by the same `K`. -/
theorem quittingPositiveSingletonStageSupport_card_le_of_KActive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time K : ℕ)
    (hK : HasQuittingSupportCardAtMost K
      (quittingProfileLiveRoot reward profile time)) :
    (quittingPositiveSingletonStageSupport reward profile time).card ≤ K := by
  exact (Finset.card_le_card
    (quittingPositiveSingletonStageSupport_subset_positiveHazardSupport
      reward profile time)).trans hK

/-- **Saturated-support rigidity for one retained edge.**  If the source has
`K` positive singleton atoms and the target live root is `K`-active, positive
retention of those singleton atoms forces the two supports to agree. -/
theorem quittingPositiveSingletonStageSupport_eq_of_saturated_retention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor) (time K : ℕ)
    (hretain : ∀ owner,
      factor * quittingStageCoalitionMass reward source time
          (quittingSingletonTerminal owner) ≤
        quittingStageCoalitionMass reward target time
          (quittingSingletonTerminal owner))
    (hsourceCard :
      (quittingPositiveSingletonStageSupport reward source time).card = K)
    (htargetK : HasQuittingSupportCardAtMost K
      (quittingProfileLiveRoot reward target time)) :
    quittingPositiveSingletonStageSupport reward source time =
      quittingPositiveSingletonStageSupport reward target time := by
  have hsubset := quittingPositiveSingletonStageSupport_mono_of_retention
    reward source target factor hfactor time hretain
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hsourceCard]
  exact quittingPositiveSingletonStageSupport_card_le_of_KActive
    reward target time K htargetK

/-- **Saturated-support rigidity along a retention chain.**  If the source
has exactly `K` positive singleton atoms and the selected target phase is
`K`-active at the same stage, positive retention forces equal support. -/
theorem quittingPositiveSingletonStageSupport_eq_of_saturated_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (phase time K : ℕ)
    (hstep : ∀ owner, RetainsQuittingStageAtomOnInterval
      reward factor profiles 0 phase
        (quittingSingletonTerminal owner) time)
    (hsourceCard :
      (quittingPositiveSingletonStageSupport reward (profiles 0) time).card = K)
    (hphaseK : HasQuittingSupportCardAtMost K
      (quittingProfileLiveRoot reward (profiles phase) time)) :
    quittingPositiveSingletonStageSupport reward (profiles 0) time =
      quittingPositiveSingletonStageSupport reward (profiles phase) time := by
  have hsubset :
      quittingPositiveSingletonStageSupport reward (profiles 0) time ⊆
        quittingPositiveSingletonStageSupport reward (profiles phase) time := by
    simpa using quittingPositiveSingletonStageSupport_mono_of_resetChain
      reward profiles factor hfactor 0 phase time hstep
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hsourceCard]
  exact quittingPositiveSingletonStageSupport_card_le_of_KActive
    reward (profiles phase) time K hphaseK

/-! ## Finite support-change budget -/

/-- Reset indices at which positive singleton support changes at one fixed
chronological stage. -/
def quittingSingletonSupportChangeTimes
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (time cutoff : ℕ) : Finset ℕ :=
  changeTimes
    (fun phase => quittingPositiveSingletonStageSupport
      reward (profiles phase) time) cutoff

/-- **`K`-active support-change budget.** Along a chain retaining every
singleton atom at the selected time, the initial support size plus the number
of genuine changes is at most the support cap at the final phase. -/
theorem initialSingletonCard_add_supportChanges_le_K
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (cutoff time K : ℕ)
    (hstep : ∀ owner, RetainsQuittingStageAtomOnInterval
      reward factor profiles 0 cutoff
        (quittingSingletonTerminal owner) time)
    (hcutoffK : HasQuittingSupportCardAtMost K
      (quittingProfileLiveRoot reward (profiles cutoff) time)) :
    (quittingPositiveSingletonStageSupport reward (profiles 0) time).card +
        (quittingSingletonSupportChangeTimes reward profiles time cutoff).card ≤ K := by
  let support : ℕ → Finset ι := fun phase =>
    quittingPositiveSingletonStageSupport reward (profiles phase) time
  have hmono : ∀ phase < cutoff, support phase ⊆ support (phase + 1) := by
    intro phase hphase
    exact quittingPositiveSingletonStageSupport_mono_of_retention
      reward (profiles phase) (profiles (phase + 1)) factor hfactor time
        (fun owner => by simpa using hstep owner phase hphase)
  have hbudget := initialCard_add_changeTimes_card_le_finalCard
    support cutoff hmono
  have hfinal : (support cutoff).card ≤ K :=
    quittingPositiveSingletonStageSupport_card_le_of_KActive
      reward (profiles cutoff) time K hcutoffK
  exact hbudget.trans hfinal

/-- At a one-active root, one positive singleton chronological atom identifies
the entire singleton support. -/
theorem quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (time : ℕ) (owner : ι)
    (hpositive : 0 < quittingStageCoalitionMass reward profile time
      (quittingSingletonTerminal owner))
    (hone : HasQuittingSupportCardAtMost 1
      (quittingProfileLiveRoot reward profile time)) :
    quittingPositiveSingletonStageSupport reward profile time = {owner} := by
  have hmem : owner ∈
      quittingPositiveSingletonStageSupport reward profile time := by
    simpa [quittingPositiveSingletonStageSupport] using hpositive
  have hsingletonSubset : ({owner} : Finset ι) ⊆
      quittingPositiveSingletonStageSupport reward profile time := by
    simpa using hmem
  have hcard := quittingPositiveSingletonStageSupport_card_le_of_KActive
    reward profile time 1 hone
  have hreverseCard :
      (quittingPositiveSingletonStageSupport reward profile time).card ≤
        ({owner} : Finset ι).card := by
    simpa using hcard
  exact (Finset.eq_of_subset_of_card_le
    hsingletonSubset hreverseCard).symm

/-- **One-active retained-owner lock.**  A positive source singleton atom,
positive retention, and a one-active target force that target's unique
singleton owner. No support cap is needed at the source. -/
theorem quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (factor : ℝ) (hfactor : 0 < factor)
    (phase time : ℕ) (owner : ι)
    (hstep : RetainsQuittingStageAtomOnInterval reward factor profiles 0 phase
      (quittingSingletonTerminal owner) time)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (hphaseOne : HasQuittingSupportCardAtMost 1
      (quittingProfileLiveRoot reward (profiles phase) time)) :
    quittingPositiveSingletonStageSupport reward (profiles phase) time = {owner} := by
  have htargetPositive := stageCoalitionMass_pos_of_resetChain
    reward profiles factor hfactor 0 phase
      (quittingSingletonTerminal owner) time hstep hpositive
  exact quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive
    reward (profiles phase) time owner (by simpa using htargetPositive) hphaseOne

end GameTheory
