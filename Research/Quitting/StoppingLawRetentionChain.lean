/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.StoppingLawGlobalRetention
import Research.General.FiveCycleIncidenceSupportRigidity
import Research.Quitting.KActiveCompactPath

/-!
# Iterated global retention along stopping-law reset chains

`QuittingStoppingLawGlobalRetention` proves that one half reset retains half
of every literal chronological coalition atom simultaneously.  This file
iterates that statement.  After `m` composable resets, every source atom is
still present with at least `2⁻ᵐ` of its original mass.

The important finite consequence is that one source singleton atom supplies
one common incidence label through all five phases of the exceptional reset
cycle.  The support-rigidity theorem can therefore use a constant incidence
selection and produces a consecutive two-edge window involving at most four
players.  No phasewise diagonal selection is needed.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Uniform pointwise retention of every chronological coalition atom. -/
def RetainsAllQuittingStageAtoms
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (factor : ℝ)
    (source target : (quittingGame reward).BehaviorProfile) : Prop :=
  ∀ terminal time,
    factor * quittingStageCoalitionMass reward source time terminal ≤
      quittingStageCoalitionMass reward target time terminal

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

/-- **Arbitrary finite reset-chain retention.**  If every consecutive edge
retains half of every atom, then an interval of `steps` edges retains the
factor `(1/2)^steps` simultaneously for every terminal and time. -/
theorem halfPow_mul_stageCoalitionMass_le_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (start steps : ℕ) (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ) :
    (1 / 2 : ℝ) ^ steps *
        quittingStageCoalitionMass reward (profiles start) time terminal ≤
      quittingStageCoalitionMass reward (profiles (start + steps)) time terminal := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hscaled :
          (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ steps *
                quittingStageCoalitionMass reward (profiles start) time terminal) ≤
            (1 / 2 : ℝ) *
              quittingStageCoalitionMass reward (profiles (start + steps))
                time terminal :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      calc
        (1 / 2 : ℝ) ^ (steps + 1) *
              quittingStageCoalitionMass reward (profiles start) time terminal =
            (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ steps *
                quittingStageCoalitionMass reward (profiles start) time terminal) := by
          rw [pow_succ]
          ring
        _ ≤ (1 / 2 : ℝ) *
              quittingStageCoalitionMass reward (profiles (start + steps))
                time terminal := hscaled
        _ ≤ quittingStageCoalitionMass reward
              (profiles ((start + steps) + 1)) time terminal :=
          hstep (start + steps) terminal time
        _ = quittingStageCoalitionMass reward
              (profiles (start + (steps + 1))) time terminal := by
          rw [Nat.add_assoc]

/-- Every positive chronological atom remains positive after any finite
number of half-retaining resets. -/
theorem stageCoalitionMass_pos_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (start steps : ℕ) (terminal : {S : Finset ι // S.Nonempty}) (time : ℕ)
    (hpositive : 0 <
      quittingStageCoalitionMass reward (profiles start) time terminal) :
    0 < quittingStageCoalitionMass reward
      (profiles (start + steps)) time terminal := by
  have hretained := halfPow_mul_stageCoalitionMass_le_of_resetChain
    reward profiles hstep start steps terminal time
  have hscaled : 0 < (1 / 2 : ℝ) ^ steps *
      quittingStageCoalitionMass reward (profiles start) time terminal :=
    mul_pos (pow_pos (by norm_num) steps) hpositive
  exact hscaled.trans_le hretained

/-- Singleton incidence support is monotone along an arbitrary finite reset
interval, not just across one reset. -/
theorem quittingPositiveSingletonStageSupport_mono_of_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (start steps time : ℕ) :
    quittingPositiveSingletonStageSupport reward (profiles start) time ⊆
      quittingPositiveSingletonStageSupport reward
        (profiles (start + steps)) time := by
  intro owner howner
  have hpositive : 0 < quittingStageCoalitionMass reward
      (profiles start) time (quittingSingletonTerminal owner) := by
    simpa [quittingPositiveSingletonStageSupport] using howner
  have htarget := stageCoalitionMass_pos_of_resetChain
    reward profiles hstep start steps (quittingSingletonTerminal owner) time hpositive
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

/-- **Saturated-support rigidity for one reset.**  If the source already has
`K` positive singleton atoms and the target live root is `K`-active, global
half-retention forces the target singleton support to equal the source
support exactly. -/
theorem quittingPositiveSingletonStageSupport_eq_of_saturated_halfRetention
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (source target : (quittingGame reward).BehaviorProfile)
    (time K : ℕ)
    (hretain : RetainsAllQuittingStageAtoms reward (1 / 2) source target)
    (hsourceCard :
      (quittingPositiveSingletonStageSupport reward source time).card = K)
    (htargetK : HasQuittingSupportCardAtMost K
      (quittingProfileLiveRoot reward target time)) :
    quittingPositiveSingletonStageSupport reward source time =
      quittingPositiveSingletonStageSupport reward target time := by
  have hsubset :=
    quittingPositiveSingletonStageSupport_mono_of_halfRetention
      reward source target time (fun owner => hretain _ _)
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hsourceCard]
  exact quittingPositiveSingletonStageSupport_card_le_of_KActive
    reward target time K htargetK

/-- **Saturated-support rigidity along a reset chain.**  If every target
profile is `K`-active at one fixed chronological stage and the source has
exactly `K` positive singleton atoms there, every finite reset phase has the
same singleton support. -/
theorem quittingPositiveSingletonStageSupport_eq_of_saturated_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (time K : ℕ)
    (hsourceCard :
      (quittingPositiveSingletonStageSupport reward (profiles 0) time).card = K)
    (hKActive : ∀ phase,
      HasQuittingSupportCardAtMost K
        (quittingProfileLiveRoot reward (profiles phase) time))
    (phase : ℕ) :
    quittingPositiveSingletonStageSupport reward (profiles 0) time =
      quittingPositiveSingletonStageSupport reward (profiles phase) time := by
  have hsubset :
      quittingPositiveSingletonStageSupport reward (profiles 0) time ⊆
        quittingPositiveSingletonStageSupport reward (profiles phase) time := by
    simpa using quittingPositiveSingletonStageSupport_mono_of_resetChain
      reward profiles hstep 0 phase time
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hsourceCard]
  exact quittingPositiveSingletonStageSupport_card_le_of_KActive
    reward (profiles phase) time K (hKActive phase)

/-! ## Finite support-change budget -/

/-- Indices below `cutoff` at which a finite-set sequence genuinely changes. -/
def finsetChangeTimes (support : ℕ → Finset ι) (cutoff : ℕ) : Finset ℕ :=
  (Finset.range cutoff).filter fun phase => support phase ≠ support (phase + 1)

omit [Fintype ι] in
/-- For a monotone finite-set chain, each change consumes at least one unit
of final cardinality. -/
theorem initialCard_add_changeTimes_card_le_finalCard
    (support : ℕ → Finset ι)
    (hmono : ∀ phase, support phase ⊆ support (phase + 1))
    (cutoff : ℕ) :
    (support 0).card + (finsetChangeTimes support cutoff).card ≤
      (support cutoff).card := by
  induction cutoff with
  | zero => simp [finsetChangeTimes]
  | succ cutoff ih =>
      by_cases heq : support cutoff = support (cutoff + 1)
      · have hchanges : finsetChangeTimes support (cutoff + 1) =
            finsetChangeTimes support cutoff := by
          ext phase
          by_cases hphase : phase = cutoff
          · subst phase
            simp [finsetChangeTimes, heq]
          · simp only [finsetChangeTimes, Finset.mem_filter,
              Finset.mem_range]
            constructor
            · rintro ⟨hphaseLt, hchange⟩
              exact ⟨by omega, hchange⟩
            · rintro ⟨hphaseLt, hchange⟩
              exact ⟨by omega, hchange⟩
        rw [hchanges, ← heq]
        exact ih
      · have hstrict : (support cutoff).card < (support (cutoff + 1)).card := by
          have hle := Finset.card_le_card (hmono cutoff)
          by_contra hnot
          have hreverse : (support (cutoff + 1)).card ≤ (support cutoff).card := by
            omega
          exact heq (Finset.eq_of_subset_of_card_le (hmono cutoff) hreverse)
        have hchangesSet : finsetChangeTimes support (cutoff + 1) =
            insert cutoff (finsetChangeTimes support cutoff) := by
          ext phase
          by_cases hphase : phase = cutoff
          · subst phase
            simp [finsetChangeTimes, heq]
          · simp only [finsetChangeTimes, Finset.mem_filter,
              Finset.mem_range, Finset.mem_insert]
            constructor
            · rintro ⟨hphaseLt, hchange⟩
              exact Or.inr ⟨by omega, hchange⟩
            · rintro (hphaseEq | ⟨hphaseLt, hchange⟩)
              · exact False.elim (hphase hphaseEq)
              · exact ⟨by omega, hchange⟩
        have hnotmem : cutoff ∉ finsetChangeTimes support cutoff := by
          simp [finsetChangeTimes]
        rw [hchangesSet, Finset.card_insert_of_notMem hnotmem]
        omega

/-- Reset indices at which positive singleton support changes at one fixed
chronological stage. -/
def quittingSingletonSupportChangeTimes
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (time cutoff : ℕ) : Finset ℕ :=
  finsetChangeTimes
    (fun phase => quittingPositiveSingletonStageSupport
      reward (profiles phase) time) cutoff

/-- **`K`-active support-change budget.**  Along a globally half-retaining
reset chain whose live roots are `K`-active at a fixed chronological stage,
the initial singleton-support size plus the number of genuine support
changes is at most `K`. -/
theorem initialSingletonCard_add_supportChanges_le_K
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (time K cutoff : ℕ)
    (hKActive : ∀ phase,
      HasQuittingSupportCardAtMost K
        (quittingProfileLiveRoot reward (profiles phase) time)) :
    (quittingPositiveSingletonStageSupport reward (profiles 0) time).card +
        (quittingSingletonSupportChangeTimes reward profiles time cutoff).card ≤ K := by
  let support : ℕ → Finset ι := fun phase =>
    quittingPositiveSingletonStageSupport reward (profiles phase) time
  have hmono : ∀ phase, support phase ⊆ support (phase + 1) := by
    intro phase
    apply quittingPositiveSingletonStageSupport_mono_of_halfRetention
    intro owner
    exact hstep phase (quittingSingletonTerminal owner) time
  have hbudget := initialCard_add_changeTimes_card_le_finalCard
    support hmono cutoff
  have hfinal : (support cutoff).card ≤ K :=
    quittingPositiveSingletonStageSupport_card_le_of_KActive
      reward (profiles cutoff) time K (hKActive cutoff)
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

/-- **One-active retained-owner lock.**  If every profile in a reset chain is
one-active at a fixed chronological stage, a positive source singleton atom
forces the same unique singleton owner at that stage in every reset phase. -/
theorem quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive_resetChain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (time : ℕ) (owner : ι)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal owner))
    (hone : ∀ phase,
      HasQuittingSupportCardAtMost 1
        (quittingProfileLiveRoot reward (profiles phase) time))
    (phase : ℕ) :
    quittingPositiveSingletonStageSupport reward (profiles phase) time = {owner} := by
  have hsource :=
    quittingPositiveSingletonStageSupport_eq_singleton_of_oneActive
      reward (profiles 0) time owner hpositive (hone 0)
  have hsourceCard :
      (quittingPositiveSingletonStageSupport reward (profiles 0) time).card = 1 := by
    rw [hsource]
    simp
  have hfixed := quittingPositiveSingletonStageSupport_eq_of_saturated_resetChain
    reward profiles hstep time 1 hsourceCard hone phase
  rw [← hfixed]
  exact hsource

/-! ## The exceptional five-cycle gets one common incidence label -/

/-- **Global retention collapses the phasewise incidence choice.**  A single
positive singleton atom at the source belongs to the retained support at all
five reset phases.  Selecting that one label throughout invokes the constant
incidence form of five-cycle rigidity and produces a consecutive two-edge
window omitting a player. -/
theorem exists_commonIncidence_omittedWindow_of_halfRetentionChain
    (reward : {S : Finset (Fin 5) // S.Nonempty} → Payoff (Fin 5))
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (incidenceLabel : Fin 5) (time : ℕ)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal incidenceLabel)) :
    let support : Fin 5 → Finset (Fin 5) := fun phase =>
      quittingPositiveSingletonStageSupport reward (profiles phase.val) time
    ∃ incidence : Fin 5 → Fin 5,
      IsSupportedIncidenceSelection support incidence ∧
        ∃ phase omitted,
          omitted ∉ fiveCycleResetRoleWindow incidence phase ∪
            fiveCycleResetRoleWindow incidence (phase + 1) := by
  dsimp only
  apply exists_supported_constantIncidence_omittedWindow
  intro phase
  have hphase := stageCoalitionMass_pos_of_resetChain
    reward profiles hstep 0 phase.val
      (quittingSingletonTerminal incidenceLabel) time hpositive
  simpa [quittingPositiveSingletonStageSupport] using hphase

/-! ## A general `4/N` two-reset packet -/

/-- The player labels distinguished by two composable directed reset edges
and one common retained incidence label. -/
def matchedTwoResetRoleSupport
    (firstOwner sharedRecipient secondRecipient incidenceLabel : ι) : Finset ι :=
  {firstOwner, sharedRecipient, incidenceLabel} ∪
    {sharedRecipient, secondRecipient, incidenceLabel}

omit [Fintype ι] in
/-- The matched two-reset packet has support cardinality at most four over
an arbitrary ambient player type. -/
theorem matchedTwoResetRoleSupport_card_le_four
    (firstOwner sharedRecipient secondRecipient incidenceLabel : ι) :
    (matchedTwoResetRoleSupport firstOwner sharedRecipient
      secondRecipient incidenceLabel).card ≤ 4 := by
  let roles : Finset ι :=
    {firstOwner, sharedRecipient, secondRecipient, incidenceLabel}
  have hsubset :
      matchedTwoResetRoleSupport firstOwner sharedRecipient
          secondRecipient incidenceLabel ⊆ roles := by
    intro player hplayer
    simp only [matchedTwoResetRoleSupport, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hplayer ⊢
    aesop
  have hfour : roles.card ≤ 4 := by
    dsimp only [roles]
    have h1 := Finset.card_insert_le firstOwner
      ({sharedRecipient, secondRecipient, incidenceLabel} : Finset ι)
    have h2 := Finset.card_insert_le sharedRecipient
      ({secondRecipient, incidenceLabel} : Finset ι)
    have h3 := Finset.card_insert_le secondRecipient
      ({incidenceLabel} : Finset ι)
    simp only [Finset.card_singleton] at h3
    omega
  exact (Finset.card_le_card hsubset).trans hfour

/-- If the ambient game has more than four players, every matched two-reset
packet omits at least one player. -/
theorem exists_omitted_of_matchedTwoResetRoleSupport
    (hcard : 4 < Fintype.card ι)
    (firstOwner sharedRecipient secondRecipient incidenceLabel : ι) :
    ∃ omitted,
      omitted ∉ matchedTwoResetRoleSupport firstOwner sharedRecipient
        secondRecipient incidenceLabel := by
  let roles := matchedTwoResetRoleSupport firstOwner sharedRecipient
    secondRecipient incidenceLabel
  have hlt : roles.card < Fintype.card ι :=
    lt_of_le_of_lt
      (matchedTwoResetRoleSupport_card_le_four firstOwner sharedRecipient
        secondRecipient incidenceLabel) hcard
  have hproper : roles ≠ Finset.univ := by
    intro heq
    have heqCard : roles.card = Fintype.card ι := by
      rw [heq, Finset.card_univ]
    omega
  by_contra hnone
  push Not at hnone
  exact hproper (Finset.eq_univ_iff_forall.mpr hnone)

/-- **General local `4/N` reset alternative.**  At a minimum terminal-law
point, following one positive debt transfer through its recipient either
produces a quantitative excess charge or a second transfer.  In the latter
branch the two composable edges, together with any fixed globally retained
incidence label, use at most four ambient players and retain one quarter of
every source chronological atom. -/
theorem exists_twoReset_K4RoleWindow_or_excessCharge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (firstMover incidenceLabel : ι)
    (hfirstDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) firstMover)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ firstTargetProfile : (quittingGame reward).BehaviorProfile,
      let source := quittingTerminalSemanticPair reward profile
      let firstTarget := quittingTerminalSemanticPair reward firstTargetProfile
      let excess := quittingTerminalSemanticDebtSum firstTarget -
        quittingTerminalSemanticDebtSum source
      ∃ secondMover ∈ Finset.univ.erase firstMover,
        0 < quittingTerminalSemanticDebtChange source firstTarget secondMover ∧
        0 < quittingTerminalSemanticDebt firstTarget secondMover ∧
        0 ≤ excess ∧
        (∀ terminal time,
          (1 / 2) * quittingStageCoalitionMass reward profile time terminal ≤
            quittingStageCoalitionMass reward firstTargetProfile time terminal) ∧
        (quittingTerminalSemanticDebt firstTarget secondMover / 4 ≤ excess ∨
          ∃ secondTargetProfile : (quittingGame reward).BehaviorProfile,
            ∃ thirdMover ∈ Finset.univ.erase secondMover,
              0 < quittingTerminalSemanticDebtChange firstTarget
                (quittingTerminalSemanticPair reward secondTargetProfile)
                thirdMover ∧
              (matchedTwoResetRoleSupport firstMover secondMover
                thirdMover incidenceLabel).card ≤ 4 ∧
              ∀ terminal time,
                (1 / 4) *
                    quittingStageCoalitionMass reward profile time terminal ≤
                  quittingStageCoalitionMass reward secondTargetProfile
                    time terminal) := by
  obtain ⟨firstBestResponse, hfirst⟩ :=
    exists_twoMatchedHalfResets_or_firstExcessCharge
      reward profile firstMover hfirstDebt hminimum
  dsimp only at hfirst
  let firstMixedStrategy := quittingStoppingLawMixtureBehaviorStrategy
    reward firstMover (profile firstMover) firstBestResponse
      (1 / 2) (by norm_num) (by norm_num)
  let firstTargetProfile :=
    Function.update profile firstMover firstMixedStrategy
  obtain ⟨secondMover, hsecondMem, hsecondChange, hsecondDebt, hexcess,
      hhalfRetention, hcase⟩ := hfirst
  refine ⟨firstTargetProfile, secondMover, hsecondMem, hsecondChange,
    hsecondDebt, hexcess, hhalfRetention, ?_⟩
  rcases hcase with hexcessCharge | htwo
  · exact Or.inl hexcessCharge
  · right
    obtain ⟨secondBestResponse, hsecond⟩ := htwo
    let secondMixedStrategy :=
      quittingStoppingLawMixtureBehaviorStrategy reward secondMover
        (firstTargetProfile secondMover) secondBestResponse
        (1 / 2) (by norm_num) (by norm_num)
    let secondTargetProfile :=
      Function.update firstTargetProfile secondMover secondMixedStrategy
    obtain ⟨thirdMover, hthirdMem, hthirdChange, hquarterRetention⟩ := hsecond
    exact ⟨secondTargetProfile, thirdMover, hthirdMem, hthirdChange,
      matchedTwoResetRoleSupport_card_le_four
        firstMover secondMover thirdMover incidenceLabel,
      hquarterRetention⟩

/-- For `4 < N`, the successful two-reset branch additionally returns a
literal ambient player omitted from the local packet. -/
theorem exists_twoReset_omittedPlayer_or_excessCharge
    (hcard : 4 < Fintype.card ι)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile)
    (firstMover incidenceLabel : ι)
    (hfirstDebt : 0 < quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) firstMover)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward profile) ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ firstTargetProfile : (quittingGame reward).BehaviorProfile,
      let source := quittingTerminalSemanticPair reward profile
      let firstTarget := quittingTerminalSemanticPair reward firstTargetProfile
      let excess := quittingTerminalSemanticDebtSum firstTarget -
        quittingTerminalSemanticDebtSum source
      ∃ secondMover ∈ Finset.univ.erase firstMover,
        0 < quittingTerminalSemanticDebtChange source firstTarget secondMover ∧
        0 < quittingTerminalSemanticDebt firstTarget secondMover ∧
        0 ≤ excess ∧
        (quittingTerminalSemanticDebt firstTarget secondMover / 4 ≤ excess ∨
          ∃ secondTargetProfile : (quittingGame reward).BehaviorProfile,
            ∃ thirdMover ∈ Finset.univ.erase secondMover,
              0 < quittingTerminalSemanticDebtChange firstTarget
                (quittingTerminalSemanticPair reward secondTargetProfile)
                thirdMover ∧
              ∃ omitted,
                omitted ∉ matchedTwoResetRoleSupport firstMover secondMover
                  thirdMover incidenceLabel ∧
                ∀ terminal time,
                  (1 / 4) *
                      quittingStageCoalitionMass reward profile time terminal ≤
                    quittingStageCoalitionMass reward secondTargetProfile
                      time terminal) := by
  obtain ⟨firstTargetProfile, hpacket⟩ :=
    exists_twoReset_K4RoleWindow_or_excessCharge reward profile
      firstMover incidenceLabel hfirstDebt hminimum
  dsimp only at hpacket
  obtain ⟨secondMover, hsecondMem, hsecondChange, hsecondDebt, hexcess,
      _hhalfRetention, hcase⟩ := hpacket
  refine ⟨firstTargetProfile, secondMover, hsecondMem, hsecondChange,
    hsecondDebt, hexcess, ?_⟩
  rcases hcase with hexcessCharge | htwo
  · exact Or.inl hexcessCharge
  · right
    obtain ⟨secondTargetProfile, thirdMover, hthirdMem, hthirdChange,
      _hfour, hquarterRetention⟩ := htwo
    obtain ⟨omitted, homitted⟩ :=
      exists_omitted_of_matchedTwoResetRoleSupport hcard
        firstMover secondMover thirdMover incidenceLabel
    exact ⟨secondTargetProfile, thirdMover, hthirdMem, hthirdChange,
      omitted, homitted, hquarterRetention⟩

/-! ## The general `(m+2)/N` retained-role law -/

/-- An `m`-edge composable reset chain is represented by its `m+1` transfer
vertices.  One common retained incidence label is added to those vertices. -/
def resetChainRoleSupport (edges : ℕ)
    (vertex : Fin (edges + 1) → ι) (incidenceLabel : ι) : Finset ι :=
  insert incidenceLabel (Finset.univ.image vertex)

omit [Fintype ι] in
/-- **General local role bound.**  An `m`-edge chain plus one retained atom
distinguishes at most `m+2` player labels, irrespective of ambient `N`. -/
theorem resetChainRoleSupport_card_le (edges : ℕ)
    (vertex : Fin (edges + 1) → ι) (incidenceLabel : ι) :
    (resetChainRoleSupport edges vertex incidenceLabel).card ≤ edges + 2 := by
  have hinsert := Finset.card_insert_le incidenceLabel (Finset.univ.image vertex)
  have himage : (Finset.univ.image vertex).card ≤ edges + 1 := by
    calc
      (Finset.univ.image vertex).card ≤ (Finset.univ : Finset (Fin (edges + 1))).card :=
        Finset.card_image_le
      _ = edges + 1 := by simp
  unfold resetChainRoleSupport
  omega

/-- Whenever `m+2 < N`, the retained-role packet omits an ambient player. -/
theorem exists_omitted_of_resetChainRoleSupport
    (edges : ℕ) (hcard : edges + 2 < Fintype.card ι)
    (vertex : Fin (edges + 1) → ι) (incidenceLabel : ι) :
    ∃ omitted, omitted ∉ resetChainRoleSupport edges vertex incidenceLabel := by
  let roles := resetChainRoleSupport edges vertex incidenceLabel
  have hlt : roles.card < Fintype.card ι :=
    lt_of_le_of_lt
      (resetChainRoleSupport_card_le edges vertex incidenceLabel) hcard
  have hproper : roles ≠ Finset.univ := by
    intro heq
    have heqCard : roles.card = Fintype.card ι := by
      rw [heq, Finset.card_univ]
    omega
  by_contra hnone
  push Not at hnone
  exact hproper (Finset.eq_univ_iff_forall.mpr hnone)

/-- **General retained `K/N` packet.**  Along `m` half-retaining resets, one
positive source singleton atom supplies a common incidence label at every
one of the `m+1` chain vertices, with quantitative retention `2⁻ᵖ` at phase
`p`.  Coupled with any composable transfer-vertex word, all distinguished
roles lie in a set of cardinality at most `m+2`. -/
theorem resetChain_has_commonIncidence_rolePacket
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (edges : ℕ) (vertex : Fin (edges + 1) → ι)
    (incidenceLabel : ι) (time : ℕ)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal incidenceLabel)) :
    (resetChainRoleSupport edges vertex incidenceLabel).card ≤ edges + 2 ∧
      ∀ phase : Fin (edges + 1),
        (1 / 2 : ℝ) ^ phase.val *
            quittingStageCoalitionMass reward (profiles 0) time
              (quittingSingletonTerminal incidenceLabel) ≤
          quittingStageCoalitionMass reward (profiles phase.val) time
            (quittingSingletonTerminal incidenceLabel) ∧
        incidenceLabel ∈ quittingPositiveSingletonStageSupport
          reward (profiles phase.val) time := by
  refine ⟨resetChainRoleSupport_card_le edges vertex incidenceLabel, ?_⟩
  intro phase
  have hretained := halfPow_mul_stageCoalitionMass_le_of_resetChain
    reward profiles hstep 0 phase.val
      (quittingSingletonTerminal incidenceLabel) time
  have hphase := stageCoalitionMass_pos_of_resetChain
    reward profiles hstep 0 phase.val
      (quittingSingletonTerminal incidenceLabel) time hpositive
  constructor
  · simpa using hretained
  · simpa [quittingPositiveSingletonStageSupport] using hphase

/-- Omitted-player form of the general packet when `m+2 < N`. -/
theorem resetChain_has_commonIncidence_omittedPlayer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (hstep : ∀ n,
      RetainsAllQuittingStageAtoms reward (1 / 2) (profiles n) (profiles (n + 1)))
    (edges : ℕ) (hcard : edges + 2 < Fintype.card ι)
    (vertex : Fin (edges + 1) → ι)
    (incidenceLabel : ι) (time : ℕ)
    (hpositive : 0 < quittingStageCoalitionMass reward (profiles 0) time
      (quittingSingletonTerminal incidenceLabel)) :
    ∃ omitted,
      omitted ∉ resetChainRoleSupport edges vertex incidenceLabel ∧
      ∀ phase : Fin (edges + 1),
        incidenceLabel ∈ quittingPositiveSingletonStageSupport
          reward (profiles phase.val) time := by
  obtain ⟨_hroles, hcommon⟩ := resetChain_has_commonIncidence_rolePacket
    reward profiles hstep edges vertex incidenceLabel time hpositive
  obtain ⟨omitted, homitted⟩ :=
    exists_omitted_of_resetChainRoleSupport edges hcard vertex incidenceLabel
  exact ⟨omitted, homitted, fun phase => (hcommon phase).2⟩

end GameTheory
