/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOffDiagonalStaticOrientationDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerResetAdapter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect

/-!
# Source-row atomic dispatch for a negative stopping-law collision

A positive rectangle atom with negative observer reward is carried by a loss
of terminal mass at the target endpoint.  Consequently the useful mass lies
at the literal source endpoint, where the target endpoint's vanishing
observer debt cannot be transported.

This file keeps that endpoint asymmetry.  It proves a uniform lower bound on
the source terminal mass, identifies the observer's finite pure stopping date,
and applies the atomic blocker barrier at the actual reached source row.  The
result is a state-matched finite strategic alternative: either a named
outsider has a root Nash defect of at least the counterexample gap against
the literal source continuation, or the observer has a punishment-refusal
certificate of the same size.  The persistent source-stage mass is retained
in both branches.  A finite-label extraction then freezes this alternative:
either one fixed outsider has a uniformly positive legal source-row gain, or
the refusal certificate persists along a strict subsequence.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal source endpoint of a rectangle packet after installing the
observer's selected pure-time response. -/
def quittingStoppingLawRectangleSourceProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq (packet.rank n)))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- The normalized persistent mass supplied by a negative rectangle atom. -/
def quittingStoppingLawNegativeCollisionMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : ℝ :=
  (packet.charge / 4) /
    ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      quittingRewardBound reward)

/-- The game-facing output at every actual source row carrying a fixed
negative collision.  The row is reached with uniform mass, the observer
Quits surely there, and either an outsider carries the full counterexample
gap as a state-matched root Nash defect or the observer carries the same gap
as an atomic punishment-refusal certificate. -/
def HasQuittingStoppingLawNegativeCollisionAtomicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (lower : ℝ) : Prop :=
  ∃ stop : ℕ → ℕ,
    (∀ n, packet.quitTime n = some (stop n)) ∧
    ∀ n,
      let profile := quittingStoppingLawRectangleSourceProfile packet n
      let root := quittingProfileLiveRoot reward profile (stop n)
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (stop n + 1))
      lower ≤ quittingStageCoalitionMass reward profile (stop n)
          packet.terminal ∧
        root packet.observer = PMF.pure true ∧
        ((∃ who, who ≠ packet.observer ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile (stop n)
                packet.terminal *
                  quittingRootCoordinateNashDefect reward tail.1 root who) ∨
          (regime.terminalGap ≤
              max 0
                (-quittingAtomicBlockerBalance reward root packet.observer) ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile (stop n)
                packet.terminal *
                  max 0
                    (-quittingAtomicBlockerBalance reward root
                      packet.observer)))

/-- The persistent source-mass scale is strictly positive on the negative
collision orientation. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.negativeCollisionMassLower_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    0 < quittingStoppingLawNegativeCollisionMassLower packet := by
  unfold quittingStoppingLawNegativeCollisionMassLower
  exact div_pos (div_pos packet.charge_pos (by norm_num))
    (mul_pos (by positivity) packet.rewardBound_pos)

/-- The repulsive atom quantitatively stores its mass at the source endpoint.
This is the negative-reward counterpart of the target-mass estimate used by
the positive marked-collision consumer. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.negativeCollision_sourceMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hnegative : reward packet.terminal packet.observer < 0) (n : ℕ) :
    quittingStoppingLawNegativeCollisionMassLower packet ≤
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleSourceProfile packet n)
        (some packet.terminal) := by
  classical
  let card : ℝ := Fintype.card (QuittingTerminalOutcome ι)
  let M := quittingRewardBound reward
  let targetProfile := Function.update
    (quittingStoppingLawRectangleTargetProfile packet n) packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))
  let sourceProfile := quittingStoppingLawRectangleSourceProfile packet n
  let targetMass := quittingTerminalOutcomeMass reward targetProfile
    (some packet.terminal)
  let sourceMass := quittingTerminalOutcomeMass reward sourceProfile
    (some packet.terminal)
  have hcard : 0 < card := by
    dsimp only [card]
    exact_mod_cast Fintype.card_pos
  have hMpos : 0 < M := packet.rewardBound_pos
  have htargetNonneg : 0 ≤ targetMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward targetProfile).1
      (some packet.terminal)
  have hsourceNonneg : 0 ≤ sourceMass :=
    (quittingTerminalOutcomeMass_mem_stdSimplex reward sourceProfile).1
      (some packet.terminal)
  have hbound := packet.atom_bound n
  have hsourceUpdate : Function.update
      (frontier.profiles (frontier.subseq (packet.rank n))) packet.mover.1
      (frontier.profiles (frontier.subseq (packet.rank n)) packet.mover.1) =
        frontier.profiles (frontier.subseq (packet.rank n)) :=
    Function.update_eq_self _ _
  rw [hsourceUpdate] at hbound
  change packet.charge / 4 ≤ card *
      ((targetMass - sourceMass) *
        reward packet.terminal packet.observer) at hbound
  have hnegativeBound : -reward packet.terminal packet.observer ≤ M := by
    rw [← abs_of_neg hnegative]
    exact abs_reward_le_quittingRewardBound reward packet.terminal
      packet.observer
  have hproductLe :
      (targetMass - sourceMass) * reward packet.terminal packet.observer ≤
        sourceMass * M := by
    calc
      (targetMass - sourceMass) * reward packet.terminal packet.observer =
          (sourceMass - targetMass) *
            (-reward packet.terminal packet.observer) := by ring
      _ ≤ sourceMass * (-reward packet.terminal packet.observer) := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (neg_nonneg.mpr hnegative.le)
      _ ≤ sourceMass * M := by
        exact mul_le_mul_of_nonneg_left hnegativeBound hsourceNonneg
  have hscaled := mul_le_mul_of_nonneg_left hproductLe hcard.le
  have htotal : packet.charge / 4 ≤ card * (sourceMass * M) :=
    hbound.trans hscaled
  unfold quittingStoppingLawNegativeCollisionMassLower
  apply (div_le_iff₀ (mul_pos hcard hMpos)).2
  change packet.charge / 4 ≤
    quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleSourceProfile packet n)
        (some packet.terminal) * (card * M)
  calc
    packet.charge / 4 ≤ card * (sourceMass * M) := htotal
    _ = sourceMass * (card * M) := by ring

/-- A negative observer-containing rectangle cannot use `Never`; its source
mass is concentrated at the observer's displayed finite pure stopping date. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_sourceStop_with_stageMassLower
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hnegative : reward packet.terminal packet.observer < 0) :
    ∃ stop : ℕ → ℕ,
      (∀ n, packet.quitTime n = some (stop n)) ∧
      ∀ n, quittingStoppingLawNegativeCollisionMassLower packet ≤
        quittingStageCoalitionMass reward
          (quittingStoppingLawRectangleSourceProfile packet n) (stop n)
          packet.terminal := by
  classical
  have hpositiveLower : 0 <
      quittingStoppingLawNegativeCollisionMassLower packet :=
    packet.negativeCollisionMassLower_pos
  have hfinite : ∀ n, ∃ stop, packet.quitTime n = some stop := by
    intro n
    cases htime : packet.quitTime n with
    | none =>
        have hsourceZero :=
          quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero reward
            (frontier.profiles (frontier.subseq (packet.rank n)))
            packet.observer packet.terminal hobserver
        have hlower := packet.negativeCollision_sourceMassLower hnegative n
        rw [quittingStoppingLawRectangleSourceProfile, htime,
          hsourceZero] at hlower
        exact False.elim ((not_lt_of_ge hlower) hpositiveLower)
    | some stop => exact ⟨stop, rfl⟩
  choose stop hstop using hfinite
  refine ⟨stop, hstop, ?_⟩
  intro n
  have hlower := packet.negativeCollision_sourceMassLower hnegative n
  rw [quittingStoppingLawRectangleSourceProfile, hstop n,
    quittingTerminalOutcomeMass_update_pureTime_some_mem_eq_at reward
      (frontier.profiles (frontier.subseq (packet.rank n)))
      packet.observer (stop n) packet.terminal hobserver] at hlower
  simpa [quittingStoppingLawRectangleSourceProfile, hstop n] using hlower

/-- **Negative-collision source-row closure.**  The repulsive rectangle
orientation reaches a literal source row with uniform mass.  At that same
row, and against its actual continuation value, either a named outsider has
the full counterexample-gap Nash defect or the observer has a punishment
refusal certificate of the same size. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.negativeCollision_atomicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hnegative : reward packet.terminal packet.observer < 0) :
    HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
      (quittingStoppingLawNegativeCollisionMassLower packet) := by
  classical
  obtain ⟨stop, hstop, hstage⟩ :=
    packet.exists_sourceStop_with_stageMassLower hobserver hnegative
  refine ⟨stop, hstop, ?_⟩
  intro n
  let profile := quittingStoppingLawRectangleSourceProfile packet n
  let root := quittingProfileLiveRoot reward profile (stop n)
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (stop n + 1))
  have howner : root packet.observer = PMF.pure true := by
    dsimp only [root, profile, quittingStoppingLawRectangleSourceProfile]
    rw [quittingProfileLiveRoot_update_pureTime_self, hstop n,
      quittingPureTimeHazard_some_self]
  have hbarrier := regime.terminalGap_le_atomicBlockerBarrier howner
  have hstageN : quittingStoppingLawNegativeCollisionMassLower packet ≤
      quittingStageCoalitionMass reward profile (stop n) packet.terminal := by
    simpa only [profile] using hstage n
  refine ⟨hstageN, howner, ?_⟩
  by_cases hdefect : regime.terminalGap ≤
      quittingForcedOwnerOutsiderDefect reward root packet.observer
  · left
    obtain ⟨who, hwho, hcoordinate⟩ :=
      exists_outsider_coordinateNashDefect_ge_of_forcedOwnerDefect_ge
        reward tail.1 root packet.observer howner regime.terminalGap_pos
          hdefect
    refine ⟨who, hwho, hcoordinate, ?_⟩
    exact mul_le_mul hstageN hcoordinate regime.terminalGap_pos.le
      (quittingStageCoalitionMass_nonneg reward profile (stop n)
        packet.terminal)
  · right
    have hrefusal : regime.terminalGap ≤
        max 0 (-quittingAtomicBlockerBalance reward root packet.observer) := by
      have hdefectLt :
          quittingForcedOwnerOutsiderDefect reward root packet.observer <
            regime.terminalGap := lt_of_not_ge hdefect
      by_contra hnot
      have hrefusalLt :
          max 0 (-quittingAtomicBlockerBalance reward root packet.observer) <
            regime.terminalGap := lt_of_not_ge hnot
      exact (not_lt_of_ge hbarrier) (max_lt hdefectLt hrefusalLt)
    refine ⟨hrefusal, ?_⟩
    exact mul_le_mul hstageN hrefusal regime.terminalGap_pos.le
      (quittingStageCoalitionMass_nonneg reward profile (stop n)
        packet.terminal)

/-! ## Fixed actual-source alternative -/

/-- **Negative-collision actual-source extraction.**  Along a strict
subsequence, either one fixed outsider has the full root defect and its
canonical legal source-row deviation has gain at least `lower * terminalGap`
at every selected row, or the observer's atomic refusal certificate persists
at every selected row.

No positivity premise on `lower` is required for this exact projection.  When
`lower` is the canonical negative-collision mass floor, its positivity follows
separately from `negativeCollisionMassLower_pos`. -/
theorem negativeCollisionAtomicDispatch_fixedActualSourceSubsequence
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    {lower : ℝ}
    (dispatch : HasQuittingStoppingLawNegativeCollisionAtomicDispatch
      packet lower) :
    ∃ (stop : ℕ → ℕ) (subseq : ℕ → ℕ),
      StrictMono subseq ∧
      (∀ rank, packet.quitTime (subseq rank) = some (stop (subseq rank))) ∧
      ((∃ who, who ≠ packet.observer ∧ ∀ rank,
          let profile := quittingStoppingLawRectangleSourceProfile packet
            (subseq rank)
          let root := quittingProfileLiveRoot reward profile
            (stop (subseq rank))
          let tail := quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile
              (stop (subseq rank) + 1))
          let action := quittingRootBestEndpointAction reward tail.1 root who
          let deviation := quittingStagePureEndpointBehaviorDeviation
            reward profile who (stop (subseq rank)) action
          lower ≤ quittingStageCoalitionMass reward profile
              (stop (subseq rank)) packet.terminal ∧
            root packet.observer = PMF.pure true ∧
            regime.terminalGap ≤
              quittingRootCoordinateNashDefect reward tail.1 root who ∧
            quittingTerminalPayoff reward
                  (Function.update profile who deviation) who -
                quittingTerminalPayoff reward profile who =
              quittingLiveMass reward profile (stop (subseq rank)) *
                quittingRootCoordinateNashDefect reward tail.1 root who ∧
            lower * regime.terminalGap ≤
              quittingTerminalPayoff reward
                  (Function.update profile who deviation) who -
                quittingTerminalPayoff reward profile who) ∨
        (∀ rank,
          let profile := quittingStoppingLawRectangleSourceProfile packet
            (subseq rank)
          let root := quittingProfileLiveRoot reward profile
            (stop (subseq rank))
          lower ≤ quittingStageCoalitionMass reward profile
              (stop (subseq rank)) packet.terminal ∧
            root packet.observer = PMF.pure true ∧
            regime.terminalGap ≤
              max 0 (-quittingAtomicBlockerBalance reward root
                packet.observer) ∧
            lower * regime.terminalGap ≤
              quittingStageCoalitionMass reward profile
                (stop (subseq rank)) packet.terminal *
                max 0 (-quittingAtomicBlockerBalance reward root
                  packet.observer))) := by
  classical
  obtain ⟨stop, hstop, hrows⟩ := dispatch
  let outsider : ℕ → ι → Prop := fun n who =>
    let profile := quittingStoppingLawRectangleSourceProfile packet n
    let root := quittingProfileLiveRoot reward profile (stop n)
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile (stop n + 1))
    who ≠ packet.observer ∧
      regime.terminalGap ≤
        quittingRootCoordinateNashDefect reward tail.1 root who ∧
      lower * regime.terminalGap ≤
        quittingStageCoalitionMass reward profile (stop n) packet.terminal *
          quittingRootCoordinateNashDefect reward tail.1 root who
  by_cases hfrequent : ∃ᶠ n in atTop, ∃ who, outsider n who
  · rw [Filter.frequently_exists] at hfrequent
    obtain ⟨who, hwhoFrequent⟩ := hfrequent
    obtain ⟨subseq, hsubseq, hwho⟩ :=
      extraction_of_frequently_atTop hwhoFrequent
    refine ⟨stop, subseq, hsubseq, fun rank => hstop (subseq rank),
      Or.inl ⟨who, (hwho 0).1, ?_⟩⟩
    intro rank
    dsimp only
    let profile := quittingStoppingLawRectangleSourceProfile packet
      (subseq rank)
    let root := quittingProfileLiveRoot reward profile (stop (subseq rank))
    let tail := quittingTerminalSemanticPair reward
      (quittingAllContinueProfileSpine reward profile
        (stop (subseq rank) + 1))
    obtain ⟨hmass, howner, _⟩ := hrows (subseq rank)
    have hfixed := hwho rank
    dsimp only [outsider] at hfixed
    have hgain :=
      quittingTerminalPayoff_stageBestEndpointDeviation_sub_eq_liveMass_mul_defect
        reward profile who (stop (subseq rank))
    have hlive : quittingStageCoalitionMass reward profile
        (stop (subseq rank)) packet.terminal ≤
        quittingLiveMass reward profile (stop (subseq rank)) :=
      quittingStageCoalitionMass_le_liveMass reward profile
        (stop (subseq rank)) packet.terminal
    have hdefectNonneg : 0 ≤ quittingRootCoordinateNashDefect reward
        tail.1 root who :=
      quittingRootCoordinateNashDefect_nonneg reward tail.1 root who
    have hweighted : lower * regime.terminalGap ≤
        quittingLiveMass reward profile (stop (subseq rank)) *
          quittingRootCoordinateNashDefect reward tail.1 root who :=
      hfixed.2.2.trans
        (mul_le_mul_of_nonneg_right hlive hdefectNonneg)
    refine ⟨hmass, howner, hfixed.2.1, ?_, ?_⟩
    · simpa only [profile, tail, root] using hgain
    · rw [hgain]
      simpa only [profile, tail, root] using hweighted
  · have hnoOutsider : ∀ᶠ n in atTop, ¬ ∃ who, outsider n who :=
      not_frequently.mp hfrequent
    obtain ⟨start, hstart⟩ := eventually_atTop.1 hnoOutsider
    let subseq : ℕ → ℕ := fun rank => start + rank
    have hsubseq : StrictMono subseq := fun _ _ hlt =>
      Nat.add_lt_add_left hlt start
    refine ⟨stop, subseq, hsubseq, fun rank => hstop (subseq rank),
      Or.inr ?_⟩
    intro rank
    dsimp only
    let profile := quittingStoppingLawRectangleSourceProfile packet
      (subseq rank)
    let root := quittingProfileLiveRoot reward profile (stop (subseq rank))
    obtain ⟨hmass, howner, halt⟩ := hrows (subseq rank)
    have hnone : ¬ ∃ who, outsider (subseq rank) who :=
      hstart (subseq rank) (Nat.le_add_right start rank)
    have hrefusal : regime.terminalGap ≤
          max 0 (-quittingAtomicBlockerBalance reward root packet.observer) ∧
        lower * regime.terminalGap ≤
          quittingStageCoalitionMass reward profile (stop (subseq rank))
            packet.terminal *
            max 0 (-quittingAtomicBlockerBalance reward root
              packet.observer) := by
      rcases halt with houtsider | hrefusal
      · exfalso
        apply hnone
        obtain ⟨who, hwho⟩ := houtsider
        exact ⟨who, by simpa only [outsider, profile, root] using hwho⟩
      · simpa only [profile, root] using hrefusal
    exact ⟨hmass, howner, hrefusal⟩

namespace QuittingCounterexampleStoppingLawFrontier

/-- **Exhaustive static frontier with negative collisions consumed.** The
negative observer-containing collision is routed to a persistent,
state-matched atomic source-row dispatch. The unconsumed atom orientations are
the prescribed comparison and the
observer-absent rectangle; the singleton and both collision signs have named
strategic consumers. -/
theorem exists_prescribed_or_absent_or_staticStrategicDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {regime : QuittingCounterexampleRegime reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier regime) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        packet.observer ∉ packet.terminal.val ∨
          HasQuittingStoppingLawSingletonStrategicOrientation packet ∨
          HasQuittingStoppingLawNegativeCollisionAtomicDispatch packet
            (quittingStoppingLawNegativeCollisionMassLower packet) ∨
          HasQuittingStoppingLawPositiveCollisionMarkedTailDispatch packet
            ((packet.charge / 4) /
              ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
                quittingRewardBound reward)) := by
  classical
  rcases frontier.exists_prescribed_or_staticRectangleDispatch with
    hprescribed | ⟨packet, habsent | hsingleton | hnegative | hmarked⟩
  · exact Or.inl hprescribed
  · exact Or.inr ⟨packet, Or.inl habsent⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inl hsingleton)⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inr (Or.inl
      (packet.negativeCollision_atomicDispatch hnegative.1
        hnegative.2.2)))⟩
  · exact Or.inr ⟨packet, Or.inr (Or.inr (Or.inr hmarked))⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
