import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Quitting.Terminal.OpponentTightTerminalSemanticRealization

/-!
# First outcome-law escape account

This module refines one already selected terminal-semantic/stopping-law
subsequence by the compact terminal-outcome simplex.  It then transports
finite-cut coalition masses through the same refinement.  The account proves
a strict common subsequence and nonnegative escape masses.  It makes no
reward-sign, strictly-positive-escape, cap, debt, minimum, surplus,
finite-player-specialization, or downstream-consumer claim.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame
open _root_.Math.Probability _root_.Math.ProbabilityMassFunction
open _root_.Math.Probability.DiscreteHazard
open scoped BigOperators ENNReal Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

omit [Nontrivial ι] in
private theorem quittingStageCoalitionMass_compactStoppingLawProfile
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingCompactStoppingLawProfile reward laws) time terminal =
      (∏ who ∈ terminal.val,
        (laws who).realMass ({WithTop.some time} : Set CompactStoppingTime)) *
      ∏ who ∈ terminal.valᶜ,
        (1 - ∑ date ∈ Finset.range (time + 1),
          (laws who).realMass
            ({WithTop.some date} : Set CompactStoppingTime)) := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro who _
    rw [quittingBehaviorStoppingLaw_compactStoppingLawProfile]
    exact CompactStoppingLaw.toPMF_apply_toReal (laws who) (WithTop.some time)
  · apply Finset.prod_congr rfl
    intro who _
    have hsum := sum_quittingHazardStopMass
      (quittingBehaviorLiveHazard reward
        (quittingCompactStoppingLawProfile reward laws who)) (time + 1)
    have hfinite :
        (∑ date ∈ Finset.range (time + 1),
          quittingHazardStopMass
            (quittingBehaviorLiveHazard reward
              (quittingCompactStoppingLawProfile reward laws who)) date) =
        ∑ date ∈ Finset.range (time + 1),
          (laws who).realMass
            ({WithTop.some date} : Set CompactStoppingTime) := by
      apply Finset.sum_congr rfl
      intro date hdate
      rw [← quittingBehaviorStoppingLaw_some_toReal]
      rw [quittingBehaviorStoppingLaw_compactStoppingLawProfile]
      exact CompactStoppingLaw.toPMF_apply_toReal
        (laws who) (WithTop.some date)
    rw [hfinite] at hsum
    linarith

omit [Nontrivial ι] in
private theorem tendsto_quittingStageCoalitionMass_compactStoppingLawProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {lawSeq : ℕ → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (time : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun n => quittingStageCoalitionMass reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)) time terminal)
      atTop (nhds (quittingStageCoalitionMass reward
        (quittingCompactStoppingLawProfile reward laws) time terminal)) := by
  simp_rw [quittingStageCoalitionMass_compactStoppingLawProfile]
  apply Filter.Tendsto.mul
  · apply tendsto_finsetProd terminal.val
    intro player hplayer
    exact CompactStoppingLaw.tendsto_realMass_of_isClopen
      (hlaw player) (compactStoppingTime_finiteSingleton_isClopen time)
  · apply tendsto_finsetProd terminal.valᶜ
    intro player hplayer
    apply tendsto_const_nhds.sub
    apply tendsto_finsetSum (Finset.range (time + 1))
    intro date hdate
    exact CompactStoppingLaw.tendsto_realMass_of_isClopen
      (hlaw player) (compactStoppingTime_finiteSingleton_isClopen date)

omit [Nontrivial ι] in
/-- Coordinatewise weak convergence of all complete stopping laws transports
every fixed finite-cutoff coalition mass. -/
theorem tendsto_quittingAbsorbedMass_compactStoppingLawProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {lawSeq : ℕ → ι → CompactStoppingLaw}
    {laws : ι → CompactStoppingLaw}
    (hlaw : ∀ player,
      Tendsto (fun n => lawSeq n player) atTop (nhds (laws player)))
    (cutoff : ℕ) (terminal : {S : Finset ι // S.Nonempty}) :
    Tendsto (fun n => quittingAbsorbedMass reward
        (quittingCompactStoppingLawProfile reward (lawSeq n)) cutoff terminal)
      atTop (nhds (quittingAbsorbedMass reward
        (quittingCompactStoppingLawProfile reward laws) cutoff terminal)) := by
  simp_rw [quittingAbsorbedMass_eq_sum_stageCoalitionMass]
  apply tendsto_finsetSum (Finset.range cutoff)
  intro time htime
  exact tendsto_quittingStageCoalitionMass_compactStoppingLawProfile
    hlaw time terminal

omit [Nontrivial ι] in
private theorem quittingStageCoalitionMass_eq_compactStoppingLawProfile_extracted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (time : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingStageCoalitionMass reward profile time terminal =
      quittingStageCoalitionMass reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile))
        time terminal := by
  rw [quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct,
    quittingStageCoalitionMass_eq_stoppingLawProduct_mul_tailProduct]
  apply congrArg₂ (fun x y : ℝ => x * y)
  · apply Finset.prod_congr rfl
    intro player hplayer
    simp [quittingCompactStoppingLawsOfProfile]
  · apply Finset.prod_congr rfl
    intro player hplayer
    have hsumLeft := sum_quittingHazardStopMass
      (quittingBehaviorLiveHazard reward (profile player)) (time + 1)
    have hsumRight := sum_quittingHazardStopMass
      (quittingBehaviorLiveHazard reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile) player))
      (time + 1)
    have hfinite :
        (∑ date ∈ Finset.range (time + 1),
          quittingHazardStopMass
            (quittingBehaviorLiveHazard reward (profile player)) date) =
        ∑ date ∈ Finset.range (time + 1),
          quittingHazardStopMass
            (quittingBehaviorLiveHazard reward
              (quittingCompactStoppingLawProfile reward
                (quittingCompactStoppingLawsOfProfile reward profile) player))
            date := by
      apply Finset.sum_congr rfl
      intro date hdate
      rw [← quittingBehaviorStoppingLaw_some_toReal,
        ← quittingBehaviorStoppingLaw_some_toReal]
      simp [quittingCompactStoppingLawsOfProfile]
    rw [hfinite] at hsumLeft
    linarith

omit [Nontrivial ι] in
private theorem quittingAbsorbedMass_eq_compactStoppingLawProfile_extracted
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (cutoff : ℕ)
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingAbsorbedMass reward profile cutoff terminal =
      quittingAbsorbedMass reward
        (quittingCompactStoppingLawProfile reward
          (quittingCompactStoppingLawsOfProfile reward profile))
        cutoff terminal := by
  simp_rw [quittingAbsorbedMass_eq_sum_stageCoalitionMass]
  apply Finset.sum_congr rfl
  intro time htime
  exact quittingStageCoalitionMass_eq_compactStoppingLawProfile_extracted
    reward profile time terminal

omit [Nontrivial ι] in
/-- A jointly selected terminal-outcome limit dominates every coalition mass
of the behavior reconstructed from the simultaneously selected marginal
stopping laws. -/
theorem quittingTerminalOutcomeMass_compactStoppingLawProfile_le_jointLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {profiles : ℕ → (quittingGame reward).BehaviorProfile}
    {laws : ι → CompactStoppingLaw}
    {mass : QuittingTerminalOutcome ι → ℝ}
    (hlaw : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward (profiles n) player)
        atTop (nhds (laws player)))
    (hmass : Tendsto (fun n => quittingTerminalOutcomeMass reward (profiles n))
      atTop (nhds mass))
    (terminal : {S : Finset ι // S.Nonempty}) :
    quittingTerminalOutcomeMass reward
        (quittingCompactStoppingLawProfile reward laws) (some terminal) ≤
      mass (some terminal) := by
  have hcoordinate : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward (profiles n) (some terminal))
      atTop (nhds (mass (some terminal))) :=
    tendsto_pi_nhds.mp hmass (some terminal)
  have hcut (cutoff : ℕ) :
      quittingAbsorbedMass reward
          (quittingCompactStoppingLawProfile reward laws) cutoff terminal ≤
        mass (some terminal) := by
    have hleft : Tendsto (fun n => quittingAbsorbedMass reward
        (profiles n) cutoff terminal) atTop
        (nhds (quittingAbsorbedMass reward
          (quittingCompactStoppingLawProfile reward laws) cutoff terminal)) := by
      apply (tendsto_quittingAbsorbedMass_compactStoppingLawProfile
        hlaw cutoff terminal).congr'
      exact Filter.Eventually.of_forall fun n =>
        (quittingAbsorbedMass_eq_compactStoppingLawProfile_extracted
          reward (profiles n) cutoff terminal).symm
    exact le_of_tendsto_of_tendsto hleft hcoordinate
      (Filter.Eventually.of_forall fun n => by
        simpa [quittingTerminalOutcomeMass] using
          quittingAbsorbedMass_le_limit reward (profiles n) cutoff terminal)
  change quittingAbsorbedMassLimit reward
      (quittingCompactStoppingLawProfile reward laws) terminal ≤ _
  apply le_of_tendsto
    (tendsto_quittingAbsorbedMass reward
      (quittingCompactStoppingLawProfile reward laws) terminal)
  exact Filter.Eventually.of_forall hcut

/-- Finite-coalition mass present in the selected outcome-law limit but absent
from the executable profile reconstructed from the selected marginal laws. -/
def quittingTerminalEscapeMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (terminal : {S : Finset ι // S.Nonempty}) : ℝ :=
  mass (some terminal) - quittingTerminalOutcomeMass reward
    (quittingCompactStoppingLawProfile reward laws) (some terminal)

omit [DecidableEq ι] [Nontrivial ι] in
private theorem sum_quittingTerminalEscapeMass_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (hmass : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι)) :
    (∑ terminal, quittingTerminalEscapeMass reward laws mass terminal) =
      quittingTerminalOutcomeMass reward
          (quittingCompactStoppingLawProfile reward laws) none - mass none := by
  have hactual := quittingTerminalOutcomeMass_mem_stdSimplex reward
    (quittingCompactStoppingLawProfile reward laws)
  have hmassTotal := hmass.2
  have hactualTotal := hactual.2
  rw [Fintype.sum_option] at hmassTotal hactualTotal
  simp only [quittingTerminalEscapeMass, Finset.sum_sub_distrib]
  linarith

omit [DecidableEq ι] [Nontrivial ι] in
private theorem quittingTerminalRewardMoment_sub_compactProfile_eq_escape
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (laws : ι → CompactStoppingLaw)
    (mass : QuittingTerminalOutcome ι → ℝ) (player : ι) :
    quittingTerminalRewardMoment reward mass player -
        quittingTerminalPayoff reward
          (quittingCompactStoppingLawProfile reward laws) player =
      ∑ terminal, quittingTerminalEscapeMass reward laws mass terminal *
        reward terminal player := by
  rw [← congrFun (quittingTerminalRewardMoment_outcomeMass reward
    (quittingCompactStoppingLawProfile reward laws)) player]
  unfold quittingTerminalRewardMoment
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [quittingTerminalOutcomeReward, Pi.zero_apply, mul_zero, zero_add,
    quittingTerminalEscapeMass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro terminal hterminal
  ring

/-- The complete first escape account obtained from one common refinement.
The same strict subsequence carries the outcome-law, semantic, and every
marginal-law convergence. -/
structure QuittingTerminalSemanticEscapeAccount
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (selected : QuittingTerminalSemanticSelectedLawLimit reward target) where
  mass : QuittingTerminalOutcome ι → ℝ
  subseq : ℕ → ℕ
  mass_mem : mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι)
  subseq_strictMono : StrictMono subseq
  outcome_tendsto : Tendsto (fun n => quittingTerminalOutcomeMass reward
      (selected.sourceProfile (selected.subseq (subseq n))))
    atTop (nhds mass)
  semantic_tendsto : Tendsto (fun n => quittingTerminalSemanticPair reward
      (selected.sourceProfile (selected.subseq (subseq n))))
    atTop (nhds target)
  law_tendsto : ∀ player, Tendsto (fun n =>
      quittingCompactStoppingLawsOfProfile reward
        (selected.sourceProfile (selected.subseq (subseq n))) player)
    atTop (nhds (selected.laws player))
  coalitionMass_le : ∀ terminal,
    quittingTerminalOutcomeMass reward
        (quittingCompactStoppingLawProfile reward selected.laws)
        (some terminal) ≤ mass (some terminal)
  escapeMass_nonneg : ∀ terminal,
    0 ≤ quittingTerminalEscapeMass reward selected.laws mass terminal
  totalEscapeMass_eq :
    (∑ terminal, quittingTerminalEscapeMass reward selected.laws mass terminal) =
      quittingTerminalOutcomeMass reward
          (quittingCompactStoppingLawProfile reward selected.laws) none - mass none
  escapedRewardMoment_eq : ∀ player,
    target.1 player - quittingTerminalPayoff reward
        (quittingCompactStoppingLawProfile reward selected.laws) player =
      ∑ terminal, quittingTerminalEscapeMass reward selected.laws mass terminal *
        reward terminal player

omit [Nontrivial ι] in
/-- The account's refinement composed with the selected source subsequence is
itself a strict source subsequence. -/
theorem QuittingTerminalSemanticEscapeAccount.sourceSubseq_strictMono
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    {selected : QuittingTerminalSemanticSelectedLawLimit reward target}
    (account : QuittingTerminalSemanticEscapeAccount reward target selected) :
    StrictMono (fun n => selected.subseq (account.subseq n)) :=
  selected.subseq_strictMono.comp account.subseq_strictMono

omit [Nontrivial ι] in
/-- A terminal-semantic/stopping-law selection has one further strict
subsequence on which the actual terminal-outcome laws converge, while both
previous limits remain unchanged. -/
theorem exists_quittingTerminalOutcomeMass_tendsto_refinement
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    (selected : QuittingTerminalSemanticSelectedLawLimit reward target) :
    ∃ (mass : QuittingTerminalOutcome ι → ℝ)
        (subseq : ℕ → ℕ),
      mass ∈ stdSimplex ℝ (QuittingTerminalOutcome ι) ∧
      StrictMono subseq ∧
      Tendsto (fun n => quittingTerminalOutcomeMass reward
          (selected.sourceProfile (selected.subseq (subseq n))))
        atTop (nhds mass) ∧
      Tendsto (fun n => quittingTerminalSemanticPair reward
          (selected.sourceProfile (selected.subseq (subseq n))))
        atTop (nhds target) ∧
      ∀ player, Tendsto (fun n => quittingCompactStoppingLawsOfProfile reward
          (selected.sourceProfile (selected.subseq (subseq n))) player)
        atTop (nhds (selected.laws player)) := by
  let masses : ℕ → QuittingTerminalOutcome ι → ℝ := fun n =>
    quittingTerminalOutcomeMass reward
      (selected.sourceProfile (selected.subseq n))
  have hmasses : ∀ n, masses n ∈
      stdSimplex ℝ (QuittingTerminalOutcome ι) := fun n =>
    quittingTerminalOutcomeMass_mem_stdSimplex reward
      (selected.sourceProfile (selected.subseq n))
  obtain ⟨mass, hmass, subseq, hsubseq, hmassLimit⟩ :=
    (isCompact_stdSimplex ℝ (QuittingTerminalOutcome ι)).tendsto_subseq hmasses
  refine ⟨mass, subseq, hmass, hsubseq, ?_, ?_, ?_⟩
  · simpa [masses, Function.comp_def] using hmassLimit
  · exact selected.semantic_tendsto.comp hsubseq.tendsto_atTop
  · intro player
    exact (selected.law_tendsto player).comp hsubseq.tendsto_atTop

omit [Nontrivial ι] in
/-- Equations (1)--(3): one common refined outcome-law subsequence, its
finite-cut lower-semicontinuity account, and the resulting nonnegative escape
mass balance and reward-moment identity. -/
theorem exists_quittingTerminalSemanticEscapeAccount
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {target : QuittingTerminalSemanticPair ι}
    (selected : QuittingTerminalSemanticSelectedLawLimit reward target) :
    Nonempty (QuittingTerminalSemanticEscapeAccount reward target selected) := by
  obtain ⟨mass, subseq, hmass, hsubseq, hmassLimit, hsemantic, hlaw⟩ :=
    exists_quittingTerminalOutcomeMass_tendsto_refinement selected
  let profiles : ℕ → (quittingGame reward).BehaviorProfile := fun n =>
    selected.sourceProfile (selected.subseq (subseq n))
  have hcoalition : ∀ terminal,
      quittingTerminalOutcomeMass reward
          (quittingCompactStoppingLawProfile reward selected.laws)
          (some terminal) ≤ mass (some terminal) := by
    intro terminal
    exact quittingTerminalOutcomeMass_compactStoppingLawProfile_le_jointLimit
      (profiles := profiles) hlaw hmassLimit terminal
  have hmomentLimit : Tendsto (fun n =>
      quittingTerminalRewardMoment reward
        (quittingTerminalOutcomeMass reward (profiles n))) atTop
      (nhds (quittingTerminalRewardMoment reward mass)) :=
    (continuous_quittingTerminalRewardMoment reward).tendsto mass |>.comp
      hmassLimit
  have htargetLimit : Tendsto (fun n =>
      quittingTerminalRewardMoment reward
        (quittingTerminalOutcomeMass reward (profiles n))) atTop
      (nhds target.1) := by
    have hpayoff := (continuous_fst.tendsto target).comp hsemantic
    simpa only [profiles, quittingTerminalSemanticPair, Function.comp_def,
      quittingTerminalRewardMoment_outcomeMass] using hpayoff
  have hmoment : quittingTerminalRewardMoment reward mass = target.1 :=
    tendsto_nhds_unique hmomentLimit htargetLimit
  refine ⟨{
    mass := mass
    subseq := subseq
    mass_mem := hmass
    subseq_strictMono := hsubseq
    outcome_tendsto := hmassLimit
    semantic_tendsto := hsemantic
    law_tendsto := hlaw
    coalitionMass_le := hcoalition
    escapeMass_nonneg := fun terminal => sub_nonneg.mpr (hcoalition terminal)
    totalEscapeMass_eq := sum_quittingTerminalEscapeMass_eq
      reward selected.laws mass hmass
    escapedRewardMoment_eq := ?_ }⟩
  intro player
  rw [← hmoment]
  exact quittingTerminalRewardMoment_sub_compactProfile_eq_escape
    reward selected.laws mass player

omit [Nontrivial ι] in
/-- Every point in the terminal-semantic carrier admits one selected source
sequence together with its first nonnegative escape account. -/
theorem exists_quittingTerminalSemanticEscapeAccount_of_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (target : QuittingTerminalSemanticPair ι)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward) :
    ∃ selected : QuittingTerminalSemanticSelectedLawLimit reward target,
      Nonempty (QuittingTerminalSemanticEscapeAccount reward target selected) := by
  let selected : QuittingTerminalSemanticSelectedLawLimit reward target :=
    Classical.choice
      (nonempty_terminalSemanticSelectedLawLimit_of_mem_carrier
        reward target htarget)
  exact ⟨selected, exists_quittingTerminalSemanticEscapeAccount selected⟩

end GameTheory
