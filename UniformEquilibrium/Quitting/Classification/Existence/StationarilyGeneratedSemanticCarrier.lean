/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.Existence.StationarilyGeneratedBranch
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum

/-!
# Structured semantic carrier for stationary-prefix witnesses

Literal behavior profiles are not closed at the all-Continue boundary.  This
module retains exactly the finite-dimensional data of a stationarily
generated witness that does survive compact limits:

* the repeated product root, in simplex coordinates;
* a fixed finite prefix length and punished player;
* the terminal prescribed/envelope pair of the punishment tail;
* the punishment cap; and
* the terminal debt of the full repeated-prefix splice.

For each fixed prefix length and punished player, the resulting cell is
compact.  The natural-number prefix length is intentionally not hidden in a
compact product: a sequence of witnesses must split into a bounded-length
subsequence or a length tending to infinity.  Likewise strict positive live
mass is handled by closed cells with an explicit nonnegative floor.
-/

noncomputable section

namespace GameTheory

open Filter StochasticGame Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Apply the same root prefix a fixed number of times to a terminal semantic
pair. -/
def quittingTerminalSemanticPrefixFold
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) : ℕ →
      QuittingTerminalSemanticPair ι → QuittingTerminalSemanticPair ι
  | 0, tail => tail
  | steps + 1, tail =>
      quittingTerminalSemanticPrefix reward root
        (quittingTerminalSemanticPrefixFold reward root steps tail)

/-- Simplex-coordinate form of the repeated-prefix semantic fold. -/
def quittingTerminalSemanticPrefixFoldSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (steps : ℕ)
    (data : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefixFold reward
    (quittingRootOfSimplex data.1) steps data.2

/-- Simplex-coordinate form of one terminal semantic prefix action. -/
def quittingTerminalSemanticPrefixSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (data : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  quittingTerminalSemanticPrefix reward (quittingRootOfSimplex data.1) data.2

/-- Joint continuity of one semantic prefix in the simplex root and the tail
semantic pair. -/
theorem continuous_quittingTerminalSemanticPrefixSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (quittingTerminalSemanticPrefixSimplex reward) := by
  unfold quittingTerminalSemanticPrefixSimplex
  have hprescribed : Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
      quittingRootSuccessorPayoff reward data.2.1
        (quittingRootOfSimplex data.1)) := by
    let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
        Payoff ι × QuittingRootSimplex ι := fun data => (data.2.1, data.1)
    have hsource : Continuous source :=
      (continuous_fst.comp continuous_snd).prodMk continuous_fst
    have h := (continuous_quittingRootSuccessorPayoff_simplex reward).comp hsource
    change Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootSuccessorPayoff reward data.2.1
          (quittingRootOfSimplex data.1)) at h
    exact h
  have henvelope : Continuous (fun data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
      fun who => max
        (quittingRootQuitPayoff reward data.2.1
          (quittingRootOfSimplex data.1) who)
        (quittingRootContinuePayoff reward
          (Function.update data.2.1 who (data.2.2 who))
          (quittingRootOfSimplex data.1) who)) := by
    apply continuous_pi
    intro who
    have hquit : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootQuitPayoff reward data.2.1
          (quittingRootOfSimplex data.1) who) := by
      let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
          Payoff ι × QuittingRootSimplex ι := fun data => (data.2.1, data.1)
      have hsource : Continuous source :=
        (continuous_fst.comp continuous_snd).prodMk continuous_fst
      have h := (continuous_quittingRootQuitPayoff_simplex reward who).comp hsource
      change Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
          quittingRootQuitPayoff reward data.2.1
            (quittingRootOfSimplex data.1) who) at h
      exact h
    have htail : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        Function.update data.2.1 who (data.2.2 who)) := by
      apply continuous_pi
      intro player
      by_cases hplayer : player = who
      · subst player
        simpa [Function.update_self] using (show Continuous (fun data :
          QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
            data.2.2 who) by fun_prop)
      · simpa [Function.update_of_ne hplayer] using (show Continuous (fun data :
          QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
            data.2.1 player) by fun_prop)
    have hcontinue : Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
        quittingRootContinuePayoff reward
          (Function.update data.2.1 who (data.2.2 who))
          (quittingRootOfSimplex data.1) who) := by
      let source : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι →
          Payoff ι × QuittingRootSimplex ι := fun data =>
        (Function.update data.2.1 who (data.2.2 who), data.1)
      have hsource : Continuous source := htail.prodMk continuous_fst
      have h :=
        (continuous_quittingRootContinuePayoff_simplex reward who).comp hsource
      change Continuous (fun data :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι =>
          quittingRootContinuePayoff reward
            (Function.update data.2.1 who (data.2.2 who))
            (quittingRootOfSimplex data.1) who) at h
      exact h
    exact hquit.max hcontinue
  simpa only [quittingTerminalSemanticPrefix] using
    hprescribed.prodMk henvelope

/-- For every fixed prefix length, the structured semantic fold is jointly
continuous in the repeated root and punishment-tail semantic pair. -/
theorem continuous_quittingTerminalSemanticPrefixFoldSimplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (steps : ℕ) :
    Continuous (quittingTerminalSemanticPrefixFoldSimplex reward steps) := by
  induction steps with
  | zero => exact continuous_snd
  | succ steps ih =>
      exact (continuous_quittingTerminalSemanticPrefixSimplex reward).comp
        (continuous_fst.prodMk ih)

/-- Repeating a fixed root finitely many times preserves the compact terminal
semantic carrier. -/
theorem quittingTerminalSemanticPrefixFold_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (steps : ℕ)
    (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    quittingTerminalSemanticPrefixFold reward root steps pair ∈
      quittingTerminalSemanticCarrier reward := by
  induction steps with
  | zero => exact hpair
  | succ steps ih =>
      exact quittingTerminalSemanticPrefix_mem_carrier reward root _ ih

omit [DecidableEq ι] in
/-- The all-Continue mass is continuous in simplex root coordinates. -/
theorem continuous_quittingStationaryContinueMass_simplex :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingStationaryContinueMass (quittingRootOfSimplex root)) := by
  simp_rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    quittingRootOfSimplex_apply_toReal]
  exact continuous_finsetProd _ fun who _ => (continuous_apply false).comp
    (continuous_subtype_val.comp (continuous_apply who))

/-- The structured closed cell at fixed prefix length and punished player.
`liveFloor` is non-strict so the cell remains closed; a positive floor records
uniformly surviving roots, while floor zero includes the vanishing boundary. -/
def QuittingStationaryPrefixSemanticCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (steps : ℕ) (punished : ι) (punishmentError equilibriumError liveFloor : ℝ) :
    Set (QuittingRootSimplex ι × QuittingTerminalSemanticPair ι) :=
  {data | data.2 ∈ quittingTerminalSemanticCarrier reward ∧
    data.2.2 punished ≤
      quittingPunishmentValue reward punished + punishmentError ∧
    (∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefixFoldSimplex reward steps data) who ≤
        equilibriumError) ∧
    liveFloor ≤
      quittingStationaryContinueMass (quittingRootOfSimplex data.1)}

/-- Every fixed-length, fixed-owner structured semantic cell is closed. -/
theorem isClosed_quittingStationaryPrefixSemanticCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (steps : ℕ) (punished : ι) (punishmentError equilibriumError liveFloor : ℝ) :
    IsClosed (QuittingStationaryPrefixSemanticCell reward steps punished
      punishmentError equilibriumError liveFloor) := by
  have htail : IsClosed {data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
      data.2 ∈ quittingTerminalSemanticCarrier reward} :=
    (quittingTerminalSemanticCarrier_isCompact reward).isClosed.preimage continuous_snd
  have hpunish : IsClosed {data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
      data.2.2 punished ≤
        quittingPunishmentValue reward punished + punishmentError} := by
    exact isClosed_le ((continuous_apply punished).comp continuous_snd.snd)
      continuous_const
  have hdebt : IsClosed {data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
      ∀ who, quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefixFoldSimplex reward steps data) who ≤
          equilibriumError} := by
    rw [show {data : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
        ∀ who, quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefixFoldSimplex reward steps data) who ≤
            equilibriumError} = ⋂ who, {data |
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefixFoldSimplex reward steps data) who ≤
            equilibriumError} by ext data; simp]
    exact isClosed_iInter fun who => isClosed_le
      ((continuous_quittingTerminalSemanticDebt who).comp
        (continuous_quittingTerminalSemanticPrefixFoldSimplex reward steps))
      continuous_const
  have hlive : IsClosed {data :
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
      liveFloor ≤
        quittingStationaryContinueMass (quittingRootOfSimplex data.1)} := by
    exact isClosed_le continuous_const
      (continuous_quittingStationaryContinueMass_simplex.comp continuous_fst)
  exact htail.inter (hpunish.inter (hdebt.inter hlive))

/-- Every fixed-length, fixed-owner structured semantic cell is compact. -/
theorem isCompact_quittingStationaryPrefixSemanticCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (steps : ℕ) (punished : ι) (punishmentError equilibriumError liveFloor : ℝ) :
    IsCompact (QuittingStationaryPrefixSemanticCell reward steps punished
      punishmentError equilibriumError liveFloor) := by
  have hambient : IsCompact
      ((Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
        quittingTerminalSemanticCarrier reward) :=
    isCompact_univ.prod (quittingTerminalSemanticCarrier_isCompact reward)
  apply hambient.of_isClosed_subset
    (isClosed_quittingStationaryPrefixSemanticCell reward steps punished
      punishmentError equilibriumError liveFloor)
  intro data hdata
  exact ⟨Set.mem_univ data.1, hdata.1⟩

/-- An exact structured cell already contains a zero-debt point of the
attainable terminal-semantic closure, and therefore yields a uniform
equilibrium payoff. This conclusion is weaker than identifying an `S.1` or
`S.3` witness: the semantic tail need not itself be attained by one profile. -/
theorem exists_uniformEquilibriumPayoff_of_mem_exact_stationaryPrefixSemanticCell
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (steps : ℕ) (punished : ι) (liveFloor : ℝ)
    (data : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι)
    (hdata : data ∈ QuittingStationaryPrefixSemanticCell reward steps
      punished 0 0 liveFloor) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  letI : Nonempty ι := ⟨punished⟩
  let full := quittingTerminalSemanticPrefixFoldSimplex reward steps data
  have hfullCarrier : full ∈ quittingTerminalSemanticCarrier reward := by
    exact quittingTerminalSemanticPrefixFold_mem_carrier reward
      (quittingRootOfSimplex data.1) steps data.2 hdata.1
  have hdebt : ∀ who, quittingTerminalSemanticDebt full who ≤ 0 := by
    exact hdata.2.2.1
  by_contra hno
  have hpositive :=
    quittingTerminalExploitabilityInf_pos_of_no_uniformEquilibriumPayoff reward hno
  have hcarrierBound :=
    quittingTerminalExploitabilityInf_le_semanticCarrier reward hfullCarrier
  have hexploitability : quittingTerminalSemanticExploitability full ≤ 0 := by
    unfold quittingTerminalSemanticExploitability
    apply QuittingBoundaryHolonomy.finitePlayerMax_le
    intro who
    simp only [max_le_iff]
    exact ⟨le_rfl, hdebt who⟩
  linarith

/-- At fixed prefix length and punished player, vanishing punishment and
equilibrium errors have an exact structured semantic subsequential limit.
The non-strict live-mass floor survives unchanged. -/
theorem exists_exact_quittingStationaryPrefixSemanticCell_limit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (steps : ℕ) (punished : ι) (punishmentError equilibriumError : ℕ → ℝ)
    (data : ℕ → QuittingRootSimplex ι × QuittingTerminalSemanticPair ι)
    (liveFloor : ℝ)
    (hpunishmentError : Tendsto punishmentError atTop (nhds 0))
    (hequilibriumError : Tendsto equilibriumError atTop (nhds 0))
    (hdata : ∀ n, data n ∈ QuittingStationaryPrefixSemanticCell reward steps
      punished (punishmentError n) (equilibriumError n) liveFloor) :
    ∃ limit : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι,
      limit ∈ QuittingStationaryPrefixSemanticCell reward steps punished 0 0 liveFloor ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto (data ∘ subsequence) atTop (nhds limit) := by
  have hambient : ∀ n, data n ∈
      (Set.univ : Set (QuittingRootSimplex ι)) ×ˢ
        quittingTerminalSemanticCarrier reward := by
    intro n
    exact ⟨Set.mem_univ _, (hdata n).1⟩
  obtain ⟨limit, hlimitAmbient, subsequence, hsubsequence, hlimit⟩ :=
    (isCompact_univ.prod
      (quittingTerminalSemanticCarrier_isCompact reward)).tendsto_subseq hambient
  have hpunishmentErrorSub : Tendsto (punishmentError ∘ subsequence) atTop (nhds 0) :=
    hpunishmentError.comp hsubsequence.tendsto_atTop
  have hequilibriumErrorSub : Tendsto (equilibriumError ∘ subsequence) atTop (nhds 0) :=
    hequilibriumError.comp hsubsequence.tendsto_atTop
  have htailLimit : Tendsto (fun n ↦ (data (subsequence n)).2.2 punished)
      atTop (nhds (limit.2.2 punished)) :=
    ((continuous_apply punished).comp continuous_snd.snd).tendsto limit |>.comp hlimit
  have hpunishmentLimit : Tendsto
      (fun n ↦ quittingPunishmentValue reward punished +
        punishmentError (subsequence n)) atTop
      (nhds (quittingPunishmentValue reward punished)) := by
    simpa only [Function.comp_apply, add_zero] using
      tendsto_const_nhds.add hpunishmentErrorSub
  have hpunish : limit.2.2 punished ≤ quittingPunishmentValue reward punished :=
    le_of_tendsto_of_tendsto htailLimit hpunishmentLimit
      (Filter.Eventually.of_forall fun n ↦ (hdata (subsequence n)).2.1)
  have hdebt : ∀ who, quittingTerminalSemanticDebt
      (quittingTerminalSemanticPrefixFoldSimplex reward steps limit) who ≤ 0 := by
    intro who
    have hdebtLimit : Tendsto (fun n ↦ quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefixFoldSimplex reward steps
          (data (subsequence n))) who) atTop
        (nhds (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPrefixFoldSimplex reward steps limit) who)) :=
      ((continuous_quittingTerminalSemanticDebt who).comp
        (continuous_quittingTerminalSemanticPrefixFoldSimplex reward steps)).tendsto
        limit |>.comp hlimit
    exact le_of_tendsto_of_tendsto hdebtLimit hequilibriumErrorSub
      (Filter.Eventually.of_forall fun n ↦ (hdata (subsequence n)).2.2.1 who)
  have hlive : liveFloor ≤
      quittingStationaryContinueMass (quittingRootOfSimplex limit.1) := by
    have hclosed : IsClosed {candidate :
        QuittingRootSimplex ι × QuittingTerminalSemanticPair ι |
        liveFloor ≤ quittingStationaryContinueMass
          (quittingRootOfSimplex candidate.1)} :=
      isClosed_le continuous_const
        (continuous_quittingStationaryContinueMass_simplex.comp continuous_fst)
    exact hclosed.mem_of_tendsto hlimit
      (Filter.Eventually.of_forall fun n ↦ (hdata (subsequence n)).2.2.2)
  refine ⟨limit, ⟨hlimitAmbient.2, ?_, hdebt, hlive⟩,
    subsequence, hsubsequence, hlimit⟩
  simpa only [add_zero] using hpunish

/-- `sSup` and `iSup` presentations of the behavioral best-response envelope
agree. -/
theorem quittingContinuationBestResponseValue_eq_bestReplyValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (who : ι) :
    quittingContinuationBestResponseValue reward profile who =
      quittingBestReplyValue reward profile who := by
  unfold quittingContinuationBestResponseValue quittingBestReplyValue
  rw [sSup_range]

/-- A behavioral terminal `ε`-Nash certificate bounds every coordinate of
the corresponding finite-dimensional semantic debt by `ε`. -/
theorem quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profile : (quittingGame reward).BehaviorProfile) (ε : ℝ)
    (hnash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) ε profile) (who : ι) :
    quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who ≤ ε := by
  letI : Nonempty ((quittingGame reward).BehaviorStrategy who) :=
    ⟨fun _time _history => PMF.pure false⟩
  change quittingContinuationBestResponseValue reward profile who -
    quittingTerminalPayoff reward profile who ≤ ε
  rw [quittingContinuationBestResponseValue_eq_bestReplyValue]
  unfold quittingBestReplyValue
  have hsup : (⨆ deviation : (quittingGame reward).BehaviorStrategy who,
      quittingTerminalPayoff reward (Function.update profile who deviation) who) ≤
      quittingTerminalPayoff reward profile who + ε := by
    apply ciSup_le
    intro deviation
    exact hnash who deviation
  linarith

/-! ## Exact extraction from stationary-prefix witnesses -/

/-- The finite-dimensional structured datum carried by one stationary-prefix
witness: its repeated root and the terminal semantics of its punishment tail. -/
def quittingStationaryPrefixSemanticData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (punishment : ℕ → ι → PMF Bool) :
    QuittingRootSimplex ι × QuittingTerminalSemanticPair ι :=
  (quittingSimplexOfRoot root,
    quittingTerminalSemanticPair reward
      (quittingRootSequenceProfile reward punishment 0))

omit [DecidableEq ι] in
/-- Removing the first repeated root from a positive-length stationary prefix
decrements its horizon by one. -/
theorem quittingRootSequenceProfile_stationaryPrefixThenRoots_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) :
    quittingRootSequenceProfile reward
        (quittingStationaryPrefixThenRoots root (horizon + 1) punishment) 1 =
      quittingRootSequenceProfile reward
        (quittingStationaryPrefixThenRoots root horizon punishment) 0 := by
  funext player time history
  simp only [quittingRootSequenceProfile, Nat.zero_add]
  by_cases htime : time ≤ horizon
  · rw [quittingStationaryPrefixThenRoots_of_le root horizon punishment htime]
    rw [quittingStationaryPrefixThenRoots_of_le root (horizon + 1) punishment]
    omega
  · change
      (if 1 + time ≤ horizon + 1 then root
        else punishment (1 + time - (horizon + 1 + 1))) player =
      (if time ≤ horizon then root
        else punishment (time - (horizon + 1))) player
    rw [if_neg (by omega), if_neg htime]
    rw [show 1 + time - (horizon + 1 + 1) = time - (horizon + 1) by omega]

omit [DecidableEq ι] in
/-- At horizon zero, removing the single repeated root exposes the declared
punishment sequence. -/
theorem quittingRootSequenceProfile_stationaryPrefixThenRoots_zero_tail
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (punishment : ℕ → ι → PMF Bool) :
    quittingRootSequenceProfile reward
        (quittingStationaryPrefixThenRoots root 0 punishment) 1 =
      quittingRootSequenceProfile reward punishment 0 := by
  funext player time history
  simp only [quittingRootSequenceProfile, Nat.zero_add]
  rw [show 1 + time = 0 + 1 + time by omega,
    quittingStationaryPrefixThenRoots_add]

/-- The terminal semantic pair of a stationary prefix is the finite iterate
of the one-root semantic prefix action on the punishment tail's pair. -/
theorem quittingTerminalSemanticPair_stationaryPrefixThenRoots
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (horizon : ℕ)
    (punishment : ℕ → ι → PMF Bool) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingStationaryPrefixThenRoots root horizon punishment) 0) =
      quittingTerminalSemanticPrefixFold reward root (horizon + 1)
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward punishment 0)) := by
  induction horizon with
  | zero =>
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingStationaryPrefixThenRoots_of_le root 0 punishment le_rfl,
        quittingRootSequenceProfile_stationaryPrefixThenRoots_zero_tail,
        quittingTerminalSemanticPair_rootThenContinuation]
      rfl
  | succ horizon ih =>
      rw [quittingRootSequenceProfile_eq_rootThenContinuation,
        quittingStationaryPrefixThenRoots_of_le root (horizon + 1) punishment
          (Nat.zero_le _),
        quittingRootSequenceProfile_stationaryPrefixThenRoots_succ,
        quittingTerminalSemanticPair_rootThenContinuation, ih]
      rfl

/-- One diffuse stationarily generated witness maps canonically to the
structured closed cell. Strict positive live mass is retained as a side fact;
it is not folded into the cell because strict positivity is not closed. -/
theorem quittingStationaryPrefixSemanticData_mem_cell_of_witness
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (horizon : ℕ) (punished : ι)
    (punishment : ℕ → ι → PMF Bool) {δ η : ℝ}
    (hpunish : IsQuittingRootSequencePunishmentWithin
      reward punished δ punishment)
    (hnash : IsεQuittingRootSequenceNash reward η
      (quittingStationaryPrefixThenRoots root horizon punishment))
    (hlive : 0 < quittingStationaryContinueMass root) :
    quittingStationaryPrefixSemanticData reward root punishment ∈
        QuittingStationaryPrefixSemanticCell reward (horizon + 1)
          punished δ η 0 ∧
      0 < quittingStationaryContinueMass
        (quittingRootOfSimplex
          (quittingStationaryPrefixSemanticData reward root punishment).1) := by
  let tailProfile := quittingRootSequenceProfile reward punishment 0
  let data := quittingStationaryPrefixSemanticData reward root punishment
  have hroot : quittingRootOfSimplex data.1 = root := by
    dsimp only [data]
    exact quittingRootOfSimplex_simplexOfRoot root
  have htailMem : data.2 ∈ quittingTerminalSemanticCarrier reward := by
    apply subset_closure
    exact ⟨tailProfile, rfl⟩
  have htailCap : data.2.2 punished ≤
      quittingPunishmentValue reward punished + δ := by
    change quittingContinuationBestResponseValue reward tailProfile punished ≤ _
    rw [quittingContinuationBestResponseValue_eq_bestReplyValue]
    exact (isQuittingRootSequencePunishmentWithin_iff_bestReplyValue
      reward punished δ punishment).mp hpunish
  have hbehavior : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) η
      (quittingRootSequenceProfile reward
        (quittingStationaryPrefixThenRoots root horizon punishment) 0) :=
    (isεQuittingRootSequenceNash_iff_isεAsymptoticNash reward η _).mp hnash
  have hfold : quittingTerminalSemanticPrefixFoldSimplex reward (horizon + 1) data =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingStationaryPrefixThenRoots root horizon punishment) 0) := by
    rw [quittingTerminalSemanticPrefixFoldSimplex, hroot]
    exact (quittingTerminalSemanticPair_stationaryPrefixThenRoots
      reward root horizon punishment).symm
  refine ⟨⟨htailMem, htailCap, ?_, ?_⟩, ?_⟩
  · intro who
    rw [hfold]
    exact quittingTerminalSemanticDebt_pair_le_of_isεAsymptoticNash
      reward _ η hbehavior who
  · rw [hroot]
    exact quittingStationaryContinueMass_nonneg root
  · rw [hroot]
    exact hlive

/-- At fixed horizon and punished player, a vanishing-error family of actual
stationary-prefix witnesses has an exact structured semantic subsequential
limit. This is the closed part of the stationarily-generated compactification;
it does not assert that the limiting semantic tail is literally attained. -/
theorem exists_exact_semantic_limit_of_stationaryPrefix_witnesses
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (punished : ι) (root : ℕ → ι → PMF Bool)
    (punishment : ℕ → ℕ → ι → PMF Bool)
    (punishmentError equilibriumError : ℕ → ℝ)
    (liveFloor : ℝ)
    (hpunishmentError : Tendsto punishmentError atTop (nhds 0))
    (hequilibriumError : Tendsto equilibriumError atTop (nhds 0))
    (hpunish : ∀ n, IsQuittingRootSequencePunishmentWithin reward punished
      (punishmentError n) (punishment n))
    (hnash : ∀ n, IsεQuittingRootSequenceNash reward (equilibriumError n)
      (quittingStationaryPrefixThenRoots (root n) horizon (punishment n)))
    (hliveFloor : 0 < liveFloor)
    (hlive : ∀ n, liveFloor ≤ quittingStationaryContinueMass (root n)) :
    ∃ limit : QuittingRootSimplex ι × QuittingTerminalSemanticPair ι,
      limit ∈ QuittingStationaryPrefixSemanticCell reward (horizon + 1)
        punished 0 0 liveFloor ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧
        Tendsto
          (fun n ↦ quittingStationaryPrefixSemanticData reward
            (root (subsequence n)) (punishment (subsequence n)))
          atTop (nhds limit) := by
  let data : ℕ → QuittingRootSimplex ι × QuittingTerminalSemanticPair ι :=
    fun n ↦ quittingStationaryPrefixSemanticData reward (root n) (punishment n)
  have hdata : ∀ n, data n ∈ QuittingStationaryPrefixSemanticCell reward
      (horizon + 1) punished (punishmentError n) (equilibriumError n) liveFloor := by
    intro n
    have hwitness := quittingStationaryPrefixSemanticData_mem_cell_of_witness
      reward (root n) horizon punished (punishment n) (hpunish n) (hnash n)
        (hliveFloor.trans_le (hlive n))
    refine ⟨hwitness.1.1, hwitness.1.2.1, hwitness.1.2.2.1, ?_⟩
    simpa [data, quittingStationaryPrefixSemanticData] using hlive n
  simpa [data, Function.comp_def] using
    exists_exact_quittingStationaryPrefixSemanticCell_limit reward
      (horizon + 1) punished punishmentError equilibriumError data
      liveFloor hpunishmentError hequilibriumError hdata

/-- The fixed-horizon, fixed-owner, uniformly positive-live regime of
stationarily-generated witnesses is already sufficient for a uniform
equilibrium payoff. No realization of the limiting punishment tail is used. -/
theorem exists_uniformEquilibriumPayoff_of_stationaryPrefix_witnesses
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (horizon : ℕ) (punished : ι) (root : ℕ → ι → PMF Bool)
    (punishment : ℕ → ℕ → ι → PMF Bool)
    (punishmentError equilibriumError : ℕ → ℝ)
    (liveFloor : ℝ)
    (hpunishmentError : Tendsto punishmentError atTop (nhds 0))
    (hequilibriumError : Tendsto equilibriumError atTop (nhds 0))
    (hpunish : ∀ n, IsQuittingRootSequencePunishmentWithin reward punished
      (punishmentError n) (punishment n))
    (hnash : ∀ n, IsεQuittingRootSequenceNash reward (equilibriumError n)
      (quittingStationaryPrefixThenRoots (root n) horizon (punishment n)))
    (hliveFloor : 0 < liveFloor)
    (hlive : ∀ n, liveFloor ≤ quittingStationaryContinueMass (root n)) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨limit, hlimit, _subsequence, _hsubsequence, _htendsto⟩ :=
    exists_exact_semantic_limit_of_stationaryPrefix_witnesses reward
      horizon punished root punishment punishmentError equilibriumError
      liveFloor hpunishmentError hequilibriumError hpunish hnash hliveFloor hlive
  exact exists_uniformEquilibriumPayoff_of_mem_exact_stationaryPrefixSemanticCell
    reward (horizon + 1) punished liveFloor limit hlimit

end GameTheory
