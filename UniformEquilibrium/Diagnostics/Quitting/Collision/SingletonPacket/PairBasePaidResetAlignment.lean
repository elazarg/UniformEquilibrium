/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import
  UniformEquilibrium.Diagnostics.Quitting.Collision.SingletonPacket.PairBaseStationaryDebtLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn

/-!
# Same-profile pair-base paid reset alignment on four players

Choose a two-player sure-Quit base disjoint from a prescribed owner.  The
owner belongs to the complementary induced game and therefore has zero
unrestricted semantic debt.  A base player Quits surely, giving the owner one
full unit of opponent incidence.  On the very same stationary profile and
terminal law, terminal exploitability localizes a full-gap paid row to the
two-player base.

Thus the pair-base source is simultaneously an actual fixed-law reset target
for the prescribed owner and an actual paid-row source.  The concluding
consumer applies the existing fixed-law reset dispatch from any supplied
positive global-minimum carrier source.  It does not identify the returned
reset-face minimizer with the stationary paid profile or construct a payoff
near-return.
-/

noncomputable section

namespace GameTheory

open Finset Set
open Math.Probability Math.PMFProduct

/-- A product root in which a genuine opponent Quits surely has unit
first-stage opponent incidence. -/
private theorem pairBase_quittingRootOpponentIncidenceMass_eq_one_of_pureQuit
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (root : iota → PMF Bool) (owner other : iota) (hne : other ≠ owner)
    (hother : root other = PMF.pure true) :
    quittingRootOpponentIncidenceMass owner other root = 1 := by
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hother
  have hzero : ∀ terminal : {S : Finset iota // S.Nonempty},
      other ∉ terminal.val → quittingRootCoalitionMass root terminal.val = 0 := by
    intro terminal hnot
    have hupper := quittingRootCoalitionMass_le_continueProbability_of_not_mem
      root terminal.val other hnot
    rw [hother] at hupper
    norm_num at hupper
    exact le_antisymm hupper
      (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root terminal.val)
  have hfilter :
      (∑ terminal ∈ (Finset.univ.filter fun terminal :
          {S : Finset iota // S.Nonempty} ↦ other ∈ terminal.val),
        quittingRootCoalitionMass root terminal.val) =
        ∑ terminal : {S : Finset iota // S.Nonempty},
          quittingRootCoalitionMass root terminal.val := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro terminal _
    by_cases hmem : other ∈ terminal.val
    · simp [hmem]
    · simp [hmem, hzero terminal hmem]
  unfold quittingRootOpponentIncidenceMass
  have hevent : (Finset.univ.filter fun terminal :
      {S : Finset iota // S.Nonempty} ↦
        other ∈ terminal.val ∧ other ≠ owner) =
      Finset.univ.filter fun terminal : {S : Finset iota // S.Nonempty} ↦
        other ∈ terminal.val := by
    ext terminal
    simp [hne]
  rw [hevent, hfilter]
  rw [← Finset.sum_subtype (Finset.univ.erase (∅ : Finset iota))
    (fun coalition ↦ by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact Finset.nonempty_iff_ne_empty.symm)
    (quittingRootCoalitionMass root)]
  rw [quittingRootCoalitionMass_sum_nonempty, hcontinue]
  norm_num

/-- Unit root incidence passes to the complete terminal law of the literal
stationary profile. -/
private theorem pairBase_stationaryOutcome_incidence_eq_one_of_pureQuit
    {iota : Type} [Fintype iota] [DecidableEq iota]
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (root : iota → PMF Bool) (owner other : iota) (hne : other ≠ owner)
    (hother : root other = PMF.pure true) :
    quittingTerminalOpponentIncidenceMass owner other
        (quittingTerminalOutcomeMass reward
          (quittingStationaryProfile reward root)) = 1 := by
  let profile := quittingStationaryProfile reward root
  let mass := quittingTerminalOutcomeMass reward profile
  have hcontinue : quittingStationaryContinueMass root = 0 :=
    quittingStationaryContinueMass_of_sureQuitter hother
  have hrootIncidence :
      quittingRootOpponentIncidenceMass owner other root = 1 :=
    pairBase_quittingRootOpponentIncidenceMass_eq_one_of_pureQuit
      root owner other hne hother
  have hlaw : mass = quittingTerminalOutcomeLawPrefix root mass := by
    symm
    simpa only [mass, profile,
      quittingRootThenContinuationProfile_stationary] using
      (quittingTerminalOutcomeLawPrefix_outcomeMass reward root profile)
  change quittingTerminalOpponentIncidenceMass owner other mass = 1
  rw [hlaw, quittingTerminalOpponentIncidenceMass_lawPrefix,
    hrootIncidence, hcontinue]
  simp

/-- One stationary profile and law simultaneously provide the prescribed
owner reset, unit incidence, and a base-localized full-gap paid row. -/
structure FinFourPairBasePaidResetTarget
    (reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4))
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner baseFirst baseSecond : Fin 4) where
  owner_ne_first : owner ≠ baseFirst
  owner_ne_second : owner ≠ baseSecond
  base_ne : baseFirst ≠ baseSecond
  localization : FinFourPairBaseStationaryDebtLocalization reward witness
    {baseFirst, baseSecond}
  target_joint :
    (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingPersistentBaseRoot {baseFirst, baseSecond}
            (finFourPairBaseComplement {baseFirst, baseSecond})
              localization.point)),
      quittingTerminalOutcomeMass reward
        (quittingStationaryProfile reward
          (quittingPersistentBaseRoot {baseFirst, baseSecond}
            (finFourPairBaseComplement {baseFirst, baseSecond})
              localization.point))) ∈
      quittingTerminalSemanticLawCarrier reward
  owner_reset : quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward
        (quittingStationaryProfile reward
          (quittingPersistentBaseRoot {baseFirst, baseSecond}
            (finFourPairBaseComplement {baseFirst, baseSecond})
              localization.point))) owner = 0
  first_incidence : quittingTerminalOpponentIncidenceMass owner baseFirst
      (quittingTerminalOutcomeMass reward
        (quittingStationaryProfile reward
          (quittingPersistentBaseRoot {baseFirst, baseSecond}
            (finFourPairBaseComplement {baseFirst, baseSecond})
              localization.point))) = 1

namespace FinFourPairBasePaidResetTarget

/-- The common stationary profile underlying the reset and paid data. -/
def profile
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) : (quittingGame reward).BehaviorProfile :=
  quittingStationaryProfile reward
    (quittingPersistentBaseRoot {baseFirst, baseSecond}
      (finFourPairBaseComplement {baseFirst, baseSecond})
        target.localization.point)

/-- The common actual terminal semantic pair. -/
def semanticPair
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) : QuittingTerminalSemanticPair (Fin 4) :=
  quittingTerminalSemanticPair reward target.profile

/-- The common actual terminal law. -/
def mass
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) : QuittingTerminalOutcome (Fin 4) → ℝ :=
  quittingTerminalOutcomeMass reward target.profile

theorem debtor_mem_base
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) :
    target.localization.debtor ∈
      ({baseFirst, baseSecond} : Finset (Fin 4)) :=
  target.localization.debtor_mem

theorem debtor_gap
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) :
    witness.terminalGap ≤
      quittingTerminalSemanticDebt target.semanticPair
        target.localization.debtor :=
  target.localization.debtor_gap

theorem paid_row
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {owner baseFirst baseSecond : Fin 4}
    (target : FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) :
    Nonempty (QuittingPaidFirstDisagreementRow reward target.profile
      target.localization.debtor witness.terminalGap) :=
  target.localization.paid_row

end FinFourPairBasePaidResetTarget

/-- Any prescribed owner and any disjoint pair base produce the same-profile
paid reset target. -/
theorem nonempty_finFourPairBasePaidResetTarget
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (owner baseFirst baseSecond : Fin 4)
    (hownerFirst : owner ≠ baseFirst)
    (hownerSecond : owner ≠ baseSecond)
    (hbase : baseFirst ≠ baseSecond) :
    Nonempty (FinFourPairBasePaidResetTarget reward witness owner
      baseFirst baseSecond) := by
  let base : Finset (Fin 4) := {baseFirst, baseSecond}
  obtain ⟨localization⟩ :=
    nonempty_finFourPairBaseStationaryDebtLocalization
      witness base (by simp [base, hbase])
  let root := quittingPersistentBaseRoot base
    (finFourPairBaseComplement base) localization.point
  let profile := quittingStationaryProfile reward root
  let pair := quittingTerminalSemanticPair reward profile
  let mass := quittingTerminalOutcomeMass reward profile
  have hownerFree : owner ∈ finFourPairBaseComplement base := by
    simp [finFourPairBaseComplement, base, hownerFirst, hownerSecond]
  have hreset : quittingTerminalSemanticDebt pair owner = 0 :=
    (localization.free_solved owner hownerFree).1
  have hfirstRoot : root baseFirst = PMF.pure true := by
    exact quittingPersistentBaseRoot_apply_of_mem_base base
      (finFourPairBaseComplement base) localization.point (by
        simp [base])
  have hincidence :
      quittingTerminalOpponentIncidenceMass owner baseFirst mass = 1 := by
    exact pairBase_stationaryOutcome_incidence_eq_one_of_pureQuit
      reward root owner baseFirst hownerFirst.symm hfirstRoot
  have hjoint : (pair, mass) ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPoint_mem_carrier reward profile
  exact ⟨{
    owner_ne_first := hownerFirst
    owner_ne_second := hownerSecond
    base_ne := hbase
    localization := localization
    target_joint := hjoint
    owner_reset := hreset
    first_incidence := hincidence }⟩

/-- The same-profile paid reset target enters the existing fixed-law reset
dispatch from a supplied positive global-minimum semantic source. -/
theorem QuittingTerminalExploitabilityWitness.exists_finFour_pairBasePaidResetDispatch
    {reward : {S : Finset (Fin 4) // S.Nonempty} → Payoff (Fin 4)}
    (witness : QuittingTerminalExploitabilityWitness reward)
    (minimum : QuittingTerminalSemanticPair (Fin 4))
    (hminimumMem : minimum ∈ quittingTerminalSemanticCarrier reward)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (owner baseFirst baseSecond : Fin 4)
    (hownerFirst : owner ≠ baseFirst)
    (hownerSecond : owner ≠ baseSecond)
    (hbase : baseFirst ≠ baseSecond) :
    ∃ target : FinFourPairBasePaidResetTarget reward witness owner
        baseFirst baseSecond,
      ∃ returned, QuittingFixedLawResetDispatch (reward := reward)
        minimum target.semanticPair target.mass owner baseFirst returned := by
  obtain ⟨target⟩ := nonempty_finFourPairBasePaidResetTarget
    witness owner baseFirst baseSecond hownerFirst hownerSecond hbase
  have hsourcePositive : 0 < quittingTerminalSemanticDebtSum minimum :=
    hminimumPositive.trans_le (hminimum minimum hminimumMem)
  have hincidence : quittingTerminalOpponentIncidenceMass owner baseFirst
      target.mass = 1 := by
    simpa [FinFourPairBasePaidResetTarget.mass,
      FinFourPairBasePaidResetTarget.profile] using target.first_incidence
  obtain ⟨returned, hreturned⟩ := witness.exists_fixedLawResetDispatch
    minimum target.semanticPair target.mass owner baseFirst hminimum
      hsourcePositive target.target_joint target.owner_reset (by
        rw [hincidence]
        norm_num)
  exact ⟨target, returned, hreturned⟩

end GameTheory
