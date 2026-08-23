/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.StoppingLaw.OffDiagonal.AtomSequenceDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetSurfaceTension

/-!
# Reset-face return for the off-diagonal rectangle endpoint

The fixed-label rectangle sequence already supplies literal double endpoints:
first replace the active mover, then install the observer's selected pure-time
response.  The observer debt of these executable profiles tends to zero.

Compactifying the complete semantic/law points therefore gives an exact
observer-reset cluster.  The existing reset-face minimizer then produces a
point no higher than that cluster.  It either lies on the global minimum
fiber, or it is an off-minimum reset point whose only exact cap--Nash root is
all-Continue.  This removes any additional endpoint-return hypothesis from
the rectangle branch.

The original fixed atom, player labels, terminal label, and literal profiles
remain exact along the selected subsequence.  The final reset-face minimizer
is only a semantic consumer: it need not preserve the cluster's terminal law,
the signed atom, or the original chronology.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal double endpoint: the mover replacement followed by the selected
observer pure-time response. -/
def quittingStoppingLawRectangleDoubleEndpointProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (quittingStoppingLawRectangleTargetProfile packet n)
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- The comparison endpoint in which the mover keeps its prescribed
strategy and the same observer response is installed. -/
def quittingStoppingLawRectangleSourceResponseProfile
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : (quittingGame reward).BehaviorProfile :=
  Function.update (frontier.profiles (frontier.subseq (packet.rank n)))
    packet.observer
    (quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n))

/-- Complete endpoint-return packet for a fixed rectangle sequence.  The
cluster retains the limiting terminal law of the literal double endpoints.
The returned point records the separate semantic reset-face minimization. -/
structure QuittingStoppingLawRectangleResetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  rank_strictMono : StrictMono (packet.rank ∘ subseq)
  cluster : QuittingTerminalSemanticLawPoint ι
  cluster_mem : cluster ∈ quittingTerminalSemanticLawCarrier reward
  doubleEndpoint_tendsto : Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n))))
    atTop (nhds cluster)
  cluster_observer_reset :
    quittingTerminalSemanticDebt cluster.1 packet.observer = 0
  cluster_fiber_or_separated :
    quittingTerminalSemanticDebtSum cluster.1 =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum cluster.1
  returned : QuittingTerminalSemanticPair ι
  returned_mem : returned ∈ quittingTerminalSemanticCarrier reward
  returned_observer_reset :
    quittingTerminalSemanticDebt returned packet.observer = 0
  base_le_returned : quittingTerminalSemanticDebtSum frontier.base ≤
    quittingTerminalSemanticDebtSum returned
  returned_le_cluster : quittingTerminalSemanticDebtSum returned ≤
    quittingTerminalSemanticDebtSum cluster.1
  opponent_transfer_identity :
    (∑ other ∈ Finset.univ.erase packet.observer,
        quittingTerminalSemanticDebtChange frontier.base returned other) =
      (quittingTerminalSemanticDebtSum returned -
          quittingTerminalSemanticDebtSum frontier.base) +
        quittingTerminalSemanticDebt frontier.base packet.observer
  opponent_transfer : quittingTerminalSemanticDebt frontier.base
      packet.observer ≤
    ∑ other ∈ Finset.univ.erase packet.observer,
      quittingTerminalSemanticDebtChange frontier.base returned other
  returned_fiber_or_separated :
    quittingTerminalSemanticDebtSum returned =
        quittingTerminalSemanticDebtSum frontier.base ∨
      quittingTerminalSemanticDebtSum frontier.base <
        quittingTerminalSemanticDebtSum returned
  allContinue_nash : IsεQuittingRootNash reward returned.2 0
    (quittingAllContinueRoot : ι → PMF Bool)
  allContinue_fixed :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
      returned
  unique_capNash : ∀ root : ι → PMF Bool,
    IsεQuittingRootNash reward returned.2 0 root →
      root = (quittingAllContinueRoot : ι → PMF Bool)

/-- The fixed signed rectangle atom remains literally true on every selected
rank.  This concerns the original double endpoints, not the semantic point
`dispatch.returned`. -/
theorem QuittingStoppingLawRectangleResetFaceDispatch.atom_bound
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    (dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet)
    (n : ℕ) :
    packet.charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingStoppingLawRectangleDoubleEndpointProfile packet
            (dispatch.subseq n))
          (quittingStoppingLawRectangleSourceResponseProfile packet
            (dispatch.subseq n))
          packet.observer (some packet.terminal) := by
  simpa only [quittingStoppingLawRectangleDoubleEndpointProfile,
    quittingStoppingLawRectangleTargetProfile,
    quittingStoppingLawRectangleSourceResponseProfile,
    Function.update_eq_self] using packet.atom_bound (dispatch.subseq n)

/-- **Unconditional rectangle endpoint return/separation.**  No metric-return
or near-minimality assumption on the double endpoints is needed. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_resetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    Nonempty (QuittingStoppingLawRectangleResetFaceDispatch packet) := by
  let endpoint : ℕ → QuittingTerminalSemanticLawPoint ι := fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet n),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet n))
  have hendpointMem : ∀ n,
      endpoint n ∈ quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨cluster, hcluster, subseq, hsubseq, hendpoint⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      hendpointMem
  have hdebtCluster :=
    ((continuous_quittingTerminalSemanticDebt packet.observer).comp
      continuous_fst).tendsto cluster |>.comp hendpoint
  have hdebtZero := packet.observer_debt_tendsto_zero.comp
    hsubseq.tendsto_atTop
  change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)).1 packet.observer) atTop (nhds 0) at hdebtZero
  have hclusterReset : quittingTerminalSemanticDebt cluster.1
      packet.observer = 0 := by
    change Tendsto (fun n => quittingTerminalSemanticDebt
      (endpoint (subseq n)).1 packet.observer) atTop
      (nhds (quittingTerminalSemanticDebt cluster.1 packet.observer)) at hdebtCluster
    exact tendsto_nhds_unique hdebtCluster hdebtZero
  have hclusterCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier cluster hcluster
  have hclusterFloor := frontier.base_minimum cluster.1 hclusterCarrier
  have hclusterFiber := hclusterFloor.eq_or_lt.imp Eq.symm id
  obtain ⟨returned, hreturned, hreturnedReset, hbaseLe, hreturnedLe,
      htransferIdentity, htransfer, hreturnedFiber, hnash, hfixed,
      hunique⟩ :=
    exists_resetFace_minimizer_with_unique_allContinue_capNash
      (reward := reward) frontier.base cluster.1 packet.observer
      frontier.base_minimum frontier.base_positive hclusterCarrier
      hclusterReset
  refine ⟨⟨subseq, hsubseq, packet.rank_strictMono.comp hsubseq,
    cluster, hcluster, ?_, hclusterReset, hclusterFiber, returned, hreturned,
    hreturnedReset, hbaseLe, hreturnedLe, htransferIdentity, htransfer,
    hreturnedFiber, hnash, hfixed, hunique⟩⟩
  change Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet (subseq n))))
    atTop (nhds cluster) at hendpoint
  exact hendpoint

namespace QuittingCounterexampleStoppingLawFrontier

/-- Regime-facing dispatch: the prescribed atom branch remains open, while
every rectangle branch reaches the semantic reset-face return/separation
consumer without an extra endpoint-return hypothesis. -/
theorem exists_prescribedAtomSequence_or_rectangleResetFaceDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    (frontier : QuittingCounterexampleStoppingLawFrontier witness) :
    Nonempty (QuittingStoppingLawPrescribedAtomSequence frontier) ∨
      ∃ packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier,
        Nonempty (QuittingStoppingLawRectangleResetFaceDispatch packet) := by
  rcases frontier.exists_prescribedAtomSequence_or_vanishingDebtRectangleSequence
      with hprescribed | hrectangle
  · exact Or.inl hprescribed
  · obtain ⟨packet⟩ := hrectangle
    exact Or.inr ⟨packet, packet.nonempty_resetFaceDispatch⟩

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
/-!
# Fixed-law return of the rectangle endpoint atom

The semantic reset-face dispatch retains the complete endpoint law only at
its cluster, not at its constrained returned point.  Here the comparison law
is compactified on the same subsequence.  The signed rectangle atom therefore
survives as an exact inequality between two limiting laws.

When the fixed atom pays the observer positively and its coalition contains
an actual opponent, the endpoint law has positive mass on that coalition.
The cluster consequently has positive observer--opponent incidence.  The
existing fixed-law reset dispatcher then preserves the whole endpoint law,
the atom-supporting incidence, and a strict static toggle.  Dynamically it
gives either a positive-survival absorbing reset-face return or an
all-Continue cap fixed point.

This does not make all-Continue unique at the fixed-law minimizer.  Prefixing
changes the law, while fixed-law minimality compares only points with the old
law.  Exact cap-root rigidity follows only from the additional premise that
the same returned point minimizes debt on the entire reset face.  This is the
sharp separation between law retention and the semantic surface-tension
selector.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Joint semantic/law point of one literal rectangle double endpoint. -/
def quittingStoppingLawRectangleDoubleEndpointPoint
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : QuittingTerminalSemanticLawPoint ι :=
  (quittingTerminalSemanticPair reward
      (quittingStoppingLawRectangleDoubleEndpointProfile packet n),
    quittingTerminalOutcomeMass reward
      (quittingStoppingLawRectangleDoubleEndpointProfile packet n))

/-- A common subsequence on which both literal laws in the rectangle atom
converge.  The endpoint limit is the exact joint cluster already selected by
the semantic reset-face dispatch. -/
structure QuittingStoppingLawRectangleJointAtomLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    (dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet) where
  subseq : ℕ → ℕ
  subseq_strictMono : StrictMono subseq
  comparison : QuittingTerminalSemanticLawPoint ι
  comparison_mem : comparison ∈ quittingTerminalSemanticLawCarrier reward
  endpoint_tendsto : Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet
          (dispatch.subseq (subseq n))),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet
          (dispatch.subseq (subseq n)))))
    atTop (nhds dispatch.cluster)
  comparison_tendsto : Tendsto (fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleSourceResponseProfile packet
          (dispatch.subseq (subseq n))),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleSourceResponseProfile packet
          (dispatch.subseq (subseq n)))))
    atTop (nhds comparison)
  atom_bound : packet.charge / 4 ≤
    (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
      ((dispatch.cluster.2 (some packet.terminal) -
          comparison.2 (some packet.terminal)) *
        reward packet.terminal packet.observer)

/-- The comparison profiles can be compactified without changing the
already-selected endpoint cluster. -/
theorem QuittingStoppingLawRectangleResetFaceDispatch.nonempty_jointAtomLimit
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    (dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet) :
    Nonempty (QuittingStoppingLawRectangleJointAtomLimit dispatch) := by
  let comparisonPoint : ℕ → QuittingTerminalSemanticLawPoint ι := fun n =>
    (quittingTerminalSemanticPair reward
        (quittingStoppingLawRectangleSourceResponseProfile packet
          (dispatch.subseq n)),
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleSourceResponseProfile packet
          (dispatch.subseq n)))
  have hcomparisonMem : ∀ n,
      comparisonPoint n ∈ quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward _
  obtain ⟨comparison, hcomparison, subseq, hsubseq, hcomparisonLimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq
      hcomparisonMem
  have hendpointLimit := dispatch.doubleEndpoint_tendsto.comp
    hsubseq.tendsto_atTop
  have hendpointMass : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleDoubleEndpointProfile packet
          (dispatch.subseq (subseq n))) (some packet.terminal)) atTop
      (nhds (dispatch.cluster.2 (some packet.terminal))) := by
    exact (continuous_apply (some packet.terminal)).tendsto dispatch.cluster.2
      |>.comp (continuous_snd.tendsto dispatch.cluster |>.comp hendpointLimit)
  have hcomparisonMass : Tendsto (fun n =>
      quittingTerminalOutcomeMass reward
        (quittingStoppingLawRectangleSourceResponseProfile packet
          (dispatch.subseq (subseq n))) (some packet.terminal)) atTop
      (nhds (comparison.2 (some packet.terminal))) := by
    have hlaw := continuous_snd.tendsto comparison |>.comp hcomparisonLimit
    exact (continuous_apply (some packet.terminal)).tendsto comparison.2
      |>.comp hlaw
  have hatomLimit : Tendsto (fun n =>
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        ((quittingTerminalOutcomeMass reward
              (quittingStoppingLawRectangleDoubleEndpointProfile packet
                (dispatch.subseq (subseq n))) (some packet.terminal) -
            quittingTerminalOutcomeMass reward
              (quittingStoppingLawRectangleSourceResponseProfile packet
                (dispatch.subseq (subseq n))) (some packet.terminal)) *
          reward packet.terminal packet.observer)) atTop
      (nhds ((Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        ((dispatch.cluster.2 (some packet.terminal) -
            comparison.2 (some packet.terminal)) *
          reward packet.terminal packet.observer))) := by
    exact tendsto_const_nhds.mul
      ((hendpointMass.sub hcomparisonMass).mul tendsto_const_nhds)
  have hatomBound : packet.charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        ((dispatch.cluster.2 (some packet.terminal) -
            comparison.2 (some packet.terminal)) *
          reward packet.terminal packet.observer) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hatomLimit
    exact Eventually.of_forall fun n => by
      have hbound := dispatch.atom_bound (subseq n)
      simpa only [quittingTerminalPayoffDifferenceAtom,
        quittingTerminalOutcomeReward] using hbound
  refine ⟨⟨subseq, hsubseq, comparison, hcomparison, ?_, ?_, hatomBound⟩⟩
  · exact hendpointLimit
  · change Tendsto (fun n =>
      (quittingTerminalSemanticPair reward
          (quittingStoppingLawRectangleSourceResponseProfile packet
            (dispatch.subseq (subseq n))),
        quittingTerminalOutcomeMass reward
          (quittingStoppingLawRectangleSourceResponseProfile packet
            (dispatch.subseq (subseq n))))) atTop (nhds comparison) at hcomparisonLimit
    exact hcomparisonLimit

/-- Positive observer reward turns the limiting signed atom into positive
mass on the endpoint cluster's displayed terminal. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.endpoint_terminalMass_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (hreward : 0 < reward packet.terminal packet.observer) :
    0 < dispatch.cluster.2 (some packet.terminal) := by
  have hcard : 0 < (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hscaled : 0 <
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        ((dispatch.cluster.2 (some packet.terminal) -
            limit.comparison.2 (some packet.terminal)) *
          reward packet.terminal packet.observer) :=
    (div_pos packet.charge_pos (by norm_num)).trans_le limit.atom_bound
  have hatom : 0 <
      (dispatch.cluster.2 (some packet.terminal) -
          limit.comparison.2 (some packet.terminal)) *
        reward packet.terminal packet.observer := by
    rw [mul_comm] at hscaled
    exact pos_of_mul_pos_left hscaled hcard.le
  have hdiff : 0 < dispatch.cluster.2 (some packet.terminal) -
      limit.comparison.2 (some packet.terminal) :=
    pos_of_mul_pos_left hatom hreward.le
  have hcomparisonSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    limit.comparison limit.comparison_mem
  have hcomparisonNonneg := hcomparisonSimplex.1 (some packet.terminal)
  linarith

/-- A positive atom on a coalition containing a genuine opponent gives a
positive incidence coordinate in the exact endpoint cluster law. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.endpoint_opponentIncidence_pos
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (hreward : 0 < reward packet.terminal packet.observer)
    (other : ι) (hother : other ∈ packet.terminal.val)
    (hotherNe : other ≠ packet.observer) :
    0 < quittingTerminalOpponentIncidenceMass packet.observer other
      dispatch.cluster.2 := by
  have hmassPos := limit.endpoint_terminalMass_pos hreward
  have hmassSimplex := terminalSemanticLawCarrier_mass_mem_stdSimplex
    dispatch.cluster dispatch.cluster_mem
  have hterminal : packet.terminal ∈
      Finset.univ.filter
        (fun terminal : {S : Finset ι // S.Nonempty} =>
          other ∈ terminal.val ∧ other ≠ packet.observer) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hother, hotherNe⟩
  unfold quittingTerminalOpponentIncidenceMass
  exact hmassPos.trans_le (Finset.single_le_sum
    (fun terminal _ => hmassSimplex.1 (some terminal)) hterminal)

/-- **Fixed-law atom consumer.**  A positive-reward rectangle atom whose
coalition contains another player reaches the existing same-law reset
dispatcher.  Thus the complete endpoint law and a concrete atom-supported
incidence survive reset-face minimization, together with a strict toggle and
the absorbing-return/all-Continue dynamic alternative. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.exists_fixedLawResetDispatch
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (hreward : 0 < reward packet.terminal packet.observer)
    (other : ι) (hother : other ∈ packet.terminal.val)
    (hotherNe : other ≠ packet.observer) :
    ∃ returned,
      QuittingFixedLawResetDispatch (reward := reward) frontier.base
        dispatch.cluster.1 dispatch.cluster.2 packet.observer other returned := by
  have hincidence := limit.endpoint_opponentIncidence_pos
    hreward other hother hotherNe
  exact witness.exists_fixedLawResetDispatch frontier.base
      dispatch.cluster.1 dispatch.cluster.2 packet.observer other
      frontier.base_minimum
      frontier.base_positive dispatch.cluster_mem
      dispatch.cluster_observer_reset hincidence

/-- Fixed-law minimality alone cannot prove cap-root rigidity, because a cap
prefix changes the law.  The exact additional premise is minimality on the
whole reset face; under it, positive global debt forces every exact cap--Nash
root to be all-Continue. -/
theorem fixedLawResetPoint_unique_allContinue_of_globalResetFaceMinimum
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (source : QuittingTerminalSemanticPair ι)
    (returned : QuittingTerminalSemanticLawPoint ι) (owner : ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt returned.1 owner = 0)
    (hfaceMinimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebt candidate owner = 0 →
        quittingTerminalSemanticDebtSum returned.1 ≤
          quittingTerminalSemanticDebtSum candidate) :
    ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward returned.1.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool) := by
  intro root hnash
  let prefixed := quittingTerminalSemanticPrefix reward root returned.1
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier reward root returned.1
      hreturnedCarrier
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root owner hnash, hreset, mul_zero]
  have hface := hfaceMinimum prefixed hprefixed hprefixedReset
  have hscale : quittingTerminalSemanticDebtSum prefixed =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum returned.1 :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root hnash
  have hreturnedPositive : 0 <
      quittingTerminalSemanticDebtSum returned.1 := by
    exact hsourcePositive.trans_le (hminimum returned.1 hreturnedCarrier)
  have hcontinueLe := quittingStationaryContinueMass_le_one root
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    rw [hscale] at hface
    nlinarith
  funext player
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hcontinue player
  simpa only [quittingAllContinueRoot] using hpure

/-! ## Exact comparison of the two reset-face selectors -/

/-- The data obtained by comparing global reset-face minimization with
minimization at the fixed endpoint law.

The equality branch is the desired provenance bridge: one and the same point
retains the atom-supporting law and is globally minimal on the reset face, so
its exact cap correspondence is the singleton all-Continue root.  The strict
branch records the exact positive price of retaining that law.  Its
`fixed_dispatch.dynamic_exit` field still supplies the existing absorbing
descent/all-Continue alternative; no claim is made that this price vanishes. -/
structure QuittingStoppingLawRectangleMinimizerBridge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (other : ι) where
  global : QuittingTerminalSemanticLawPoint ι
  global_mem : global ∈ quittingTerminalSemanticLawCarrier reward
  global_reset : quittingTerminalSemanticDebt global.1 packet.observer = 0
  global_minimal : ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
    quittingTerminalSemanticDebt candidate.1 packet.observer = 0 →
      quittingTerminalSemanticDebtSum global.1 ≤
        quittingTerminalSemanticDebtSum candidate.1
  fixed : QuittingTerminalSemanticPair ι
  fixed_dispatch : QuittingFixedLawResetDispatch (reward := reward)
    frontier.base dispatch.cluster.1 dispatch.cluster.2 packet.observer other
      fixed
  global_le_fixed : quittingTerminalSemanticDebtSum global.1 ≤
    quittingTerminalSemanticDebtSum fixed
  atom_mass_retained : 0 < dispatch.cluster.2 (some packet.terminal)
  aligned_or_lawPremium :
    (quittingTerminalSemanticDebtSum fixed =
        quittingTerminalSemanticDebtSum global.1 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward fixed.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool)) ∨
      0 < quittingTerminalSemanticDebtSum fixed -
        quittingTerminalSemanticDebtSum global.1

/-- **Fixed-law/global reset-face bridge.**

For the positive-reward, observer-containing rectangle orientation, the two
reset selectors have an exact comparison.  Either their debt values agree,
in which case the fixed-law selector also has unique all-Continue exact cap
roots, or retaining the atom law costs a strictly positive debt premium.

Thus failure of the provenance bridge is not qualitative ambiguity: it is a
named positive scalar separation, still carrying the full fixed-law dynamic
exit and supported-toggle passport. -/
theorem QuittingStoppingLawRectangleJointAtomLimit.nonempty_minimizerBridge
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    (limit : QuittingStoppingLawRectangleJointAtomLimit dispatch)
    (hreward : 0 < reward packet.terminal packet.observer)
    (other : ι) (hother : other ∈ packet.terminal.val)
    (hotherNe : other ≠ packet.observer) :
    Nonempty (QuittingStoppingLawRectangleMinimizerBridge limit other) := by
  obtain ⟨global, hglobal, hglobalReset, hglobalMin⟩ :=
    exists_joint_resetFace_debtMinimizer dispatch.cluster.1
      dispatch.cluster.2 packet.observer
      dispatch.cluster_mem
      dispatch.cluster_observer_reset
  obtain ⟨fixed, hfixed⟩ :=
    limit.exists_fixedLawResetDispatch hreward other hother hotherNe
  have hglobalLeFixed : quittingTerminalSemanticDebtSum global.1 ≤
      quittingTerminalSemanticDebtSum fixed :=
    hglobalMin (fixed, dispatch.cluster.2) hfixed.joint hfixed.reset
  have hatomMass := limit.endpoint_terminalMass_pos hreward
  refine ⟨⟨global, hglobal, hglobalReset, hglobalMin, fixed, hfixed,
    hglobalLeFixed, hatomMass, ?_⟩⟩
  rcases hglobalLeFixed.eq_or_lt with haligned | hpremium
  · left
    refine ⟨haligned.symm, ?_⟩
    intro root hnash
    let prefixed := quittingTerminalSemanticPrefix reward root fixed
    let prefixedMass :=
      quittingTerminalOutcomeLawPrefix root dispatch.cluster.2
    have hprefixedJoint : (prefixed, prefixedMass) ∈
        quittingTerminalSemanticLawCarrier reward :=
      quittingTerminalSemanticLawPrefix_mem_carrier reward root
        (fixed, dispatch.cluster.2) hfixed.joint
    have hprefixedReset : quittingTerminalSemanticDebt prefixed
        packet.observer = 0 := by
      rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) fixed root packet.observer hnash,
        hfixed.reset, mul_zero]
    have hminimalPrefix : quittingTerminalSemanticDebtSum fixed ≤
        quittingTerminalSemanticDebtSum prefixed := by
      rw [← haligned]
      exact hglobalMin (prefixed, prefixedMass) hprefixedJoint hprefixedReset
    have hscale : quittingTerminalSemanticDebtSum prefixed =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum fixed :=
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) fixed root hnash
    have hfixedPositive : 0 < quittingTerminalSemanticDebtSum fixed :=
      frontier.base_positive.trans_le hfixed.source_le
    have hcontinueLe := quittingStationaryContinueMass_le_one root
    have hcontinue : quittingStationaryContinueMass root = 1 := by
      rw [hscale] at hminimalPrefix
      nlinarith
    funext player
    have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
      hcontinue player
    simpa only [quittingAllContinueRoot] using hpure
  · exact Or.inr (sub_pos.mpr hpremium)

/-- End-to-end production consumer from the literal rectangle packet.

The witnesses keep the reset endpoint cluster, the common comparison-law
subsequence, the fixed atom law, and the global/fixed minimizer comparison in
one dependent chain.  The chain ends in a static reset dispatch; it does not
assert a chronological return. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.nonempty_fixedLawAtomReturn
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hreward : 0 < reward packet.terminal packet.observer)
    (other : ι) (hother : other ∈ packet.terminal.val)
    (hotherNe : other ≠ packet.observer) :
    ∃ dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet,
      ∃ limit : QuittingStoppingLawRectangleJointAtomLimit dispatch,
        Nonempty
          (QuittingStoppingLawRectangleMinimizerBridge limit other) := by
  obtain ⟨dispatch⟩ := packet.nonempty_resetFaceDispatch
  obtain ⟨limit⟩ := dispatch.nonempty_jointAtomLimit
  exact ⟨dispatch, limit,
    limit.nonempty_minimizerBridge hreward other hother hotherNe⟩

/-- In the strict law-premium branch, the premium is visible on the same
literal double-endpoint profiles that carry the fixed signed atom.  More
precisely, those endpoints eventually remain at least half the premium above
the global reset-face minimum, while their atom lower bound is unchanged.

This is the sharp literal obstruction to approximating the global reset-face
minimum while retaining the selected endpoint law.  It is not by itself a
profitable deviation: the atom still compares two counterfactual mover
endpoints. -/
theorem QuittingStoppingLawRectangleMinimizerBridge.eventually_literal_lawPremium
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {witness : QuittingTerminalExploitabilityWitness reward}
    {frontier : QuittingCounterexampleStoppingLawFrontier witness}
    {packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier}
    {dispatch : QuittingStoppingLawRectangleResetFaceDispatch packet}
    {limit : QuittingStoppingLawRectangleJointAtomLimit dispatch}
    {other : ι}
    (bridge : QuittingStoppingLawRectangleMinimizerBridge limit other)
    (hpremium : 0 < quittingTerminalSemanticDebtSum bridge.fixed -
      quittingTerminalSemanticDebtSum bridge.global.1) :
    ∀ᶠ n in atTop,
        ((quittingTerminalSemanticDebtSum bridge.fixed -
              quittingTerminalSemanticDebtSum bridge.global.1) / 2 <
          quittingTerminalSemanticDebtSum
              (quittingStoppingLawRectangleDoubleEndpointPoint packet
                (dispatch.subseq (limit.subseq n))).1 -
            quittingTerminalSemanticDebtSum bridge.global.1) ∧
        packet.charge / 4 ≤
          (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
            quittingTerminalPayoffDifferenceAtom reward
              (quittingStoppingLawRectangleDoubleEndpointProfile packet
                (dispatch.subseq (limit.subseq n)))
              (quittingStoppingLawRectangleSourceResponseProfile packet
                (dispatch.subseq (limit.subseq n)))
              packet.observer (some packet.terminal) := by
  have hdebtTendsto : Tendsto (fun n =>
      quittingTerminalSemanticDebtSum
        (quittingStoppingLawRectangleDoubleEndpointPoint packet
          (dispatch.subseq (limit.subseq n))).1) atTop
      (nhds (quittingTerminalSemanticDebtSum dispatch.cluster.1)) := by
    have hjoint : Tendsto (fun n =>
        quittingStoppingLawRectangleDoubleEndpointPoint packet
          (dispatch.subseq (limit.subseq n))) atTop
        (nhds dispatch.cluster) := by
      simpa only [quittingStoppingLawRectangleDoubleEndpointPoint] using
        limit.endpoint_tendsto
    exact (continuous_quittingTerminalSemanticDebtSum.comp
      continuous_fst).continuousAt.tendsto.comp hjoint
  have hthreshold : quittingTerminalSemanticDebtSum bridge.global.1 +
        (quittingTerminalSemanticDebtSum bridge.fixed -
          quittingTerminalSemanticDebtSum bridge.global.1) / 2 <
      quittingTerminalSemanticDebtSum dispatch.cluster.1 := by
    have hfixedLeCluster := bridge.fixed_dispatch.target_ge
    linarith
  have heventually := hdebtTendsto.eventually
    (Ioi_mem_nhds hthreshold)
  filter_upwards [heventually] with n hn
  exact ⟨by linarith, dispatch.atom_bound (limit.subseq n)⟩

end GameTheory
