/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.Endpoint.MinimumFiberSupportDrop
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# Retained joint lift and exact horizontal debt transfer on the minimum fiber

Two accounts of what a supplied realizing object retains.

A convergent sequence of executable profiles has a strictly increasing
subsequence along which the joint terminal semantic/law points converge in
`quittingTerminalSemanticLawCarrier`, and the semantic coordinate of that
joint limit is the original semantic limit.  The supplied profile sequence
appears in the conclusion, so the joint limit lifts those realizers rather
than some other sequence with the same semantic limit.

A `QuittingPositiveMinimumDebtTangentFamily.FullReplacementCluster` lying on
the minimum total-debt fiber has an exact debt account.  Its active mover has
zero debt at the cluster and positive debt at the base, and total debt is
unchanged, so the aggregate debt change over the remaining players is exactly
the mover's base debt.  Some player other than the mover therefore gains at
least `d / (Fintype.card ι - 1)`, where `d` is the mover's base debt.  This
account uses neither flatness of the tangent column nor absence of entry into
the inactive debt support.

Two consequences are recorded as statements rather than remarks.
Coordinatewise debt nonincrease across such an endpoint is impossible, and
the total positive part of the debt change over the other players is at least
the mover's base debt, hence not uniformly small.  More strongly, a single
vanishing error cannot compare every nonmover behavioral deviation gain on
the two literal profile sequences.

Debt is the gap between the best-response envelope and the prescribed payoff,
so a lower bound on debt change bounds no envelope coordinate on its own: the
prescribed payoff may move together with the envelope.  Nothing here asserts
that the raw envelope vectors at the base and at the cluster are close.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- A convergent sequence of executable profiles has a strictly increasing
subsequence whose joint terminal semantic/law points converge in the joint
carrier, the semantic coordinate of the limit being the supplied semantic
limit.  The supplied profiles appear in the conclusion, so the joint point is
a lift of that very sequence. -/
theorem exists_retainedProfile_terminalSemanticLawCluster
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (limitPair : QuittingTerminalSemanticPair ι)
    (hprofiles : Tendsto
      (fun n ↦ quittingTerminalSemanticPair reward (profiles n))
      atTop (nhds limitPair)) :
    ∃ subseq : ℕ → ℕ, ∃ joint : QuittingTerminalSemanticLawPoint ι,
      StrictMono subseq ∧
        joint ∈ quittingTerminalSemanticLawCarrier reward ∧
        Tendsto (fun rank ↦
            (quittingTerminalSemanticPair reward (profiles (subseq rank)),
              quittingTerminalOutcomeMass reward (profiles (subseq rank))))
          atTop (nhds joint) ∧
        joint.1 = limitPair := by
  have hpoints : ∀ n,
      (quittingTerminalSemanticPair reward (profiles n),
          quittingTerminalOutcomeMass reward (profiles n)) ∈
        quittingTerminalSemanticLawCarrier reward :=
    fun n ↦ quittingTerminalSemanticLawPoint_mem_carrier reward (profiles n)
  obtain ⟨joint, hjoint, subseq, hsubseq, hlimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward).tendsto_subseq hpoints
  refine ⟨subseq, joint, hsubseq, hjoint, hlimit, ?_⟩
  have hjointFst : Tendsto
      (fun rank ↦ quittingTerminalSemanticPair reward (profiles (subseq rank)))
      atTop (nhds joint.1) := (continuous_fst.tendsto joint).comp hlimit
  have hpairFst : Tendsto
      (fun rank ↦ quittingTerminalSemanticPair reward (profiles (subseq rank)))
      atTop (nhds limitPair) := hprofiles.comp hsubseq.tendsto_atTop
  exact tendsto_nhds_unique hjointFst hpairFst

/-- A uniform comparison of every unilateral deviation gain controls the
corresponding terminal-semantic debt coordinates.  The deviations are full
behavior strategies; no attainment of either best-response supremum is used. -/
theorem abs_quittingTerminalSemanticDebt_sub_le_of_forall_deviationGain_abs_le
    (source target : (quittingGame reward).BehaviorProfile)
    (observer : ι) {error : ℝ}
    (hle : ∀ response : (quittingGame reward).BehaviorStrategy observer,
      |(quittingTerminalPayoff reward
            (Function.update target observer response) observer -
          quittingTerminalPayoff reward target observer) -
        (quittingTerminalPayoff reward
            (Function.update source observer response) observer -
          quittingTerminalPayoff reward source observer)| ≤ error) :
    |quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) observer| ≤ error := by
  have htarget : quittingContinuationBestResponseValue reward target observer ≤
      quittingTerminalPayoff reward target observer +
        (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward source) observer + error) := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨response, rfl⟩
    have hsource : quittingTerminalPayoff reward
          (Function.update source observer response) observer ≤
        quittingContinuationBestResponseValue reward source observer :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward source observer response
    have hsigned := (le_abs_self _).trans (hle response)
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  have hsource : quittingContinuationBestResponseValue reward source observer ≤
      quittingTerminalPayoff reward source observer +
        (quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward target) observer + error) := by
    unfold quittingContinuationBestResponseValue
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨response, rfl⟩
    have htargetCap : quittingTerminalPayoff reward
          (Function.update target observer response) observer ≤
        quittingContinuationBestResponseValue reward target observer :=
      quittingTerminalPayoff_update_le_continuationBestResponseValue
        reward target observer response
    have hsigned := (neg_le_abs _).trans (hle response)
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    linarith
  rw [abs_le]
  constructor <;>
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at * <;>
      linarith

namespace QuittingPositiveMinimumDebtTangentFamily

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The active mover of a positive-minimum tangent family has strictly
positive base debt. -/
theorem base_moverDebt_pos
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    0 < quittingTerminalSemanticDebt frontier.base mover.1 :=
  (frontier.positiveDebtSupport_iff mover.1).1 mover.2

/-- An active mover has a distinct opponent: its negative tangent diagonal
forces a positive off-diagonal coordinate.  No endpoint cluster and no
minimum-fiber hypothesis are involved. -/
theorem nonmover_nonempty
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    (Finset.univ.erase mover.1).Nonempty := by
  obtain ⟨observer, hobserver, -⟩ := frontier.exists_positiveOffDiagonal mover.2
  exact ⟨observer, Finset.mem_erase.mpr ⟨hobserver, Finset.mem_univ observer⟩⟩

/-- A positive-minimum tangent family with an active mover has at least two
players. -/
theorem two_le_card
    (frontier : QuittingPositiveMinimumDebtTangentFamily reward)
    (mover : {who // who ∈ frontier.positiveDebtSupport}) :
    2 ≤ Fintype.card ι := by
  have hcard : 0 < (Finset.univ.erase mover.1).card :=
    Finset.card_pos.mpr (frontier.nonmover_nonempty mover)
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at hcard
  omega

namespace FullReplacementCluster

variable {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
  {mover : {who // who ∈ frontier.positiveDebtSupport}}

/-- Uniformly vanishing distortion of every nonmover's behavioral deviation
gain across the literal full-replacement seam. -/
def HasVanishingHorizontalDeviationLeak
    (endpoint : FullReplacementCluster frontier mover) : Prop :=
  ∃ error : ℕ → ℝ,
    (∀ rank, 0 ≤ error rank) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ rank observer, observer ≠ mover.1 →
        ∀ response : (quittingGame reward).BehaviorStrategy observer,
          |(quittingTerminalPayoff reward
                (Function.update
                  (frontier.fullReplacementProfile mover
                    (endpoint.subseq rank)) observer response) observer -
              quittingTerminalPayoff reward
                (frontier.fullReplacementProfile mover
                  (endpoint.subseq rank)) observer) -
            (quittingTerminalPayoff reward
                (Function.update (frontier.source (endpoint.subseq rank))
                  observer response) observer -
              quittingTerminalPayoff reward
                (frontier.source (endpoint.subseq rank)) observer)| ≤
            error rank

/-- On the minimum total-debt fiber, the aggregate debt change over the
players other than the active mover is exactly the mover's base debt. -/
theorem nonmover_debtChange_sum_eq_moverDebt
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    (∑ observer ∈ Finset.univ.erase mover.1,
        quittingTerminalSemanticDebtChange frontier.base endpoint.cluster
          observer) =
      quittingTerminalSemanticDebt frontier.base mover.1 := by
  have hexact :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      frontier.base endpoint.cluster mover.1 endpoint.mover_debt_eq_zero
  rw [hexact, hminimumFiber, sub_self, zero_add]

/-- **Exact horizontal debt transfer.**  At a full-replacement endpoint
cluster on the minimum total-debt fiber, the active mover's debt is zero at
the cluster and positive at the base, total debt is unchanged, and the
aggregate debt change over the other players equals the mover's base debt. -/
theorem minimumFiber_debtTransfer
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    quittingTerminalSemanticDebt endpoint.cluster mover.1 = 0 ∧
      0 < quittingTerminalSemanticDebt frontier.base mover.1 ∧
        quittingTerminalSemanticDebtSum endpoint.cluster =
            quittingTerminalSemanticDebtSum frontier.base ∧
          (∑ observer ∈ Finset.univ.erase mover.1,
              quittingTerminalSemanticDebtChange frontier.base
                endpoint.cluster observer) =
            quittingTerminalSemanticDebt frontier.base mover.1 :=
  ⟨endpoint.mover_debt_eq_zero, frontier.base_moverDebt_pos mover,
    hminimumFiber, endpoint.nonmover_debtChange_sum_eq_moverDebt hminimumFiber⟩

/-- **Equal-share leakage.**  Some player other than the active mover absorbs
at least a `(Fintype.card ι - 1)`-th part of the mover's base debt, and that
share is strictly positive. -/
theorem exists_nonmover_debtChange_moverDebt_div_card_le
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    ∃ observer, observer ≠ mover.1 ∧
      0 < quittingTerminalSemanticDebt frontier.base mover.1 /
          ((Fintype.card ι : ℝ) - 1) ∧
        quittingTerminalSemanticDebt frontier.base mover.1 /
            ((Fintype.card ι : ℝ) - 1) ≤
          quittingTerminalSemanticDebtChange frontier.base endpoint.cluster
            observer := by
  have hcard := frontier.two_le_card mover
  have hdenom : 0 < (Fintype.card ι : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    linarith
  have hshare : 0 < quittingTerminalSemanticDebt frontier.base mover.1 /
      ((Fintype.card ι : ℝ) - 1) :=
    div_pos (frontier.base_moverDebt_pos mover) hdenom
  have hcardCast : ((Finset.univ.erase mover.1).card : ℝ) =
      (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Nat.cast_sub (by omega : 1 ≤ Fintype.card ι), Nat.cast_one]
  obtain ⟨observer, hobserver, hle⟩ :=
    exists_opponent_average_le_debtChange frontier.base endpoint.cluster mover.1
      (frontier.base_moverDebt_pos mover)
      (le_of_eq (endpoint.nonmover_debtChange_sum_eq_moverDebt
        hminimumFiber).symm)
  rw [hcardCast] at hle
  exact ⟨observer, (Finset.mem_erase.mp hobserver).1, hshare, hle⟩

/-- The four-player equal share.  Some player other than the active mover
absorbs at least a third of the mover's base debt. -/
theorem exists_nonmover_debtChange_moverDebt_div_three_le
    (endpoint : FullReplacementCluster frontier mover)
    (hcard : Fintype.card ι = 4)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    ∃ observer, observer ≠ mover.1 ∧
      0 < quittingTerminalSemanticDebt frontier.base mover.1 / 3 ∧
        quittingTerminalSemanticDebt frontier.base mover.1 / 3 ≤
          quittingTerminalSemanticDebtChange frontier.base endpoint.cluster
            observer := by
  have hdenom : ((Fintype.card ι : ℝ) - 1) = 3 := by
    rw [hcard]
    norm_num
  obtain ⟨observer, hne, hshare, hle⟩ :=
    endpoint.exists_nonmover_debtChange_moverDebt_div_card_le hminimumFiber
  rw [hdenom] at hshare hle
  exact ⟨observer, hne, hshare, hle⟩

/-- No coordinatewise debt nonincrease across a minimum-fiber full-replacement
endpoint: some coordinate strictly rises. -/
theorem not_forall_debt_le_base
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    ¬ ∀ observer,
        quittingTerminalSemanticDebt endpoint.cluster observer ≤
          quittingTerminalSemanticDebt frontier.base observer := by
  intro hnonincrease
  obtain ⟨observer, _, hshare, hle⟩ :=
    endpoint.exists_nonmover_debtChange_moverDebt_div_card_le hminimumFiber
  have hobserver := hnonincrease observer
  unfold quittingTerminalSemanticDebtChange at hle
  linarith

/-- The debt increase over the players other than the active mover has total
positive part at least the mover's base debt, so it is not uniformly small. -/
theorem moverDebt_le_sum_positivePart_nonmover_debtChange
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    quittingTerminalSemanticDebt frontier.base mover.1 ≤
      ∑ observer ∈ Finset.univ.erase mover.1,
        max 0 (quittingTerminalSemanticDebtChange frontier.base
          endpoint.cluster observer) := by
  rw [← endpoint.nonmover_debtChange_sum_eq_moverDebt hminimumFiber]
  exact Finset.sum_le_sum fun observer _ ↦ le_max_right _ _

/-- The exact minimum-fibre debt transfer rules out uniformly vanishing
distortion of every nonmover's full behavioral deviation gain across the
literal replacement seam. -/
theorem not_hasVanishingHorizontalDeviationLeak_of_minimumFiber
    (endpoint : FullReplacementCluster frontier mover)
    (hminimumFiber :
      quittingTerminalSemanticDebtSum endpoint.cluster =
        quittingTerminalSemanticDebtSum frontier.base) :
    ¬ endpoint.HasVanishingHorizontalDeviationLeak := by
  rintro ⟨error, _herrorNonneg, herrorZero, hgain⟩
  obtain ⟨observer, hobserver, hshare, hle⟩ :=
    endpoint.exists_nonmover_debtChange_moverDebt_div_card_le hminimumFiber
  have hsourcePair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (frontier.source (endpoint.subseq rank))) atTop
      (nhds frontier.base) :=
    frontier.source_tendsto.comp endpoint.subseq_strictMono.tendsto_atTop
  have htargetPair : Tendsto (fun rank ↦
      quittingTerminalSemanticPair reward
        (frontier.fullReplacementProfile mover
          (endpoint.subseq rank))) atTop (nhds endpoint.cluster) :=
    endpoint.fullReplacement_tendsto
  have hsourceDebt :=
    (continuous_quittingTerminalSemanticDebt observer).tendsto
      frontier.base |>.comp hsourcePair
  have htargetDebt :=
    (continuous_quittingTerminalSemanticDebt observer).tendsto
      endpoint.cluster |>.comp htargetPair
  have hdifference : Tendsto (fun rank ↦
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.fullReplacementProfile mover
              (endpoint.subseq rank))) observer -
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (frontier.source (endpoint.subseq rank))) observer)
      atTop (nhds (quittingTerminalSemanticDebtChange frontier.base
        endpoint.cluster observer)) := by
    simpa only [Function.comp_apply, quittingTerminalSemanticDebtChange] using
      htargetDebt.sub hsourceDebt
  have hdebtBound : ∀ rank,
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.fullReplacementProfile mover
                (endpoint.subseq rank))) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.source (endpoint.subseq rank))) observer| ≤
        error rank := by
    intro rank
    exact abs_quittingTerminalSemanticDebt_sub_le_of_forall_deviationGain_abs_le
      (frontier.source (endpoint.subseq rank))
      (frontier.fullReplacementProfile mover (endpoint.subseq rank))
      observer (hgain rank observer hobserver)
  have habsZero : Tendsto (fun rank ↦
      |quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.fullReplacementProfile mover
                (endpoint.subseq rank))) observer -
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (frontier.source (endpoint.subseq rank))) observer|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ ↦ abs_nonneg _
    · exact Eventually.of_forall hdebtBound
    · exact herrorZero
  have habsLimit := hdifference.abs
  have hzero :
      |quittingTerminalSemanticDebtChange frontier.base
        endpoint.cluster observer| = 0 :=
    tendsto_nhds_unique habsLimit habsZero
  have hchangeZero : quittingTerminalSemanticDebtChange frontier.base
      endpoint.cluster observer = 0 := abs_eq_zero.mp hzero
  linarith

end FullReplacementCluster

end QuittingPositiveMinimumDebtTangentFamily

end GameTheory
