/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticElementaryTailCompression
import Research.Quitting.PureTimeWitnessEscapeDichotomy
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.ContinuePrefixAtomAccess
import UniformEquilibrium.Diagnostics.Quitting.StoppingLaw.OffDiagonal.AtomRectangleSequenceAlternative

/-!
# A four-way normal form for the literal stopping-law rectangle sequence

The off-diagonal atom sequence already has a fixed terminal label, a uniform
positive rectangle atom, and observer debt tending to zero.  The only datum
still allowed to switch arbitrarily is its selected pure quit time.

After one strict subsequence it is either fixed finite, literal `Never`, or a
finite time escaping to infinity.  In the escaping case the exact
pure-time/`Never` transport identity gives a useful dichotomy at the fixed
scale `charge / 8`: either `Never` is within `charge / 16` of the selected
response, or the reached endpoint has local Quit-minus-Continue gap at least
`charge / 16`.

The restriction constructor below retains the *same literal profiles*,
terminal coalition, atom inequality, and vanishing observer debt.  The final
section records what unconditional elementary tail compression supplies at
every late local endpoint: the marked root and atom chronology are retained,
the continuation becomes an exact finite semantic recursion, and its
semantic pair can be made arbitrarily close.  It does not make the marked root
Nash against that recursion; that is the remaining state-match.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability
open Math.PureTimeWitnessNormalForm
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Restrict a fixed-label rectangle packet along a strict subsequence.  All
literal and asymptotic provenance is retained definitionally. -/
def QuittingStoppingLawVanishingDebtRectangleSequence.restrict
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) :
    QuittingStoppingLawVanishingDebtRectangleSequence frontier where
  mover := packet.mover
  observer := packet.observer
  charge := packet.charge
  observer_ne_mover := packet.observer_ne_mover
  charge_pos := packet.charge_pos
  rank := packet.rank ∘ subseq
  rank_strictMono := packet.rank_strictMono.comp hsubseq
  quitTime := packet.quitTime ∘ subseq
  terminal := packet.terminal
  atom_bound := fun n => packet.atom_bound (subseq n)
  observer_debt_tendsto_zero :=
    packet.observer_debt_tendsto_zero.comp hsubseq.tendsto_atTop

@[simp] theorem quittingStoppingLawRectangleTargetProfile_restrict
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (n : ℕ) :
    quittingStoppingLawRectangleTargetProfile
        (packet.restrict subseq hsubseq) n =
      quittingStoppingLawRectangleTargetProfile packet (subseq n) := by
  rfl

/-- The literal target root word seen by the observer before inserting its
selected pure-time response. -/
def quittingStoppingLawRectangleTargetRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) : ι → PMF Bool :=
  quittingProfileLiveRoot reward
    (quittingStoppingLawRectangleTargetProfile packet n) time

@[simp] theorem quittingStoppingLawRectangleTargetRoots_restrict
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (n time : ℕ) :
    quittingStoppingLawRectangleTargetRoots
        (packet.restrict subseq hsubseq) n time =
      quittingStoppingLawRectangleTargetRoots packet (subseq n) time := by
  rfl

@[simp] theorem quittingStoppingLawRectangleQuitTime_restrict
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq) (n : ℕ) :
    (packet.restrict subseq hsubseq).quitTime n =
      packet.quitTime (subseq n) := by
  rfl

/-- The selected pure-time observer payoff on the literal target word. -/
def quittingStoppingLawRectangleSelectedPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward
    (quittingStoppingLawRectangleTargetRoots packet n) packet.observer
    (packet.quitTime n) 0

/-- The literal `Never` payoff against the same target opponent word. -/
def quittingStoppingLawRectangleNeverPayoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) : ℝ :=
  quittingRootSequencePureTimeTerminalValue reward
    (quittingStoppingLawRectangleTargetRoots packet n) packet.observer none 0

/-- The four exhaustive temporal modes.  In the last mode, the local gap is
at an actually reached date: opponent survival to that date is positive. -/
def HasQuittingStoppingLawRectanglePureTimeNormalForm
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) : Prop :=
  (∃ time : ℕ, ∀ n, packet.quitTime n = some time) ∨
    (∀ n, packet.quitTime n = none) ∨
    (∃ time : ℕ → ℕ,
      Tendsto time atTop atTop ∧
      (∀ n, packet.quitTime n = some (time n)) ∧
      ∀ n,
        quittingStoppingLawRectangleSelectedPayoff packet n ≤
          quittingStoppingLawRectangleNeverPayoff packet n +
            packet.charge / 16) ∨
    ∃ time : ℕ → ℕ,
      Tendsto time atTop atTop ∧
      (∀ n, packet.quitTime n = some (time n)) ∧
      ∀ n,
        packet.charge / 16 ≤
            quittingRootEndpointDifference reward
              (fun _ => quittingRootSequencePureTimeTerminalValue reward
                (quittingStoppingLawRectangleTargetRoots packet n)
                packet.observer none (time n + 1))
              (quittingStoppingLawRectangleTargetRoots packet n (time n))
              packet.observer ∧
          0 < quittingOpponentSurvivalWeight
            (quittingStoppingLawRectangleTargetRoots packet n)
            packet.observer 0 (time n)

/-- **Literal four-way rectangle normal form.**  The returned packet is only
a restriction of the supplied packet.  Consequently its terminal label and
atom bound remain literal, and its observer debt still tends to zero. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.exists_restrict_pureTimeNormalForm
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier) :
    ∃ subseq : ℕ → ℕ, ∃ hsubseq : StrictMono subseq,
      HasQuittingStoppingLawRectanglePureTimeNormalForm
        (packet.restrict subseq hsubseq) := by
  let eta := packet.charge / 8
  have heta : 0 < eta := div_pos packet.charge_pos (by norm_num)
  let roots : ℕ → ℕ → ι → PMF Bool := fun n =>
    quittingStoppingLawRectangleTargetRoots packet n
  let prescribed : ℕ → ℝ := fun n =>
    quittingStoppingLawRectangleSelectedPayoff packet n - eta
  have hgain : ∀ n,
      eta ≤
        quittingRootSequencePureTimeTerminalValue reward (roots n)
            packet.observer (packet.quitTime n) 0 - prescribed n := by
    intro n
    dsimp only [prescribed, roots,
      quittingStoppingLawRectangleSelectedPayoff]
    linarith
  obtain ⟨subseq, hsubseq, hmode⟩ :=
    exists_pureTimeWitness_fixed_never_or_escapingDichotomy reward roots
      packet.observer packet.quitTime prescribed eta heta hgain
  refine ⟨subseq, hsubseq, ?_⟩
  let restricted := packet.restrict subseq hsubseq
  change HasQuittingStoppingLawRectanglePureTimeNormalForm restricted
  rcases hmode with hfixed | hnever | ⟨time, htime, hquit, hescape⟩
  · left
    obtain ⟨fixed, hfixed⟩ := hfixed
    exact ⟨fixed, hfixed⟩
  · exact Or.inr (Or.inl hnever)
  · rcases hescape with hneverFunded | hlate
    · exact Or.inr (Or.inr (Or.inl ⟨time, htime, hquit, fun n => by
        have h := hneverFunded n
        change
          quittingRootSequencePureTimeTerminalValue reward
              (quittingStoppingLawRectangleTargetRoots packet (subseq n))
              packet.observer (packet.quitTime (subseq n)) 0 ≤
            quittingRootSequencePureTimeTerminalValue reward
                (quittingStoppingLawRectangleTargetRoots packet (subseq n))
                packet.observer none 0 + packet.charge / 16
        dsimp only [eta, prescribed, roots,
          quittingStoppingLawRectangleSelectedPayoff] at h
        linarith⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨time, htime, hquit, fun n => by
        have h := hlate n
        change packet.charge / 16 ≤
              quittingRootEndpointDifference reward
                (fun _ => quittingRootSequencePureTimeTerminalValue reward
                  (quittingStoppingLawRectangleTargetRoots packet (subseq n))
                  packet.observer none (time n + 1))
                (quittingStoppingLawRectangleTargetRoots packet (subseq n)
                  (time n)) packet.observer ∧
            0 < quittingOpponentSurvivalWeight
              (quittingStoppingLawRectangleTargetRoots packet (subseq n))
              packet.observer 0 (time n)
        dsimp only [eta, roots] at h
        have hscale : packet.charge / 8 / 2 = packet.charge / 16 := by ring
        rw [hscale] at h
        exact h⟩))

/-- For a terminal label containing the observer, the literal `Never` mode is
impossible: a player prescribed never to Quit assigns zero mass to every
terminal coalition containing it, contradicting the packet's positive atom. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.pureTimeNormalForm_of_observer_mem
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val)
    (hnormal : HasQuittingStoppingLawRectanglePureTimeNormalForm packet) :
    (∃ time : ℕ, ∀ n, packet.quitTime n = some time) ∨
      (∃ time : ℕ → ℕ,
        Tendsto time atTop atTop ∧
        (∀ n, packet.quitTime n = some (time n)) ∧
        ∀ n,
          quittingStoppingLawRectangleSelectedPayoff packet n ≤
            quittingStoppingLawRectangleNeverPayoff packet n +
              packet.charge / 16) ∨
      ∃ time : ℕ → ℕ,
        Tendsto time atTop atTop ∧
        (∀ n, packet.quitTime n = some (time n)) ∧
        ∀ n,
          packet.charge / 16 ≤
              quittingRootEndpointDifference reward
                (fun _ => quittingRootSequencePureTimeTerminalValue reward
                  (quittingStoppingLawRectangleTargetRoots packet n)
                  packet.observer none (time n + 1))
                (quittingStoppingLawRectangleTargetRoots packet n (time n))
                packet.observer ∧
            0 < quittingOpponentSurvivalWeight
              (quittingStoppingLawRectangleTargetRoots packet n)
              packet.observer 0 (time n) := by
  rcases hnormal with hfixed | hnever | hfunded | hlate
  · exact Or.inl hfixed
  · have hbound := packet.atom_bound 0
    rw [hnever 0] at hbound
    have htargetZero :=
      quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero reward
        (Function.update
          (frontier.source (packet.rank 0))
          packet.mover.1
          (frontier.replacement packet.mover
            (packet.rank 0)))
        packet.observer packet.terminal hobserver
    have hsourceZero :=
      quittingTerminalOutcomeMass_update_pureTime_none_mem_eq_zero reward
        (Function.update
          (frontier.source (packet.rank 0))
          packet.mover.1
          (frontier.source (packet.rank 0)
            packet.mover.1))
        packet.observer packet.terminal hobserver
    unfold quittingTerminalPayoffDifferenceAtom at hbound
    rw [htargetZero, hsourceZero] at hbound
    simp only [sub_self, zero_mul, mul_zero] at hbound
    exact False.elim ((not_le_of_gt
      (div_pos packet.charge_pos (by norm_num))) hbound)
  · exact Or.inr (Or.inl hfunded)
  · exact Or.inr (Or.inr hlate)

namespace QuittingStoppingLawVanishingDebtRectangleSequence

/-- Observer-containing rectangle packets therefore have a three-way
subsequential temporal form: fixed finite, escaping and `Never`-funded, or
escaping with a positive late local gap.  Fixed terminal and vanishing debt
remain fields of the restricted packet. -/
theorem exists_restrict_observerContaining_pureTimeNormalForm
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (hobserver : packet.observer ∈ packet.terminal.val) :
    ∃ subseq : ℕ → ℕ, ∃ hsubseq : StrictMono subseq,
      let restricted := packet.restrict subseq hsubseq
      (∃ time : ℕ, ∀ n, restricted.quitTime n = some time) ∨
        (∃ time : ℕ → ℕ,
          Tendsto time atTop atTop ∧
          (∀ n, restricted.quitTime n = some (time n)) ∧
          ∀ n,
            quittingStoppingLawRectangleSelectedPayoff restricted n ≤
              quittingStoppingLawRectangleNeverPayoff restricted n +
                restricted.charge / 16) ∨
        ∃ time : ℕ → ℕ,
          Tendsto time atTop atTop ∧
          (∀ n, restricted.quitTime n = some (time n)) ∧
          ∀ n,
            restricted.charge / 16 ≤
                quittingRootEndpointDifference reward
                  (fun _ => quittingRootSequencePureTimeTerminalValue reward
                    (quittingStoppingLawRectangleTargetRoots restricted n)
                    restricted.observer none (time n + 1))
                  (quittingStoppingLawRectangleTargetRoots restricted n
                    (time n)) restricted.observer ∧
              0 < quittingOpponentSurvivalWeight
                (quittingStoppingLawRectangleTargetRoots restricted n)
                restricted.observer 0 (time n) := by
  obtain ⟨subseq, hsubseq, hnormal⟩ :=
    packet.exists_restrict_pureTimeNormalForm
  refine ⟨subseq, hsubseq, ?_⟩
  exact (packet.restrict subseq hsubseq).pureTimeNormalForm_of_observer_mem
    hobserver hnormal

end QuittingStoppingLawVanishingDebtRectangleSequence

/-! ## Unconditional finite semantics at a marked late endpoint -/

namespace QuittingStoppingLawVanishingDebtRectangleSequence

/-- At every finite selected date, the actual continuation after the marked
root admits an elementary finite-semantic representative.  It retains the
marked root (and any requested following entrance block) literally, keeps all
marked terminal-coalition masses exact, and approximates every continuation
payoff, envelope, and debt coordinate.

This is an immediate game-facing specialization of the unconditional
elementary-tail theorem. -/
theorem exists_elementaryFiniteSemanticTail_after_selectedTime
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time retainedAfterMark : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ tailCutoff,
      retainedAfterMark + 1 ≤ tailCutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum
        (fun offset =>
          quittingStoppingLawRectangleTargetRoots packet n
            (time + 1 + offset)) cap ∧
      (∀ date < time + 1 + tailCutoff,
        quittingElementaryTailRoots
            (quittingStoppingLawRectangleTargetRoots packet n)
            (time + 1 + tailCutoff) cap date =
          quittingStoppingLawRectangleTargetRoots packet n date) ∧
      (∀ terminal,
        quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward
              (quittingStoppingLawRectangleTargetRoots packet n) 0)
            (time + 1) terminal =
          quittingStageCoalitionMass reward
            (quittingRootSequenceProfile reward
              (quittingElementaryTailRoots
                (quittingStoppingLawRectangleTargetRoots packet n)
                (time + 1 + tailCutoff) cap) 0)
            (time + 1) terminal) ∧
      (∀ observer,
        |(quittingRootSequenceContinuationSemanticPair reward
              (quittingStoppingLawRectangleTargetRoots packet n)
              (time + 1)).1 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots
                (quittingStoppingLawRectangleTargetRoots packet n)
                (time + 1 + tailCutoff) cap)
              (time + 1)).1 observer| < δ ∧
        |(quittingRootSequenceContinuationSemanticPair reward
              (quittingStoppingLawRectangleTargetRoots packet n)
              (time + 1)).2 observer -
            (quittingRootSequenceContinuationSemanticPair reward
              (quittingElementaryTailRoots
                (quittingStoppingLawRectangleTargetRoots packet n)
                (time + 1 + tailCutoff) cap)
              (time + 1)).2 observer| < δ ∧
        |quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair reward
                (quittingStoppingLawRectangleTargetRoots packet n)
                (time + 1)) observer -
            quittingTerminalSemanticDebt
              (quittingRootSequenceContinuationSemanticPair reward
                (quittingElementaryTailRoots
                  (quittingStoppingLawRectangleTargetRoots packet n)
                  (time + 1 + tailCutoff) cap)
                (time + 1)) observer| < δ) ∧
      quittingRootSequenceContinuationSemanticPair reward
          (quittingElementaryTailRoots
            (quittingStoppingLawRectangleTargetRoots packet n)
            (time + 1 + tailCutoff) cap) (time + 1) =
        quittingFinitePrefixSemanticEval reward
          (fun offset =>
            quittingStoppingLawRectangleTargetRoots packet n
              (time + 1 + offset)) tailCutoff
          (quittingElementaryBoundarySemanticPair reward cap) := by
  exact exists_markedDate_elementaryCompression_continuationSemantics_close
    reward (quittingStoppingLawRectangleTargetRoots packet n) (time + 1)
      retainedAfterMark hδ

end QuittingStoppingLawVanishingDebtRectangleSequence

/-- Force the rectangle observer to Continue forever while leaving every
opponent root literal.  This is the root word whose payoff is the `Never`
term in the escaping-witness transport identity. -/
def quittingStoppingLawRectangleNeverRoots
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ) : ι → PMF Bool :=
  Function.update (quittingStoppingLawRectangleTargetRoots packet n time)
    packet.observer (PMF.pure false)

/-- The prescribed observer coordinate of the forced-Continue word is
definitionally its pure-time `Never` payoff. -/
theorem quittingStoppingLawRectangleNeverRoots_payoff
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n start : ℕ) :
    (quittingRootSequenceContinuationSemanticPair reward
        (quittingStoppingLawRectangleNeverRoots packet n) start).1
        packet.observer =
      quittingRootSequencePureTimeTerminalValue reward
        (quittingStoppingLawRectangleTargetRoots packet n) packet.observer
        none start := by
  rfl

namespace QuittingStoppingLawVanishingDebtRectangleSequence

/-- **Finite-semantic consumer for the escaping late-gap mode.**  A positive
late endpoint gap survives unconditional elementary compression of its
forced-Continue tail.  The compressed continuation is evaluated by a finite
backward recursion and retains the whole root word through the marked root.

What this does not prove is `IsQuittingRootEndpointNash` for the marked root
against the displayed finite evaluator. -/
theorem exists_elementaryFiniteSemanticTail_preserving_positiveEndpointGap
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n time : ℕ)
    (hgap : packet.charge / 16 ≤
      quittingRootEndpointDifference reward
        (fun _ => quittingRootSequencePureTimeTerminalValue reward
          (quittingStoppingLawRectangleTargetRoots packet n)
          packet.observer none (time + 1))
        (quittingStoppingLawRectangleTargetRoots packet n time)
        packet.observer) :
    ∃ cap : QuittingElementaryTailCap ι, ∃ tailCutoff,
      1 ≤ tailCutoff ∧
      QuittingElementaryCapMatchesSurvivalStratum
        (fun offset => quittingStoppingLawRectangleNeverRoots packet n
          (time + 1 + offset)) cap ∧
      (∀ date < time + 1 + tailCutoff,
        quittingElementaryTailRoots
            (quittingStoppingLawRectangleNeverRoots packet n)
            (time + 1 + tailCutoff) cap date =
          quittingStoppingLawRectangleNeverRoots packet n date) ∧
      quittingRootSequenceContinuationSemanticPair reward
          (quittingElementaryTailRoots
            (quittingStoppingLawRectangleNeverRoots packet n)
            (time + 1 + tailCutoff) cap) (time + 1) =
        quittingFinitePrefixSemanticEval reward
          (fun offset => quittingStoppingLawRectangleNeverRoots packet n
            (time + 1 + offset)) tailCutoff
          (quittingElementaryBoundarySemanticPair reward cap) ∧
      packet.charge / 32 <
        quittingRootEndpointDifference reward
          (quittingRootSequenceContinuationSemanticPair reward
            (quittingElementaryTailRoots
              (quittingStoppingLawRectangleNeverRoots packet n)
              (time + 1 + tailCutoff) cap) (time + 1)).1
          (quittingStoppingLawRectangleTargetRoots packet n time)
          packet.observer := by
  let δ := packet.charge / 32
  have hδ : 0 < δ := div_pos packet.charge_pos (by norm_num)
  obtain ⟨cap, tailCutoff, hlate, hmatch, hprefix, _hmass,
      hsemantic, heval⟩ :=
    exists_markedDate_elementaryCompression_continuationSemantics_close
      reward (quittingStoppingLawRectangleNeverRoots packet n) (time + 1) 0
      hδ
  refine ⟨cap, tailCutoff, by simpa using hlate, hmatch, hprefix, heval, ?_⟩
  let originalTail : Payoff ι := fun _ =>
    quittingRootSequencePureTimeTerminalValue reward
      (quittingStoppingLawRectangleTargetRoots packet n) packet.observer none
      (time + 1)
  let compressedTail : Payoff ι :=
    (quittingRootSequenceContinuationSemanticPair reward
      (quittingElementaryTailRoots
        (quittingStoppingLawRectangleNeverRoots packet n)
        (time + 1 + tailCutoff) cap) (time + 1)).1
  have htailClose : |originalTail packet.observer -
      compressedTail packet.observer| < δ := by
    have h := (hsemantic packet.observer).1
    rw [quittingStoppingLawRectangleNeverRoots_payoff] at h
    exact h
  have hendpointClose :=
    abs_quittingRootEndpointDifference_sub_le_tail reward originalTail
      compressedTail
      (quittingStoppingLawRectangleTargetRoots packet n time) packet.observer
  have hendpointClose' :
      |quittingRootEndpointDifference reward originalTail
          (quittingStoppingLawRectangleTargetRoots packet n time)
          packet.observer -
        quittingRootEndpointDifference reward compressedTail
          (quittingStoppingLawRectangleTargetRoots packet n time)
          packet.observer| < δ :=
    hendpointClose.trans_lt htailClose
  rw [abs_lt] at hendpointClose'
  have hgap' : packet.charge / 16 ≤
      quittingRootEndpointDifference reward originalTail
        (quittingStoppingLawRectangleTargetRoots packet n time)
        packet.observer := by
    simpa only [originalTail] using hgap
  change packet.charge / 32 <
    quittingRootEndpointDifference reward compressedTail
      (quittingStoppingLawRectangleTargetRoots packet n time)
      packet.observer
  dsimp only [δ] at hendpointClose'
  linarith

end QuittingStoppingLawVanishingDebtRectangleSequence

/-! ## Fixed-label access through an exact prefix -/

/-- The packet's fixed rectangle atom lifts through any prefix whose
mover-deleted survival is at least one half.  Both players Continue through
the prefix and then use the literal terminal strategies from the packet.  In
particular, the terminal coalition label and the pure-time normal mode are
not reselected by prefix access. -/
theorem QuittingStoppingLawVanishingDebtRectangleSequence.fixedAtom_lifts_through_continuePrefix
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {frontier : QuittingPositiveMinimumDebtTangentFamily reward}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (n : ℕ) (roots : List (ι → PMF Bool))
    (hsurvival : 1 / 2 ≤
      quittingLiteralRootStackOpponentSurvival roots packet.mover.1) :
    let terminal := frontier.source (packet.rank n)
    let target := quittingStoppingLawRectangleTargetProfile packet n
    let response := quittingPureTimeBehaviorStrategy reward packet.observer
      (packet.quitTime n)
    let moverRoots :=
      quittingLiteralRootStackForceContinue roots packet.mover.1
    let rectangleRoots :=
      quittingLiteralRootStackForceContinue moverRoots packet.observer
    packet.charge / 8 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (quittingLiteralRootStackProfile reward rectangleRoots
            (Function.update target packet.observer response))
          (quittingLiteralRootStackProfile reward rectangleRoots
            (Function.update terminal packet.observer response))
          packet.observer (some packet.terminal) := by
  classical
  dsimp only
  let terminal := frontier.source (packet.rank n)
  let target := quittingStoppingLawRectangleTargetProfile packet n
  let response := quittingPureTimeBehaviorStrategy reward packet.observer
    (packet.quitTime n)
  let moverRoots :=
    quittingLiteralRootStackForceContinue roots packet.mover.1
  let rectangleRoots :=
    quittingLiteralRootStackForceContinue moverRoots packet.observer
  have hmoverSurvival :
      quittingLiteralRootStackJointSurvival moverRoots =
        quittingLiteralRootStackOpponentSurvival roots packet.mover.1 :=
    quittingLiteralRootStackJointSurvival_forceContinue roots packet.mover.1
  have hrectangleSurvival : 1 / 2 ≤
      quittingLiteralRootStackJointSurvival rectangleRoots := by
    exact hsurvival.trans <| by
      rw [← hmoverSurvival]
      exact quittingLiteralRootStackJointSurvival_le_forceContinue
        moverRoots packet.observer
  have hatom := packet.atom_bound n
  have hsourceUpdate : Function.update terminal packet.mover.1
      (terminal packet.mover.1) = terminal := Function.update_eq_self _ _
  change packet.charge / 4 ≤
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update target packet.observer response)
          (Function.update
            (Function.update terminal packet.mover.1
              (terminal packet.mover.1)) packet.observer response)
          packet.observer (some packet.terminal) at hatom
  rw [hsourceUpdate] at hatom
  rw [quittingTerminalPayoffDifferenceAtom_literalRootStack]
  have hcard : 0 <
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) := by positivity
  have hscaledPos : 0 <
      (Fintype.card (QuittingTerminalOutcome ι) : ℝ) *
        quittingTerminalPayoffDifferenceAtom reward
          (Function.update target packet.observer response)
          (Function.update terminal packet.observer response)
          packet.observer (some packet.terminal) :=
    (div_pos packet.charge_pos (by norm_num)).trans_le hatom
  have hatomNonneg : 0 ≤
      quittingTerminalPayoffDifferenceAtom reward
        (Function.update target packet.observer response)
        (Function.update terminal packet.observer response)
        packet.observer (some packet.terminal) := by
    exact (pos_of_mul_pos_right hscaledPos hcard.le).le
  nlinarith [mul_le_mul_of_nonneg_right hrectangleSurvival hatomNonneg]

end GameTheory
