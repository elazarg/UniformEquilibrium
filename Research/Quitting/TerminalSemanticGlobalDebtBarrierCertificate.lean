/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Research.Quitting.ElementaryTailSemanticReduction
import UniformEquilibrium.Quitting.Root.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawExploitabilityFloor
import UniformEquilibrium.Quitting.Terminal.ExploitabilityGap

/-!
# An inductive barrier certificate for a global terminal-debt floor

This experiment gives concrete counterexample search a sound positive-floor
certificate.  A barrier in the finite-dimensional terminal-semantic space
must contain the Never boundary pair, be invariant under every one-stage
product-root prefix, and carry the proposed debt floor.  The sure-joint and
sure-solo elementary boundaries are themselves one prefix step from Never,
so this reduced interface is equivalent to requiring all `card ι + 2`
elementary boundary pairs.  Finite backward induction then covers every
elementary capped word.
Unconditional elementary-tail density transfers the floor to every literal
behavior profile, and closure transfers it to the whole semantic carrier.

The certificate has no cutoff parameter.  For a barrier described by finitely
many polynomial inequalities, its boundary, prefix-invariance, and floor
obligations are finite-dimensional semialgebraic formulas (the root ranges
over one Boolean simplex per player, and the prefix map is piecewise
polynomial through `max`).  Thus quantifier elimination or a checked SOS
proof can in principle discharge a proposed certificate.

This is a certificate *schema*, not an automatic finite-support theorem.
Elementary compression supplies no reward-table-dependent uniform cutoff:
the approximating cutoff may grow with both the profile and the requested
accuracy.
-/

noncomputable section

namespace GameTheory
namespace TerminalSemanticGlobalDebtBarrierCertificate

open Filter Math.Probability Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A finite-dimensional inductive certificate for a proposed global lower
bound on total literal terminal debt.  No topological closure assumption on
`barrier` is needed: approximation is used only after applying `debt_floor`.
-/
structure Certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) where
  barrier : Set (QuittingTerminalSemanticPair ι)
  elementaryBoundary_mem : ∀ cap : QuittingElementaryTailCap ι,
    quittingElementaryBoundarySemanticPair reward cap ∈ barrier
  prefix_mem : ∀ (pair : QuittingTerminalSemanticPair ι), pair ∈ barrier →
    ∀ root : ι → PMF Bool,
      quittingTerminalSemanticPrefix reward root pair ∈ barrier
  debt_floor : ∀ pair ∈ barrier,
    δ ≤ quittingTerminalSemanticDebtSum pair

/-- Minimal form of an inductive debt-barrier certificate.  Prefix invariance
generates the sure-joint and sure-solo elementary boundaries from the single
Never boundary, so no other boundary hypotheses are needed. -/
structure ReducedCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) where
  barrier : Set (QuittingTerminalSemanticPair ι)
  neverBoundary_mem : quittingNeverBoundarySemanticPair reward ∈ barrier
  prefix_mem : ∀ (pair : QuittingTerminalSemanticPair ι), pair ∈ barrier →
    ∀ root : ι → PMF Bool,
      quittingTerminalSemanticPrefix reward root pair ∈ barrier
  debt_floor : ∀ pair ∈ barrier,
    δ ≤ quittingTerminalSemanticDebtSum pair

omit [DecidableEq ι] in
/-- The Never boundary gives a table-level ceiling on every certified debt
floor.  No prefix-invariance or closure hypothesis is needed for this bound:
the prescribed Never payoff is zero and its cap is the positive part of the
singleton quitting payoff in each coordinate. -/
theorem debtFloor_le_sum_positiveSingleton
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (barrier : Set (QuittingTerminalSemanticPair ι)) (δ : ℝ)
    (hnever : quittingNeverBoundarySemanticPair reward ∈ barrier)
    (hfloor : ∀ pair ∈ barrier,
      δ ≤ quittingTerminalSemanticDebtSum pair) :
    δ ≤ ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  have h := hfloor _ hnever
  simpa [quittingNeverBoundarySemanticPair,
    quittingTerminalSemanticDebtSum, quittingTerminalSemanticDebt] using h

/-- Certificate-facing form of the Never-boundary ceiling. -/
theorem ReducedCertificate.floor_le_sum_positiveSingleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ : ℝ}
    (certificate : ReducedCertificate reward δ) :
    δ ≤ ∑ who, max 0 (reward (quittingSingletonTerminal who) who) := by
  exact debtFloor_le_sum_positiveSingleton reward certificate.barrier δ
    certificate.neverBoundary_mem certificate.debt_floor

/-- A reduced certificate supplies the legacy all-elementary-boundary
interface: each non-Never boundary is one certified prefix step from Never. -/
def ReducedCertificate.toCertificate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ : ℝ}
    (certificate : ReducedCertificate reward δ) : Certificate reward δ where
  barrier := certificate.barrier
  elementaryBoundary_mem := by
    intro cap
    cases cap with
    | never => exact certificate.neverBoundary_mem
    | sureJoint =>
        exact certificate.prefix_mem _ certificate.neverBoundary_mem
          quittingSureJointRoot
    | sureSolo owner =>
        exact certificate.prefix_mem _ certificate.neverBoundary_mem
          (quittingSureSoloRoot owner)
  prefix_mem := certificate.prefix_mem
  debt_floor := certificate.debt_floor

/-- Forget the redundant elementary-boundary hypotheses of a legacy
certificate. -/
def Certificate.toReducedCertificate
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {δ : ℝ}
    (certificate : Certificate reward δ) : ReducedCertificate reward δ where
  barrier := certificate.barrier
  neverBoundary_mem := certificate.elementaryBoundary_mem .never
  prefix_mem := certificate.prefix_mem
  debt_floor := certificate.debt_floor

/-- The reduced and legacy certificate interfaces are equi-inhabited. -/
theorem nonempty_reducedCertificate_iff_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) :
    Nonempty (ReducedCertificate reward δ) ↔
      Nonempty (Certificate reward δ) := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.toCertificate⟩
  · rintro ⟨certificate⟩
    exact ⟨certificate.toReducedCertificate⟩

/-- The finite-prefix reachable set generated by the finitely many elementary
semantic boundaries.  The word length is existential and unbounded. -/
def finiteElementarySemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  {pair | ∃ (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
      (cap : QuittingElementaryTailCap ι),
    pair = quittingFinitePrefixSemanticEval reward roots cutoff
      (quittingElementaryBoundarySemanticPair reward cap)}

/-- The finite-prefix reachable set generated from the Never boundary alone.
The word length remains existential and unbounded. -/
def neverGeneratedSemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Set (QuittingTerminalSemanticPair ι) :=
  {pair | ∃ (roots : ℕ → ι → PMF Bool) (cutoff : ℕ),
    pair = quittingFinitePrefixSemanticEval reward roots cutoff
      (quittingNeverBoundarySemanticPair reward)}

/-- The Never-generated reachable set is closed under one further root
prefix. -/
theorem quittingTerminalSemanticPrefix_mem_neverGeneratedSemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (pair : QuittingTerminalSemanticPair ι)
    (hpair : pair ∈ neverGeneratedSemanticReachable reward) :
    quittingTerminalSemanticPrefix reward root pair ∈
      neverGeneratedSemanticReachable reward := by
  obtain ⟨roots, cutoff, rfl⟩ := hpair
  let prefixedRoots : ℕ → ι → PMF Bool
    | 0 => root
    | time + 1 => roots time
  refine ⟨prefixedRoots, cutoff + 1, ?_⟩
  simp only [quittingFinitePrefixSemanticEval]
  change _ = quittingTerminalSemanticPrefix reward root
    (quittingFinitePrefixSemanticEval reward roots cutoff
      (quittingNeverBoundarySemanticPair reward))
  congr 1

/-- Every elementary boundary is already Never-generated: sure boundaries
are the corresponding sure-root prefix of Never. -/
theorem quittingElementaryBoundarySemanticPair_mem_neverGenerated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cap : QuittingElementaryTailCap ι) :
    quittingElementaryBoundarySemanticPair reward cap ∈
      neverGeneratedSemanticReachable reward := by
  cases cap with
  | never =>
      exact ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  | sureJoint =>
      apply quittingTerminalSemanticPrefix_mem_neverGeneratedSemanticReachable
        reward quittingSureJointRoot
      exact ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩
  | sureSolo owner =>
      apply quittingTerminalSemanticPrefix_mem_neverGeneratedSemanticReachable
        reward (quittingSureSoloRoot owner)
      exact ⟨fun _ => quittingAllContinueRoot, 0, rfl⟩

/-- The apparent `card ι + 2` boundary generator family is redundant:
finite root words from all elementary boundaries give exactly the same set as
finite root words from Never alone. -/
theorem finiteElementarySemanticReachable_eq_neverGenerated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    finiteElementarySemanticReachable reward =
      neverGeneratedSemanticReachable reward := by
  apply Set.Subset.antisymm
  · rintro pair ⟨roots, cutoff, cap, rfl⟩
    induction cutoff generalizing roots with
    | zero =>
        exact quittingElementaryBoundarySemanticPair_mem_neverGenerated
          reward cap
    | succ cutoff ih =>
        simp only [quittingFinitePrefixSemanticEval]
        exact quittingTerminalSemanticPrefix_mem_neverGeneratedSemanticReachable
          reward (roots 0) _ (ih (fun time => roots (time + 1)))
  · rintro pair ⟨roots, cutoff, rfl⟩
    exact ⟨roots, cutoff, .never, rfl⟩

/-- Every finite elementary evaluation is literally attainable, hence lies in
the semantic carrier. -/
theorem finiteElementarySemanticReachable_subset_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    finiteElementarySemanticReachable reward ⊆
      quittingTerminalSemanticCarrier reward := by
  rintro pair ⟨roots, cutoff, cap, rfl⟩
  apply subset_closure
  refine ⟨quittingRootSequenceProfile reward
      (quittingElementaryTailRoots roots cutoff cap) 0, ?_⟩
  exact quittingTerminalSemanticPair_elementaryTail_eq_finiteEval
    reward roots cutoff cap

/-- Every literal semantic pair is a limit of finite elementary evaluations.
The cutoff may depend on the accuracy and is not uniformly bounded. -/
theorem attainable_subset_closure_finiteElementarySemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingAttainableTerminalSemanticPairs reward ⊆
      closure (finiteElementarySemanticReachable reward) := by
  rintro _ ⟨profile, rfl⟩
  let accuracy : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have haccuracy : ∀ n, 0 < accuracy n := by
    intro n
    dsimp [accuracy]
    positivity
  have hexists : ∀ n, ∃ cap : QuittingElementaryTailCap ι, ∃ cutoff,
      ∀ observer,
        |(quittingTerminalSemanticPair reward profile).1 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).1
                observer| < accuracy n ∧
        |(quittingTerminalSemanticPair reward profile).2 observer -
            (quittingTerminalSemanticPair reward
              (quittingElementaryCompressedProfile reward profile cutoff cap)).2
                observer| < accuracy n := by
    intro n
    obtain ⟨cap, cutoff, hclose⟩ :=
      exists_elementaryCompressedProfile_terminalSemantics_close
        reward profile (haccuracy n)
    exact ⟨cap, cutoff, fun observer =>
      ⟨(hclose observer).1, (hclose observer).2.1⟩⟩
  choose caps cutoffs hclose using hexists
  let approximant : ℕ → QuittingTerminalSemanticPair ι := fun n =>
    quittingTerminalSemanticPair reward
      (quittingElementaryCompressedProfile reward profile (cutoffs n) (caps n))
  have hmem : ∀ n, approximant n ∈
      finiteElementarySemanticReachable reward := by
    intro n
    refine ⟨quittingProfileLiveRoot reward profile, cutoffs n, caps n, ?_⟩
    dsimp [approximant]
    exact quittingTerminalSemanticPair_elementaryCompressedProfile_eq_finiteEval
      reward profile (cutoffs n) (caps n)
  have haccuracyLimit : Tendsto accuracy atTop (𝓝 0) := by
    simpa [accuracy] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htendsto : Tendsto approximant atTop
      (𝓝 (quittingTerminalSemanticPair reward profile)) := by
    apply (Prod.tendsto_iff _ _).2
    constructor
    · apply tendsto_pi_nhds.2
      intro observer
      apply Metric.tendsto_atTop.2
      intro ε hε
      have heventually : ∀ᶠ n : ℕ in atTop, accuracy n < ε :=
        (tendsto_order.1 haccuracyLimit).2 ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
      exact ⟨N, fun n hn => by
        have hnclose := (hclose n observer).1
        simpa [approximant, Real.dist_eq, abs_sub_comm] using
          hnclose.trans (hN n hn)⟩
    · apply tendsto_pi_nhds.2
      intro observer
      apply Metric.tendsto_atTop.2
      intro ε hε
      have heventually : ∀ᶠ n : ℕ in atTop, accuracy n < ε :=
        (tendsto_order.1 haccuracyLimit).2 ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventually
      exact ⟨N, fun n hn => by
        have hnclose := (hclose n observer).2
        simpa [approximant, Real.dist_eq, abs_sub_comm] using
          hnclose.trans (hN n hn)⟩
  exact mem_closure_iff_seq_limit.mpr ⟨approximant, hmem, htendsto⟩

/-- Exact reachable-set characterization of the compact semantic carrier:
it is the closure of finite words generated from the `card ι + 2` elementary
boundaries.  This is the conceptual completeness statement behind inductive
barrier certificates. -/
theorem terminalSemanticCarrier_eq_closure_finiteElementarySemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalSemanticCarrier reward =
      closure (finiteElementarySemanticReachable reward) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
      (attainable_subset_closure_finiteElementarySemanticReachable
        reward)
      isClosed_closure
  · apply closure_minimal
      (finiteElementarySemanticReachable_subset_carrier reward)
      isClosed_closure

/-- Never alone is an exact finite-word generator of the compact semantic
carrier after closure. -/
theorem terminalSemanticCarrier_eq_closure_neverGeneratedSemanticReachable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    quittingTerminalSemanticCarrier reward =
      closure (neverGeneratedSemanticReachable reward) := by
  rw [← finiteElementarySemanticReachable_eq_neverGenerated]
  exact terminalSemanticCarrier_eq_closure_finiteElementarySemanticReachable
    reward

/-- Every finite prefix evaluated from an elementary boundary lies in an
inductive barrier. -/
theorem finitePrefixSemanticEval_mem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ)
    (certificate : Certificate reward δ)
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (cap : QuittingElementaryTailCap ι) :
    quittingFinitePrefixSemanticEval reward roots cutoff
        (quittingElementaryBoundarySemanticPair reward cap) ∈
      certificate.barrier := by
  induction cutoff generalizing roots with
  | zero =>
      simpa [quittingFinitePrefixSemanticEval] using
        certificate.elementaryBoundary_mem cap
  | succ cutoff ih =>
      simp only [quittingFinitePrefixSemanticEval]
      exact certificate.prefix_mem _
        (ih (fun time => roots (time + 1))) (roots 0)

/-- **Global debt barrier theorem.**  An inductive certificate proves its
debt floor on the entire compact attainable-semantic carrier, hence in
particular on every behavioral quitting profile.

The only approximation step is the already proved unconditional elementary
tail compression.  The strict contradiction below avoids assuming that the
barrier itself is closed. -/
theorem globalDebtFloor_of_certificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ)
    (certificate : Certificate reward δ) :
    ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair := by
  have hattainable : ∀ pair ∈ quittingAttainableTerminalSemanticPairs reward,
      δ ≤ quittingTerminalSemanticDebtSum pair := by
    rintro _ ⟨profile, rfl⟩
    by_contra hnotFloor
    have hstrict :
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward profile) < δ :=
      lt_of_not_ge hnotFloor
    let margin := δ - quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile)
    have hmargin : 0 < margin := by
      dsimp [margin]
      linarith
    let playerCount : ℝ := Fintype.card ι
    have hplayerCount : 0 < playerCount := by
      dsimp [playerCount]
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
    let accuracy := margin / (2 * playerCount)
    have haccuracy : 0 < accuracy := by
      dsimp [accuracy]
      positivity
    obtain ⟨cap, cutoff, hclose⟩ :=
      exists_elementaryCompressedProfile_terminalSemantics_close
        reward profile haccuracy
    let compressed :=
      quittingElementaryCompressedProfile reward profile cutoff cap
    have hcompressedBarrier :
        quittingTerminalSemanticPair reward compressed ∈
          certificate.barrier := by
      rw [quittingTerminalSemanticPair_elementaryCompressedProfile_eq_finiteEval
        reward profile cutoff cap]
      exact finitePrefixSemanticEval_mem
        reward δ certificate (quittingProfileLiveRoot reward profile)
          cutoff cap
    have hcompressedFloor :
        δ ≤ quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward compressed) :=
      certificate.debt_floor _ hcompressedBarrier
    have hcoordinate : ∀ who,
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward compressed) who <
          quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) who + accuracy := by
      intro who
      have hdebtClose := (hclose who).2.2
      rw [abs_lt] at hdebtClose
      linarith
    have hsum :
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward compressed) <
          quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward profile) +
            playerCount * accuracy := by
      unfold quittingTerminalSemanticDebtSum
      calc
        ∑ who, quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward compressed) who <
            ∑ who, (quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) who + accuracy) := by
              apply Finset.sum_lt_sum
              · intro who _
                exact (hcoordinate who).le
              · let who : ι := Classical.choice inferInstance
                exact ⟨who, Finset.mem_univ who, hcoordinate who⟩
        _ = (∑ who, quittingTerminalSemanticDebt
              (quittingTerminalSemanticPair reward profile) who) +
              playerCount * accuracy := by
            rw [Finset.sum_add_distrib]
            simp [playerCount]
    have hscale : playerCount * accuracy = margin / 2 := by
      dsimp [accuracy]
      field_simp [ne_of_gt hplayerCount]
    have hbelow :
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward compressed) < δ := by
      rw [hscale] at hsum
      dsimp [margin] at hsum
      linarith
    linarith
  intro pair hpair
  have hfloorClosed : IsClosed
      {candidate : QuittingTerminalSemanticPair ι |
        δ ≤ quittingTerminalSemanticDebtSum candidate} :=
    isClosed_le continuous_const continuous_quittingTerminalSemanticDebtSum
  exact (closure_minimal hattainable hfloorClosed) hpair

/-- Global debt-floor soundness for the minimal Never-only certificate
interface. -/
theorem globalDebtFloor_of_reducedCertificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ)
    (certificate : ReducedCertificate reward δ) :
    ∀ pair ∈ quittingTerminalSemanticCarrier reward,
      δ ≤ quittingTerminalSemanticDebtSum pair := by
  exact globalDebtFloor_of_certificate reward δ certificate.toCertificate

/-- The barrier schema is logically complete: a certified barrier implies the
global floor, while any true global floor admits the whole semantic carrier as
an invariant barrier.  The reverse witness is generally not an effective
certificate; concrete search must still discover a finitely described
semialgebraic superset with the required invariant and floor proofs. -/
theorem nonempty_certificate_iff_globalDebtFloor
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) :
    Nonempty (Certificate reward δ) ↔
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        δ ≤ quittingTerminalSemanticDebtSum pair := by
  constructor
  · rintro ⟨certificate⟩
    exact globalDebtFloor_of_certificate
      reward δ certificate
  · intro hfloor
    refine ⟨{
      barrier := quittingTerminalSemanticCarrier reward
      elementaryBoundary_mem := fun cap => ?_
      prefix_mem := fun pair hpair root =>
        quittingTerminalSemanticPrefix_mem_carrier
          reward root pair hpair
      debt_floor := hfloor }⟩
    apply finiteElementarySemanticReachable_subset_carrier reward
    exact ⟨fun _ => quittingAllContinueRoot, 0, cap, by
      simp [quittingFinitePrefixSemanticEval]⟩

/-- Logical completeness is unchanged by removing the redundant elementary
boundary fields.  As for the legacy interface, the reverse witness may be the
whole carrier and need not be an effective finitely described certificate. -/
theorem nonempty_reducedCertificate_iff_globalDebtFloor
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) :
    Nonempty (ReducedCertificate reward δ) ↔
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        δ ≤ quittingTerminalSemanticDebtSum pair := by
  rw [nonempty_reducedCertificate_iff_certificate]
  exact nonempty_certificate_iff_globalDebtFloor reward δ

/-- Profile-facing consumer for certified search. -/
theorem behavioralDebtFloor_of_certificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ)
    (certificate : Certificate reward δ)
    (profile : (quittingGame reward).BehaviorProfile) :
    δ ≤ quittingTerminalDebtSum reward profile := by
  exact globalDebtFloor_of_certificate reward δ certificate
    (quittingTerminalSemanticPair reward profile)
    (subset_closure ⟨profile, rfl⟩)

/-- Profile-facing consumer for the reduced Never-only certificate. -/
theorem behavioralDebtFloor_of_reducedCertificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ)
    (certificate : ReducedCertificate reward δ)
    (profile : (quittingGame reward).BehaviorProfile) :
    δ ≤ quittingTerminalDebtSum reward profile := by
  exact behavioralDebtFloor_of_certificate reward δ certificate.toCertificate profile

/-- A positive certified total-debt floor gives a fixed terminal
exploitability gap.  The factor `2` pays for approaching the behavioral
best-response supremum by an executable deviation; no attainment assumption
is made. -/
theorem hasTerminalExploitabilityGap_of_certificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {δ : ℝ}
    (hδ : 0 < δ) (certificate : Certificate reward δ) :
    HasTerminalExploitabilityGap reward
      (δ / (2 * (Fintype.card ι : ℝ))) := by
  intro profile
  let playerCount : ℝ := Fintype.card ι
  have hplayerCount : 0 < playerCount := by
    dsimp [playerCount]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  let gap := δ / (2 * playerCount)
  have hgap : 0 < gap := by
    dsimp [gap]
    positivity
  have hfloor : δ ≤ quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward profile) :=
    behavioralDebtFloor_of_certificate reward δ certificate profile
  have hsumBound :=
    quittingTerminalSemanticDebtSum_le_card_mul_terminalExploitability
      reward profile
  have hexploit : δ / playerCount ≤
      quittingTerminalExploitability reward profile := by
    apply (div_le_iff₀ hplayerCount).2
    simpa [playerCount, mul_comm] using hfloor.trans hsumBound
  obtain ⟨who, _, hwho⟩ := Finset.exists_mem_eq_sup'
    Finset.univ_nonempty
    (fun who => max 0 (quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who))
  have hwhoNonneg : 0 ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who :=
    quittingTerminalDeviationDebt_nonneg reward profile who
  have hwhoDebt : δ / playerCount ≤ quittingTerminalSemanticDebt
      (quittingTerminalSemanticPair reward profile) who := by
    rw [← quittingTerminalSemanticExploitability_pair] at hexploit
    unfold quittingTerminalSemanticExploitability
      QuittingBoundaryHolonomy.finitePlayerMax at hexploit
    rw [hwho, max_eq_right hwhoNonneg] at hexploit
    exact hexploit
  obtain ⟨deviation, hdeviation⟩ :=
    exists_quittingContinuation_deviation_ge_sub
      reward profile who hgap
  refine ⟨who, deviation, ?_⟩
  change quittingTerminalPayoff reward profile who + gap ≤
    quittingTerminalPayoff reward
      (Function.update profile who deviation) who
  change δ / playerCount ≤
    quittingContinuationBestResponseValue reward profile who -
      quittingTerminalPayoff reward profile who at hwhoDebt
  have htwice : δ / playerCount = 2 * gap := by
    dsimp [gap]
    field_simp [ne_of_gt hplayerCount]
  rw [htwice] at hwhoDebt
  linarith

/-- Named conjecture-level consumer: a positive inductive barrier certificate
rules out every uniform-equilibrium payoff. -/
theorem not_exists_uniformEquilibriumPayoff_of_certificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {δ : ℝ}
    (hδ : 0 < δ) (certificate : Certificate reward δ) :
    ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have hplayerCount : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  exact quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
    reward (div_pos hδ (mul_pos (by norm_num) hplayerCount))
      (hasTerminalExploitabilityGap_of_certificate
        reward hδ certificate)

/-- A positive reduced Never-only certificate gives the same fixed terminal
exploitability gap as the legacy elementary-boundary certificate. -/
theorem hasTerminalExploitabilityGap_of_reducedCertificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {δ : ℝ}
    (hδ : 0 < δ) (certificate : ReducedCertificate reward δ) :
    HasTerminalExploitabilityGap reward
      (δ / (2 * (Fintype.card ι : ℝ))) := by
  exact hasTerminalExploitabilityGap_of_certificate reward hδ
    certificate.toCertificate

/-- Named conjecture-level consumer for the minimal Never-only interface. -/
theorem not_exists_uniformEquilibriumPayoff_of_reducedCertificate
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {δ : ℝ}
    (hδ : 0 < δ) (certificate : ReducedCertificate reward δ) :
    ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  exact not_exists_uniformEquilibriumPayoff_of_certificate reward hδ
    certificate.toCertificate

end TerminalSemanticGlobalDebtBarrierCertificate
end GameTheory

namespace GameTheory.TerminalSemanticGlobalDebtBarrierCertificate


end GameTheory.TerminalSemanticGlobalDebtBarrierCertificate
