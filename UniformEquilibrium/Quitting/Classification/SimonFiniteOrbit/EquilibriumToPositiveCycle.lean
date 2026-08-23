/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.SimonFiniteOrbit.SuppliedCorrespondence
import UniformEquilibrium.Quitting.Projective.FiniteForwardProjectiveLasso
import UniformEquilibrium.Quitting.Punishment.ZeroSoloDisjunct

/-!
# The corrected Simon equilibrium-to-positive-cycle assembly

This module gives a production-semantic target to the repaired necessity
argument in Simon's finite-orbit proof.  The target is an exact finite cyclic
`F_epsilon` orbit: every phase retains its product-root witness, support-local
optimality, approximate individual rationality, and one phase has positive
absorption.

The repository already proves the finite-dimensional closing step.  A common
compact carrier carrying exact forward Bellman packets of arbitrarily large
absorption charge closes to a single-seam projective lasso; cyclic correction
then gives the exact positive `F_epsilon` orbit.  The theorem
`quittingSimonPositiveCyclicOrbitCondition_of_arbitrarilyChargedForwardPackets`
is that unconditional assembly.

What is not asserted here is the source extraction of those packets from an
arbitrary behavioral approximate equilibrium.  The primary supplied
predicate retains the zero-solo alternative, because the corrected hard
branch does not force a positive charged packet on that class.  Its intended
proof uses the corrected compact uniform-rho motion lemma, the repaired first
crossing, and the subsequent uniformly-reached support purification.  In
particular, the crossing row is not charged as an approximate Bellman seam
before rationality of its actual tail has been established.

The conditional capstones prove only the hard-branch zero-solo/positive-cycle
split and its checked consumers.  They do not assert Simon's full Theorem 3,
an orbit-condition classification, or an inhabitant of the supplied
extraction predicate.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A positive finite cyclic `F_epsilon` orbit at one accuracy.

The phase value is the payoff entering that phase, and the phase root reads
the next cyclic value as its continuation.  Thus the policy and support
fields are exactly the witnessed `QuittingSimonFEdgeAt` relation from the
next value to the current value. -/
def QuittingSimonPositiveCyclicOrbitConditionAt
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (epsilon : ℝ) : Prop :=
  ∃ (period : ℕ) (cycle : Fin period → iota → PMF Bool)
      (value : Fin period → Payoff iota) (absorbingPhase : Fin period),
    IsQuittingFiniteSupportRationalCycle
        reward cycle value epsilon epsilon ∧
      0 < quittingRootAbsorptionMass (cycle absorbingPhase)

/-- Positive finite cyclic `F_epsilon` orbits at every positive accuracy. -/
def QuittingSimonPositiveCyclicOrbitCondition
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    QuittingSimonPositiveCyclicOrbitConditionAt reward epsilon

/-- A positive cyclic orbit remains one when both its support and rationality
tolerances are relaxed. -/
theorem QuittingSimonPositiveCyclicOrbitConditionAt.mono
    {reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota}
    {epsilon epsilon' : ℝ}
    (horbit : QuittingSimonPositiveCyclicOrbitConditionAt reward epsilon)
    (hle : epsilon ≤ epsilon') :
    QuittingSimonPositiveCyclicOrbitConditionAt reward epsilon' := by
  obtain ⟨period, cycle, value, absorbingPhase, hcycle, habsorbing⟩ :=
    horbit
  refine ⟨period, cycle, value, absorbingPhase, ?_, habsorbing⟩
  refine ⟨hcycle.1, ?_, ?_⟩
  · intro phase who
    constructor
    · intro hquit
      have hbound := (hcycle.2.1 phase who).1 hquit
      linarith
    · intro hcontinue
      have hbound := (hcycle.2.1 phase who).2 hcontinue
      linarith
  · intro target phase
    have hir := hcycle.2.2 target phase
    linarith

/-- Every phase of a positive cyclic orbit is literally an edge of the
production Simon correspondence, in its predecessor orientation. -/
theorem QuittingSimonPositiveCyclicOrbitConditionAt.fEdge
    {reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota}
    {epsilon : ℝ}
    (horbit : QuittingSimonPositiveCyclicOrbitConditionAt reward epsilon) :
    ∃ (period : ℕ) (cycle : Fin period → iota → PMF Bool)
        (value : Fin period → Payoff iota) (absorbingPhase : Fin period),
      (∀ phase,
        QuittingSimonFEdgeAt reward epsilon
          (value (finRotate period phase)) (value phase)) ∧
        (∀ phase,
          QuittingSimonRationalPayoffAt reward epsilon (value phase)) ∧
        0 < quittingRootAbsorptionMass (cycle absorbingPhase) := by
  obtain ⟨period, cycle, value, absorbingPhase, hcycle, habsorbing⟩ :=
    horbit
  refine ⟨period, cycle, value, absorbingPhase, ?_, ?_, habsorbing⟩
  · intro phase
    exact ⟨cycle phase, hcycle.2.1 phase, (hcycle.1 phase).symm⟩
  · intro phase who
    exact hcycle.2.2 who phase

/-- A common compact carrier supports exact forward Bellman packets with
arbitrarily large raw absorption charge at every positive support accuracy.

This is the payload shape consumed by the already checked finite charged
closing compiler.  Compactness is common to all charge targets; it cannot be
chosen afresh for each finite packet. -/
def QuittingSimonArbitrarilyChargedForwardPacketCondition
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ∃ carrier : Set (Payoff iota),
    IsCompact carrier ∧
      ∀ supportError : ℝ, 0 < supportError →
        ∀ chargeTarget : ℝ, 0 ≤ chargeTarget →
          Nonempty (QuittingFiniteForwardPacket
            reward carrier supportError chargeTarget)

/-- Single-seam projective lassos at every positive error already contain
the exact positive cyclic `F_epsilon` conclusion.  The lasso is requested at
half the target error because cyclic correction doubles support and
rationality errors. -/
theorem
    quittingSimonPositiveCyclicOrbitCondition_of_singleSeamProjectiveLassos
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hlassos : ∀ error : ℝ, 0 < error →
      ∃ period : ℕ,
        Nonempty (QuittingFiniteSingleSeamProjectiveLasso
          reward period error)) :
    QuittingSimonPositiveCyclicOrbitCondition reward := by
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  obtain ⟨period, ⟨lasso⟩⟩ := hlassos (epsilon / 2) hhalf
  refine ⟨period, lasso.cycle, lasso.toWeighted.exactValue,
    lasso.absorbingPhase, ?_, lasso.absorbing⟩
  have hcycle := lasso.toWeighted.toFiniteSupportRationalCycle
  have herror : (2 : ℝ) * (epsilon / 2) = epsilon := by ring
  simpa only [herror,
    QuittingFiniteSingleSeamProjectiveLasso.toWeighted] using hcycle

/-- The existing finite charged closer turns arbitrarily charged forward
packets into exact positive cyclic `F_epsilon` orbits.  The half-error call
accounts exactly for the cyclic correction from a single-seam lasso. -/
theorem
    quittingSimonPositiveCyclicOrbitCondition_of_arbitrarilyChargedForwardPackets
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hpackets : QuittingSimonArbitrarilyChargedForwardPacketCondition reward) :
    QuittingSimonPositiveCyclicOrbitCondition reward := by
  obtain ⟨carrier, hcarrier, hproducer⟩ := hpackets
  apply quittingSimonPositiveCyclicOrbitCondition_of_singleSeamProjectiveLassos
    reward
  intro error herror
  exact
    exists_singleSeamProjectiveLasso_of_finiteForwardPackets
      reward carrier hcarrier hproducer error herror

/-- The primary supplied boundary for the repaired Simon hard-branch
necessity direction.

No inhabitant is proved in this repository.  A proof may return the zero-solo
branch; otherwise it must extract the common compact carrier and every
charged forward packet from the corrected hard branch and an arbitrary
root-sequence approximate equilibrium.  This is narrower than supplying the
desired zero-solo/positive-cycle conclusion itself: both branch consumers,
the closing theorem, and cyclic correction are checked below.

The intended source proof factors through the corrected compact uniform-rho
motion lemma, the repaired first crossing, and a corrected adapter for the
uniformly reached support-purified prefix.  The exact-packet disjunct is
substantively stronger than the literal output in the audited note, which is
an approximate forward path with a summable seam budget.  Exactifying every
seam while retaining arbitrarily large charge inside one common compact
carrier is a separate missing adapter; it is not silently claimed here. -/
def SuppliedQuittingSimonHardBranchForwardPacketNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ¬QuittingStationarilyGeneratedApproximateEquilibria reward →
    ¬QuittingInstantPunishmentεEquilibriumExistence reward →
      QuittingApproximateEquilibriumExistence reward →
        IsQuittingZeroSolo reward ∨
          QuittingSimonArbitrarilyChargedForwardPacketCondition reward

/-- The earlier packet-only supplied boundary.  This remains a useful
stronger interface, but it suppresses the genuine zero-solo alternative and
therefore is not the primary formulation of the repaired hard branch. -/
def SuppliedQuittingSimonEquilibriumForwardPacketNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota) :
    Prop :=
  ¬QuittingStationarilyGeneratedApproximateEquilibria reward →
    ¬QuittingInstantPunishmentεEquilibriumExistence reward →
      QuittingApproximateEquilibriumExistence reward →
        QuittingSimonArbitrarilyChargedForwardPacketCondition reward

/-- The stronger packet-only supplied interface implies the primary split
interface. -/
theorem suppliedQuittingSimonHardBranchForwardPacketNecessity_of_packetOnly
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity :
      SuppliedQuittingSimonEquilibriumForwardPacketNecessity reward) :
    SuppliedQuittingSimonHardBranchForwardPacketNecessity reward := by
  intro hgenerated hinstant hequilibrium
  exact Or.inr (hnecessity hgenerated hinstant hequilibrium)

/-- **Primary conditional hard-branch assembly.**  Supplied extraction gives
the honest zero-solo/positive-cyclic structural alternative.  This refines
the shape of the hard branch; it is not needed merely to obtain a
uniform-equilibrium payoff, which follows directly from
`QuittingApproximateEquilibriumExistence`. -/
theorem
    isQuittingZeroSolo_or_simonPositiveCyclicOrbitCondition_of_suppliedHardBranch
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity :
      SuppliedQuittingSimonHardBranchForwardPacketNecessity reward)
    (hgenerated :
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward) :
    IsQuittingZeroSolo reward ∨
      QuittingSimonPositiveCyclicOrbitCondition reward := by
  rcases hnecessity hgenerated hinstant hequilibrium with hzero | hpackets
  · exact Or.inl hzero
  · exact Or.inr
      (quittingSimonPositiveCyclicOrbitCondition_of_arbitrarilyChargedForwardPackets
        reward hpackets)

/-- Off the zero-solo class, the primary supplied split yields the positive
cyclic conclusion. -/
theorem
    quittingSimonPositiveCyclicOrbitCondition_of_suppliedHardBranch_of_not_zeroSolo
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity :
      SuppliedQuittingSimonHardBranchForwardPacketNecessity reward)
    (hnotZero : ¬IsQuittingZeroSolo reward)
    (hgenerated :
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward) :
    QuittingSimonPositiveCyclicOrbitCondition reward := by
  exact
    (isQuittingZeroSolo_or_simonPositiveCyclicOrbitCondition_of_suppliedHardBranch
      reward hnecessity hgenerated hinstant hequilibrium).resolve_left hnotZero

/-- **Stronger packet-only conditional assembly.**  This compatibility
theorem uses the older supplied interface which excludes the zero-solo
alternative.  Prefer the split theorem above for the repaired hard branch. -/
theorem
    quittingSimonPositiveCyclicOrbitCondition_of_suppliedEquilibriumForwardPacketNecessity
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (hnecessity :
      SuppliedQuittingSimonEquilibriumForwardPacketNecessity reward)
    (hgenerated :
      ¬QuittingStationarilyGeneratedApproximateEquilibria reward)
    (hinstant : ¬QuittingInstantPunishmentεEquilibriumExistence reward)
    (hequilibrium : QuittingApproximateEquilibriumExistence reward) :
    QuittingSimonPositiveCyclicOrbitCondition reward := by
  exact
    quittingSimonPositiveCyclicOrbitCondition_of_arbitrarilyChargedForwardPackets
      reward (hnecessity hgenerated hinstant hequilibrium)

/-- The production periodic support-witness consumer shows that the positive
cyclic condition is sufficient for a uniform-equilibrium payoff.  This is a
consumer of supplied cycles, not a claim that arbitrary games produce them. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_simonPositiveCyclicOrbitCondition
    [Nonempty iota]
    (reward : {coalition : Finset iota // coalition.Nonempty} → Payoff iota)
    (horbit : QuittingSimonPositiveCyclicOrbitCondition reward) :
    ∃ payoff : Payoff iota,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_finiteSupportRationalCycles
    reward
  intro epsilon hepsilon
  exact horbit epsilon hepsilon

end GameTheory
