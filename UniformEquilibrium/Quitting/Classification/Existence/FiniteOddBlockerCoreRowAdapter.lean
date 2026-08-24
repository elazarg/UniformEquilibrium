/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import Mathlib.GroupTheory.Perm.Fin
import UniformEquilibrium.Quitting.Classification.Existence.FiniteOddBlockerCore
import UniformEquilibrium.Quitting.Classification.Existence.OddBlockerCoreRowAdapter

/-!
# Literal row adapter for arbitrary finite odd blocker cores

The source below checks only payoff coordinates belonging to an embedded
`Fin n` core.  A core owner receives its baseline on every nonempty terminal
coalition that omits it.  Its Quit reward is strictly above the baseline when
the next cyclic core player is absent and strictly below it when that blocker
is present.  All outside payoff coordinates remain unrestricted.
-/

noncomputable section

namespace GameTheory

open Equiv Math Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Literal finite reward-table conditions for a strictly switching embedded
odd blocker cycle.  The `three_le` field supplies both the positive-opponent
condition and fixed-point-freeness; no ambient `Nonempty` instance is needed. -/
structure IsLiteralStrictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι) : Prop where
  three_le : 3 ≤ n
  odd_card : Odd n
  passive : ∀ (phase : Fin n)
    (S : {S : Finset ι // S.Nonempty}),
    core phase ∉ S.1 → reward S (core phase) = baseline (core phase)
  switch : ∀ (phase : Fin n) (background : Finset ι),
    core phase ∉ background →
    core (finRotate n phase) ∉ background →
      baseline (core phase) <
          reward ⟨insert (core phase) background,
            Finset.insert_nonempty _ _⟩ (core phase) ∧
        reward ⟨insert (core (finRotate n phase))
            (insert (core phase) background),
          Finset.insert_nonempty _ _⟩ (core phase) <
          baseline (core phase)

omit [Fintype ι] [DecidableEq ι] in
/-- A cyclic successor in a core of size at least three is distinct from its
owner after applying the core embedding. -/
theorem finiteOddBlocker_ne
    {n : ℕ} (hn : 3 ≤ n) (core : Fin n ↪ ι) (phase : Fin n) :
    core (finRotate n phase) ≠ core phase := by
  apply core.injective.ne
  have hmem : phase ∈ (finRotate n).support := by
    rw [support_finRotate_of_le (by omega)]
    simp
  exact Equiv.Perm.mem_support.mp hmem

/-- The literal finite row check supplies the polynomial stationary-face
source for the arbitrary finite odd-core compact construction. -/
theorem IsLiteralStrictFiniteOddBlockerCore.toStationaryFace
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {baseline : Payoff ι} {n : ℕ} {core : Fin n ↪ ι}
    (hcore : IsLiteralStrictFiniteOddBlockerCore
      reward baseline n core) :
    IsStrictFiniteOddBlockerCore reward baseline n core where
  three_le := hcore.three_le
  odd_card := hcore.odd_card
  passive := by
    intro phase hazard _ _
    exact excludedValue_eq_baseline_of_passive_rows (core phase)
      (hcore.passive phase) hazard
  lower := by
    intro phase hazard h0 h1 hface
    exact baseline_lt_sigmaValue_of_strictBlockerAbsentRows
      (finiteOddBlocker_ne hcore.three_le core phase)
      (fun background howner hblocker =>
        (hcore.switch phase background howner hblocker).1)
      hazard h0 h1 hface
  upper := by
    intro phase hazard h0 h1 hface
    exact sigmaValue_lt_baseline_of_strictBlockerPresentRows
      (finiteOddBlocker_ne hcore.three_le core phase)
      (fun background howner hblocker =>
        (hcore.switch phase background howner hblocker).2)
      hazard h0 h1 hface

/-- Literal odd-cycle rows produce a stationary exact terminal Nash
certificate with interior hazards on the entire core. -/
theorem exists_stationaryCertificate_of_literalStrictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsLiteralStrictFiniteOddBlockerCore
      reward baseline n core) :
    Nonempty (FiniteOddBlockerCoreStationaryCertificate
      reward baseline n core) :=
  exists_stationaryCertificate_of_strictFiniteOddBlockerCore
    reward baseline n core hcore.toStationaryFace

/-- Headline all-behavior uniform-payoff consequence of the literal finite
odd-cycle row conditions. -/
theorem isUniformEquilibriumPayoff_of_literalStrictFiniteOddBlockerCore
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (baseline : Payoff ι) (n : ℕ) (core : Fin n ↪ ι)
    (hcore : IsLiteralStrictFiniteOddBlockerCore
      reward baseline n core) :
    ∃ value : Payoff ι,
      (∀ phase, value (core phase) = baseline (core phase)) ∧
        (quittingGame reward).IsUniformEquilibriumPayoff none value :=
  isUniformEquilibriumPayoff_of_strictFiniteOddBlockerCore
    reward baseline n core hcore.toStationaryFace

end GameTheory
