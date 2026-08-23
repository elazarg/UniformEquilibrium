/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Debt.Quantitative
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorPrefixBridge

/-!
# Counterexample consequences of the exact-debt prefix bridge

The production bridge reverses any floor-anchorable exact-debt segment into
an exact punishment-floor prefix. A terminal exploitability witness then bounds the
segment by its canonical prefix capacity. Cofinal floor-dominating endpoints
therefore force summable absorption, leaving eventual floor violation as the
only alternative.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingTerminalExploitabilityWitness

/-- Every floor-anchorable exact-debt segment inherits the regime's common
prefix-charge bound. -/
theorem dynamicDebtTail_sum_absorptionCharge_le_of_endpoint_floor
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (horizon : ℕ)
    (hfloor : ∀ who,
      quittingPunishmentValue reward who ≤ (tail horizon).1.1 who) :
    (∑ time ∈ Finset.range horizon,
        quittingDynamicDebtTailAbsorptionCharge tail time) ≤
      quittingPunishmentFloorPrefixChargeBound reward := by
  let cert := quittingDynamicDebtSegmentToPunishmentFloorPrefix tail horizon
    (fun time _ ↦ hbox time) (fun time _ ↦ hedge time) hfloor
  rw [← quittingDynamicDebtSegmentToPunishmentFloorPrefix_charge tail horizon
    (fun time _ ↦ hbox time) (fun time _ ↦ hedge time) hfloor]
  exact witness.prefixCharge_le cert

/-- **Tail/prefix bridge.**  If the positive exact-debt tail returns
cofinally to the coordinatewise punishment-floor region, then its full joint
absorption charge is summable.  Thus any nonsummable counterexample tail must
eventually avoid that region at every date. -/
theorem summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1)))
    (hcofinal : HasCofinalQuittingPunishmentFloorEndpoints reward tail) :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail) := by
  apply summable_of_sum_range_le
    (c := quittingPunishmentFloorPrefixChargeBound reward)
    (quittingDynamicDebtTailAbsorptionCharge_nonneg tail)
  intro cutoff
  obtain ⟨horizon, hcutoff, hfloor⟩ := hcofinal cutoff
  calc
    (∑ time ∈ Finset.range cutoff,
        quittingDynamicDebtTailAbsorptionCharge tail time) ≤
        ∑ time ∈ Finset.range horizon,
          quittingDynamicDebtTailAbsorptionCharge tail time := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono hcutoff
      · intro time _ _
        exact quittingDynamicDebtTailAbsorptionCharge_nonneg tail time
    _ ≤ quittingPunishmentFloorPrefixChargeBound reward :=
      witness.dynamicDebtTail_sum_absorptionCharge_le_of_endpoint_floor
        tail hbox hedge horizon hfloor

/-- Every boxed exact-debt tail in a terminal exploitability witness satisfies a sharp
carrier alternative: either its joint absorption is summable, or from some
date onward every endpoint violates the punishment floor in at least one
coordinate.  The violating player may depend on the date. -/
theorem summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
    (witness : QuittingTerminalExploitabilityWitness reward)
    (tail : ℕ → QuittingDebtPoint ι)
    (hbox : ∀ time, tail time ∈ quittingDebtBox reward)
    (hedge : ∀ time,
      IsQuittingDynamicDebtEdge reward (tail time) (tail (time + 1))) :
    Summable (quittingDynamicDebtTailAbsorptionCharge tail) ∨
      ∃ start, ∀ horizon, start ≤ horizon →
        ∃ who, (tail horizon).1.1 who <
          quittingPunishmentValue reward who := by
  by_cases hcofinal :
      HasCofinalQuittingPunishmentFloorEndpoints reward tail
  · exact Or.inl
      (witness.summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
        tail hbox hedge hcofinal)
  · right
    unfold HasCofinalQuittingPunishmentFloorEndpoints at hcofinal
    push Not at hcofinal
    exact hcofinal

/-- The projectively extracted positive-debt obstruction can be chosen with
the carrier alternative above attached.  Thus a counterexample's optimized
tail has a positive debt owner and either globally summable absorption, or
an eventual coordinatewise failure of individual rationality at every
date. -/
theorem exists_positiveDynamicDebtTail_with_absorptionAlternative
    (witness : QuittingTerminalExploitabilityWitness reward) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail
          ι _ _ witness.nonempty_players reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      witness.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      (Summable (quittingDynamicDebtTailAbsorptionCharge limit) ∨
        ∃ start, ∀ horizon, start ≤ horizon →
          ∃ player, (limit horizon).1.1 player <
            quittingPunishmentValue reward player) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge,
      hdebt, hclock⟩ := witness.exists_terminalGapDynamicDebtTail
  have halternative :=
    witness.summable_dynamicDebtTailAbsorptionCharge_or_eventually_floorViolation
      limit hbox hedge
  exact ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock,
    halternative⟩

/-- **Nonpositive-punishment counterexample normal form.**  When the
behavioral punishment vector is coordinatewise nonpositive, the optimized
projective tail inherits individual rationality from its zero-boundary finite
approximants.  The tail/prefix bridge then upgrades the owner's summable
opponent clock to summability of the full joint absorption charge, while
retaining the quantitative terminal-gap lower bound on initial debt. -/
theorem exists_terminalGapDynamicDebtTail_with_summableAbsorption_of_nonpos
    (witness : QuittingTerminalExploitabilityWitness reward)
    (hpunishment : ∀ who, quittingPunishmentValue reward who ≤ 0) :
    ∃ (limit : ℕ → QuittingDebtPoint ι) (subseq : ℕ → ℕ) (who : ι),
      StrictMono subseq ∧
      Tendsto
        ((fun cutoff ↦ @quittingFiniteMinMaxDynamicDebtTail
          ι _ _ witness.nonempty_players reward cutoff) ∘
          subseq) atTop (nhds limit) ∧
      (∀ time, limit time ∈ quittingDebtBox reward) ∧
      (∀ time, IsQuittingDynamicDebtEdge reward
        (limit time) (limit (time + 1))) ∧
      witness.terminalGap ≤ (limit 0).2 who ∧
      Summable (quittingOpponentClockCharge
        (quittingDynamicDebtTailRoots limit) who) ∧
      (∀ time player, quittingPunishmentValue reward player ≤
        (limit time).1.1 player) ∧
      Summable (quittingDynamicDebtTailAbsorptionCharge limit) := by
  letI : Nonempty ι := witness.nonempty_players
  obtain ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge,
      hdebt, hclock⟩ := witness.exists_terminalGapDynamicDebtTail
  have hfloor : ∀ time player, quittingPunishmentValue reward player ≤
      (limit time).1.1 player := by
    intro time player
    exact quittingPunishmentValue_le_projectiveDynamicDebtTail_of_nonpos
      reward hpunishment subseq limit hlimit time player
  have hcofinal :
      HasCofinalQuittingPunishmentFloorEndpoints reward limit := by
    intro start
    exact ⟨start, le_rfl, hfloor start⟩
  have hsummable :=
    witness.summable_dynamicDebtTailAbsorptionCharge_of_cofinal_floor
      limit hbox hedge hcofinal
  exact ⟨limit, subseq, who, hsubseq, hlimit, hbox, hedge, hdebt, hclock,
    hfloor, hsummable⟩

end QuittingTerminalExploitabilityWitness

end GameTheory
