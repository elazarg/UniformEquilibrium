/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegime.Toggles
import UniformEquilibrium.Quitting.Stationary.TogglePotential

/-!
# Counterexample consequences of finite toggle instability

The production toggle API packages the exact coalition toggle, its finite
exploitability ceilings, the analogous stationary cap ceiling, and the
ordinal-potential sufficient condition.  This module records only what a
quitting counterexample regime forces against those generic objects.

It also chooses one improving toggle at every coalition and extracts a closed
walk in the finite coalition cube.  That walk is a static recurrence witness,
not a quitting-game chronology or Bellman cycle.
-/

noncomputable section

namespace GameTheory

open Set
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

namespace QuittingCounterexampleRegime

/-- The terminal gap is realized by an exact membership toggle at every
coalition. -/
theorem exists_exactToggle_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    ∃ who, quittingSetReward reward S who + regime.terminalGap ≤
      quittingSetReward reward (quittingToggleCoalition S who) who := by
  rcases regime.exists_leave_or_join_gain S with hleave | hjoin
  · obtain ⟨who, hmem, hgain⟩ := hleave
    exact ⟨who, by simpa [quittingToggleCoalition_of_mem hmem] using hgain⟩
  · obtain ⟨who, hnot, hgain⟩ := hjoin
    exact ⟨who, by simpa [quittingToggleCoalition_of_notMem hnot] using hgain⟩

/-- Pointwise pure-toggle exploitability dominates the regime margin. -/
theorem terminalGap_le_pureToggleExploitability
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    regime.terminalGap ≤ @quittingPureToggleExploitability ι _ _
      regime.nonempty_players reward S := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨who, hgain⟩ := regime.exists_exactToggle_gain S
  unfold quittingPureToggleExploitability quittingPureToggleGain
  exact (by linarith : regime.terminalGap ≤
      quittingSetReward reward (quittingToggleCoalition S who) who -
        quittingSetReward reward S who) |>.trans
    (Finset.le_sup' (quittingPureToggleGain reward S)
      (Finset.mem_univ who))

/-- **Computable pure-toggle ceiling.**  Every counterexample terminal margin
is below the minimum, over all coalitions, of their best membership-toggle
gain. -/
theorem terminalGap_le_pureToggleCeiling
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ @quittingPureToggleCeiling ι _ _
      regime.nonempty_players reward := by
  letI : Nonempty ι := regime.nonempty_players
  unfold quittingPureToggleCeiling
  rw [Finset.le_inf'_iff]
  exact fun S _ => regime.terminalGap_le_pureToggleExploitability S

/-! ## A finite closed improvement orbit -/

/-- A chosen player witnessing the exact toggle gain at a coalition. -/
noncomputable def improvingTogglePlayer
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) : ι :=
  Classical.choose (regime.exists_exactToggle_gain S)

/-- The chosen outgoing neighbor in the coalition improvement graph. -/
noncomputable def improvingToggleNext
    (regime : QuittingCounterexampleRegime reward)
    (S : Finset ι) : Finset ι :=
  quittingToggleCoalition S (regime.improvingTogglePlayer S)

theorem improvingToggleNext_gain
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    quittingSetReward reward S (regime.improvingTogglePlayer S) +
        regime.terminalGap ≤
      quittingSetReward reward (regime.improvingToggleNext S)
        (regime.improvingTogglePlayer S) := by
  exact Classical.choose_spec (regime.exists_exactToggle_gain S)

theorem improvingToggleNext_ne
    (regime : QuittingCounterexampleRegime reward) (S : Finset ι) :
    regime.improvingToggleNext S ≠ S :=
  quittingToggleCoalition_ne S (regime.improvingTogglePlayer S)

/-- The chosen finite improvement graph has a closed directed walk whose
length is a positive multiple of four.  Every edge carries a payoff gain of
at least the terminal margin, though the gaining player may change from edge
to edge.  This is a finite recurrence witness, not a telescoping payoff
contradiction. -/
theorem exists_closedImprovementWalk_multiple_four
    (regime : QuittingCounterexampleRegime reward) :
    ∃ start stop : ℕ, start < stop ∧ 4 ∣ stop - start ∧
      let next := regime.improvingToggleNext
      (next^[start]) ∅ = (next^[stop]) ∅ ∧
      ∀ time,
        quittingSetReward reward ((next^[time]) ∅)
              (regime.improvingTogglePlayer ((next^[time]) ∅)) +
            regime.terminalGap ≤
          quittingSetReward reward ((next^[time + 1]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) := by
  let next := regime.improvingToggleNext
  obtain ⟨first, second, hne, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun block : ℕ => (next^[4 * block]) (∅ : Finset ι))
  have hedge : ∀ time,
      quittingSetReward reward ((next^[time]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) +
          regime.terminalGap ≤
        quittingSetReward reward ((next^[time + 1]) ∅)
          (regime.improvingTogglePlayer ((next^[time]) ∅)) := by
    intro time
    have hgain := regime.improvingToggleNext_gain ((next^[time]) ∅)
    change quittingSetReward reward ((next^[time]) ∅)
            (regime.improvingTogglePlayer ((next^[time]) ∅)) +
          regime.terminalGap ≤
        quittingSetReward reward (next ((next^[time]) ∅))
          (regime.improvingTogglePlayer ((next^[time]) ∅)) at hgain
    simpa only [Function.iterate_succ_apply'] using hgain
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨4 * first, 4 * second, by omega, ?_, heq, hedge⟩
    exact ⟨second - first, by omega⟩
  · refine ⟨4 * second, 4 * first, by omega, ?_, heq.symm, hedge⟩
    exact ⟨first - second, by omega⟩

end QuittingCounterexampleRegime

namespace QuittingCounterexampleRegime

/-- Pointwise stationary-cap exploitability dominates the regime margin. -/
theorem terminalGap_le_stationaryCapExploitability
    (regime : QuittingCounterexampleRegime reward)
    (root : ι → PMF Bool) :
    regime.terminalGap ≤ @quittingStationaryCapExploitability ι _ _
      regime.nonempty_players reward root := by
  letI : Nonempty ι := regime.nonempty_players
  obtain ⟨who, hgain⟩ := regime.exists_stationaryCap_gain root
  unfold quittingStationaryCapExploitability
  exact (by linarith : regime.terminalGap ≤
      quittingStationaryUnilateralCap reward root who -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who) |>.trans
    (Finset.le_sup'
      (fun who => quittingStationaryUnilateralCap reward root who -
        quittingTerminalPayoff reward
          (quittingStationaryProfile reward root) who)
      (Finset.mem_univ who))

/-- **Stationary-cap infimum ceiling.**  The regime margin lies below the
infimum of stationary selected-cap exploitability. -/
theorem terminalGap_le_stationaryCapCeiling
    (regime : QuittingCounterexampleRegime reward) :
    regime.terminalGap ≤ @quittingStationaryCapCeiling ι _ _
      regime.nonempty_players reward := by
  letI : Nonempty ι := regime.nonempty_players
  unfold quittingStationaryCapCeiling
  have hnonempty :
      (Set.range (quittingStationaryCapExploitability reward)).Nonempty :=
    ⟨quittingStationaryCapExploitability reward
        quittingAllContinueRoot,
      ⟨quittingAllContinueRoot, rfl⟩⟩
  have hbounded :
      BddBelow (Set.range (quittingStationaryCapExploitability reward)) :=
    ⟨regime.terminalGap, by
      rintro _ ⟨root, rfl⟩
      exact regime.terminalGap_le_stationaryCapExploitability root⟩
  rw [le_csInf_iff hbounded hnonempty]
  rintro _ ⟨root, rfl⟩
  exact regime.terminalGap_le_stationaryCapExploitability root

end QuittingCounterexampleRegime

end GameTheory
