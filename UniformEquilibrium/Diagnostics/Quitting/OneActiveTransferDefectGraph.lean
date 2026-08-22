/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Root.OneActiveCoalitionMass
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Quitting.Punishment.SoloQuitterEquilibrium

/-!
# The exceptional `3 + 2` graph in the one-active five-player stratum

The `K`-active compact-path interface becomes especially rigid at `K = 1`.
Every positive opponent-coalition atom is then either the empty coalition or
a singleton.  Thus a fixed nonempty polarity atom uses one defect player and
one opponent partner, while reset transport supplies a directed path of debt
owners and recipients.

This module isolates the resulting finite graph.  If a consecutive two-edge
window together with the fixed defect edge ever omits a player, it has four
roles.  If no such window omits a player in a five-player game, the transfer
path is forced to have period three.  The only exceptional support pattern is
therefore a directed three-cycle together with a disjoint fixed edge.

This is a structural reduction, not yet a cardinal reduction for games.  A
game-facing application must still produce one compatible one-active reset
chronology carrying the same positive polarity atom and must then consume the
four-role window or the exceptional `3 + 2` pattern without changing the
fixed reward table.
-/

noncomputable section

namespace GameTheory

open Finset Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## A fixed tight defect edge prices the singleton clock -/

/-- Against a solo-quitter row, a singleton-tight inactive player sees
exactly `hazard * insertion surplus`.  The constant term vanishes. -/
theorem quittingRootEndpointDifference_solo_eq_hazard_mul_toggle_of_tight
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (htight : quittingSoloReward reward other other =
      quittingSoloReward reward owner other) :
    quittingRootEndpointDifference reward (quittingSoloReward reward owner)
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) := by
  rw [quittingRootEndpointDifference_soloStationaryRoot_other
    reward hne, htight]
  have hsum := quittingSoloHazardMass_add hazard
  calc
    (hazard false).toReal * quittingSoloReward reward owner other +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other =
      ((hazard false).toReal + (hazard true).toReal - 1) *
          quittingSoloReward reward owner other +
        (hazard true).toReal *
          (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward owner other) := by ring
    _ = (hazard true).toReal *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) := by rw [hsum]; ring

/-- Therefore endpoint-Nash error pays for the product of the active
singleton clock and the tight player's insertion surplus. -/
theorem tightInsertionToggle_mul_hazard_le_endpointNashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (htight : quittingSoloReward reward other other =
      quittingSoloReward reward owner other)
    {epsilon : ℝ}
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) epsilon
        (quittingSoloStationaryRoot owner hazard)) :
    (hazard true).toReal *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) ≤ epsilon := by
  have hother := (hnash other).1
  rw [quittingSoloStationaryRoot_apply_other hne] at hother
  rw [quittingRootEndpointDifference_solo_eq_hazard_mul_toggle_of_tight
    reward hne hazard htight] at hother
  simpa using hother

/-- Quantitative persistent-versus-diffuse split.  If both the clock and the
strict insertion surplus have fixed positive floors, the Nash error has the
corresponding fixed product floor.  Hence a vanishing-error exceptional
`3 + 2` chronology cannot retain both floors. -/
theorem clockFloor_mul_toggleFloor_le_endpointNashError
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (htight : quittingSoloReward reward other other =
      quittingSoloReward reward owner other)
    {eta gamma epsilon : ℝ}
    (hclock : eta ≤ (hazard true).toReal)
    (hgamma : gamma ≤
      quittingSingletonCollisionReward reward owner other -
        quittingSoloReward reward owner other)
    (hgamma0 : 0 ≤ gamma)
    (hnash : IsεQuittingRootEndpointNash reward
      (quittingSoloReward reward owner) epsilon
        (quittingSoloStationaryRoot owner hazard)) :
    eta * gamma ≤ epsilon := by
  calc
    eta * gamma ≤ (hazard true).toReal * gamma :=
      mul_le_mul_of_nonneg_right hclock hgamma0
    _ ≤ (hazard true).toReal *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other) :=
      mul_le_mul_of_nonneg_left hgamma ENNReal.toReal_nonneg
    _ ≤ epsilon :=
      tightInsertionToggle_mul_hazard_le_endpointNashError
        reward hne hazard htight hnash

/-! ## Directed transfer path plus a fixed defect edge -/

/-- The five labels visible in two consecutive transfer edges and one fixed
nonempty polarity atom.  The middle transfer vertex is shared. -/
def quittingTransferDefectRoleWindow
    (firstOwner sharedRecipient secondRecipient defectPlayer defectPartner :
      Fin 5) : Finset (Fin 5) :=
  {firstOwner, sharedRecipient, secondRecipient, defectPlayer, defectPartner}

/-- The three consecutive transfer vertices in a two-edge window. -/
def quittingTransferTriple (path : ℕ → Fin 5) (time : ℕ) : Finset (Fin 5) :=
  {path time, path (time + 1), path (time + 2)}

/-- The two labels of a fixed nonempty polarity atom. -/
def quittingDefectEdge
    (defectPlayer defectPartner : Fin 5) : Finset (Fin 5) :=
  {defectPlayer, defectPartner}

/-- Four explicitly listed labels have cardinality at most four. -/
private theorem fourRoleSet_card_le_four
    (a b c d : Fin 5) : ({a, b, c, d} : Finset (Fin 5)).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b, c, d} : Finset (Fin 5))
  have h2 := Finset.card_insert_le b ({c, d} : Finset (Fin 5))
  have h3 := Finset.card_insert_le c ({d} : Finset (Fin 5))
  simp only [Finset.card_singleton] at h3
  omega

/-- If two overlapping five-role windows are both full, their new transfer
vertex must equal the vertex dropped from the preceding window. -/
theorem next_eq_first_of_consecutive_transferDefect_windows_full
    (a b c d defectPlayer defectPartner : Fin 5)
    (hfirst : quittingTransferDefectRoleWindow
      a b c defectPlayer defectPartner = Finset.univ)
    (hsecond : quittingTransferDefectRoleWindow
      b c d defectPlayer defectPartner = Finset.univ) :
    d = a := by
  let oldFour : Finset (Fin 5) := {b, c, defectPlayer, defectPartner}
  have haNot : a ∉ oldFour := by
    intro ha
    have heq : quittingTransferDefectRoleWindow
        a b c defectPlayer defectPartner = oldFour := by
      ext player
      simp only [quittingTransferDefectRoleWindow, oldFour,
        Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hfull : oldFour = Finset.univ := heq.symm.trans hfirst
    have hcard : oldFour.card ≤ 4 := by
      exact fourRoleSet_card_le_four b c defectPlayer defectPartner
    have : oldFour.card = 5 := by
      rw [hfull, Finset.card_univ]
      norm_num
    omega
  have haSecond : a ∈ quittingTransferDefectRoleWindow
      b c d defectPlayer defectPartner := by
    rw [hsecond]
    simp
  have hab : a ≠ b := by
    intro h
    apply haNot
    simp [oldFour, h]
  have hac : a ≠ c := by
    intro h
    apply haNot
    simp [oldFour, h]
  have haw : a ≠ defectPlayer := by
    intro h
    apply haNot
    simp [oldFour, h]
  have haj : a ≠ defectPartner := by
    intro h
    apply haNot
    simp [oldFour, h]
  simp only [quittingTransferDefectRoleWindow, Finset.mem_insert,
    Finset.mem_singleton] at haSecond
  rcases haSecond with h | h | h | h | h
  · exact False.elim (hab h)
  · exact False.elim (hac h)
  · exact h.symm
  · exact False.elim (haw h)
  · exact False.elim (haj h)

/-- If every two-edge/fixed-edge window uses all five players, the transfer
path is exactly period three. -/
theorem transferPath_periodThree_of_all_defect_windows_full
    (path : ℕ → Fin 5) (defectPlayer defectPartner : Fin 5)
    (hfull : ∀ time,
      quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          defectPlayer defectPartner = Finset.univ) :
    ∀ time, path (time + 3) = path time := by
  intro time
  have h := next_eq_first_of_consecutive_transferDefect_windows_full
    (path time) (path (time + 1)) (path (time + 2)) (path (time + 3))
      defectPlayer defectPartner (hfull time) (hfull (time + 1))
  exact h

/-- A full five-role window is not merely a covering: the transfer triple
and fixed defect edge are disjoint, have cardinalities three and two, and
partition the player set. -/
theorem transferTriple_defectEdge_partition_of_window_full
    (path : ℕ → Fin 5) (defectPlayer defectPartner : Fin 5) (time : ℕ)
    (hfull : quittingTransferDefectRoleWindow
      (path time) (path (time + 1)) (path (time + 2))
        defectPlayer defectPartner = Finset.univ) :
    Disjoint (quittingTransferTriple path time)
        (quittingDefectEdge defectPlayer defectPartner) ∧
      (quittingTransferTriple path time).card = 3 ∧
      (quittingDefectEdge defectPlayer defectPartner).card = 2 ∧
      quittingTransferTriple path time ∪
        quittingDefectEdge defectPlayer defectPartner = Finset.univ := by
  let triple := quittingTransferTriple path time
  let edge := quittingDefectEdge defectPlayer defectPartner
  have hunion : triple ∪ edge = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro player
    have hmem : player ∈ quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          defectPlayer defectPartner := by
      rw [hfull]
      simp
    simp only [triple, edge, quittingTransferTriple, quittingDefectEdge,
      quittingTransferDefectRoleWindow, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hmem ⊢
    aesop
  have hunionCard : (triple ∪ edge).card = 5 := by
    rw [hunion, Finset.card_univ]
    norm_num
  have htripleLe : triple.card ≤ 3 := by
    dsimp only [triple, quittingTransferTriple]
    have h1 := Finset.card_insert_le (path time)
      ({path (time + 1), path (time + 2)} : Finset (Fin 5))
    have h2 := Finset.card_insert_le (path (time + 1))
      ({path (time + 2)} : Finset (Fin 5))
    simp only [Finset.card_singleton] at h2
    omega
  have hedgeLe : edge.card ≤ 2 := by
    dsimp only [edge, quittingDefectEdge]
    have h := Finset.card_insert_le defectPlayer
      ({defectPartner} : Finset (Fin 5))
    simpa only [Finset.card_singleton, Nat.reduceAdd] using h
  have hlower : 5 ≤ triple.card + edge.card := by
    have h := Finset.card_union_le triple edge
    omega
  have hsum : triple.card + edge.card = 5 := by omega
  have htriple : triple.card = 3 := by omega
  have hedge : edge.card = 2 := by omega
  have hinterCard : (triple ∩ edge).card = 0 := by
    have h := Finset.card_union_add_card_inter triple edge
    omega
  have hdisjoint : Disjoint triple edge := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hinterCard
  exact ⟨hdisjoint, htriple, hedge, hunion⟩

/-- Exact five-player dichotomy: either one consecutive transfer window plus
the fixed defect edge omits a player, or the transfer chronology is forced
onto the exceptional period-three orbit. -/
theorem exists_fourRoleTransferDefectWindow_or_periodThree
    (path : ℕ → Fin 5) (defectPlayer defectPartner : Fin 5) :
    (∃ time omitted,
        omitted ∉ quittingTransferDefectRoleWindow
          (path time) (path (time + 1)) (path (time + 2))
            defectPlayer defectPartner) ∨
      ∀ time, path (time + 3) = path time := by
  by_cases hfull : ∀ time,
      quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          defectPlayer defectPartner = Finset.univ
  · exact Or.inr
      (transferPath_periodThree_of_all_defect_windows_full
        path defectPlayer defectPartner hfull)
  · left
    push Not at hfull
    obtain ⟨time, hproper⟩ := hfull
    have homitted : ∃ omitted,
        omitted ∉ quittingTransferDefectRoleWindow
          (path time) (path (time + 1)) (path (time + 2))
            defectPlayer defectPartner := by
      by_contra hnone
      push Not at hnone
      exact hproper (Finset.eq_univ_iff_forall.mpr hnone)
    exact ⟨time, homitted⟩

/-- Strong exceptional normal form.  Failure of a four-role window forces,
at every time, the same literal `3 + 2` partition as well as period three. -/
theorem exists_fourRoleTransferDefectWindow_or_threeCycle_disjointEdge
    (path : ℕ → Fin 5) (defectPlayer defectPartner : Fin 5) :
    (∃ time omitted,
        omitted ∉ quittingTransferDefectRoleWindow
          (path time) (path (time + 1)) (path (time + 2))
            defectPlayer defectPartner) ∨
      ((∀ time, path (time + 3) = path time) ∧
        ∀ time,
          Disjoint (quittingTransferTriple path time)
              (quittingDefectEdge defectPlayer defectPartner) ∧
            (quittingTransferTriple path time).card = 3 ∧
            (quittingDefectEdge defectPlayer defectPartner).card = 2 ∧
            quittingTransferTriple path time ∪
              quittingDefectEdge defectPlayer defectPartner = Finset.univ) := by
  by_cases hfull : ∀ time,
      quittingTransferDefectRoleWindow
        (path time) (path (time + 1)) (path (time + 2))
          defectPlayer defectPartner = Finset.univ
  · right
    exact ⟨transferPath_periodThree_of_all_defect_windows_full
        path defectPlayer defectPartner hfull,
      fun time => transferTriple_defectEdge_partition_of_window_full
        path defectPlayer defectPartner time (hfull time)⟩
  · left
    push Not at hfull
    obtain ⟨time, hproper⟩ := hfull
    have homitted : ∃ omitted,
        omitted ∉ quittingTransferDefectRoleWindow
          (path time) (path (time + 1)) (path (time + 2))
            defectPlayer defectPartner := by
      by_contra hnone
      push Not at hnone
      exact hproper (Finset.eq_univ_iff_forall.mpr hnone)
    exact ⟨time, homitted⟩

/-! ## Regression fence -/

/-- The canonical period-three transfer orbit inside `Fin 5`. -/
def periodThreeTransferPath (time : ℕ) : Fin 5 :=
  if time % 3 = 0 then 0 else if time % 3 = 1 then 1 else 2

/-- The exceptional branch is real at the level of finite graph geometry:
the period-three transfer orbit `0 → 1 → 2 → 0` and the fixed defect edge
`3 -- 4` make every window full. -/
theorem periodThree_plus_disjointEdge_full_regression (time : ℕ) :
    quittingTransferDefectRoleWindow
      (periodThreeTransferPath time)
      (periodThreeTransferPath (time + 1))
      (periodThreeTransferPath (time + 2))
      (3 : Fin 5) (4 : Fin 5) = Finset.univ := by
  have hmod : time % 3 < 3 := Nat.mod_lt time (by norm_num)
  have hcases : time % 3 = 0 ∨ time % 3 = 1 ∨ time % 3 = 2 := by omega
  rcases hcases with htime | htime | htime
  all_goals
    have hnext : (time + 1) % 3 = (time % 3 + 1) % 3 := by omega
    have hnextNext : (time + 2) % 3 = (time % 3 + 2) % 3 := by omega
    ext player
    fin_cases player <;>
      simp [quittingTransferDefectRoleWindow, periodThreeTransferPath,
        htime, hnext, hnextNext]

end GameTheory
