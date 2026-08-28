/-
Copyright (c) 2026 UniformEquilibrium contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: UniformEquilibrium contributors
-/

import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorInfiniteOrbitChargeDichotomy
import UniformEquilibrium.Quitting.Stationary.ReturnedBlockTangentObstruction

/-!
# A fixed signed terminal label in a nontrivial summable port

The displacement of a summable exact floor orbit is the absolutely convergent
sum of its coalition-labelled Bellman increments.  A finite pigeonhole
argument therefore selects one player, one sign, and one fixed nonempty
terminal coalition carrying a quantitative share of every nonzero limiting
displacement.
-/

noncomputable section

namespace GameTheory

open Filter Math.PMFProduct Math.Probability

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingPunishmentFloorInfiniteOrbit

/-- The positive signed contribution of one terminal coalition at one orbit
stage. -/
def signedTerminalContribution
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : iota) (sign : ℝ) (time : ℕ) (terminal : Finset iota) : ℝ :=
  quittingRootCoalitionMass (orbit.roots time) terminal *
    max (sign *
      (quittingProjectiveCoalitionReward reward terminal who -
        orbit.value time who)) 0

/-- Exact coalition decomposition of one Bellman increment. -/
theorem value_succ_sub_eq_sum_coalitionIncrement
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (time : ℕ) (who : iota) :
    orbit.value (time + 1) who - orbit.value time who =
      ∑ terminal ∈ Finset.univ.erase (∅ : Finset iota),
        quittingRootCoalitionMass (orbit.roots time) terminal *
          (quittingProjectiveCoalitionReward reward terminal who -
            orbit.value time who) := by
  rw [orbit.policy time,
    quittingRootSuccessorPayoff_eq_smallHazardExpectation]
  unfold smallHazardExpectation quittingRootCoalitionMass
  have hterminalSum :
      (∑ terminal ∈ Finset.univ.erase (∅ : Finset iota),
        coalitionMass (quittingRootQuitRates (orbit.roots time)) terminal *
          quittingRootScalarTerminal reward who terminal) =
      ∑ terminal ∈ Finset.univ.erase (∅ : Finset iota),
        coalitionMass (quittingRootQuitRates (orbit.roots time)) terminal *
          quittingProjectiveCoalitionReward reward terminal who := by
    apply Finset.sum_congr rfl
    intro terminal hterminal
    have hnonempty : terminal.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hterminal)
    simp [quittingRootScalarTerminal,
      quittingProjectiveCoalitionReward, hnonempty]
  rw [hterminalSum]
  have hmass := sum_coalitionMass_nonempty
    (quittingRootQuitRates (orbit.roots time))
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  linear_combination (orbit.value time who) * hmass

/-- One nonempty coalition mass is bounded by the total one-stage absorption
charge. -/
theorem coalitionMass_le_absorptionMass
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (time : ℕ) (terminal : Finset iota) (hnonempty : terminal.Nonempty) :
    quittingRootCoalitionMass (orbit.roots time) terminal ≤
      quittingRootAbsorptionMass (orbit.roots time) := by
  calc
    quittingRootCoalitionMass (orbit.roots time) terminal ≤
        ∑ coalition ∈ Finset.univ.erase (∅ : Finset iota),
          quittingRootCoalitionMass (orbit.roots time) coalition := by
      apply Finset.single_le_sum
      · intro coalition _
        exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
          (orbit.roots time) coalition
      · simp [hnonempty.ne_empty]
    _ = quittingRootAbsorptionMass (orbit.roots time) := by
      simpa [quittingRootAbsorptionMass] using
        quittingRootCoalitionMass_sum_nonempty (orbit.roots time)

/-- Every signed coalition contribution is nonnegative. -/
theorem signedTerminalContribution_nonneg
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : iota) (sign : ℝ) (time : ℕ) (terminal : Finset iota) :
    0 ≤ orbit.signedTerminalContribution who sign time terminal := by
  exact mul_nonneg
    (MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      (orbit.roots time) terminal)
    (le_max_right _ _)

/-- Under a common coordinate bound, a signed terminal contribution is at
most `2M` times its coalition mass. -/
theorem signedTerminalContribution_le_two_mul_mass
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : iota) (sign : ℝ) (time : ℕ) (terminal : Finset iota)
    (hnonempty : terminal.Nonempty) {M : ℝ}
    (hsign : sign = 1 ∨ sign = -1)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hvalue : |orbit.value time who| ≤ M) :
    orbit.signedTerminalContribution who sign time terminal ≤
      2 * M * quittingRootCoalitionMass (orbit.roots time) terminal := by
  have hM := quittingRewardCoordinateBound_nonneg_of_player reward who hreward
  have hprojective :
      quittingProjectiveCoalitionReward reward terminal who =
        reward ⟨terminal, hnonempty⟩ who := by
    simp [quittingProjectiveCoalitionReward, hnonempty]
  have hterminalBound :
      |quittingProjectiveCoalitionReward reward terminal who| ≤ M := by
    rw [hprojective]
    exact hreward ⟨terminal, hnonempty⟩ who
  have hbracket : sign *
      (quittingProjectiveCoalitionReward reward terminal who -
        orbit.value time who) ≤ 2 * M := by
    rcases hsign with rfl | rfl
    · simp only [one_mul]
      exact (sub_le_iff_le_add).2 (by
        have hup := le_of_abs_le hterminalBound
        have hlow := neg_le_of_abs_le hvalue
        linarith)
    · simp only [neg_mul, one_mul]
      have hup := le_of_abs_le hvalue
      have hlow := neg_le_of_abs_le hterminalBound
      linarith
  unfold signedTerminalContribution
  calc
    quittingRootCoalitionMass (orbit.roots time) terminal *
        max (sign *
          (quittingProjectiveCoalitionReward reward terminal who -
            orbit.value time who)) 0 ≤
        quittingRootCoalitionMass (orbit.roots time) terminal * (2 * M) := by
      apply mul_le_mul_of_nonneg_left
        (max_le hbracket (by linarith))
      exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        (orbit.roots time) terminal
    _ = 2 * M * quittingRootCoalitionMass (orbit.roots time) terminal := by
      ring

/-- The sum of the positive signed pieces dominates the corresponding signed
Bellman increment. -/
theorem signed_valueIncrement_le_sum_signedTerminalContribution
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (who : iota) (sign : ℝ) (time : ℕ) :
    sign * (orbit.value (time + 1) who - orbit.value time who) ≤
      ∑ terminal ∈ Finset.univ.erase (∅ : Finset iota),
        orbit.signedTerminalContribution who sign time terminal := by
  rw [orbit.value_succ_sub_eq_sum_coalitionIncrement,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro terminal hterminal
  unfold signedTerminalContribution
  rw [show sign *
      (quittingRootCoalitionMass (orbit.roots time) terminal *
        (quittingProjectiveCoalitionReward reward terminal who -
          orbit.value time who)) =
      quittingRootCoalitionMass (orbit.roots time) terminal *
        (sign * (quittingProjectiveCoalitionReward reward terminal who -
          orbit.value time who)) by ring]
  apply mul_le_mul_of_nonneg_left (le_max_left _ _)
  exact MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
    (orbit.roots time) terminal

private theorem exists_sum_le_card_mul_of_nonempty
    {alpha : Type} (set : Finset alpha) (hset : set.Nonempty)
    (f : alpha → ℝ) :
    ∃ item ∈ set, ∑ other ∈ set, f other ≤ (set.card : ℝ) * f item := by
  classical
  let values := set.image f
  have hvalues : values.Nonempty := hset.image f
  let largest := values.max' hvalues
  obtain ⟨item, hitem, hitemValue⟩ :=
    Finset.mem_image.mp (values.max'_mem hvalues)
  refine ⟨item, hitem, ?_⟩
  rw [hitemValue]
  simpa [nsmul_eq_mul] using set.sum_le_card_nsmul f largest (by
    intro other hother
    exact Finset.le_max' values (f other) (Finset.mem_image.mpr
      ⟨other, hother, rfl⟩))

/-- A quantitative fixed signed terminal label carried by a summable orbit. -/
structure SummableChargeSignedTerminalPort
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (rho M : ℝ) where
  rho_pos : 0 < rho
  who : iota
  sign : ℝ
  sign_eq_one_or_neg_one : sign = 1 ∨ sign = -1
  terminal : Finset iota
  terminal_nonempty : terminal.Nonempty
  contribution_lower :
    rho / ((2 ^ Fintype.card iota - 1 : ℕ) : ℝ) ≤
      ∑' time, orbit.signedTerminalContribution who sign time terminal
  mass_lower :
    rho / (2 * M * ((2 ^ Fintype.card iota - 1 : ℕ) : ℝ)) ≤
      ∑' time, quittingRootCoalitionMass (orbit.roots time) terminal

/-- A nonzero displacement into a summable all-Continue port selects one
coordinate, sign, and nonempty terminal coalition with the sharp finite-label
share and its consequent probability-mass lower bound. -/
theorem nonempty_summableChargeSignedTerminalPort_of_displacement
    [Nonempty iota]
    (orbit : QuittingPunishmentFloorInfiniteOrbit reward)
    (port : orbit.SummableChargeAllContinuePort) {rho M : ℝ}
    (hrho : 0 < rho) (hM : 0 < M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hvalue : ∀ time player, |orbit.value time player| ≤ M)
    (hdisplacement : ∃ who,
      rho ≤ |port.limit who - orbit.value 0 who|) :
    Nonempty (SummableChargeSignedTerminalPort orbit rho M) := by
  obtain ⟨who, hwho⟩ := hdisplacement
  let sign : ℝ := if 0 ≤ port.limit who - orbit.value 0 who then 1 else -1
  have hsign : sign = 1 ∨ sign = -1 := by
    dsimp only [sign]
    split <;> simp
  have hsignedDisplacement :
      rho ≤ sign * (port.limit who - orbit.value 0 who) := by
    dsimp only [sign]
    split
    · simpa [abs_of_nonneg ‹0 ≤ port.limit who - orbit.value 0 who›] using
        hwho
    · have hnegative : port.limit who - orbit.value 0 who < 0 :=
        lt_of_not_ge ‹¬0 ≤ port.limit who - orbit.value 0 who›
      simpa [abs_of_neg hnegative] using hwho
  let labels : Finset (Finset iota) := Finset.univ.erase ∅
  have hlabels : labels.Nonempty := by
    obtain ⟨player⟩ := ‹Nonempty iota›
    exact ⟨{player}, by simp [labels]⟩
  have hmassSummable : ∀ terminal ∈ labels,
      Summable (fun time =>
        quittingRootCoalitionMass (orbit.roots time) terminal) := by
    intro terminal hterminal
    have hnonempty : terminal.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr
        (Finset.ne_of_mem_erase hterminal)
    exact Summable.of_nonneg_of_le
      (fun time =>
        MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
          (orbit.roots time) terminal)
      (fun time => orbit.coalitionMass_le_absorptionMass
        time terminal hnonempty)
      port.absorption_summable
  have hcontributionSummable : ∀ terminal ∈ labels,
      Summable (fun time =>
        orbit.signedTerminalContribution who sign time terminal) := by
    intro terminal hterminal
    have hnonempty : terminal.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr
        (Finset.ne_of_mem_erase hterminal)
    exact Summable.of_nonneg_of_le
      (fun time => orbit.signedTerminalContribution_nonneg
        who sign time terminal)
      (fun time => orbit.signedTerminalContribution_le_two_mul_mass
        who sign time terminal hnonempty hsign hreward
          (hvalue time who))
      ((hmassSummable terminal hterminal).mul_left (2 * M))
  let totalContribution : ℕ → ℝ := fun time =>
    ∑ terminal ∈ labels,
      orbit.signedTerminalContribution who sign time terminal
  have htotalSummable : Summable totalContribution :=
    summable_sum hcontributionSummable
  have hfinite : ∀ horizon,
      sign * (orbit.value horizon who - orbit.value 0 who) ≤
        ∑ time ∈ Finset.range horizon, totalContribution time := by
    intro horizon
    have htelescope :
        (∑ time ∈ Finset.range horizon,
          (orbit.value (time + 1) who - orbit.value time who)) =
            orbit.value horizon who - orbit.value 0 who := by
      induction horizon with
      | zero => simp
      | succ horizon ih =>
          rw [Finset.sum_range_succ, ih]
          ring
    rw [← htelescope, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro time _htime
    exact orbit.signed_valueIncrement_le_sum_signedTerminalContribution
      who sign time
  have hleft : Tendsto (fun horizon =>
      sign * (orbit.value horizon who - orbit.value 0 who)) atTop
      (nhds (sign * (port.limit who - orbit.value 0 who))) :=
    ((port.value_tendsto who).sub_const (orbit.value 0 who)).const_mul sign
  have htotalLower : rho ≤ ∑' time, totalContribution time := by
    apply hsignedDisplacement.trans
    exact le_of_tendsto_of_tendsto' hleft
      htotalSummable.hasSum.tendsto_sum_nat hfinite
  have hswap :
      (∑' time, totalContribution time) =
        ∑ terminal ∈ labels,
          ∑' time,
            orbit.signedTerminalContribution who sign time terminal := by
    exact Summable.tsum_finsetSum hcontributionSummable
  rw [hswap] at htotalLower
  obtain ⟨terminal, hterminal, haverage⟩ :=
    exists_sum_le_card_mul_of_nonempty labels hlabels
      (fun coalition => ∑' time,
        orbit.signedTerminalContribution who sign time coalition)
  have hselected : rho ≤ (labels.card : ℝ) *
      ∑' time,
        orbit.signedTerminalContribution who sign time terminal :=
    htotalLower.trans haverage
  have hcard : labels.card = 2 ^ Fintype.card iota - 1 := by
    dsimp only [labels]
    rw [Finset.card_erase_of_mem (Finset.mem_univ ∅),
      Finset.card_univ, Fintype.card_finset]
  have hcardPos : 0 < (labels.card : ℝ) := by
    exact_mod_cast hlabels.card_pos
  have hcontributionLower :
      rho / ((2 ^ Fintype.card iota - 1 : ℕ) : ℝ) ≤
        ∑' time,
          orbit.signedTerminalContribution who sign time terminal := by
    rw [← hcard]
    exact (div_le_iff₀ hcardPos).2 (by
      simpa [mul_comm] using hselected)
  have hnonempty : terminal.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hterminal)
  have hcontributionMass :
      (∑' time,
        orbit.signedTerminalContribution who sign time terminal) ≤
      2 * M * ∑' time,
        quittingRootCoalitionMass (orbit.roots time) terminal := by
    calc
      (∑' time,
          orbit.signedTerminalContribution who sign time terminal) ≤
          ∑' time, 2 * M *
            quittingRootCoalitionMass (orbit.roots time) terminal :=
        (hcontributionSummable terminal hterminal).tsum_le_tsum
          (fun time => orbit.signedTerminalContribution_le_two_mul_mass
            who sign time terminal hnonempty hsign hreward
              (hvalue time who))
          ((hmassSummable terminal hterminal).mul_left (2 * M))
      _ = 2 * M * ∑' time,
          quittingRootCoalitionMass (orbit.roots time) terminal := by
        rw [tsum_mul_left]
  have hmassProduct : rho ≤
      (labels.card : ℝ) * (2 * M) *
        ∑' time,
          quittingRootCoalitionMass (orbit.roots time) terminal := by
    calc
      rho ≤ (labels.card : ℝ) *
          ∑' time,
            orbit.signedTerminalContribution who sign time terminal :=
        hselected
      _ ≤ (labels.card : ℝ) *
          (2 * M * ∑' time,
            quittingRootCoalitionMass (orbit.roots time) terminal) :=
        mul_le_mul_of_nonneg_left hcontributionMass hcardPos.le
      _ = (labels.card : ℝ) * (2 * M) *
          ∑' time,
            quittingRootCoalitionMass (orbit.roots time) terminal := by ring
  have hdenomPos : 0 <
      2 * M * ((2 ^ Fintype.card iota - 1 : ℕ) : ℝ) := by
    rw [← hcard]
    positivity
  have hmassLower :
      rho / (2 * M * ((2 ^ Fintype.card iota - 1 : ℕ) : ℝ)) ≤
        ∑' time,
          quittingRootCoalitionMass (orbit.roots time) terminal := by
    rw [← hcard]
    apply (div_le_iff₀ (by positivity :
      0 < 2 * M * (labels.card : ℝ))).2
    nlinarith [hmassProduct]
  exact ⟨{
    rho_pos := hrho
    who := who
    sign := sign
    sign_eq_one_or_neg_one := hsign
    terminal := terminal
    terminal_nonempty := hnonempty
    contribution_lower := hcontributionLower
    mass_lower := hmassLower }⟩

end QuittingPunishmentFloorInfiniteOrbit

end GameTheory
