/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors.
-/

import Research.Quitting.ConcentratedCollisionThreeRoleEndpointLaw

/-!
# Normalized return from a fixed-pair minimum-tail family

This module factors the compact selection and normalized-passport consumer
away from any particular Fin4 producer.  The input is one literal decorated
family with uniform positive marked-mass and gain floors whose tail debt tends
to a displayed positive global minimum.  It produces its own compact
subsequence, passport, slice minimizer, and actual minimum-return endpoint law.

The selected point belongs to the enlarged arbitrary-prefix slice, not
necessarily to the original family cluster.  The strict arm is an inert
normalized-slice obstruction, not a uniform equilibrium.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}
variable {family : QuittingMarkedPairDecoratedFamily reward}
variable {minimum : QuittingTerminalSemanticPair iota}

/-- Source-independent quantitative data sufficient to compactify one fixed
decorated family on a positive global minimum tail fibre. -/
structure QuittingMarkedPairMinimumTailSource
    (family : QuittingMarkedPairDecoratedFamily reward)
    (minimum : QuittingTerminalSemanticPair iota) where
  minimum_mem : minimum ∈ quittingTerminalSemanticCarrier reward
  minimum_global : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
    quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum candidate
  minimum_pos : 0 < quittingTerminalSemanticDebtSum minimum
  markedMassFloor : ℝ
  markedMassFloor_pos : 0 < markedMassFloor
  markedMass_floor : ∀ rank,
    markedMassFloor ≤ (family.baseDecoration rank).markedMass
  actualGainFloor : ℝ
  actualGainFloor_pos : 0 < actualGainFloor
  actualGain_floor : ∀ rank,
    actualGainFloor ≤ (family.baseDecoration rank).actualGain
  tailDebt_tendsto : Tendsto
    (fun rank ↦ (family.baseDecoration rank).tailDebt) atTop
      (nhds (quittingTerminalSemanticDebtSum minimum))

/-- A compactly convergent subsequence selected from the supplied literal
family.  No convergence datum is accepted from the caller. -/
structure QuittingMarkedPairMinimumTailSelection
    (source : QuittingMarkedPairMinimumTailSource family minimum) where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  limit : QuittingMarkedPairDecoration iota
  limit_mem_ambient : limit ∈ family.prefixOrbitAmbient
  decorations_tendsto : Tendsto (family.baseDecoration ∘ subsequence)
    atTop (nhds limit)

namespace QuittingMarkedPairMinimumTailSelection

variable {source : QuittingMarkedPairMinimumTailSource family minimum}

/-- The literal family restricted to the compactly convergent subsequence. -/
def selectedFamily
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    QuittingMarkedPairDecoratedFamily reward where
  sourceProfile := family.sourceProfile ∘ selection.subsequence
  profile := family.profile ∘ selection.subsequence
  mark := family.mark ∘ selection.subsequence
  terminal := family.terminal
  markedOwner := family.markedOwner
  gainMover := family.gainMover
  markedMass_pos := fun rank ↦
    family.markedMass_pos (selection.subsequence rank)
  actualGain_pos := fun rank ↦
    family.actualGain_pos (selection.subsequence rank)
  markedOwnerDefect_eq_zero := fun rank ↦
    family.markedOwnerDefect_eq_zero (selection.subsequence rank)

/-- The reindexed family converges to the selected full decoration. -/
theorem selectedFamily_baseDecoration_tendsto
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    Tendsto selection.selectedFamily.baseDecoration atTop
      (nhds selection.limit) := by
  change Tendsto (family.baseDecoration ∘ selection.subsequence) atTop
    (nhds selection.limit)
  exact selection.decorations_tendsto

/-- Global positive minimality makes the selected whole-debt limit positive. -/
theorem limit_wholeDebt_pos
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    0 < selection.limit.wholeDebt := by
  have hcarrier :=
    QuittingMarkedPairDecoratedFamily.semantic_mem_carrier_of_law_mem_carrier
      selection.limit.whole selection.limit_mem_ambient.1.1
  exact source.minimum_pos.trans_le
    (source.minimum_global selection.limit.whole.1 hcarrier)

/-- The uniform marked-mass floor survives compactification. -/
theorem limit_markedMass_pos
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    0 < selection.limit.markedMass := by
  have hlimit : Tendsto
      (fun rank ↦ (selection.selectedFamily.baseDecoration rank).markedMass)
      atTop (nhds selection.limit.markedMass) :=
    ((continuous_fst.comp continuous_snd).tendsto selection.limit).comp
      selection.selectedFamily_baseDecoration_tendsto
  have hlower : source.markedMassFloor ≤ selection.limit.markedMass :=
    ge_of_tendsto' hlimit fun rank ↦
      source.markedMass_floor (selection.subsequence rank)
  exact source.markedMassFloor_pos.trans_le hlower

/-- The uniform actual-gain floor survives compactification. -/
theorem limit_actualGain_pos
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    0 < selection.limit.actualGain := by
  have hlimit : Tendsto
      (fun rank ↦ (selection.selectedFamily.baseDecoration rank).actualGain)
      atTop (nhds selection.limit.actualGain) :=
    ((continuous_snd.comp continuous_snd).tendsto selection.limit).comp
      selection.selectedFamily_baseDecoration_tendsto
  have hlower : source.actualGainFloor ≤ selection.limit.actualGain :=
    ge_of_tendsto' hlimit fun rank ↦
      source.actualGain_floor (selection.subsequence rank)
  exact source.actualGainFloor_pos.trans_le hlower

/-- Tail-debt convergence pins the selected tail to the displayed minimum
debt exactly. -/
theorem limit_tailDebt_eq_minimum
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    selection.limit.tailDebt = quittingTerminalSemanticDebtSum minimum := by
  have hlimit : Tendsto
      (fun rank ↦ (selection.selectedFamily.baseDecoration rank).tailDebt)
      atTop (nhds selection.limit.tailDebt) :=
    (QuittingMarkedPairDecoration.continuous_tailDebt.tendsto
      selection.limit).comp selection.selectedFamily_baseDecoration_tendsto
  have hminimum := source.tailDebt_tendsto.comp
    selection.subsequence_strictMono.tendsto_atTop
  exact tendsto_nhds_unique hlimit hminimum

/-- The generic convergent passport derived from the selected actual rows. -/
def passport (selection : QuittingMarkedPairMinimumTailSelection source) :
    QuittingMarkedPairDecoratedFamily.ConvergentPassport
      selection.selectedFamily minimum where
  limit := selection.limit
  tendsto_base := selection.selectedFamily_baseDecoration_tendsto
  tailDebt_eq := selection.limit_tailDebt_eq_minimum
  wholeDebt_pos := selection.limit_wholeDebt_pos
  markedMass_pos := selection.limit_markedMass_pos
  actualGain_pos := selection.limit_actualGain_pos

/-- Canonical positive marked-mass density at the selected limit. -/
def massDensity
    (selection : QuittingMarkedPairMinimumTailSelection source) : ℝ :=
  selection.limit.markedMass / (2 * selection.limit.wholeDebt)

/-- Canonical positive actual-gain density at the selected limit. -/
def gainDensity
    (selection : QuittingMarkedPairMinimumTailSelection source) : ℝ :=
  selection.limit.actualGain / (2 * selection.limit.wholeDebt)

theorem massDensity_pos
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    0 < selection.massDensity :=
  div_pos selection.limit_markedMass_pos
    (mul_pos (by norm_num) selection.limit_wholeDebt_pos)

theorem gainDensity_pos
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    0 < selection.gainDensity :=
  div_pos selection.limit_actualGain_pos
    (mul_pos (by norm_num) selection.limit_wholeDebt_pos)

theorem massDensity_mul_wholeDebt_lt
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    selection.massDensity * selection.limit.wholeDebt <
      selection.limit.markedMass := by
  rw [massDensity]
  calc
    selection.limit.markedMass / (2 * selection.limit.wholeDebt) *
          selection.limit.wholeDebt = selection.limit.markedMass / 2 := by
      field_simp [ne_of_gt selection.limit_wholeDebt_pos]
    _ < selection.limit.markedMass := by
      linarith [selection.limit_markedMass_pos]

theorem gainDensity_mul_wholeDebt_lt
    (selection : QuittingMarkedPairMinimumTailSelection source) :
    selection.gainDensity * selection.limit.wholeDebt <
      selection.limit.actualGain := by
  rw [gainDensity]
  calc
    selection.limit.actualGain / (2 * selection.limit.wholeDebt) *
          selection.limit.wholeDebt = selection.limit.actualGain / 2 := by
      field_simp [ne_of_gt selection.limit_wholeDebt_pos]
    _ < selection.limit.actualGain := by
      linarith [selection.limit_actualGain_pos]

end QuittingMarkedPairMinimumTailSelection

namespace QuittingMarkedPairMinimumTailSource

/-- Compactness selects the simultaneous full-decoration subsequence. -/
theorem nonempty_selection
    (source : QuittingMarkedPairMinimumTailSource family minimum) :
    Nonempty (QuittingMarkedPairMinimumTailSelection source) := by
  have hmem : ∀ rank, family.baseDecoration rank ∈
      family.prefixOrbitAmbient := by
    intro rank
    simpa only [QuittingMarkedPairDecoratedFamily.rawDecoration_nil] using
      family.rawDecoration_mem_ambient rank []
  obtain ⟨limit, hlimit, subsequence, hsubsequence, htendsto⟩ :=
    family.prefixOrbitAmbient_isCompact.tendsto_subseq hmem
  exact ⟨{
    subsequence := subsequence
    subsequence_strictMono := hsubsequence
    limit := limit
    limit_mem_ambient := hlimit
    decorations_tendsto := htendsto
  }⟩

end QuittingMarkedPairMinimumTailSource

/-- The strongest generic normalized-return result.  The equality arm stores
an actual raw-prefix family and an actual three-role endpoint law. -/
structure QuittingMarkedPairMinimumTailNormalizedResult
    (source : QuittingMarkedPairMinimumTailSource family minimum) where
  selection : QuittingMarkedPairMinimumTailSelection source
  point : QuittingMarkedPairDecoration iota
  point_mem : point ∈ selection.selectedFamily.normalizedPassportSlice minimum
    selection.massDensity selection.gainDensity
  point_minimal : ∀ candidate ∈
      selection.selectedFamily.normalizedPassportSlice minimum
        selection.massDensity selection.gainDensity,
    point.wholeDebt ≤ candidate.wholeDebt
  minimum_le_point : quittingTerminalSemanticDebtSum minimum ≤ point.wholeDebt
  outcome :
    (∃ actualizer : QuittingMarkedPairMinimumReturnActualizer
        selection.selectedFamily minimum selection.massDensity
          selection.gainDensity point,
      point.wholeDebt = quittingTerminalSemanticDebtSum minimum ∧
        ∃ mover recipient,
          Nonempty (ConcentratedCollisionThreeRoleEndpointLaw minimum
            actualizer.packet mover recipient)) ∨
    (quittingTerminalSemanticDebtSum minimum < point.wholeDebt ∧
      ∀ root : iota → PMF Bool,
        IsεQuittingRootNash reward point.whole.1.2 0 root ↔
          root = (quittingAllContinueRoot : iota → PMF Bool))

namespace QuittingMarkedPairMinimumTailSource

/-- A genuine fixed nonsingleton terminal compiles the generic normalized
minimum-return source to an endpoint-law return or strict inert point. -/
theorem nonempty_normalizedThreeRole_or_strictInert
    [Nonempty iota]
    (source : QuittingMarkedPairMinimumTailSource family minimum)
    (hterminal : 1 < family.terminal.val.card) :
    Nonempty (QuittingMarkedPairMinimumTailNormalizedResult source) := by
  obtain ⟨selection⟩ := source.nonempty_selection
  obtain ⟨point, hpoint, hminimal, hlower, hbranch⟩ :=
    selection.selectedFamily.exists_minimum_normalizedPassportSlice_eq_or_strict_inert
      minimum source.minimum_global source.minimum_pos selection.passport
        selection.massDensity selection.gainDensity
          selection.massDensity_mul_wholeDebt_lt
          selection.gainDensity_mul_wholeDebt_lt
  refine ⟨{
    selection := selection
    point := point
    point_mem := hpoint
    point_minimal := hminimal
    minimum_le_point := hlower
    outcome := ?_
  }⟩
  rcases hbranch with hreturn | hinert
  · left
    obtain ⟨actualizer⟩ := nonempty_quittingMarkedPairMinimumReturnActualizer
      selection.selectedFamily minimum selection.massDensity
        selection.gainDensity point selection.massDensity_pos
          selection.gainDensity_pos source.minimum_pos hpoint hreturn
    obtain ⟨mover, recipient, endpoint⟩ :=
      actualizer.nonempty_threeRoleEndpointLaw_of_minimumReturn
        source.minimum_mem source.minimum_global source.minimum_pos hterminal
          hreturn hpoint.2.1
    exact ⟨actualizer, hreturn, mover, recipient, endpoint⟩
  · exact Or.inr hinert

end QuittingMarkedPairMinimumTailSource

end GameTheory
