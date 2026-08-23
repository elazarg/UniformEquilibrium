/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.FiveCycleResetWindowHelix

/-!
# Support rigidity of the exceptional five-cycle

The production helix theorem classifies one selected incidence label at each
of five reset phases.  A complete stopping-law reset actually retains all
finite terminal windows simultaneously, so the incidence witness may be
selected after the reset edge and
its debt recipient are known.

This file upgrades the finite classification accordingly.  Give every phase
a nonempty set of legally retained incidence labels.  Then either one legal
selection produces two consecutive reset windows omitting a player, or every
support is the singleton forced by the lag-three pentagram helix.  Thus the
exceptional branch is support-rigid, not merely a possible labelling.

The theorem is still finite combinatorics.  A game-facing cardinal reduction
must show that positive retained terminal atoms define these supports along
one compatible recurrent reset chronology, and must consume the omitted
player or the rigid singleton-support helix.
-/


namespace GameTheory

/-- A phasewise incidence selector is legal when it lies in the retained
support at every phase. -/
def IsSupportedIncidenceSelection
    (support : Fin 5 → Finset (Fin 5)) (incidence : Fin 5 → Fin 5) : Prop :=
  ∀ phase, incidence phase ∈ support phase

/-- **Two-edge four-role principle.**  Two composable transfer edges with one
common retained incidence label use at most four of five players.  The middle
player is simultaneously the first debt recipient and the next reset owner.

This elementary fact is stronger than the five-phase helix classification
once a fixed polarity label can be retained: only two literal directed
transfers are needed. -/
theorem exists_omitted_matchedTwoEdgeWindow_of_constantIncidence
    (firstOwner sharedRecipient secondRecipient incidenceLabel : Fin 5) :
    ∃ omitted,
      omitted ∉ ({firstOwner, sharedRecipient, incidenceLabel} : Finset (Fin 5)) ∪
        {sharedRecipient, secondRecipient, incidenceLabel} := by
  let window : Finset (Fin 5) :=
    {firstOwner, sharedRecipient, incidenceLabel} ∪
      {sharedRecipient, secondRecipient, incidenceLabel}
  have hsubset : window ⊆
      ({firstOwner, sharedRecipient, secondRecipient, incidenceLabel} :
        Finset (Fin 5)) := by
    intro player hplayer
    simp only [window, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hplayer ⊢
    aesop
  have hfour :
      ({firstOwner, sharedRecipient, secondRecipient, incidenceLabel} :
        Finset (Fin 5)).card ≤ 4 := by
    have h1 := Finset.card_insert_le firstOwner
      ({sharedRecipient, secondRecipient, incidenceLabel} : Finset (Fin 5))
    have h2 := Finset.card_insert_le sharedRecipient
      ({secondRecipient, incidenceLabel} : Finset (Fin 5))
    have h3 := Finset.card_insert_le secondRecipient
      ({incidenceLabel} : Finset (Fin 5))
    simp only [Finset.card_singleton] at h3
    omega
  have hcard : window.card < Fintype.card (Fin 5) := by
    have := Finset.card_le_card hsubset
    norm_num
    omega
  have hproper : window ≠ Finset.univ := by
    intro heq
    have : window.card = Fintype.card (Fin 5) := by
      rw [heq, Finset.card_univ]
    omega
  have homitted : ∃ omitted, omitted ∉ window := by
    by_contra hnone
    push Not at hnone
    exact hproper (Finset.eq_univ_iff_forall.mpr hnone)
  simpa only [window] using homitted

/-- **Support-level helix dichotomy.**  Multiple retained choices cannot hide
inside the exceptional five-cycle.  Either some supported selection has an
omitted label in a consecutive two-edge window, or every phase support is the
forced lag-three singleton. -/
theorem exists_supported_omitted_window_or_support_eq_helixSingleton
    (support : Fin 5 → Finset (Fin 5))
    (hnonempty : ∀ phase, (support phase).Nonempty) :
    (∃ incidence : Fin 5 → Fin 5,
        IsSupportedIncidenceSelection support incidence ∧
          ∃ phase omitted,
            omitted ∉ fiveCycleResetRoleWindow incidence phase ∪
              fiveCycleResetRoleWindow incidence (phase + 1)) ∨
      ∀ phase, support phase = {phase + 3} := by
  classical
  by_cases hselection : ∃ incidence : Fin 5 → Fin 5,
      IsSupportedIncidenceSelection support incidence ∧
        ¬ ∀ phase, incidence phase = phase + 3
  · left
    obtain ⟨incidence, hsupported, hnotHelix⟩ := hselection
    rcases exists_omitted_fiveCycleResetWindow_or_helix incidence with
        homitted | hhelix
    · exact ⟨incidence, hsupported, homitted⟩
    · exact False.elim (hnotHelix hhelix)
  · right
    push Not at hselection
    let base : Fin 5 → Fin 5 := fun phase => (hnonempty phase).choose
    have hbaseSupported : IsSupportedIncidenceSelection support base := by
      intro phase
      exact (hnonempty phase).choose_spec
    have hbaseHelix : ∀ phase, base phase = phase + 3 :=
      hselection base hbaseSupported
    intro phase
    apply Finset.Subset.antisymm
    · intro incidenceLabel hlabel
      let modified : Fin 5 → Fin 5 :=
        Function.update base phase incidenceLabel
      have hmodifiedSupported :
          IsSupportedIncidenceSelection support modified := by
        intro current
        by_cases hcurrent : current = phase
        · subst current
          simpa [modified] using hlabel
        · simpa [modified, hcurrent] using hbaseSupported current
      have hmodifiedHelix : ∀ current,
          modified current = current + 3 :=
        hselection modified hmodifiedSupported
      have hatPhase := hmodifiedHelix phase
      simp [modified] at hatPhase
      simpa only [Finset.mem_singleton] using hatPhase
    · intro incidenceLabel hsingleton
      have hlabel : incidenceLabel = phase + 3 := by
        simpa only [Finset.mem_singleton] using hsingleton
      rw [hlabel, ← hbaseHelix phase]
      exact hbaseSupported phase

/-- A single phase with two distinct supported incidence labels already rules
out the rigid helix and produces a supported consecutive window omitting a
player. -/
theorem exists_supported_omitted_window_of_two_incidenceLabels
    (support : Fin 5 → Finset (Fin 5))
    (hnonempty : ∀ phase, (support phase).Nonempty)
    (phase first second : Fin 5)
    (hfirst : first ∈ support phase) (hsecond : second ∈ support phase)
    (hne : first ≠ second) :
    ∃ incidence : Fin 5 → Fin 5,
      IsSupportedIncidenceSelection support incidence ∧
        ∃ current omitted,
          omitted ∉ fiveCycleResetRoleWindow incidence current ∪
            fiveCycleResetRoleWindow incidence (current + 1) := by
  rcases exists_supported_omitted_window_or_support_eq_helixSingleton
      support hnonempty with homitted | hrigid
  · exact homitted
  · have hfirstEq : first = phase + 3 := by
      have : first ∈ ({phase + 3} : Finset (Fin 5)) := by
        simpa only [hrigid phase] using hfirst
      simpa only [Finset.mem_singleton] using this
    have hsecondEq : second = phase + 3 := by
      have : second ∈ ({phase + 3} : Finset (Fin 5)) := by
        simpa only [hrigid phase] using hsecond
      simpa only [Finset.mem_singleton] using this
    exact False.elim (hne (hfirstEq.trans hsecondEq.symm))

/-- A single incidence player retained through all five reset phases can
never realize the exceptional helix.  Hence it forces an omitted-player
two-edge window without any averaging or choice of phasewise labels. -/
theorem exists_omitted_fiveCycleResetWindow_of_constantIncidence
    (incidenceLabel : Fin 5) :
    ∃ phase omitted,
      omitted ∉
        fiveCycleResetRoleWindow (fun _ ↦ incidenceLabel) phase ∪
          fiveCycleResetRoleWindow (fun _ ↦ incidenceLabel) (phase + 1) := by
  rcases exists_omitted_fiveCycleResetWindow_or_helix
      (fun _ : Fin 5 ↦ incidenceLabel) with homitted | hhelix
  · exact homitted
  · have hzero := hhelix 0
    have hone := hhelix 1
    norm_num at hzero hone
    have himpossible : (3 : Fin 5) = 4 := hzero.symm.trans hone
    omega

/-- Support form: if one common incidence label is retained at every phase,
then selecting it throughout the word produces an omitted-player window. -/
theorem exists_supported_constantIncidence_omittedWindow
    (support : Fin 5 → Finset (Fin 5)) (incidenceLabel : Fin 5)
    (hcommon : ∀ phase, incidenceLabel ∈ support phase) :
    ∃ incidence : Fin 5 → Fin 5,
      IsSupportedIncidenceSelection support incidence ∧
        ∃ phase omitted,
          omitted ∉ fiveCycleResetRoleWindow incidence phase ∪
            fiveCycleResetRoleWindow incidence (phase + 1) := by
  refine ⟨fun _ ↦ incidenceLabel, hcommon, ?_⟩
  exact exists_omitted_fiveCycleResetWindow_of_constantIncidence incidenceLabel

/-! ## Quantitative maturation of the rigid helix -/

/-- On a literal sequence of half-retaining reset edges, an incidence atom in
the exceptional helix survives with at least one quarter of its mass until
the same player becomes the debt recipient two phases later.

This is the quantitative content of the lag-two identity.  It requires an
actual composable reset chronology; the finite support classification alone
does not supply one. -/
theorem helix_incidenceMass_le_four_mul_lagTwoRecipientMass
    (incidence : Fin 5 → Fin 5) (mass : Fin 5 → Fin 5 → ℝ)
    (hhelix : ∀ phase, incidence phase = phase + 3)
    (hretain : ∀ phase label,
      (1 / 2) * mass phase label ≤ mass (phase + 1) label) :
    ∀ phase,
      (1 / 4) * mass phase (incidence phase) ≤
        mass (phase + 2) ((phase + 2) + 1) := by
  intro phase
  have hfirst := hretain phase (incidence phase)
  have hsecond := hretain (phase + 1) (incidence phase)
  have hscaled : (1 / 2) * ((1 / 2) * mass phase (incidence phase)) ≤
      (1 / 2) * mass (phase + 1) (incidence phase) :=
    mul_le_mul_of_nonneg_left hfirst (by norm_num)
  have hquarter : (1 / 4) * mass phase (incidence phase) ≤
      mass ((phase + 1) + 1) (incidence phase) := by
    calc
      (1 / 4) * mass phase (incidence phase) =
          (1 / 2) * ((1 / 2) * mass phase (incidence phase)) := by ring
      _ ≤ (1 / 2) * mass (phase + 1) (incidence phase) := hscaled
      _ ≤ mass ((phase + 1) + 1) (incidence phase) := hsecond
  have hlags := fiveCycleResetHelix_lagTwo_matches incidence hhelix phase
  rw [hlags.1] at hquarter ⊢
  fin_cases phase <;> simpa using hquarter

/-- Positive marked mass therefore remains positive when its label matures
into the lag-two debt recipient. -/
theorem helix_positive_incidenceMass_reaches_lagTwoRecipient
    (incidence : Fin 5 → Fin 5) (mass : Fin 5 → Fin 5 → ℝ)
    (hhelix : ∀ phase, incidence phase = phase + 3)
    (hretain : ∀ phase label,
      (1 / 2) * mass phase label ≤ mass (phase + 1) label)
    (phase : Fin 5) (hpositive : 0 < mass phase (incidence phase)) :
    0 < mass (phase + 2) ((phase + 2) + 1) := by
  have hquarter :=
    helix_incidenceMass_le_four_mul_lagTwoRecipientMass
      incidence mass hhelix hretain phase
  have hscaled : 0 < (1 / 4) * mass phase (incidence phase) :=
    mul_pos (by norm_num) hpositive
  exact hscaled.trans_le hquarter

end GameTheory
