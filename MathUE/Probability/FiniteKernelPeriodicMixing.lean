/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.FiniteDirectedPeriod
import MathUE.Probability.HarmonicPeriodicCore

/-!
# Periodic mixing for finite closed communicating classes

This file compiles the support graph of a finite stochastic kernel into the concrete periodic
mixing data consumed by `PeriodicClosedCoreMixing`.  The graph period supplies one common power
whose rows have full support on each cyclic phase.  Finiteness then makes the phasewise
total-variation coefficient strictly smaller than one.

The construction concerns only the recurrent closed class.  It does not bound the occupation of
states outside that class.
-/

namespace Math.Probability

noncomputable section

open Quiver

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- A state of a displayed finite core, retaining the kernel in its type so the support quiver is
inferred without an ambiguous local instance. -/
structure CoreState (kernel : Omega → PMF Omega) (core : Finset Omega) where
  state : Omega
  mem : state ∈ core

instance (kernel : Omega → PMF Omega) (core : Finset Omega) :
    DecidableEq (CoreState kernel core) :=
  fun first second => decidable_of_iff (first.state = second.state) ⟨by
    intro equality
    cases first
    cases second
    simp_all, congrArg CoreState.state⟩

noncomputable instance (kernel : Omega → PMF Omega) (core : Finset Omega) :
    Fintype (CoreState kernel core) :=
  Fintype.ofEquiv {state : Omega // state ∈ core}
    { toFun := fun state => ⟨state.1, state.2⟩
      invFun := fun state => ⟨state.state, state.mem⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => by cases ‹CoreState kernel core›; rfl }

/-- The support quiver induced by a kernel on a finite core. -/
@[reducible] def coreSupportQuiver (kernel : Omega → PMF Omega) (core : Finset Omega) :
    Quiver (CoreState kernel core) where
  Hom source destination :=
    PLift (PMFSupportStep kernel source.state destination.state)

instance (kernel : Omega → PMF Omega) (core : Finset Omega) :
    Quiver (CoreState kernel core) := coreSupportQuiver kernel core

omit [DecidableEq Omega] in
/-- Two finite PMFs sharing a positive atom have total-variation distance strictly below one. -/
theorem pmfTV_lt_one_of_common_support (first second : PMF Omega) {state : Omega}
    (first_pos : first state ≠ 0) (second_pos : second state ≠ 0) :
    pmfTV first second < 1 := by
  rw [← pmf_toReal_sum_one first]
  change (∑ current : Omega,
    max ((first current).toReal - (second current).toReal) 0) <
      ∑ current : Omega, (first current).toReal
  apply Finset.sum_lt_sum
  · intro current _
    exact max_le (by
      have hsecond : 0 ≤ (second current).toReal := ENNReal.toReal_nonneg
      linarith) ENNReal.toReal_nonneg
  · refine ⟨state, Finset.mem_univ state, ?_⟩
    have hfirst : 0 < (first state).toReal :=
      ENNReal.toReal_pos first_pos (PMF.apply_ne_top first state)
    have hsecond : 0 < (second state).toReal :=
      ENNReal.toReal_pos second_pos (PMF.apply_ne_top second state)
    rcases le_total (first state).toReal (second state).toReal with hle | hle
    · rw [max_eq_right]
      · exact hfirst
      · linarith
    · rw [max_eq_left]
      · linarith
      · linarith

namespace CoreSupport

variable (kernel : Omega → PMF Omega) (core : Finset Omega)

omit [Fintype Omega] [DecidableEq Omega] in
theorem mem_of_reachable
    (closed : IsPMFClosed kernel core) {source destination : Omega}
    (source_mem : source ∈ core) (reachable : PMFReachable kernel source destination) :
    destination ∈ core := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl => exact source_mem
  | head step _ ih =>
      exact ih (closed source_mem step)

omit [Fintype Omega] [DecidableEq Omega] in
/-- A support-quiver path gives positive mass in the matching kernel iterate. -/
theorem iter_ne_zero_of_path {source destination : CoreState kernel core}
    (path : Path source destination) :
    Math.PMFIter.iter kernel path.length source.state destination.state ≠ 0 := by
  induction path with
  | nil => simp [Math.PMFIter.iter_zero]
  | @cons middle destination path arrow ih =>
      rw [Path.length_cons, Math.PMFIter.iter_succ']
      change destination.state ∈
        ((Math.PMFIter.iter kernel path.length source.state).bind kernel).support
      rw [PMF.mem_support_bind_iff]
      exact ⟨middle.state, ih, arrow.down⟩

omit [Fintype Omega] in
/-- A supported iterate endpoint gives a path of exactly the iteration length in the support
quiver, provided the source lies in the closed core. -/
theorem exists_path_of_iter_ne_zero
    (closed : IsPMFClosed kernel core) {source destination : Omega}
    (source_mem : source ∈ core) {steps : ℕ}
    (positive : Math.PMFIter.iter kernel steps source destination ≠ 0) :
    ∃ (destination_mem : destination ∈ core)
      (path : Path (⟨source, source_mem⟩ : CoreState kernel core)
        (⟨destination, destination_mem⟩ : CoreState kernel core)),
      path.length = steps := by
  induction steps generalizing source destination with
  | zero =>
      have equality : destination = source := by
        simpa [Math.PMFIter.iter_zero] using positive
      subst destination
      exact ⟨source_mem, Path.nil, rfl⟩
  | succ steps ih =>
      rw [Math.PMFIter.iter_succ'] at positive
      change destination ∈
        ((Math.PMFIter.iter kernel steps source).bind kernel).support at positive
      rw [PMF.mem_support_bind_iff] at positive
      obtain ⟨middle, hprefix, hstep⟩ := positive
      obtain ⟨middle_mem, initialPath, hlength⟩ := ih source_mem hprefix
      have destination_mem : destination ∈ core := closed middle_mem hstep
      let arrow : (⟨middle, middle_mem⟩ : CoreState kernel core) ⟶
          (⟨destination, destination_mem⟩ : CoreState kernel core) := ⟨hstep⟩
      exact ⟨destination_mem, initialPath.cons arrow, by simp [hlength]⟩

omit [Fintype Omega] in
/-- Communication inside a closed core gives a path in its support quiver. -/
theorem nonempty_path_of_reachable
    (closed : IsPMFClosed kernel core)
    {source destination : CoreState kernel core}
    (reachable : PMFReachable kernel source.state destination.state) :
    Nonempty (Path source destination) := by
  obtain ⟨steps, positive⟩ := exists_iter_support_of_pmfReachable kernel reachable
  obtain ⟨destination_mem, path, _⟩ :=
    exists_path_of_iter_ne_zero kernel core closed source.mem positive
  exact ⟨by simpa only using path⟩

end CoreSupport

/-- A finite closed communicating class supplies the periodic mixing data needed by the harmonic
core argument.  The phase labels are the natural residues of its support-graph period. -/
theorem exists_periodicClosedCoreMixing_of_reachableClosedClass
    (kernel : Omega → PMF Omega) (initial : Omega)
    (closedClass : ReachableClosedClass kernel initial) :
    Nonempty (PeriodicClosedCoreMixing (Phase := ℕ) kernel closedClass.states) := by
  let Core := CoreState kernel closedClass.states
  let connected : IsStronglyConnected Core := by
    intro first second
    exact CoreSupport.nonempty_path_of_reachable kernel closedClass.states
      closedClass.closed (closedClass.communicates first.mem second.mem)
  let base : Core := ⟨closedClass.entry, closedClass.entry_mem⟩
  let period := Math.DirectedPeriod.returnPeriod base
  obtain ⟨successor, hsuccessor⟩ := (kernel base.state).support_nonempty
  have successor_mem : successor ∈ closedClass.states :=
    closedClass.closed base.mem hsuccessor
  let successorState : Core := ⟨successor, successor_mem⟩
  let firstArrow : base ⟶ successorState :=
    ⟨by simpa [PMFSupportStep, PMF.mem_support_iff] using hsuccessor⟩
  let returnPath := (connected successorState base).some
  let positiveCycle : Path base base := firstArrow.toPath.comp returnPath
  have period_pos : 0 < period := by
    apply Math.DirectedPeriod.returnPeriod_pos_of_exists_positive_path positiveCycle
    simp [positiveCycle]
  let phaseCore : Core → ℕ :=
    Math.DirectedPeriod.phaseIndex connected base
  have phasePath := fun (first second : Core) (same : phaseCore first = phaseCore second) =>
    Math.DirectedPeriod.eventually_exists_path_of_phaseIndex_eq connected base same
  let threshold : Core × Core → ℕ := fun pair =>
    if same : phaseCore pair.1 = phaseCore pair.2 then
      Classical.choose (phasePath pair.1 pair.2 same)
    else 0
  let totalThreshold : ℕ := ∑ pair : Core × Core, threshold pair
  let block : ℕ := period * (totalThreshold + 1)
  have threshold_le_total (pair : Core × Core) : threshold pair ≤ totalThreshold := by
    apply Finset.single_le_sum (fun other _ => Nat.zero_le (threshold other))
    exact Finset.mem_univ pair
  have block_pos : 0 < block := by
    dsimp only [block]
    positivity
  have period_dvd_block : period ∣ block := by
    exact dvd_mul_right period (totalThreshold + 1)
  have block_mass_pos (first second : Core) (same : phaseCore first = phaseCore second) :
      Math.PMFIter.iter kernel block first.state second.state ≠ 0 := by
    have hselected := Classical.choose_spec (phasePath first second same)
    have hthreshold : threshold (first, second) =
        Classical.choose (phasePath first second same) := by
      simp [threshold, same]
    have hlarge : Classical.choose (phasePath first second same) ≤ block := by
      rw [← hthreshold]
      have hle := threshold_le_total (first, second)
      have hone : totalThreshold + 1 ≤ block := by
        dsimp only [block]
        nlinarith
      omega
    obtain ⟨path, path_length⟩ := hselected block hlarge period_dvd_block
    have positive := CoreSupport.iter_ne_zero_of_path kernel closedClass.states path
    simpa [path_length] using positive
  let phase : Omega → ℕ := fun state =>
    if state_mem : state ∈ closedClass.states then
      phaseCore ⟨state, state_mem⟩
    else 0
  let rowDistance : ℕ → Core × Core → ℝ := fun label pair =>
    if phaseCore pair.1 = label ∧ phaseCore pair.2 = label then
      pmfTV (Math.PMFIter.iter kernel block pair.1.state)
        (Math.PMFIter.iter kernel block pair.2.state)
    else 0
  letI : Nonempty Core := ⟨base⟩
  let rho : ℕ → ℝ := fun label => finiteMax (rowDistance label)
  refine ⟨{
    phase := phase
    block := block
    block_pos := block_pos
    rho := rho
    rho_nonneg := ?_
    rho_lt_one := ?_
    closed := ?_
    successor_phase := ?_
    block_preserves_phase := ?_
    row_tv_le := ?_
  }⟩
  · intro label
    have hpoint : 0 ≤ rowDistance label (base, base) := by
      dsimp only [rowDistance]
      split_ifs
      · exact pmfTV_nonneg _ _
      · exact le_rfl
    exact hpoint.trans (le_finiteMax (rowDistance label) (base, base))
  · intro label
    apply (Finset.sup'_lt_iff Finset.univ_nonempty).mpr
    intro pair _
    dsimp only [rowDistance]
    split_ifs with hsame
    · exact pmfTV_lt_one_of_common_support _ _
        (block_mass_pos pair.1 pair.1 rfl)
        (block_mass_pos pair.2 pair.1 ((hsame.2).trans hsame.1.symm))
    · norm_num
  · intro source source_mem destination destination_mem
    exact closedClass.closed source_mem destination_mem
  · intro source source_mem first second first_mem second_mem
    have first_core : first ∈ closedClass.states :=
      closedClass.closed source_mem first_mem
    have second_core : second ∈ closedClass.states :=
      closedClass.closed source_mem second_mem
    let sourceState : Core := ⟨source, source_mem⟩
    let firstState : Core := ⟨first, first_core⟩
    let secondState : Core := ⟨second, second_core⟩
    let firstEdge : sourceState ⟶ firstState :=
      ⟨by simpa [PMFSupportStep, PMF.mem_support_iff] using first_mem⟩
    let secondEdge : sourceState ⟶ secondState :=
      ⟨by simpa [PMFSupportStep, PMF.mem_support_iff] using second_mem⟩
    have hfirst := Math.DirectedPeriod.phaseIndex_arrow connected base firstEdge
    have hsecond := Math.DirectedPeriod.phaseIndex_arrow connected base secondEdge
    dsimp only [phase]
    rw [dif_pos first_core, dif_pos second_core]
    exact hfirst.trans hsecond.symm
  · intro source source_mem destination destination_mem
    have positive : Math.PMFIter.iter kernel block source destination ≠ 0 := by
      simpa [PMF.mem_support_iff] using destination_mem
    obtain ⟨destination_core, path, path_length⟩ :=
      CoreSupport.exists_path_of_iter_ne_zero kernel closedClass.states
        closedClass.closed source_mem positive
    have path_mod : path.length ≡ 0 [MOD period] := by
      rw [path_length]
      exact Nat.modEq_zero_iff_dvd.mpr period_dvd_block
    have same :=
      (Math.DirectedPeriod.phaseIndex_eq_iff_path_modEq_zero
        connected base path).mpr path_mod
    refine ⟨destination_core, ?_⟩
    dsimp only [phase]
    rw [dif_pos destination_core, dif_pos source_mem]
    exact same.symm
  · intro first second first_mem second_mem same
    let firstState : Core := ⟨first, first_mem⟩
    let secondState : Core := ⟨second, second_mem⟩
    have sameCore : phaseCore firstState = phaseCore secondState := by
      dsimp only [phase] at same
      rw [dif_pos first_mem, dif_pos second_mem] at same
      exact same
    have hle := le_finiteMax (rowDistance (phase first)) (firstState, secondState)
    have label_eq : phase first = phaseCore firstState := by
      dsimp only [phase]
      rw [dif_pos first_mem]
    have hcondition :
        phaseCore firstState = phase first ∧ phaseCore secondState = phase first :=
      ⟨label_eq.symm, sameCore.symm.trans label_eq.symm⟩
    have hrow : rowDistance (phase first) (firstState, secondState) =
        pmfTV (Math.PMFIter.iter kernel block first)
          (Math.PMFIter.iter kernel block second) := by
      simp [rowDistance, hcondition, firstState, secondState]
    rw [hrow] at hle
    exact hle

/-- Every finite closed communicating class has a source-native periodic mixing package. -/
theorem finiteClosedClassPeriodicMixingPrinciple
    (Omega : Type*) [Fintype Omega] [DecidableEq Omega] :
    FiniteClosedClassPeriodicMixingPrinciple Omega := by
  intro kernel initial closedClass
  obtain ⟨mixing⟩ :=
    exists_periodicClosedCoreMixing_of_reachableClosedClass kernel initial closedClass
  exact ⟨{
    Phase := ℕ
    instDecidableEqPhase := inferInstance
    mixing := mixing
  }⟩

end

end Math.Probability
