/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from the normalized disk-embedding step of RiemannMapping.lean in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
The initial embedding is supplied by the pinned Mathlib theorem, not by an
assumed Riemann map or the external draft as a dependency.
-/
module

public import MathUE.Complex.UnitDiscShift
public import Mathlib.Analysis.Complex.RiemannMapping
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import all Mathlib.Analysis.Complex.RiemannMapping

/-! # Normalize an actual injective disk embedding

An open simply connected proper complex domain has an injective holomorphic
embedding into the disk, normalized at any chosen domain point and with nonzero
derivative everywhere in the domain. Surjectivity onto the disk and extension
to its boundary are not asserted.

The pinned RiemannMapping module keeps its preliminary embedding theorem
private. The supported `import all` above exposes that exact pinned declaration;
an ordinary import does not. No external draft is an imported dependency.
-/

public section

noncomputable section

namespace Math.ComplexUnitDisc

open Complex Set Function Filter
open scoped _root_.Topology

theorem exists_normalized_disk_embedding {U : Set ℂ}
    (hopen : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {origin : ℂ} (horigin : origin ∈ U) :
    ∃ f : ℂ → UnitDisc, f origin = 0 ∧ InjOn f U ∧
      ∀ z ∈ U, deriv (fun x => (f x : ℂ)) z ≠ 0 := by
  classical
  obtain ⟨raw, hrawDisk, hrawInjective, hrawDerivative⟩ :=
    Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero hopen hconnected hproper
  let embedded : ℂ → UnitDisc := fun z =>
    if hz : z ∈ U then UnitDisc.mk (raw z) (by
      simpa only [mem_ball_zero_iff] using hrawDisk hz)
    else UnitDisc.mk (raw origin) (by
      simpa only [mem_ball_zero_iff] using hrawDisk horigin)
  have hinjective : InjOn embedded U := by
    intro z hz w hw heq
    apply hrawInjective hz hw
    have hcoe := congrArg (fun x : UnitDisc => (x : ℂ)) heq
    simpa only [embedded, dite_eq_left hz, dite_eq_left hw, UnitDisc.coe_mk] using hcoe
  have hderivative : ∀ z ∈ U, deriv (fun x => (embedded x : ℂ)) z ≠ 0 := by
    intro z hz
    have hlocal : (fun x => (embedded x : ℂ)) =ᶠ[𝓝 z] raw := by
      filter_upwards [hopen.mem_nhds hz] with x hx
      simp only [embedded, dite_eq_left hx, UnitDisc.coe_mk]
    rw [hlocal.deriv_eq]
    exact hrawDerivative z hz
  refine ⟨fun z => shift (-embedded origin) (embedded z), ?_, ?_, ?_⟩
  · exact shift_neg_apply_self (embedded origin)
  · exact (shift (-embedded origin)).injective.comp_injOn hinjective
  · intro z hz
    exact deriv_shift_comp_ne_zero (-embedded origin) (hderivative z hz)

end Math.ComplexUnitDisc
