module

public import MathUE.Complex.NormalizedDiskBijection
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Topology.Homeomorph.Defs

/-! # An actual normalized homeomorphism to the disk

The checked holomorphic disk bijection is an open map, hence a homeomorphism.
This is the standard open-mapping bridge used before the boundary discussion in
Milnor, *Dynamics in One Complex Variable*, sections 15--16. Its inverse supplies
an actual continuous disk parameterization. No inverse holomorphicity, nonzero
derivative theorem, or continuous extension to the closed disk is asserted here.
The open-domain hypotheses do not include degenerate singleton carriers; those
must be handled separately in a later planar filling application.
-/

public section

namespace Math.ComplexAnalysis

open Set Metric Complex

theorem exists_normalized_disk_homeomorphism {U : Set ℂ}
    (hopen : IsOpen U) (hconnected : IsSimplyConnected U) (hproper : U ≠ univ)
    {base : ℂ} (hbase : base ∈ U) :
    ∃ (f : ℂ → ℂ) (e : U ≃ₜ ball (0 : ℂ) 1),
      DifferentiableOn ℂ f U ∧ (∀ z : U, (e z : ℂ) = f z) ∧
        (e ⟨base, hbase⟩ : ℂ) = 0 := by
  classical
  obtain ⟨f, hfd, hfbij, hfzero⟩ :=
    exists_bijOn_unitBall_map_eq_zero hopen hconnected hproper hbase
  have hnonconstant : ¬∃ c, ∀ z ∈ U, f z = c := by
    rintro ⟨c, hc⟩
    obtain ⟨z, hz, heq⟩ := hfbij.surjOn (show (1 / 2 : ℂ) ∈ ball 0 1 by
      norm_num [mem_ball_zero_iff])
    have hczero : c = 0 := (hc base hbase).symm.trans hfzero
    have : (1 / 2 : ℂ) = 0 := heq.symm.trans ((hc z hz).trans hczero)
    norm_num at this
  have hmapsOpen := ((hfd.analyticOnNhd hopen).is_constant_or_isOpen
    hconnected.isPathConnected.isConnected.isPreconnected).resolve_left hnonconstant
  let e : U ≃ ball (0 : ℂ) 1 := hfbij.equiv f
  have heq : ∀ z : U, (e z : ℂ) = f z := fun _ => rfl
  have hcontinuous : Continuous e := by
    exact hfd.continuousOn.mapsToRestrict hfbij.mapsTo
  have hopenMap : IsOpenMap e := by
    apply isOpen_ball.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    intro s hs
    have himage : (Subtype.val ∘ e) '' s = f '' (Subtype.val '' s) := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨z, hz, rfl⟩, (heq z).symm⟩
      · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨v, hv, heq v⟩
    rw [himage]
    exact hmapsOpen _ (by rintro z ⟨v, _, rfl⟩; exact v.property)
      (hopen.isOpenMap_subtype_val s hs)
  exact ⟨f, e.toHomeomorphOfContinuousOpen hcontinuous hopenMap, hfd, heq, hfzero⟩

end Math.ComplexAnalysis
