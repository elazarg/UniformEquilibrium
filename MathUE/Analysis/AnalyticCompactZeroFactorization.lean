/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache-2.0; see LICENSES/APACHE_2_0.txt.
Authors: Yury Kudryashov

Adapted from `AnalyticOnNhd.exists_finset_eq_prod_smul_nonzero` in
https://github.com/urkud/mathlib4/tree/d43061d911b1aeae0788591da437a3b115098962
under Mathlib/Analysis/Complex/RiemannMapping.lean (PR33505).
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Tactic.FunProp

/-! # Factor all zeros on a compact preconnected analytic set

The finite zero set is derived from compactness and analyticity. Removing its
linear factors with their actual analytic orders leaves an analytic vector-valued
factor nonzero on the set. The product identity holds on the whole scalar field,
although analyticity is required only near the designated set. No completeness
or supplied finite-zero certificate is assumed.
-/

public section

namespace Math.Analysis

open Set Function Filter
open scoped _root_.Topology

theorem exists_finset_eq_prod_smul_nonzero
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : 𝕜 → E} {s : Set 𝕜}
    (hanalytic : AnalyticOnNhd 𝕜 f s) (hcompact : IsCompact s)
    (hconnected : IsPreconnected s) (hnonzero : ¬EqOn f 0 s) :
    ∃ zeros : Finset 𝕜, (∀ x, x ∈ zeros ↔ x ∈ s ∧ f x = 0) ∧
      ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g s ∧
        (f = fun z => (∏ x ∈ zeros, (z - x) ^ analyticOrderNatAt f x) • g z) ∧
        ∀ z ∈ s, g z ≠ 0 := by
  classical
  have hfiniteOrder : ∀ {f : 𝕜 → E}, AnalyticOnNhd 𝕜 f s → ¬EqOn f 0 s →
      ∀ x ∈ s, analyticOrderAt f x ≠ ⊤ := by
    intro f hf hfzero x hx horder
    rw [analyticOrderAt_eq_top] at horder
    exact hfzero (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconnected hx horder)
  obtain ⟨zeros, hzeros⟩ : ∃ zeros : Finset 𝕜,
      ∀ x, x ∈ zeros ↔ x ∈ s ∧ f x = 0 := by
    use (hcompact.finite_sdiff_of_mem_codiscreteWithin
      hanalytic.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top).toFinset
    simp only [Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, not_or,
      analyticOrderAt_eq_zero, and_congr_right_iff]
    push Not
    intro x hx
    simp [hanalytic x hx, hfiniteOrder hanalytic hnonzero x hx]
  refine ⟨zeros, hzeros, ?_⟩
  induction zeros using Finset.cons_induction generalizing f with
  | empty =>
    exact ⟨f, hanalytic, by simp, by simpa using hzeros⟩
  | cons a zeros ha hinduction =>
    simp only [Finset.mem_cons] at hzeros
    have has : a ∈ s := ((hzeros a).mp (Or.inl rfl)).1
    obtain ⟨g, hg, hga, hfactor⟩ : ∃ g : 𝕜 → E,
        AnalyticOnNhd 𝕜 g s ∧ g a ≠ 0 ∧
        f = fun z => (z - a) ^ analyticOrderNatAt f a • g z := by
      obtain ⟨localFactor, hlocalAnalytic, hlocalNonzero, hlocal⟩ :=
        (hanalytic a has).analyticOrderAt_ne_top.mp
          (hfiniteOrder hanalytic hnonzero a has)
      let globalFactor := update
        (fun z => (z - a) ^ (-analyticOrderNatAt f a : ℤ) • f z) a (localFactor a)
      have hlocalEq : localFactor =ᶠ[𝓝 a] globalFactor := by
        refine hlocal.mono fun z hz => ?_
        rcases eq_or_ne z a with rfl | hza
        · simp [globalFactor]
        · simp [globalFactor, hza, hz, sub_eq_zero]
      refine ⟨globalFactor, ?_, ?_, ?_⟩
      · intro z hz
        rcases eq_or_ne z a with rfl | hza
        · exact hlocalAnalytic.congr hlocalEq
        · have heq : globalFactor =ᶠ[𝓝 z]
              fun w => (w - a) ^ (-analyticOrderNatAt f a : ℤ) • f w :=
            (eventually_ne_nhds hza).mono fun w hw => by simp [globalFactor, hw]
          rw [analyticAt_congr heq]
          refine AnalyticAt.smul (AnalyticAt.zpow ?_ (by rwa [sub_ne_zero]))
            (hanalytic z hz)
          fun_prop
      · simp [globalFactor, hlocalNonzero]
      · ext z
        rcases eq_or_ne z a with rfl | hza
        · simpa [globalFactor] using hlocal.self_of_nhds
        · simp [globalFactor, hza, sub_eq_zero]
    have hgzeros : ∀ z, z ∈ zeros ↔ z ∈ s ∧ g z = 0 := by
      rw [hfactor] at hzeros
      intro z
      rcases eq_or_ne z a with rfl | hza
      · simp [hga, ha]
      · simpa [hza, sub_eq_zero] using hzeros z
    have hgnonzero : ¬EqOn g 0 s := fun hzero => hga (hzero has)
    obtain ⟨remaining, hremaining, hremainingFactor, hremainingNonzero⟩ :=
      hinduction hg hgnonzero hgzeros
    refine ⟨remaining, hremaining, ?_, hremainingNonzero⟩
    ext z
    rw [congrFun hfactor, congrFun hremainingFactor, Finset.prod_cons, mul_smul]
    congr 2
    refine Finset.prod_congr rfl fun x hx => ?_
    congr 1
    conv_rhs => rw [hfactor, analyticOrderNatAt]
    rw [← Pi.smul_def', analyticOrderAt_smul]
    · have horder : analyticOrderAt (fun z => (z - a) ^ analyticOrderNatAt f a) x = 0 := by
        rw [analyticOrderAt_eq_zero]
        right
        simp [sub_eq_zero, ne_of_mem_of_not_mem hx ha]
      rw [horder]
      simp [analyticOrderNatAt]
    · fun_prop
    · exact hg x ((hgzeros x).mp hx).1

end Math.Analysis
