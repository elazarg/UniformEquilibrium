/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Math.Probability.FinDist
import MathUE.PMFProduct.Update

/-!
# Separately affine realization of finite independent mixtures

If each finite marginal law has a barycenter and a real observable is affine
when one coordinate is replaced by such a barycenter, then evaluating all
barycenters equals expectation under the independent product law.  This is
the finite-product algebra used when complete stopping-law mixtures are
realized as ordinary behavioral hazards.
-/

noncomputable section

namespace GameTheory.Math.Probability

namespace FinDist

theorem expect_piFin_eq_of_separatelyAffine :
    ∀ {n : ℕ} {A : Fin n → Type*}
      (barycenter : (i : Fin n) → FinDist (A i) → A i)
      (observable : ((i : Fin n) → A i) → ℝ)
      (laws : (i : Fin n) → FinDist (A i)),
      (∀ (i : Fin n) (profile : (j : Fin n) → A j)
          (law : FinDist (A i)),
        observable (Function.update profile i (barycenter i law)) =
          law.expect fun action =>
            observable (Function.update profile i action)) →
      observable (fun i => barycenter i (laws i)) =
        (piFin laws).expect observable
  | 0, A, barycenter, observable, laws => by
      intro _
      rw [piFin]
      simp only [expect_pure]
      congr
      funext i
      exact Fin.elim0 i
  | n + 1, A, barycenter, observable, laws => by
      intro haffine
      let head := barycenter 0 (laws 0)
      let tailBarycenter : (i : Fin n) → FinDist (A i.succ) → A i.succ :=
        fun i => barycenter i.succ
      let tailLaws : (i : Fin n) → FinDist (A i.succ) :=
        fun i => laws i.succ
      let tailProfile : (i : Fin n) → A i.succ :=
        fun i => barycenter i.succ (laws i.succ)
      have hprofile : (fun i => barycenter i (laws i)) =
          Fin.cons head tailProfile := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      have hhead := haffine 0
        (Fin.cons head tailProfile)
        (laws 0)
      have hhead' : observable (Fin.cons head tailProfile) =
          (laws 0).expect fun action =>
            observable (Fin.cons action tailProfile) := by
        simpa [head, Function.update, tailProfile] using hhead
      rw [hprofile, hhead']
      rw [piFin, expect_map, expect_product]
      apply expect_congr
      intro action _
      have htailAction := expect_piFin_eq_of_separatelyAffine
        tailBarycenter
        (fun tail => observable (Fin.cons action tail))
        tailLaws
        (by
          intro i profile law
          have h := haffine i.succ (Fin.cons action profile) law
          simpa [tailBarycenter, Function.update] using h)
      exact htailAction

/-- Arbitrary finite-index form of
`expect_piFin_eq_of_separatelyAffine`. -/
theorem expect_pi_eq_of_separatelyAffine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*}
    (barycenter : (i : ι) → FinDist (A i) → A i)
    (observable : ((i : ι) → A i) → ℝ)
    (laws : (i : ι) → FinDist (A i))
    (haffine : ∀ (i : ι) (profile : (j : ι) → A j)
        (law : FinDist (A i)),
      observable (Function.update profile i (barycenter i law)) =
        law.expect fun action =>
          observable (Function.update profile i action)) :
    observable (fun i => barycenter i (laws i)) =
      (pi laws).expect observable := by
  let equiv := Fintype.equivFin ι
  let profileEquiv := Equiv.piCongrLeft' A equiv
  let lawEquiv := Equiv.piCongrLeft' (fun i => FinDist (A i)) equiv
  let barycenter' : (k : Fin (Fintype.card ι)) →
      FinDist (A (equiv.symm k)) → A (equiv.symm k) :=
    fun k => barycenter (equiv.symm k)
  let laws' : (k : Fin (Fintype.card ι)) → FinDist (A (equiv.symm k)) :=
    lawEquiv laws
  let observable' : ((k : Fin (Fintype.card ι)) → A (equiv.symm k)) → ℝ :=
    fun profile => observable (profileEquiv.symm profile)
  have haffine' : ∀ (k : Fin (Fintype.card ι))
      (profile : (l : Fin (Fintype.card ι)) → A (equiv.symm l))
      (law : FinDist (A (equiv.symm k))),
      observable'
          (Function.update profile k (barycenter' k law)) =
        law.expect fun action =>
          observable' (Function.update profile k action) := by
    intro k profile law
    have h := haffine (equiv.symm k) (profileEquiv.symm profile) law
    have hupdate (action : A (equiv.symm k)) :
        profileEquiv.symm (Function.update profile k action) =
          Function.update (profileEquiv.symm profile) (equiv.symm k) action :=
      Function.piCongrLeft'_symm_update A equiv profile k action
    change observable
        (profileEquiv.symm
          (Function.update profile k (barycenter' k law))) =
      law.expect fun action =>
        observable (profileEquiv.symm (Function.update profile k action))
    rw [hupdate]
    simp_rw [hupdate]
    simpa [barycenter'] using h
  have hfin := expect_piFin_eq_of_separatelyAffine
    barycenter' observable' laws' haffine'
  rw [piFin_eq_pi] at hfin
  have hproduct := pi_unreindex A equiv laws'
  have hlaws : lawEquiv.symm laws' = laws := by
    exact lawEquiv.symm_apply_apply laws
  rw [hlaws] at hproduct
  have hexpect : (pi laws').expect observable' =
      (pi laws).expect observable := by
    rw [← hproduct, expect_map]
  have hbaryProfile : profileEquiv.symm
      (fun k => barycenter' k (laws' k)) =
        fun i => barycenter i (laws i) := by
    apply profileEquiv.injective
    rw [profileEquiv.apply_symm_apply]
    funext k
    change barycenter (equiv.symm k) (laws (equiv.symm k)) =
      barycenter (equiv.symm k) (laws (equiv.symm k))
    rfl
  rw [← hexpect]
  rw [← hbaryProfile]
  exact hfin

end FinDist

/-- A bounded observable that is affine under replacement by each displayed
law's barycenter evaluates at all barycenters as its
expectation under the independent product law. -/
theorem expect_pmfPi_eq_of_separatelyAffine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Sample A : ι -> Type*} [forall i, Nonempty (Sample i)]
    (realize : (i : ι) -> Sample i -> A i)
    (barycenter : (i : ι) -> PMF (Sample i) -> A i)
    (observable : ((i : ι) -> A i) -> Real)
    (laws : (i : ι) -> PMF (Sample i))
    {C : Real} (hbound : forall profile, |observable profile| <= C)
    (haffine : forall (i : ι) (profile : (j : ι) -> A j),
      observable (Function.update profile i (barycenter i (laws i))) =
        Math.Probability.expect (laws i) (fun action =>
          observable (Function.update profile i (realize i action)))) :
    observable (fun i => barycenter i (laws i)) =
      Math.Probability.expect (Math.PMFProduct.pmfPi laws)
        (fun samples => observable (fun i => realize i (samples i))) := by
  classical
  let randomizedFamily (active : Finset ι)
      (base : (i : ι) -> Sample i) : (i : ι) -> PMF (Sample i) :=
    fun i => if i ∈ active then laws i else PMF.pure (base i)
  let realizedProfile (active : Finset ι)
      (base : (i : ι) -> Sample i) : (i : ι) -> A i :=
    fun i => if i ∈ active then barycenter i (laws i) else realize i (base i)
  have hind : forall active : Finset ι,
      forall base : (i : ι) -> Sample i,
      observable (realizedProfile active base) =
        Math.Probability.expect
          (Math.PMFProduct.pmfPi (randomizedFamily active base))
          (fun samples => observable (fun i => realize i (samples i))) := by
    intro active
    induction active using Finset.induction_on with
    | empty =>
        intro base
        have hfamily : randomizedFamily ∅ base =
            fun i => PMF.pure (base i) := by
          funext i
          simp [randomizedFamily]
        have hprofile : realizedProfile ∅ base = fun i => realize i (base i) := by
          funext i
          simp [realizedProfile]
        rw [hfamily, Math.PMFProduct.pmfPi_pure,
          Math.Probability.expect_pure, hprofile]
    | @insert player active hnot ih =>
        intro base
        let sourceFamily := randomizedFamily active base
        have hfamily : randomizedFamily (insert player active) base =
            Function.update sourceFamily player (laws player) := by
          funext i
          by_cases hi : i = player
          · subst i
            simp [randomizedFamily]
          · simp [randomizedFamily, sourceFamily, hi]
        have hinner (action : Sample player) :
            Function.update sourceFamily player (PMF.pure action) =
              randomizedFamily active (Function.update base player action) := by
          funext i
          by_cases hi : i = player
          · subst i
            simp [randomizedFamily, hnot]
          · simp [sourceFamily, randomizedFamily, hi]
        have hrealized (action : Sample player) :
            realizedProfile active (Function.update base player action) =
            Function.update (realizedProfile active base) player
              (realize player action) := by
          funext i
          by_cases hi : i = player
          · subst i
            simp [realizedProfile, hnot]
          · simp [realizedProfile, hi]
        have htarget : realizedProfile (insert player active) base =
            Function.update (realizedProfile active base) player
              (barycenter player (laws player)) := by
          funext i
          by_cases hi : i = player
          · subst i
            simp [realizedProfile]
          · simp [realizedProfile, hi]
        rw [hfamily, Math.PMFProduct.pmfPi_update_bind,
          Math.Probability.expect_bind_of_bounded
            (laws player)
            (fun action => Math.PMFProduct.pmfPi
              (Function.update sourceFamily player (PMF.pure action)))
            (fun samples : ((i : ι) -> Sample i) =>
              observable (fun i => realize i (samples i)))
            (fun samples => hbound (fun i => realize i (samples i)))]
        simp_rw [hinner, <- ih, hrealized]
        rw [htarget, haffine]
  have hprofile : realizedProfile Finset.univ
      (fun i => Classical.choice (inferInstance : Nonempty (Sample i))) =
        fun i => barycenter i (laws i) := by
    funext i
    simp [realizedProfile]
  have hfamily : randomizedFamily Finset.univ
      (fun i => Classical.choice (inferInstance : Nonempty (Sample i))) = laws := by
    funext i
    simp [randomizedFamily]
  simpa [hprofile, hfamily] using
    hind Finset.univ
      (fun i => Classical.choice (inferInstance : Nonempty (Sample i)))

end GameTheory.Math.Probability
