/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Math.Probability.FinDist

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
end GameTheory.Math.Probability
