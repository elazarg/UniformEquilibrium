/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.NormalizedFarkasBasis
import MathUE.Probability.OccupationFlowAlternative

/-!
# Analytic occupation-flow certificates

This file develops the finite normalized Farkas encodings used to classify
analytic families of actual occupation columns along a punctured right germ.

For one distinguished transition, normalized circulation feasibility has an
eventually constant truth value. In the circulation branch, one fixed Cramer
support gives an analytic pole-cleared nonnegative flow. In the other branch,
the dual strict separator is encoded as a second normalized Farkas system
with nonnegative slack coordinates and receives the same analytic treatment.
-/

noncomputable section

namespace Math
namespace Probability

open Filter LinearAlgebra Set

variable {S I : Type*}

/-- Matrix form of a parameter-dependent occupation-column family. -/
def analyticOccupationBalance
    (column : ℝ → I → S → ℝ) :
    ℝ → Matrix S I ℝ :=
  fun t destination i => column t i destination

/-- The normalizing functional selecting one distinguished transition. -/
def distinguishedOccupationMass [DecidableEq I]
    (i₀ : I) : I → ℝ :=
  fun i => if i = i₀ then 1 else 0

/-- A pole-cleared analytic positive circulation. The distinguished
transition has exactly the common clearing mass `t ^ poleOrder`. -/
structure AnalyticPositiveCirculation
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I) where
  poleOrder : ℕ
  mass : ℝ → I → ℝ
  analytic_mass : AnalyticAt ℝ mass 0
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ i, 0 ≤ mass t i) ∧
        mass t i₀ = t ^ poleOrder ∧
        ∀ destination,
          ∑ i, mass t i * column t i destination = 0

/-- A pole-cleared analytic separator, normalized into the unit interval.
All other occupation columns have nonnegative drift, while the
distinguished column has an exact positive power-law charge. -/
structure AnalyticBoundedOccupationSeparator
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I) where
  poleOrder : ℕ
  charge : ℝ
  potential : ℝ → S → ℝ
  charge_pos : 0 < charge
  analytic_potential : AnalyticAt ℝ potential 0
  eventual :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ destination,
        0 ≤ potential t destination ∧
          potential t destination ≤ 1) ∧
      (∀ i : {i : I // i ≠ i₀},
        0 ≤ ∑ destination,
          potential t destination * column t i.1 destination) ∧
      (∑ destination,
        potential t destination * column t i₀ destination) =
          charge * t ^ poleOrder

namespace AnalyticPositiveCirculation

/-- The positive support of an analytic nonnegative circulation stabilizes
on a punctured right neighborhood. The distinguished transition belongs to
that fixed support because its mass is exactly a positive power of the
parameter. -/
theorem exists_eventually_fixed_positiveSupport
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {i₀ : I}
    (C : AnalyticPositiveCirculation column i₀) :
    ∃ support : Finset I,
      i₀ ∈ support ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∀ i, (0 < C.mass t i ↔ i ∈ support) := by
  classical
  have hanalytic :
      ∀ i, AnalyticAt ℝ (fun t => C.mass t i) 0 := by
    have hmassAnalytic := C.analytic_mass
    rw [analyticAt_pi_iff] at hmassAnalytic
    exact hmassAnalytic
  have hnonnegative :
      ∀ i,
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          0 ≤ C.mass t i := by
    intro i
    exact C.eventual.mono fun _ ht => ht.1 i
  obtain ⟨zeroMass, hzeroMass⟩ :=
    finite_analytic_nonnegative_family_eventually_active_set
      (fun i t => C.mass t i) hanalytic hnonnegative
  let support : Finset I :=
    Finset.univ.filter fun i => ¬zeroMass i
  have hsupport :
      ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ∀ i, (0 < C.mass t i ↔ i ∈ support) := by
    filter_upwards [hzeroMass] with t ht i
    simpa [support] using (ht i).2
  have hi₀ : i₀ ∈ support := by
    obtain ⟨t, ⟨htSupport, htMass⟩, htpos⟩ :=
      ((hsupport.and C.eventual).and self_mem_nhdsWithin).exists
    apply (htSupport i₀).mp
    rw [htMass.2.1]
    exact pow_pos (mem_Ioi.mp htpos) _
  exact ⟨support, hi₀, hsupport⟩

/-- Erasing the distinguished transition from the stabilized positive
support is a strict finite support-rank decrease. -/
theorem card_erase_distinguished_lt_fixedSupport
    [Fintype S] [Fintype I] [DecidableEq I]
    {column : ℝ → I → S → ℝ} {i₀ : I}
    (C : AnalyticPositiveCirculation column i₀) :
    ∃ support : Finset I,
      (support.erase i₀).card < support.card ∧
        ∀ᶠ t in nhdsWithin 0 (Ioi 0),
          ∀ i, (0 < C.mass t i ↔ i ∈ support) := by
  obtain ⟨support, hi₀, hsupport⟩ :=
    C.exists_eventually_fixed_positiveSupport
  exact ⟨support, card_erase_lt_supportRank support hi₀, hsupport⟩

end AnalyticPositiveCirculation

/-- Full-vector form of normalized positive circulation. -/
def HasFullNormalizedPositiveCirculation
    [Fintype S] [Fintype I]
    (column : I → S → ℝ) (i₀ : I) : Prop :=
  ∃ mass : I → ℝ,
    (∀ i, 0 ≤ mass i) ∧
      mass i₀ = 1 ∧
      ∀ destination,
        ∑ i, mass i * column i destination = 0

theorem hasFullNormalizedPositiveCirculation_iff
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) :
    HasFullNormalizedPositiveCirculation column i₀ ↔
      HasNormalizedPositiveCirculation column i₀ := by
  classical
  constructor
  · rintro ⟨mass, hmass, hi₀, hbalance⟩
    refine ⟨fun i => mass i.1, fun i => hmass i.1, ?_⟩
    intro destination
    have hsubtype :
        (∑ i : {i : I // i ≠ i₀},
            mass i.1 * column i.1 destination) =
          ∑ i ∈ (Finset.univ : Finset I).erase i₀,
            mass i * column i destination := by
      rw [← Finset.sum_subtype
        ((Finset.univ : Finset I).erase i₀)
        (fun i => by simp)
        (fun i => mass i * column i destination)]
    calc
      column i₀ destination +
          ∑ i : {i : I // i ≠ i₀},
            mass i.1 * column i.1 destination =
          (∑ i ∈ (Finset.univ : Finset I).erase i₀,
              mass i * column i destination) +
            mass i₀ * column i₀ destination := by
        rw [hsubtype, hi₀, one_mul, add_comm]
      _ = ∑ i, mass i * column i destination :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i₀)
      _ = 0 := hbalance destination
  · rintro ⟨alpha, halpha, hbalance⟩
    let mass : I → ℝ := fun i =>
      if hi : i = i₀ then 1
      else alpha ⟨i, hi⟩
    refine ⟨mass, ?_, by simp [mass], ?_⟩
    · intro i
      by_cases hi : i = i₀
      · simp [mass, hi]
      · simpa [mass, hi] using halpha ⟨i, hi⟩
    · intro destination
      have hsubtype :
          (∑ i : {i : I // i ≠ i₀},
              mass i.1 * column i.1 destination) =
            ∑ i ∈ (Finset.univ : Finset I).erase i₀,
              mass i * column i destination := by
        rw [← Finset.sum_subtype
          ((Finset.univ : Finset I).erase i₀)
          (fun i => by simp)
          (fun i => mass i * column i destination)]
      have hsubtype_alpha :
          (∑ i : {i : I // i ≠ i₀},
              mass i.1 * column i.1 destination) =
            ∑ i : {i : I // i ≠ i₀},
              alpha i * column i.1 destination := by
        apply Finset.sum_congr rfl
        intro i _
        simp [mass, i.property]
      calc
        ∑ i, mass i * column i destination =
            (∑ i ∈ (Finset.univ : Finset I).erase i₀,
                mass i * column i destination) +
              mass i₀ * column i₀ destination :=
          (Finset.sum_erase_add _ _ (Finset.mem_univ i₀)).symm
        _ = (∑ i : {i : I // i ≠ i₀},
              alpha i * column i.1 destination) +
            column i₀ destination := by
          rw [← hsubtype, hsubtype_alpha]
          simp [mass]
        _ = 0 := by
          rw [add_comm]
          exact hbalance destination

/-- Normalized circulation is exactly feasibility of the corresponding
normalized Farkas system. -/
theorem normalizedFarkasCertificateSet_occupation_nonempty_iff
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I) :
    (normalizedFarkasCertificateSet
      (fun destination i => column i destination)
      (distinguishedOccupationMass i₀)).Nonempty ↔
        HasNormalizedPositiveCirculation column i₀ := by
  rw [← hasFullNormalizedPositiveCirculation_iff]
  constructor
  · rintro ⟨mass, hnonnegative, hmatrix⟩
    refine ⟨mass, hnonnegative, ?_, ?_⟩
    · have htarget := congrFun hmatrix (Sum.inr ())
      simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
        Matrix.mulVec, dotProduct, distinguishedOccupationMass] using
          htarget
    · intro destination
      have hbalance := congrFun hmatrix (Sum.inl destination)
      simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
        Matrix.mulVec, dotProduct, mul_comm] using hbalance
  · rintro ⟨mass, hnonnegative, hi₀, hbalance⟩
    refine ⟨mass, hnonnegative, ?_⟩
    funext row
    cases row with
    | inl destination =>
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, mul_comm] using
            hbalance destination
    | inr u =>
        cases u
        simpa [normalizedFarkasMatrix, normalizedFarkasRhs,
          Matrix.mulVec, dotProduct, distinguishedOccupationMass] using
            hi₀

/-- Variables for a normalized strict separator: doubled signed potential
coordinates followed by one nonnegative drift slack for every
non-distinguished column. -/
abbrev OccupationSeparatorVariable
    (S I : Type*) (i₀ : I) :=
  Sum (S × Bool) {i : I // i ≠ i₀}

/-- Equality rows for the non-distinguished drift slacks. -/
def analyticOccupationSeparatorBalance
    [DecidableEq I]
    (column : ℝ → I → S → ℝ) (i₀ : I) :
    ℝ →
      Matrix {i : I // i ≠ i₀}
        (OccupationSeparatorVariable S I i₀) ℝ :=
  fun t i entry =>
    match entry with
    | Sum.inl oriented =>
        farkasOrientation oriented.2 *
          column t i.1 oriented.1
    | Sum.inr slack =>
        if slack = i then -1 else 0

/-- The separator normalization is its drift on the distinguished
occupation column. -/
def analyticOccupationSeparatorMass
    (column : ℝ → I → S → ℝ) (i₀ : I) :
    ℝ → OccupationSeparatorVariable S I i₀ → ℝ :=
  fun t entry =>
    match entry with
    | Sum.inl oriented =>
        farkasOrientation oriented.2 *
          column t i₀ oriented.1
    | Sum.inr _ => 0

/-- Reconstruct the signed potential part of a separator certificate. -/
def occupationSeparatorPotential
    (i₀ : I)
    (z : OccupationSeparatorVariable S I i₀ → ℝ) :
    S → ℝ :=
  fun destination =>
    z (Sum.inl (destination, true)) -
      z (Sum.inl (destination, false))

theorem occupationSeparatorPotential_eq_orientedFarkasToSigned
    (i₀ : I)
    (z : OccupationSeparatorVariable S I i₀ → ℝ) :
    occupationSeparatorPotential i₀ z =
      orientedFarkasToSigned
        (fun oriented : S × Bool => z (Sum.inl oriented)) := by
  rfl

/-- Every strict separator can be normalized and encoded by nonnegative
potential halves and nonnegative drift slacks. -/
theorem normalizedFarkasCertificateSet_separator_nonempty_of_strict
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I)
    (hseparator :
      ∃ h, IsUnitStrictColumnSeparator column i₀ h) :
    (normalizedFarkasCertificateSet
      (analyticOccupationSeparatorBalance
        (fun _ => column) i₀ 0)
      (analyticOccupationSeparatorMass
        (fun _ => column) i₀ 0)).Nonempty := by
  classical
  obtain ⟨h, _hunit, hother, htarget⟩ := hseparator
  let target : ℝ := ∑ destination,
    h destination * column i₀ destination
  have htarget_pos : 0 < target := htarget
  let signed : S → ℝ := fun destination =>
    h destination / target
  let oriented : S × Bool → ℝ :=
    signedFarkasToOriented signed
  let drift : {i : I // i ≠ i₀} → ℝ := fun i =>
    ∑ destination, signed destination * column i.1 destination
  let z : OccupationSeparatorVariable S I i₀ → ℝ
    | Sum.inl coordinate => oriented coordinate
    | Sum.inr i => drift i
  refine ⟨z, ?_, ?_⟩
  · intro entry
    cases entry with
    | inl coordinate =>
        exact signedFarkasToOriented_nonneg signed coordinate
    | inr i =>
        dsimp only [z, drift, signed]
        have hi := hother i
        have htarget_nonneg : 0 ≤ target := htarget_pos.le
        calc
          0 ≤
              (∑ destination,
                h destination * column i.1 destination) / target :=
            div_nonneg hi htarget_nonneg
          _ =
              ∑ destination,
                h destination / target *
                  column i.1 destination := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro destination _
            ring
  · funext row
    cases row with
    | inl i =>
        simp only [normalizedFarkasMatrix,
          normalizedFarkasRhs, Matrix.mulVec, dotProduct]
        rw [Fintype.sum_sum_type]
        have horiented :
            (∑ coordinate : S × Bool,
                (farkasOrientation coordinate.2 *
                    column i.1 coordinate.1) *
                  oriented coordinate) =
              ∑ destination,
                column i.1 destination * signed destination := by
          have horiented_mul :=
            orientedFarkasBalance_mulVec
              (fun (_ : Unit) destination =>
                column i.1 destination)
              oriented ()
          rw [show orientedFarkasToSigned oriented = signed by
            simp [oriented]] at horiented_mul
          simpa only [orientedFarkasBalance,
            Matrix.mulVec, dotProduct] using horiented_mul
        have hslack :
            (∑ slack : {j : I // j ≠ i₀},
                (if slack = i then -1 else 0) * drift slack) =
              -drift i := by
          simp
        change
          (∑ coordinate : S × Bool,
              (farkasOrientation coordinate.2 *
                  column i.1 coordinate.1) *
                oriented coordinate) +
            ∑ slack : {j : I // j ≠ i₀},
              (if slack = i then -1 else 0) * drift slack = 0
        rw [horiented, hslack]
        dsimp only [drift]
        apply sub_eq_zero.mpr
        apply Finset.sum_congr rfl
        intro destination _
        ring
    | inr u =>
        cases u
        simp only [normalizedFarkasMatrix,
          normalizedFarkasRhs, Matrix.mulVec, dotProduct]
        rw [Fintype.sum_sum_type]
        simp only [analyticOccupationSeparatorMass, z]
        have horiented :
            (∑ coordinate : S × Bool,
                (farkasOrientation coordinate.2 *
                    column i₀ coordinate.1) *
                  oriented coordinate) =
              ∑ destination,
                column i₀ destination * signed destination := by
          have horiented_mass :=
            orientedFarkasMass_dotProduct
              (fun destination => column i₀ destination) oriented
          rw [show orientedFarkasToSigned oriented = signed by
            simp [oriented]] at horiented_mass
          simpa only [orientedFarkasMass] using horiented_mass
        rw [horiented]
        dsimp only [signed, target]
        simp only [zero_mul, Finset.sum_const_zero, add_zero]
        calc
          (∑ destination,
              column i₀ destination *
                (h destination /
                  ∑ destination,
                    h destination * column i₀ destination)) =
              (∑ destination,
                  h destination * column i₀ destination) /
                (∑ destination,
                  h destination * column i₀ destination) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro destination _
            ring
          _ = 1 := div_self (ne_of_gt htarget_pos)

/-- Scaling a normalized certificate by a nonnegative scalar preserves
nonnegativity and scales its right-hand side by that scalar. -/
theorem scaled_normalizedFarkasCertificate_properties
    {Row Col : Type*} [Fintype Col]
    (balance : Matrix Row Col ℝ) (mass : Col → ℝ)
    {z scaled : Col → ℝ} {factor : ℝ}
    (hfactor : 0 ≤ factor)
    (hscaled : factor • z = scaled)
    (hz : z ∈ normalizedFarkasCertificateSet balance mass) :
    (∀ j, 0 ≤ scaled j) ∧
      Matrix.mulVec (normalizedFarkasMatrix balance mass) scaled =
        factor • normalizedFarkasRhs := by
  constructor
  · intro j
    rw [← hscaled]
    exact mul_nonneg hfactor (hz.1 j)
  · rw [← hscaled, Matrix.mulVec_smul, hz.2]

/-- Read the drift inequalities and distinguished drift from a scaled
separator certificate. -/
theorem occupationSeparatorPotential_properties
    [Fintype S] [Fintype I] [DecidableEq I]
    (column : I → S → ℝ) (i₀ : I)
    {z : OccupationSeparatorVariable S I i₀ → ℝ}
    {factor : ℝ}
    (hz_nonnegative : ∀ entry, 0 ≤ z entry)
    (hz_matrix :
      Matrix.mulVec
        (normalizedFarkasMatrix
          (analyticOccupationSeparatorBalance
            (fun _ => column) i₀ 0)
          (analyticOccupationSeparatorMass
            (fun _ => column) i₀ 0))
        z =
      factor • normalizedFarkasRhs) :
    (∀ i : {i : I // i ≠ i₀},
      0 ≤ ∑ destination,
        occupationSeparatorPotential i₀ z destination *
          column i.1 destination) ∧
    (∑ destination,
      occupationSeparatorPotential i₀ z destination *
        column i₀ destination) = factor := by
  classical
  constructor
  · intro i
    have hi := congrFun hz_matrix (Sum.inl i)
    simp only [normalizedFarkasMatrix, Matrix.mulVec, dotProduct,
      Pi.smul_apply, normalizedFarkasRhs, smul_eq_mul, mul_zero] at hi
    rw [Fintype.sum_sum_type] at hi
    simp only [analyticOccupationSeparatorBalance] at hi
    have horiented :
        (∑ coordinate : S × Bool,
            (farkasOrientation coordinate.2 *
                column i.1 coordinate.1) *
              z (Sum.inl coordinate)) =
          ∑ destination,
            occupationSeparatorPotential i₀ z destination *
              column i.1 destination := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro destination _
      simp [farkasOrientation, occupationSeparatorPotential]
      ring
    have hslack :
        (∑ slack : {j : I // j ≠ i₀},
            (if slack = i then -1 else 0) *
              z (Sum.inr slack)) =
          -z (Sum.inr i) := by
      simp
    rw [horiented, hslack] at hi
    linarith [hz_nonnegative (Sum.inr i)]
  · have hi := congrFun hz_matrix (Sum.inr ())
    simp only [normalizedFarkasMatrix, Matrix.mulVec, dotProduct,
      Pi.smul_apply, normalizedFarkasRhs, smul_eq_mul, mul_one] at hi
    rw [Fintype.sum_sum_type] at hi
    simp only [analyticOccupationSeparatorMass] at hi
    have horiented :
        (∑ coordinate : S × Bool,
            (farkasOrientation coordinate.2 *
                column i₀ coordinate.1) *
              z (Sum.inl coordinate)) =
          ∑ destination,
            occupationSeparatorPotential i₀ z destination *
              column i₀ destination := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro destination _
      simp [farkasOrientation, occupationSeparatorPotential]
      ring
    rw [horiented] at hi
    simpa using hi

end Probability
end Math
