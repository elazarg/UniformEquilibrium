/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import MathUE.Probability.AnalyticOccupationFlowCertificate

/-!
# Normalization of analytic occupation-flow certificates

This file separates the analytic Farkas-certificate mechanics from the final
occupation-flow alternative.  It decodes scaled primal certificates, proves
that primal circulations and strict dual separators are incompatible, and
normalizes analytic signed dual potentials into the unit interval.
-/

noncomputable section

namespace Math.Probability

open Filter LinearAlgebra Set

variable {S I : Type*} [DecidableEq I]

/-- Feasibility of the normalized occupation system has a stable truth value
on a punctured right neighborhood. -/
theorem analyticOccupationCertificate_eventually_stabilizes
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I)
    (hanalytic : ∀ i destination,
      AnalyticAt ℝ (fun t ↦ column t i destination) 0) :
    (∀ᶠ t in nhdsWithin 0 (Ioi 0),
        (normalizedFarkasCertificateSet
          (analyticOccupationBalance column t)
          (distinguishedOccupationMass i₀)).Nonempty) ∨
      (∀ᶠ t in nhdsWithin 0 (Ioi 0),
        ¬(normalizedFarkasCertificateSet
          (analyticOccupationBalance column t)
          (distinguishedOccupationMass i₀)).Nonempty) := by
  let balance := analyticOccupationBalance column
  let mass : ℝ → I → ℝ := fun _ ↦ distinguishedOccupationMass i₀
  apply analytic_normalizedFarkas_feasibility_eventually_stabilizes balance mass
  · intro destination i
    exact hanalytic i destination
  · intro i
    exact analyticAt_const

/-- Decode an eventually feasible analytic normalized Farkas system into a
pole-cleared analytic positive circulation. -/
theorem analyticPositiveCirculation_of_eventually_certificate
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I)
    (hanalytic : ∀ i destination,
      AnalyticAt ℝ (fun t ↦ column t i destination) 0)
    (hfeasible : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (normalizedFarkasCertificateSet
        (analyticOccupationBalance column t)
        (distinguishedOccupationMass i₀)).Nonempty) :
    Nonempty (AnalyticPositiveCirculation column i₀) := by
  classical
  let balance := analyticOccupationBalance column
  let mass : ℝ → I → ℝ := fun _ ↦ distinguishedOccupationMass i₀
  have hbalance : ∀ destination i,
      AnalyticAt ℝ (fun t ↦ balance t destination i) 0 := by
    intro destination i
    exact hanalytic i destination
  have hmass : ∀ i, AnalyticAt ℝ (fun t ↦ mass t i) 0 := by
    intro i
    exact analyticAt_const
  obtain ⟨support, poleOrder, scaled, hscaledAnalytic, hscaled⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      balance mass hbalance hmass (by simpa [balance, mass] using hfeasible)
  refine ⟨⟨poleOrder, scaled, hscaledAnalytic, ?_⟩⟩
  filter_upwards [hscaled, self_mem_nhdsWithin] with t ht htpos
  have ht_nonnegative : 0 ≤ t ^ poleOrder :=
    pow_nonneg (le_of_lt (mem_Ioi.mp htpos)) _
  have ht_scaled :
      t ^ poleOrder •
          supportCramerVector
            (normalizedFarkasMatrix (balance t) (mass t))
            normalizedFarkasRhs support = scaled t := by
    simpa using ht.1
  obtain ⟨hz_nonnegative, hz_matrix⟩ :=
    scaled_normalizedFarkasCertificate_properties
      (balance t) (mass t) ht_nonnegative ht_scaled ht.2
  refine ⟨hz_nonnegative, ?_, ?_⟩
  · have htarget := congrFun hz_matrix (Sum.inr ())
    simpa [balance, mass, normalizedFarkasMatrix, normalizedFarkasRhs,
      Matrix.mulVec, dotProduct, distinguishedOccupationMass] using htarget
  · intro destination
    have hrow := congrFun hz_matrix (Sum.inl destination)
    simpa [balance, mass, normalizedFarkasMatrix, normalizedFarkasRhs,
      Matrix.mulVec, dotProduct, analyticOccupationBalance, mul_comm] using hrow

omit [DecidableEq I] in
/-- A positive circulation and a bounded strict separator cannot hold for the
same analytic occupation-column germ. -/
theorem analyticPositiveCirculation_incompatible_boundedSeparator
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {i₀ : I}
    (positive : AnalyticPositiveCirculation column i₀)
    (separator : AnalyticBoundedOccupationSeparator column i₀) : False := by
  classical
  obtain ⟨t, htpos, htpositive, htseparator⟩ :
      ∃ t : ℝ, 0 < t ∧
        ((∀ i, 0 ≤ positive.mass t i) ∧
          positive.mass t i₀ = t ^ positive.poleOrder ∧
          ∀ destination,
            ∑ i, positive.mass t i * column t i destination = 0) ∧
        ((∀ destination, 0 ≤ separator.potential t destination ∧
            separator.potential t destination ≤ 1) ∧
          (∀ i : {i : I // i ≠ i₀}, 0 ≤ ∑ destination,
            separator.potential t destination * column t i.1 destination) ∧
          (∑ destination,
            separator.potential t destination * column t i₀ destination) =
            separator.charge * t ^ separator.poleOrder) := by
    rcases ((positive.eventual.and separator.eventual).and
      self_mem_nhdsWithin).exists with ⟨t, ht, htpos⟩
    exact ⟨t, mem_Ioi.mp htpos, ht.1, ht.2⟩
  have hpairZero :
      ∑ i, positive.mass t i *
          (∑ destination,
            separator.potential t destination * column t i destination) = 0 := by
    calc
      _ = ∑ i, ∑ destination, positive.mass t i *
          (separator.potential t destination * column t i destination) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ destination, ∑ i, positive.mass t i *
          (separator.potential t destination * column t i destination) :=
        Finset.sum_comm
      _ = ∑ destination, separator.potential t destination *
          (∑ i, positive.mass t i * column t i destination) := by
            apply Finset.sum_congr rfl
            intro destination _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by simp [htpositive.2.2]
  have hi₀mass : 0 < positive.mass t i₀ := by
    rw [htpositive.2.1]
    exact pow_pos htpos _
  have hi₀drift : 0 < ∑ destination,
      separator.potential t destination * column t i₀ destination := by
    rw [htseparator.2.2]
    exact mul_pos separator.charge_pos (pow_pos htpos _)
  have hterm : 0 < positive.mass t i₀ *
      (∑ destination,
        separator.potential t destination * column t i₀ destination) :=
    mul_pos hi₀mass hi₀drift
  have hnonnegative : ∀ i, 0 ≤ positive.mass t i *
      (∑ destination,
        separator.potential t destination * column t i destination) := by
    intro i
    by_cases hi : i = i₀
    · subst i
      exact hterm.le
    · exact mul_nonneg (htpositive.1 i) (htseparator.2.1 ⟨i, hi⟩)
  have hpairPositive : 0 < ∑ i, positive.mass t i *
      (∑ destination,
        separator.potential t destination * column t i destination) :=
    hterm.trans_le (Finset.single_le_sum
      (fun i _ ↦ hnonnegative i) (Finset.mem_univ i₀))
  linarith

/-- Normalize a positive analytic circulation at each positive parameter to
an ordinary normalized Farkas certificate. -/
theorem AnalyticPositiveCirculation.eventually_certificate
    [Fintype S] [Fintype I]
    {column : ℝ → I → S → ℝ} {i₀ : I}
    (positive : AnalyticPositiveCirculation column i₀) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (normalizedFarkasCertificateSet
        (analyticOccupationBalance column t)
        (distinguishedOccupationMass i₀)).Nonempty := by
  classical
  filter_upwards [positive.eventual, self_mem_nhdsWithin] with t ht htpos
  rw [normalizedFarkasCertificateSet_occupation_nonempty_iff]
  rw [← hasFullNormalizedPositiveCirculation_iff]
  let normalized : I → ℝ := fun i ↦
    positive.mass t i / t ^ positive.poleOrder
  have hpow_pos : 0 < t ^ positive.poleOrder :=
    pow_pos (mem_Ioi.mp htpos) _
  refine ⟨normalized, ?_, ?_, ?_⟩
  · intro i
    exact div_nonneg (ht.1 i) hpow_pos.le
  · simp [normalized, ht.2.1, ne_of_gt hpow_pos]
  · intro destination
    simp only [normalized, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    simp only [analyticOccupationBalance]
    change (∑ i, positive.mass t i * column t i destination) /
      t ^ positive.poleOrder = 0
    rw [ht.2.2 destination, zero_div]

/-- Failure of the primal occupation certificate produces eventual
feasibility of the normalized strict-separator certificate. -/
theorem eventually_separatorCertificate_of_no_occupationCertificate
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I)
    (hno : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ¬(normalizedFarkasCertificateSet
        (analyticOccupationBalance column t)
        (distinguishedOccupationMass i₀)).Nonempty) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (normalizedFarkasCertificateSet
        (analyticOccupationSeparatorBalance column i₀ t)
        (analyticOccupationSeparatorMass column i₀ t)).Nonempty := by
  classical
  filter_upwards [hno] with t ht
  have hnoNormalized :
      ¬HasNormalizedPositiveCirculation (column t) i₀ := by
    intro hnormalized
    exact ht ((normalizedFarkasCertificateSet_occupation_nonempty_iff
      (column t) i₀).2 hnormalized)
  obtain hcirculation | hseparator :=
    normalizedPositiveCirculation_xor_strictSeparator (column t) i₀
  · exact (hnoNormalized hcirculation.1).elim
  · exact normalizedFarkasCertificateSet_separator_nonempty_of_strict
      (column t) i₀ hseparator.1

omit [DecidableEq I] in
/-- Affinely shift and scale an analytic signed separator into the unit
interval. Zero column sums make the affine shift invisible to every drift. -/
theorem analyticBoundedOccupationSeparator_of_signed
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I) (poleOrder : ℕ)
    (signed : ℝ → S → ℝ) (hsignedAnalytic : AnalyticAt ℝ signed 0)
    (hzeroSum : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ i, ∑ destination, column t i destination = 0)
    (hsigned : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ i : {i : I // i ≠ i₀}, 0 ≤ ∑ destination,
        signed t destination * column t i.1 destination) ∧
      (∑ destination, signed t destination * column t i₀ destination) =
        t ^ poleOrder) :
    Nonempty (AnalyticBoundedOccupationSeparator column i₀) := by
  classical
  let bound : ℝ := ∑ destination, |signed 0 destination| + 1
  have hbound_pos : 0 < bound := by
    dsimp only [bound]
    positivity
  have hsignedBound : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ destination, |signed t destination| ≤ bound := by
    have hnear : ∀ destination, ∀ᶠ t in nhdsWithin 0 (Ioi 0),
        dist (signed t destination) (signed 0 destination) < 1 := by
      intro destination
      have hcoord : ContinuousAt (fun t ↦ signed t destination) 0 := by
        rw [analyticAt_pi_iff] at hsignedAnalytic
        exact (hsignedAnalytic destination).continuousAt
      exact ((Metric.tendsto_nhds.mp hcoord) 1 zero_lt_one).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [Filter.eventually_all.2 hnear] with t ht destination
    have habs : |signed t destination| < |signed 0 destination| + 1 := by
      calc
        |signed t destination| =
            |(signed t destination - signed 0 destination) +
              signed 0 destination| := by ring_nf
        _ ≤ |signed t destination - signed 0 destination| +
              |signed 0 destination| := abs_add_le _ _
        _ < 1 + |signed 0 destination| := by
          simpa [Real.dist_eq] using
            add_lt_add_right (ht destination) |signed 0 destination|
        _ = |signed 0 destination| + 1 := by ring
    have hterm : |signed 0 destination| ≤ ∑ u, |signed 0 u| :=
      Finset.single_le_sum (fun u _ ↦ abs_nonneg (signed 0 u))
        (Finset.mem_univ destination)
    dsimp only [bound]
    linarith
  let charge : ℝ := 1 / (2 * bound)
  let potential : ℝ → S → ℝ := fun t destination ↦
    (signed t destination + bound) / (2 * bound)
  have hcharge_pos : 0 < charge := by
    dsimp only [charge]
    positivity
  have hpotentialAnalytic : AnalyticAt ℝ potential 0 := by
    rw [analyticAt_pi_iff] at hsignedAnalytic ⊢
    intro destination
    exact ((hsignedAnalytic destination).add analyticAt_const).div_const
  have hbounded : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ destination, 0 ≤ potential t destination ∧
        potential t destination ≤ 1 := by
    filter_upwards [hsignedBound] with t ht destination
    have hlower : -bound ≤ signed t destination := neg_le_of_abs_le (ht destination)
    have hupper : signed t destination ≤ bound := le_of_abs_le (ht destination)
    dsimp only [potential]
    constructor
    · exact div_nonneg (by linarith) (by positivity)
    · rw [div_le_one (by positivity : 0 < 2 * bound)]
      linarith
  refine ⟨⟨poleOrder, charge, potential, hcharge_pos, hpotentialAnalytic, ?_⟩⟩
  filter_upwards [hsigned, hzeroSum, hbounded] with t ht hsum htbounded
  have hpotentialDrift (i : I) :
      (∑ destination, potential t destination * column t i destination) =
        (∑ destination, signed t destination * column t i destination) /
          (2 * bound) := by
    dsimp only [potential]
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    congr 1
    simp only [add_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum i]
    simp
  refine ⟨htbounded, ?_, ?_⟩
  · intro i
    rw [hpotentialDrift]
    exact div_nonneg (ht.1 i) (by positivity)
  · rw [hpotentialDrift, ht.2]
    dsimp only [charge]
    ring

/-- Decode an eventually feasible separator certificate into an analytic
bounded separator; the affine normalization is delegated to the signed API. -/
theorem analyticBoundedOccupationSeparator_of_eventually_certificate
    [Fintype S] [Fintype I]
    (column : ℝ → I → S → ℝ) (i₀ : I)
    (hanalytic : ∀ i destination,
      AnalyticAt ℝ (fun t ↦ column t i destination) 0)
    (hzeroSum : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ i, ∑ destination, column t i destination = 0)
    (hfeasible : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (normalizedFarkasCertificateSet
        (analyticOccupationSeparatorBalance column i₀ t)
        (analyticOccupationSeparatorMass column i₀ t)).Nonempty) :
    Nonempty (AnalyticBoundedOccupationSeparator column i₀) := by
  classical
  have hbalance : ∀ i entry, AnalyticAt ℝ
      (fun t ↦ analyticOccupationSeparatorBalance column i₀ t i entry) 0 := by
    intro i entry
    cases entry with
    | inl oriented => exact analyticAt_const.mul (hanalytic i.1 oriented.1)
    | inr slack => exact analyticAt_const
  have hmass : ∀ entry, AnalyticAt ℝ
      (fun t ↦ analyticOccupationSeparatorMass column i₀ t entry) 0 := by
    intro entry
    cases entry with
    | inl oriented => exact analyticAt_const.mul (hanalytic i₀ oriented.1)
    | inr slack => exact analyticAt_const
  obtain ⟨support, poleOrder, scaled, hscaledAnalytic, hscaled⟩ :=
    exists_analytic_scaled_eventual_feasible_normalizedFarkasCertificate
      (analyticOccupationSeparatorBalance column i₀)
      (analyticOccupationSeparatorMass column i₀)
      hbalance hmass hfeasible
  let signed : ℝ → S → ℝ := fun t ↦ occupationSeparatorPotential i₀ (scaled t)
  have hsignedAnalytic : AnalyticAt ℝ signed 0 := by
    rw [analyticAt_pi_iff] at hscaledAnalytic ⊢
    intro destination
    exact (hscaledAnalytic (Sum.inl (destination, true))).sub
      (hscaledAnalytic (Sum.inl (destination, false)))
  have hsigned : ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      (∀ i : {i : I // i ≠ i₀}, 0 ≤ ∑ destination,
        signed t destination * column t i.1 destination) ∧
      (∑ destination, signed t destination * column t i₀ destination) =
        t ^ poleOrder := by
    filter_upwards [hscaled, self_mem_nhdsWithin] with t ht htpos
    have ht_nonnegative : 0 ≤ t ^ poleOrder :=
      pow_nonneg (le_of_lt (mem_Ioi.mp htpos)) _
    have ht_scaled : t ^ poleOrder •
        supportCramerVector
          (normalizedFarkasMatrix
            (analyticOccupationSeparatorBalance column i₀ t)
            (analyticOccupationSeparatorMass column i₀ t))
          normalizedFarkasRhs support = scaled t := by
      simpa using ht.1
    obtain ⟨hz_nonnegative, hz_matrix⟩ :=
      scaled_normalizedFarkasCertificate_properties
        (analyticOccupationSeparatorBalance column i₀ t)
        (analyticOccupationSeparatorMass column i₀ t)
        ht_nonnegative ht_scaled ht.2
    exact occupationSeparatorPotential_properties
      (column t) i₀ hz_nonnegative hz_matrix
  exact analyticBoundedOccupationSeparator_of_signed column i₀ poleOrder
    signed hsignedAnalytic hzeroSum hsigned

end Math.Probability
