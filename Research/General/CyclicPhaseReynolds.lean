import UniformEquilibrium.ProofView.Concepts.Welfare.FolkTheorem.Periodic

/-!
# Cyclic Reynolds decomposition

This file formalizes an independent cyclic phase/Reynolds construction.

For a real signal on a nonempty finite cycle, the only persistent component is
its cycle mean.  The centered component is an exact cyclic coboundary.  Finite
windows therefore equal `horizon * mean` plus two endpoint potentials, giving
the uniform `2*C/horizon` estimate for a bounded primitive.
-/

noncomputable section

namespace Research.CyclicPhaseReynolds

open scoped BigOperators

/-- Mean of a real signal over a nonempty finite cycle. -/
def cycleMean {P : ℕ} [NeZero P] (signal : Fin P → ℝ) : ℝ :=
  (P : ℝ)⁻¹ * ∑ phase, signal phase

/-- The component orthogonal to the invariant constants. -/
def centeredSignal {P : ℕ} [NeZero P] (signal : Fin P → ℝ) : Fin P → ℝ :=
  fun phase => signal phase - cycleMean signal

/-- The centered component has zero Reynolds average. -/
theorem sum_centeredSignal_eq_zero {P : ℕ} [NeZero P]
    (signal : Fin P → ℝ) :
    ∑ phase, centeredSignal signal phase = 0 := by
  have hP : (P : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne P)
  simp only [centeredSignal, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, cycleMean]
  field_simp [hP]
  ring

/-- Explicit prefix-sum primitive of the centered signal. -/
def prefixPrimitive {P : ℕ} [NeZero P]
    (signal : Fin P → ℝ) (phase : Fin P) : ℝ :=
  -∑ k ∈ Finset.range phase.val,
    centeredSignal signal (Fin.ofNat P k)

/-- Advancing a natural-time phase is the canonical cyclic rotation. -/
theorem finRotate_finOfNat {P : ℕ} [NeZero P] (time : ℕ) :
    finRotate P (Fin.ofNat P time) = Fin.ofNat P (time + 1) := by
  rw [finRotate_apply]
  apply Fin.ext
  simp [Fin.ofNat, Fin.add_def, Nat.add_mod]

/-- The explicit primitive differentiates to the centered signal, including
the wraparound edge of the cycle. -/
theorem prefixPrimitive_sub_rotate_eq_centeredSignal
    {P : ℕ} [NeZero P] (signal : Fin P → ℝ) (phase : Fin P) :
    prefixPrimitive signal phase -
        prefixPrimitive signal (finRotate P phase) =
      centeredSignal signal phase := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne P)
  by_cases phase_last : phase = Fin.last n
  · subst phase
    rw [finRotate_last]
    simp only [prefixPrimitive, Fin.val_last, Fin.val_zero,
      Finset.range_zero, Finset.sum_empty, neg_zero, sub_zero]
    have centeredSum := sum_centeredSignal_eq_zero signal
    rw [Fin.sum_univ_castSucc] at centeredSum
    have prefixEq :
        (∑ k ∈ Finset.range n,
            centeredSignal signal (Fin.ofNat (n + 1) k)) =
          ∑ k : Fin n, centeredSignal signal k.castSucc := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k k_mem
      congr 2
      apply Fin.ext
      simp [Fin.ofNat]
    rw [prefixEq]
    linarith
  · have phase_lt : phase.val < n := Fin.val_lt_last phase_last
    rw [finRotate_of_lt phase_lt]
    unfold prefixPrimitive
    rw [Finset.sum_range_succ]
    have phase_ofNat : Fin.ofNat (n + 1) phase.val = phase := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt phase.isLt]
    rw [phase_ofNat]
    ring

/-- **Cyclic Reynolds decomposition on `Fin P`.** -/
theorem signal_eq_mean_add_coboundary
    {P : ℕ} [NeZero P] (signal : Fin P → ℝ) (phase : Fin P) :
    signal phase =
      cycleMean signal + prefixPrimitive signal phase -
        prefixPrimitive signal (finRotate P phase) := by
  have difference :=
    prefixPrimitive_sub_rotate_eq_centeredSignal signal phase
  unfold centeredSignal at difference
  linarith

/-- Existential form of the cyclic Reynolds decomposition. -/
theorem exists_cyclicPrimitive
    {P : ℕ} [NeZero P] (signal : Fin P → ℝ) :
    ∃ primitive : Fin P → ℝ, ∀ phase,
      signal phase = cycleMean signal + primitive phase -
        primitive (finRotate P phase) := by
  exact ⟨prefixPrimitive signal, signal_eq_mean_add_coboundary signal⟩

/-- Exact telescope for a shifted finite window of a cyclic signal. -/
theorem sum_window_eq_mean_add_endpoints
    {P : ℕ} [NeZero P]
    (signal primitive : Fin P → ℝ) (mean : ℝ)
    (decomposition : ∀ phase,
      signal phase = mean + primitive phase - primitive (finRotate P phase))
    (start horizon : ℕ) :
    (∑ t ∈ Finset.range horizon,
        signal (Fin.ofNat P (start + t))) =
      (horizon : ℝ) * mean + primitive (Fin.ofNat P start) -
        primitive (Fin.ofNat P (start + horizon)) := by
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [Finset.sum_range_succ, inductionHypothesis,
        decomposition, finRotate_finOfNat]
      push_cast
      rw [show start + horizon + 1 = start + (horizon + 1) by omega]
      ring

/-- Normalized shifted finite-window average. -/
def finiteWindowAverage {P : ℕ} [NeZero P]
    (signal : Fin P → ℝ) (start horizon : ℕ) : ℝ :=
  (horizon : ℝ)⁻¹ *
    ∑ t ∈ Finset.range horizon, signal (Fin.ofNat P (start + t))

/-- A bounded cyclic primitive gives a start-uniform `2*C/T` rate. -/
theorem abs_finiteWindowAverage_sub_mean_le
    {P : ℕ} [NeZero P]
    (signal primitive : Fin P → ℝ) (mean bound : ℝ)
    (decomposition : ∀ phase,
      signal phase = mean + primitive phase - primitive (finRotate P phase))
    (primitiveBound : ∀ phase, |primitive phase| ≤ bound)
    (start horizon : ℕ) (horizon_pos : 0 < horizon) :
    |finiteWindowAverage signal start horizon - mean| ≤
      2 * bound / (horizon : ℝ) := by
  have telescope := sum_window_eq_mean_add_endpoints
    signal primitive mean decomposition start horizon
  have horizon_real_pos : 0 < (horizon : ℝ) := by exact_mod_cast horizon_pos
  have endpointBound :
      |primitive (Fin.ofNat P start) -
          primitive (Fin.ofNat P (start + horizon))| ≤ 2 * bound := by
    calc
      |primitive (Fin.ofNat P start) -
          primitive (Fin.ofNat P (start + horizon))| ≤
          |primitive (Fin.ofNat P start)| +
            |primitive (Fin.ofNat P (start + horizon))| := abs_sub _ _
      _ ≤ bound + bound := add_le_add
        (primitiveBound _) (primitiveBound _)
      _ = 2 * bound := by ring
  unfold finiteWindowAverage
  rw [telescope]
  have differenceIdentity :
      (horizon : ℝ)⁻¹ *
            ((horizon : ℝ) * mean + primitive (Fin.ofNat P start) -
              primitive (Fin.ofNat P (start + horizon))) - mean =
        (primitive (Fin.ofNat P start) -
          primitive (Fin.ofNat P (start + horizon))) / (horizon : ℝ) := by
    field_simp [horizon_real_pos.ne']
    ring
  rw [differenceIdentity, abs_div, abs_of_pos horizon_real_pos]
  exact div_le_div_of_nonneg_right endpointBound horizon_real_pos.le

/-! ## The literal cyclic group `ZMod P` -/

/-- The repository's `ZMod P ≃ Fin P` identification intertwines addition by
one with `finRotate`. -/
theorem zmodFinEquiv_add_one {P : ℕ} [NeZero P] (phase : ZMod P) :
    GameTheory.KernelGame.zmodFinEquiv P (phase + 1) =
      finRotate P (GameTheory.KernelGame.zmodFinEquiv P phase) := by
  apply Fin.ext
  rw [finRotate_apply]
  simp [GameTheory.KernelGame.zmodFinEquiv, ZMod.val_add,
    ZMod.val_one_eq_one_mod, Fin.add_def, Nat.add_mod]

/-- **Cyclic Reynolds decomposition on the group `ZMod P`.** -/
theorem exists_zmod_cyclicPrimitive
    {P : ℕ} [NeZero P] (signal : ZMod P → ℝ) :
    ∃ primitive : ZMod P → ℝ, ∀ phase,
      signal phase =
        cycleMean (fun q : Fin P =>
          signal ((GameTheory.KernelGame.zmodFinEquiv P).symm q)) +
        primitive phase - primitive (phase + 1) := by
  let finSignal : Fin P → ℝ := fun q =>
    signal ((GameTheory.KernelGame.zmodFinEquiv P).symm q)
  obtain ⟨finPrimitive, decomposition⟩ := exists_cyclicPrimitive finSignal
  let primitive : ZMod P → ℝ := fun phase =>
    finPrimitive (GameTheory.KernelGame.zmodFinEquiv P phase)
  refine ⟨primitive, fun phase => ?_⟩
  have phaseSignal :
      finSignal (GameTheory.KernelGame.zmodFinEquiv P phase) = signal phase := by
    simp [finSignal]
  have atPhase := decomposition (GameTheory.KernelGame.zmodFinEquiv P phase)
  rw [phaseSignal, ← zmodFinEquiv_add_one] at atPhase
  exact atPhase

end Research.CyclicPhaseReynolds
