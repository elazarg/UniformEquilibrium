import Mathlib.Tactic

/-!
# Exact ledgers for closed finite response cycles

This module contains game-independent finite telescoping and averaging.  A
game-facing adapter must supply literal closure and invariance of a mover's
own cap on its edge.
-/

namespace MathUE.FiniteResponseCycleLedger

variable {Player : Type} [DecidableEq Player]

/-- Exact cross-coordinate accounting for a closed finite response cycle.
The mover's cap is invariant on its own edge; total cap and payoff changes
telescope because the cycle closes literally. -/
theorem closed_mover_externality_ledger
    (payoff cap : ℕ → Player → ℝ)
    (mover : ℕ → Player) (gain : ℕ → ℝ) (length : ℕ)
    (hpayoffClosed : payoff length = payoff 0)
    (hcapClosed : cap length = cap 0)
    (hcapSelf : ∀ time < length,
      cap (time + 1) (mover time) = cap time (mover time))
    (hgain : ∀ time < length,
      gain time = payoff (time + 1) (mover time) -
        payoff time (mover time))
    (observer : Player) :
    (∑ time ∈ (Finset.range length).filter (fun time => mover time ≠ observer),
        (cap (time + 1) observer - cap time observer)) = 0 ∧
      (∑ time ∈ (Finset.range length).filter
          (fun time => mover time ≠ observer),
        (payoff (time + 1) observer - payoff time observer)) =
        -(∑ time ∈ (Finset.range length).filter
          (fun time => mover time = observer), gain time) ∧
      (∑ time ∈ (Finset.range length).filter
          (fun time => mover time ≠ observer),
        ((cap (time + 1) observer - payoff (time + 1) observer) -
          (cap time observer - payoff time observer))) =
        ∑ time ∈ (Finset.range length).filter
          (fun time => mover time = observer), gain time := by
  let capChange : ℕ → ℝ := fun time =>
    cap (time + 1) observer - cap time observer
  let payoffChange : ℕ → ℝ := fun time =>
    payoff (time + 1) observer - payoff time observer
  have hcapTotal : (∑ time ∈ Finset.range length, capChange time) = 0 := by
    have htelescope :=
      Finset.sum_range_sub' (fun time => cap time observer) length
    calc
      (∑ time ∈ Finset.range length, capChange time) =
          -(∑ time ∈ Finset.range length,
            (cap time observer - cap (time + 1) observer)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro time _
        dsimp only [capChange]
        ring
      _ = -(cap 0 observer - cap length observer) := by rw [htelescope]
      _ = 0 := by rw [hcapClosed]; ring
  have hpayoffTotal : (∑ time ∈ Finset.range length, payoffChange time) = 0 := by
    have htelescope :=
      Finset.sum_range_sub' (fun time => payoff time observer) length
    calc
      (∑ time ∈ Finset.range length, payoffChange time) =
          -(∑ time ∈ Finset.range length,
            (payoff time observer - payoff (time + 1) observer)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro time _
        dsimp only [payoffChange]
        ring
      _ = -(payoff 0 observer - payoff length observer) := by rw [htelescope]
      _ = 0 := by rw [hpayoffClosed]; ring
  have hcapMover :
      (∑ time ∈ (Finset.range length).filter
        (fun time => mover time = observer), capChange time) = 0 := by
    apply Finset.sum_eq_zero
    intro time htime
    have htimeRange : time < length :=
      Finset.mem_range.mp (Finset.mem_filter.mp htime).1
    have hmover : mover time = observer := (Finset.mem_filter.mp htime).2
    dsimp only [capChange]
    rw [← hmover, hcapSelf time htimeRange]
    ring
  have hcapSplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range length) (fun time => mover time = observer) capChange
  have hcapNonmover :
      (∑ time ∈ (Finset.range length).filter
        (fun time => mover time ≠ observer), capChange time) = 0 := by
    have hsplit :
        (∑ time ∈ (Finset.range length).filter
            (fun time => mover time = observer), capChange time) +
          (∑ time ∈ (Finset.range length).filter
            (fun time => mover time ≠ observer), capChange time) =
          ∑ time ∈ Finset.range length, capChange time := by
      simpa only using hcapSplit
    linarith
  have hpayoffMover :
      (∑ time ∈ (Finset.range length).filter
        (fun time => mover time = observer), payoffChange time) =
      ∑ time ∈ (Finset.range length).filter
        (fun time => mover time = observer), gain time := by
    apply Finset.sum_congr rfl
    intro time htime
    have htimeRange : time < length :=
      Finset.mem_range.mp (Finset.mem_filter.mp htime).1
    have hmover : mover time = observer := (Finset.mem_filter.mp htime).2
    dsimp only [payoffChange]
    rw [← hmover]
    exact (hgain time htimeRange).symm
  have hpayoffSplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range length) (fun time => mover time = observer) payoffChange
  have hpayoffNonmover :
      (∑ time ∈ (Finset.range length).filter
        (fun time => mover time ≠ observer), payoffChange time) =
      -(∑ time ∈ (Finset.range length).filter
        (fun time => mover time = observer), gain time) := by
    have hsplit :
        (∑ time ∈ (Finset.range length).filter
            (fun time => mover time = observer), payoffChange time) +
          (∑ time ∈ (Finset.range length).filter
            (fun time => mover time ≠ observer), payoffChange time) =
          ∑ time ∈ Finset.range length, payoffChange time := by
      simpa only using hpayoffSplit
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact hcapNonmover
  · exact hpayoffNonmover
  · calc
      (∑ time ∈ (Finset.range length).filter
          (fun time => mover time ≠ observer),
        ((cap (time + 1) observer - payoff (time + 1) observer) -
          (cap time observer - payoff time observer))) =
          ∑ time ∈ (Finset.range length).filter
            (fun time => mover time ≠ observer),
            (capChange time - payoffChange time) := by
        apply Finset.sum_congr rfl
        intro time _
        dsimp only [capChange, payoffChange]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, hcapNonmover, hpayoffNonmover]
        ring

/-- A finite sum at least its cardinality times a threshold has a member at
least that threshold. -/
theorem exists_mem_value_ge_of_card_mul_le_sum
    {Index : Type} [DecidableEq Index]
    (indices : Finset Index) (hindices : indices.Nonempty)
    (value : Index → ℝ) (threshold : ℝ)
    (htotal : (indices.card : ℝ) * threshold ≤ ∑ index ∈ indices, value index) :
    ∃ index ∈ indices, threshold ≤ value index := by
  obtain ⟨best, hbestMem, hbest⟩ :=
    Finset.exists_max_image indices value hindices
  refine ⟨best, hbestMem, ?_⟩
  have hsum := indices.sum_le_card_nsmul value (value best) hbest
  have hsum' : (∑ index ∈ indices, value index) ≤
      (indices.card : ℝ) * value best := by
    simpa only [nsmul_eq_mul] using hsum
  have hcardPositive : 0 < (indices.card : ℝ) := by
    exact_mod_cast hindices.card_pos
  nlinarith [htotal.trans hsum']

end MathUE.FiniteResponseCycleLedger
