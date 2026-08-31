import UniformEquilibrium.Quitting.Paths.BehaviorStoppingLaw

/-!
# Bad-mass selection for quitting stopping laws

These division-free estimates locate bad stopping-law mass either at a least
finite date or at `Never`, while retaining a survival lower bound.  They do
not select a game-semantic deviation or construct a source adapter.
-/

noncomputable section

namespace GameTheory

open Math.Probability

/-- Division-free bad-set mass bound: if the expected value under the quitting
stopping law falls short of the ceiling `C` by at least `Δ`, then the mass of
choices losing at least `Δ / 2` is at least `Δ / (4 * M)`, stated without
division. -/
theorem quittingStoppingLaw_badMass_lowerBound
    (hazard : ℕ → PMF Bool) (value : Option ℕ → ℝ) (C M Δ : ℝ)
    (hval : ∀ choice, |value choice| ≤ M)
    (hC : ∀ choice, value choice ≤ C) (hCM : C ≤ M)
    (hgap : Δ ≤ C - expect (quittingHazardStoppingLaw hazard) value) :
    Δ ≤ 4 * M *
      expect (quittingHazardStoppingLaw hazard)
        (fun choice => if Δ / 2 ≤ C - value choice then 1 else 0) := by
  set ind : Option ℕ → ℝ := fun choice => if Δ / 2 ≤ C - value choice then 1 else 0 with hind
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hval none)
  have hind_nonneg : ∀ q, 0 ≤ ind q := by
    intro q
    simp only [hind]
    split <;> norm_num
  have hind_le_one : ∀ q, ind q ≤ 1 := by
    intro q
    simp only [hind]
    split <;> norm_num
  have hind_abs : ∀ q, |ind q| ≤ 1 := by
    intro q
    rw [abs_of_nonneg (hind_nonneg q)]
    exact hind_le_one q
  have hB := quittingHazardStoppingLaw_expect hazard ind hind_abs
  have hE := quittingHazardStoppingLaw_expect hazard value hval
  have hstop := hasSum_quittingHazardStopMass hazard
  have hsum_stop : Summable (quittingHazardStopMass hazard) := hstop.summable
  have hstop_nonneg := quittingHazardStopMass_nonneg hazard
  have hnever : 0 ≤ quittingHazardNeverMass hazard := quittingHazardNeverMass_nonneg hazard
  have hgsum : Summable (fun t => quittingHazardStopMass hazard t * ind (some t)) := by
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (hstop_nonneg t) (hind_nonneg _))
      (fun t => ?_) hsum_stop
    calc quittingHazardStopMass hazard t * ind (some t)
        ≤ quittingHazardStopMass hazard t * 1 :=
          mul_le_mul_of_nonneg_left (hind_le_one _) (hstop_nonneg t)
      _ = quittingHazardStopMass hazard t := mul_one _
  have hGnonneg : 0 ≤ ∑' t, quittingHazardStopMass hazard t * ind (some t) :=
    tsum_nonneg (fun t => mul_nonneg (hstop_nonneg t) (hind_nonneg _))
  have hBnonneg : 0 ≤ expect (quittingHazardStoppingLaw hazard) ind := by
    rw [hB]
    exact add_nonneg (mul_nonneg hnever (hind_nonneg _)) hGnonneg
  rcases le_or_gt Δ 0 with hΔ | hΔ
  · have hpos : 0 ≤ 4 * M * expect (quittingHazardStoppingLaw hazard) ind :=
      mul_nonneg (by linarith) hBnonneg
    linarith
  · have hlow : ∀ q, -M ≤ value q := fun q => (abs_le.1 (hval q)).1
    have hpt : ∀ q, C - value q ≤ Δ / 2 + 2 * M * ind q := by
      intro q
      by_cases hq : Δ / 2 ≤ C - value q
      · have hone : ind q = 1 := by
          simp only [hind]
          simp [hq]
        rw [hone]
        have hlq := hlow q
        linarith
      · have hzero : ind q = 0 := by
          simp only [hind]
          simp [hq]
        rw [hzero]
        have hlt := not_le.1 hq
        linarith
    have hfnonneg : ∀ t, 0 ≤ quittingHazardStopMass hazard t * (C - value (some t)) :=
      fun t => mul_nonneg (hstop_nonneg t) (sub_nonneg.2 (hC _))
    have hfle : ∀ t, quittingHazardStopMass hazard t * (C - value (some t))
        ≤ (C + M) * quittingHazardStopMass hazard t := by
      intro t
      have h1 : C - value (some t) ≤ C + M := by
        have := hlow (some t)
        linarith
      linarith [mul_le_mul_of_nonneg_left h1 (hstop_nonneg t)]
    have hf : Summable (fun t => quittingHazardStopMass hazard t * (C - value (some t))) :=
      Summable.of_nonneg_of_le hfnonneg hfle (hsum_stop.mul_left (C + M))
    have hcongr : ∀ t, C * quittingHazardStopMass hazard t -
        quittingHazardStopMass hazard t * (C - value (some t))
        = quittingHazardStopMass hazard t * value (some t) := by
      intro t
      ring
    have hvsum : Summable (fun t => quittingHazardStopMass hazard t * value (some t)) :=
      ((hsum_stop.mul_left C).sub hf).congr hcongr
    have htv : ∑' t, quittingHazardStopMass hazard t * value (some t)
        = C * (1 - quittingHazardNeverMass hazard) -
          ∑' t, quittingHazardStopMass hazard t * (C - value (some t)) := by
      have h1 : ∑' t, (C * quittingHazardStopMass hazard t -
          quittingHazardStopMass hazard t * (C - value (some t)))
          = (∑' t, C * quittingHazardStopMass hazard t) -
            ∑' t, quittingHazardStopMass hazard t * (C - value (some t)) :=
        (hsum_stop.mul_left C).tsum_sub hf
      have h2 : (∑' t, C * quittingHazardStopMass hazard t)
          = C * (1 - quittingHazardNeverMass hazard) := (hstop.mul_left C).tsum_eq
      rw [← h2, ← h1]
      exact tsum_congr (fun t => (hcongr t).symm)
    have hCE : C - expect (quittingHazardStoppingLaw hazard) value
        = quittingHazardNeverMass hazard * (C - value none) +
          ∑' t, quittingHazardStopMass hazard t * (C - value (some t)) := by
      rw [hE, htv]
      ring
    have hFle : ∑' t, quittingHazardStopMass hazard t * (C - value (some t))
        ≤ Δ / 2 * (1 - quittingHazardNeverMass hazard) +
          2 * M * ∑' t, quittingHazardStopMass hazard t * ind (some t) := by
      have hrhs : Summable (fun t => Δ / 2 * quittingHazardStopMass hazard t +
          2 * M * (quittingHazardStopMass hazard t * ind (some t))) :=
        (hsum_stop.mul_left (Δ / 2)).add (hgsum.mul_left (2 * M))
      have hle : ∀ t, quittingHazardStopMass hazard t * (C - value (some t))
          ≤ Δ / 2 * quittingHazardStopMass hazard t +
            2 * M * (quittingHazardStopMass hazard t * ind (some t)) := by
        intro t
        linarith [mul_le_mul_of_nonneg_left (hpt (some t)) (hstop_nonneg t)]
      have h2 := hf.tsum_le_tsum hle hrhs
      have h3 : ∑' t, (Δ / 2 * quittingHazardStopMass hazard t +
          2 * M * (quittingHazardStopMass hazard t * ind (some t)))
          = Δ / 2 * (1 - quittingHazardNeverMass hazard) +
            2 * M * ∑' t, quittingHazardStopMass hazard t * ind (some t) := by
        rw [(hsum_stop.mul_left (Δ / 2)).tsum_add (hgsum.mul_left (2 * M)),
          tsum_mul_left, tsum_mul_left, hstop.tsum_eq]
      rw [h3] at h2
      exact h2
    have hnone_bd : quittingHazardNeverMass hazard * (C - value none)
        ≤ quittingHazardNeverMass hazard * (Δ / 2 + 2 * M * ind none) :=
      mul_le_mul_of_nonneg_left (hpt none) hnever
    rw [hB]
    linarith [hgap, hCE, hFle, hnone_bd]

/-- Earliest supported bad stopping time with a survival floor: either the bad
set is carried by the never-stopping branch alone, or there is a least
supported bad stopping time `n`, and the bad mass is at most the survival
probability through `n`. -/
theorem quittingStoppingLaw_exists_leastBad_survival_lowerBound
    (hazard : ℕ → PMF Bool) (P : Option ℕ → Prop) [DecidablePred P] :
    ((expect (quittingHazardStoppingLaw hazard)
        (fun choice => if P choice then 1 else 0) ≤
          quittingHazardNeverMass hazard) ∧
      ∀ n, P (some n) → quittingHazardStopMass hazard n = 0) ∨
    ∃ n, P (some n) ∧ 0 < quittingHazardStopMass hazard n ∧
      (∀ m, m < n → P (some m) → quittingHazardStopMass hazard m = 0) ∧
      expect (quittingHazardStoppingLaw hazard)
          (fun choice => if P choice then 1 else 0) ≤
        quittingHazardSurvival hazard n := by
  set ind : Option ℕ → ℝ := fun choice => if P choice then 1 else 0 with hind
  have hind_nonneg : ∀ q, 0 ≤ ind q := by
    intro q
    simp only [hind]
    split <;> norm_num
  have hind_le_one : ∀ q, ind q ≤ 1 := by
    intro q
    simp only [hind]
    split <;> norm_num
  have hind_abs : ∀ q, |ind q| ≤ 1 := by
    intro q
    rw [abs_of_nonneg (hind_nonneg q)]
    exact hind_le_one q
  have hB := quittingHazardStoppingLaw_expect hazard ind hind_abs
  have hstop := hasSum_quittingHazardStopMass hazard
  have hsum_stop : Summable (quittingHazardStopMass hazard) := hstop.summable
  have hstop_nonneg := quittingHazardStopMass_nonneg hazard
  have hnever : 0 ≤ quittingHazardNeverMass hazard := quittingHazardNeverMass_nonneg hazard
  have hgsum : Summable (fun t => quittingHazardStopMass hazard t * ind (some t)) := by
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (hstop_nonneg t) (hind_nonneg _))
      (fun t => ?_) hsum_stop
    calc quittingHazardStopMass hazard t * ind (some t)
        ≤ quittingHazardStopMass hazard t * 1 :=
          mul_le_mul_of_nonneg_left (hind_le_one _) (hstop_nonneg t)
      _ = quittingHazardStopMass hazard t := mul_one _
  have hnone_bd : quittingHazardNeverMass hazard * ind none
      ≤ quittingHazardNeverMass hazard * 1 :=
    mul_le_mul_of_nonneg_left (hind_le_one none) hnever
  by_cases hex : ∃ n, P (some n) ∧ 0 < quittingHazardStopMass hazard n
  · right
    have hmin : ∀ m, m < Nat.find hex → P (some m) → quittingHazardStopMass hazard m = 0 := by
      intro m hm hPm
      have h := Nat.find_min hex hm
      exact le_antisymm (not_lt.1 (not_and.1 h hPm)) (hstop_nonneg m)
    obtain ⟨hPn, hposn⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, hPn, hposn, hmin, ?_⟩
    have hbound : ∀ t, quittingHazardStopMass hazard t * ind (some t)
        ≤ (if Nat.find hex ≤ t then quittingHazardStopMass hazard t else 0) := by
      intro t
      by_cases ht : Nat.find hex ≤ t
      · rw [if_pos ht]
        calc quittingHazardStopMass hazard t * ind (some t)
            ≤ quittingHazardStopMass hazard t * 1 :=
              mul_le_mul_of_nonneg_left (hind_le_one _) (hstop_nonneg t)
          _ = quittingHazardStopMass hazard t := mul_one _
      · rw [if_neg ht]
        have hlt : t < Nat.find hex := not_le.1 ht
        by_cases hp : P (some t)
        · rw [hmin t hlt hp]
          simp
        · have h0 : ind (some t) = 0 := by
            simp only [hind]
            simp [hp]
          rw [h0]
          simp
    have hfin : HasSum
        (fun t => if t < Nat.find hex then quittingHazardStopMass hazard t else 0)
        (∑ t ∈ Finset.range (Nat.find hex),
          (if t < Nat.find hex then quittingHazardStopMass hazard t else 0)) := by
      refine hasSum_sum_of_ne_finset_zero ?_
      intro b hb
      simp only [Finset.mem_range] at hb
      simp [hb]
    have hsumfin : (∑ t ∈ Finset.range (Nat.find hex),
        (if t < Nat.find hex then quittingHazardStopMass hazard t else 0))
        = ∑ t ∈ Finset.range (Nat.find hex), quittingHazardStopMass hazard t := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      simp only [Finset.mem_range] at ht
      rw [if_pos ht]
    rw [hsumfin] at hfin
    have htailc : ∀ t, quittingHazardStopMass hazard t -
        (if t < Nat.find hex then quittingHazardStopMass hazard t else 0)
        = (if Nat.find hex ≤ t then quittingHazardStopMass hazard t else 0) := by
      intro t
      by_cases ht : Nat.find hex ≤ t
      · rw [if_pos ht, if_neg (not_lt.2 ht)]
        ring
      · rw [if_neg ht, if_pos (not_le.1 ht)]
        ring
    have htail : HasSum
        (fun t => if Nat.find hex ≤ t then quittingHazardStopMass hazard t else 0)
        ((1 - quittingHazardNeverMass hazard) -
          ∑ t ∈ Finset.range (Nat.find hex), quittingHazardStopMass hazard t) := by
      simpa only [htailc] using hstop.sub hfin
    have htailval : ∑' t, (if Nat.find hex ≤ t then quittingHazardStopMass hazard t else 0)
        = quittingHazardSurvival hazard (Nat.find hex) - quittingHazardNeverMass hazard := by
      rw [htail.tsum_eq, sum_quittingHazardStopMass hazard (Nat.find hex)]
      ring
    have hGle : ∑' t, quittingHazardStopMass hazard t * ind (some t)
        ≤ quittingHazardSurvival hazard (Nat.find hex) - quittingHazardNeverMass hazard := by
      rw [← htailval]
      exact hgsum.tsum_le_tsum hbound htail.summable
    rw [hB]
    linarith
  · left
    have hzero : ∀ n, P (some n) → quittingHazardStopMass hazard n = 0 := by
      intro n hn
      refine le_antisymm (not_lt.1 (fun hpos => hex ⟨n, hn, hpos⟩)) (hstop_nonneg n)
    refine ⟨?_, hzero⟩
    have hterm : ∀ t, quittingHazardStopMass hazard t * ind (some t) = 0 := by
      intro t
      by_cases hp : P (some t)
      · rw [hzero t hp]
        ring
      · have h0 : ind (some t) = 0 := by
          simp only [hind]
          simp [hp]
        rw [h0]
        ring
    rw [hB, tsum_congr hterm, tsum_zero]
    linarith

/-- With no supported bad stopping time, the bad mass is under every survival
level. -/
theorem quittingStoppingLaw_badMass_le_survival_of_noFiniteBad
    (hazard : ℕ → PMF Bool) (P : Option ℕ → Prop) [DecidablePred P]
    (hnone : ∀ n, P (some n) → quittingHazardStopMass hazard n = 0) (cutoff : ℕ) :
    expect (quittingHazardStoppingLaw hazard)
        (fun choice => if P choice then 1 else 0) ≤
      quittingHazardSurvival hazard cutoff := by
  rcases quittingStoppingLaw_exists_leastBad_survival_lowerBound hazard P with
    ⟨hle, -⟩ | ⟨n, hPn, hposn, -, -⟩
  · exact hle.trans (quittingHazardNeverMass_le_survival hazard cutoff)
  · rw [hnone n hPn] at hposn
    exact absurd hposn (lt_irrefl 0)

end GameTheory
