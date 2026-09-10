import MathUE.Topology.KuhnSimplexGeometry

/-! # Coordinate-floor refinement of Kuhn simplices -/

noncomputable section

namespace Math

/-- Divide a coordinate at resolution `p * k` by `k`. -/
def kuhnFloorCoordinate (p k : ℕ) : Fin (p * k + 1) → Fin (p + 1) :=
  fun value ↦ ⟨value.1 / k, by
    apply Nat.lt_succ_iff.2
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using Nat.le_of_lt_succ value.2⟩

@[simp] theorem kuhnFloorCoordinate_val (p k : ℕ) (value : Fin (p * k + 1)) :
    (kuhnFloorCoordinate p k value).1 = value.1 / k := rfl

@[simp] theorem kuhnFloorCoordinate_zero (p k : ℕ) :
    kuhnFloorCoordinate p k 0 = 0 := by
  apply Fin.val_injective
  simp [kuhnFloorCoordinate]

@[simp] theorem kuhnFloorCoordinate_last (p k : ℕ) (hk : 0 < k) :
    kuhnFloorCoordinate p k (Fin.last (p * k)) = Fin.last p := by
  apply Fin.val_injective
  change p * k / k = p
  simpa [Nat.mul_comm] using Nat.mul_div_right p hk

theorem kuhnFloorCoordinate_mono (p k : ℕ) :
    Monotone (kuhnFloorCoordinate p k) := by
  intro first second hle
  exact Fin.mk_le_mk.2 (Nat.div_le_div_right (Fin.mk_le_mk.1 hle))

/-- If a unit fine-grid edge changes its quotient, its lower endpoint is one
less than the next multiple of the refinement factor. -/
theorem eq_mul_div_add_one_sub_one_of_succ_div_ne
    {value k : ℕ} (hk : 0 < k) (hchange : (value + 1) / k ≠ value / k) :
    value = k * (value / k + 1) - 1 := by
  have hdvd : k ∣ value + 1 := by
    by_contra hnot
    exact hchange (Nat.succ_div_of_not_dvd hnot)
  have hquotient : (value + 1) / k = value / k + 1 :=
    Nat.succ_div_of_dvd hdvd
  have hfactor : value + 1 = ((value + 1) / k) * k :=
    (Nat.div_eq_iff_eq_mul_left hk hdvd).1 rfl
  rw [hquotient] at hfactor
  rw [Nat.mul_comm] at hfactor
  omega

/-- Coordinate-floor refinement between compatible cubes. -/
def kuhnFloorVertex (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) : fine.G → coarse.G :=
  fun vertex who ↦ kuhnFloorCoordinate coarse.p k
    (Fin.cast (congrArg (fun resolution ↦ resolution + 1) hp)
      (vertex (Fin.cast hn.symm who)))

@[simp] theorem kuhnFloorVertex_val (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k)
    (vertex : fine.G) (who : Fin coarse.n) :
    (kuhnFloorVertex fine coarse k hn hp vertex who).1 =
      (vertex (Fin.cast hn.symm who)).1 / k := by
  simp [kuhnFloorVertex]

/-- Rounded images of any fine simplex form a coarse simplex when distinct. -/
theorem simplex_kuhnFloorVertex_of_injective
    {fine coarse : SpernerCube} {k m : ℕ}
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
    (vertices : Fin (m + 1) → fine.G) (hs : simplex fine m vertices)
    (hinjective : Function.Injective (fun index ↦
      kuhnFloorVertex fine coarse k hn hp (vertices index))) :
    simplex coarse m (fun index ↦
      kuhnFloorVertex fine coarse k hn hp (vertices index)) := by
  apply simplex_of_step_le _ hinjective
  · intro index who
    simp only [kuhnFloorVertex_val]
    exact Nat.div_le_div_right
      (spernerSimplex_step_le hs index (Fin.cast hn.symm who))
  · intro who
    have hwidth := spernerSimplex_val_le_succ hs (Fin.last m) 0
      (Fin.cast hn.symm who)
    have hroom := Nat.lt_mul_div_succ
      (vertices 0 (Fin.cast hn.symm who)).1 hk
    have hmul : (vertices (Fin.last m) (Fin.cast hn.symm who)).1 ≤
        k * ((vertices 0 (Fin.cast hn.symm who)).1 / k + 1) := by
      omega
    simp only [kuhnFloorVertex_val]
    exact Nat.div_le_of_le_mul hmul

end Math
