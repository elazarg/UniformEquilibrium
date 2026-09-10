import MathUE.Topology.KuhnFloorSimplexLift
import MathUE.Topology.KuhnSimplexOrientation
import FixedPointTheorems.cubical_sperner

/-! # Complete simplices under coordinate-floor label pullback -/

noncomputable section

namespace Math

/-- Refine a labeled cube by pulling its labels back along coordinate floor. -/
def floorPullbackSpernerCube (coarse : SpernerCube) (k : ℕ) (hk : 0 < k) :
    SpernerCube where
  n := coarse.n
  p := coarse.p * k
  RL vertex := coarse.RL (fun who ↦ kuhnFloorCoordinate coarse.p k (vertex who))
  rl_proper := by
    intro vertex
    refine ⟨(coarse.rl_proper _).1, fun who ↦ ⟨?_, ?_⟩⟩
    · intro hzero
      apply (coarse.rl_proper _).2 who |>.1
      simp [kuhnFloorCoordinate, hzero]
    · intro htop
      apply (coarse.rl_proper _).2 who |>.2
      have hvertex : vertex who = Fin.last (coarse.p * k) := Fin.val_injective htop
      simpa [hvertex] using congrArg Fin.val
        (kuhnFloorCoordinate_last coarse.p k hk)

@[simp] theorem floorPullbackSpernerCube_RL
    (coarse : SpernerCube) (k : ℕ) (hk : 0 < k)
    (vertex : (floorPullbackSpernerCube coarse k hk).G) :
    (floorPullbackSpernerCube coarse k hk).RL vertex =
      coarse.RL (kuhnFloorVertex (floorPullbackSpernerCube coarse k hk) coarse k
        rfl rfl vertex) := rfl

/-- Flooring a complete fine simplex gives a complete coarse simplex. -/
def floorCompleteSimplex
    (coarse : SpernerCube) (k : ℕ) (hk : 0 < k) :
    {vertices : Fin (coarse.n + 1) → (floorPullbackSpernerCube coarse k hk).G //
      complete_simplex (floorPullbackSpernerCube coarse k hk) coarse.n vertices} →
    {vertices : Fin (coarse.n + 1) → coarse.G //
      complete_simplex coarse coarse.n vertices} := fun fine ↦ by
  let rounded := fun index ↦ kuhnFloorVertex
    (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl (fine.1 index)
  have hinjective : Function.Injective rounded := by
    intro first second heq
    apply rl_inj_of_complete _ _ fine.2
    simpa only [floorPullbackSpernerCube_RL] using congrArg coarse.RL heq
  refine ⟨rounded, simplex_kuhnFloorVertex_of_injective
    (fine := floorPullbackSpernerCube coarse k hk) (coarse := coarse) rfl rfl hk
    fine.1 fine.2.1 hinjective, ?_⟩
  simpa only [rounded, floorPullbackSpernerCube_RL] using fine.2.2

/-- Canonically lift a complete coarse simplex to the pulled-back fine cube. -/
def liftCompleteSimplex
    (coarse : SpernerCube) (k : ℕ) (hk : 0 < k) :
    {vertices : Fin (coarse.n + 1) → coarse.G //
      complete_simplex coarse coarse.n vertices} →
    {vertices : Fin (coarse.n + 1) → (floorPullbackSpernerCube coarse k hk).G //
      complete_simplex (floorPullbackSpernerCube coarse k hk) coarse.n vertices} :=
  fun simplex ↦ ⟨kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk simplex.1 simplex.2.1,
    ⟨simplex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk
        simplex.1 simplex.2.1, by
      have hfun : (fun index ↦ coarse.RL (kuhnFloorVertex
          (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl
          (kuhnFloorSimplexLift (floorPullbackSpernerCube coarse k hk)
            coarse k rfl rfl hk simplex.1 simplex.2.1 index))) =
          fun index ↦ coarse.RL (simplex.1 index) := by
        funext index
        congr 1
        calc
          _ = simplex.1 (Fin.cast
              (congrArg (fun dimension ↦ dimension + 1)
                (rfl : (floorPullbackSpernerCube coarse k hk).n = coarse.n))
              index) := kuhnFloorVertex_kuhnFloorSimplexLift
                (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk
                simplex.1 simplex.2.1 index
          _ = simplex.1 index := by
            congr 1
      change Set.range (fun index ↦ coarse.RL (kuhnFloorVertex
        (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl
        (kuhnFloorSimplexLift (floorPullbackSpernerCube coarse k hk)
          coarse k rfl rfl hk simplex.1 simplex.2.1 index))) = _
      rw [hfun]
      exact simplex.2.2⟩⟩

/-- Complete coarse simplices are in literal bijection with complete simplices
of the floor-pulled fine labeling. -/
def completeSimplexFloorEquiv (coarse : SpernerCube) (k : ℕ) (hk : 0 < k) :
    {vertices : Fin (coarse.n + 1) → (floorPullbackSpernerCube coarse k hk).G //
      complete_simplex (floorPullbackSpernerCube coarse k hk) coarse.n vertices} ≃
    {vertices : Fin (coarse.n + 1) → coarse.G //
      complete_simplex coarse coarse.n vertices} where
  toFun := floorCompleteSimplex coarse k hk
  invFun := liftCompleteSimplex coarse k hk
  left_inv fine := by
    apply Subtype.ext
    symm
    apply eq_kuhnFloorSimplexLift_of_floor_eq
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk _
      (floorCompleteSimplex coarse k hk fine).2.1 fine.1 fine.2.1
    intro index
    rfl
  right_inv simplex := by
    apply Subtype.ext
    funext index
    exact kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk
      simplex.1 simplex.2.1 index

/-- Canonical lifting preserves the literal integer simplex determinant. -/
theorem kuhnFloorSimplexLift_determinant_eq
    (coarse : SpernerCube) (k : ℕ) (hk : 0 < k)
    (vertices : Fin (coarse.n + 1) → coarse.G)
    (hs : simplex coarse coarse.n vertices) :
    OrientedSimplexFacet.determinant (fun vertex coordinate =>
      ((kuhnFloorSimplexLift (floorPullbackSpernerCube coarse k hk) coarse k
        rfl rfl hk vertices hs vertex coordinate).val : ℤ)) =
    OrientedSimplexFacet.determinant (fun vertex coordinate =>
      ((vertices vertex coordinate).val : ℤ)) := by
  let lift := kuhnFloorSimplexLift
    (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk vertices hs
  have hlift := simplex_kuhnFloorSimplexLift
    (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk vertices hs
  rw [KuhnSimplex.determinant_eq_coordinateEquivalence_sign _ _ hlift,
    KuhnSimplex.determinant_eq_coordinateEquivalence_sign _ _ hs]
  apply congrArg (fun permutation : Equiv.Perm (Fin coarse.n) =>
    ((Equiv.Perm.sign permutation : ℤˣ) : ℤ))
  apply Equiv.ext
  intro step
  change spernerChainStep hlift rfl step = spernerChainStep hs rfl step
  have hinjective : Function.Injective (fun index ↦ kuhnFloorVertex
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl (lift index)) := by
    intro first second heq
    change kuhnFloorVertex (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl
      (lift first) = kuhnFloorVertex (floorPullbackSpernerCube coarse k hk)
        coarse k rfl rfl (lift second) at heq
    have hfirst := kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk vertices hs first
    have hsecond := kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk vertices hs second
    rw [hfirst, hsecond] at heq
    exact hs.1 heq
  have hstep := kuhnFloorVertex_spernerChainStep_eq
    (fine := floorPullbackSpernerCube coarse k hk) (coarse := coarse)
    rfl rfl hk lift hlift rfl hinjective step
  let rounded := fun index ↦ kuhnFloorVertex
    (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl (lift index)
  have hrounded : rounded = vertices := by
    funext index
    exact kuhnFloorVertex_kuhnFloorSimplexLift
      (floorPullbackSpernerCube coarse k hk) coarse k rfl rfl hk vertices hs index
  have hroundedSimplex := simplex_kuhnFloorVertex_of_injective
    (fine := floorPullbackSpernerCube coarse k hk) (coarse := coarse)
    rfl rfl hk lift hlift hinjective
  change spernerChainStep hroundedSimplex rfl step = _ at hstep
  change simplex coarse coarse.n rounded at hroundedSimplex
  change spernerChainStep hroundedSimplex rfl step = _ at hstep
  let fineCoordinate : Fin (floorPullbackSpernerCube coarse k hk).n :=
    spernerChainStep hlift rfl step
  let coordinate : Fin coarse.n := Fin.cast rfl fineCoordinate
  have hmemRounded : coordinate ∈ spernerChainStepSet rounded step :=
    (mem_spernerChainStepSet_iff hroundedSimplex rfl step coordinate).2 hstep.symm
  have hltRounded := mem_spernerChainStepSet.mp hmemRounded
  have hfirst := congrArg (fun vertex ↦ (vertex coordinate).1)
    (congrFun hrounded step.castSucc)
  have hsecond := congrArg (fun vertex ↦ (vertex coordinate).1)
    (congrFun hrounded step.succ)
  have hmemCoarse : coordinate ∈ spernerChainStepSet vertices step := by
    rw [mem_spernerChainStepSet]
    exact hfirst.symm.trans_lt (hltRounded.trans_eq hsecond)
  have hcoordinate :=
    (mem_spernerChainStepSet_iff hs rfl step coordinate).1 hmemCoarse
  apply Fin.ext
  simpa [coordinate, fineCoordinate] using congrArg Fin.val hcoordinate

end Math
