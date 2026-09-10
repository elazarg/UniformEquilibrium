import MathUE.Topology.KuhnFloorRefinement

/-! # Geometry of noncollapsed top-simplex floor refinement -/

noncomputable section

namespace Math

/-- The fine coordinate over a coarse lower endpoint `base`, before or after
its unique unit step. -/
def kuhnLiftCoordinate (p k base : ℕ) (hk : 0 < k) (hbase : base + 1 ≤ p)
    (raised : Bool) : Fin (p * k + 1) :=
  ⟨k * (base + 1) - 1 + if raised then 1 else 0, by
    apply Nat.lt_succ_iff.2
    have hproduct : k * (base + 1) ≤ k * p := Nat.mul_le_mul_left k hbase
    have hcomm : k * p = p * k := Nat.mul_comm _ _
    cases raised
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (Nat.sub_le _ _).trans (hproduct.trans_eq hcomm)
    · simp only [↓reduceIte]
      rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero hk.ne' (Nat.succ_ne_zero base)))]
      exact hproduct.trans_eq hcomm⟩

@[simp] theorem kuhnFloorCoordinate_kuhnLiftCoordinate_false
    (p k base : ℕ) (hk : 0 < k) (hbase : base + 1 ≤ p) :
    kuhnFloorCoordinate p k (kuhnLiftCoordinate p k base hk hbase false) =
      ⟨base, by omega⟩ := by
  apply Fin.val_injective
  simp only [kuhnFloorCoordinate_val, kuhnLiftCoordinate, Bool.false_eq_true,
    ↓reduceIte, add_zero]
  have hpos : 0 < k * (base + 1) := Nat.mul_pos hk (Nat.zero_lt_succ base)
  apply Nat.div_eq_of_lt_le
  · apply Nat.le_sub_of_add_le
    simp only [Nat.mul_add, Nat.mul_one]
    rw [Nat.mul_comm base k]
    omega
  · have := Nat.sub_lt hpos (Nat.zero_lt_one)
    simpa [Nat.mul_comm] using this

@[simp] theorem kuhnFloorCoordinate_kuhnLiftCoordinate_true
    (p k base : ℕ) (hk : 0 < k) (hbase : base + 1 ≤ p) :
    kuhnFloorCoordinate p k (kuhnLiftCoordinate p k base hk hbase true) =
      ⟨base + 1, hbase.trans_lt (Nat.lt_succ_self p)⟩ := by
  apply Fin.val_injective
  simp only [kuhnFloorCoordinate_val, kuhnLiftCoordinate, ↓reduceIte]
  rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
    (Nat.mul_ne_zero hk.ne' (Nat.succ_ne_zero base)))]
  simpa [Nat.mul_comm] using Nat.mul_div_left (base + 1) hk

theorem spernerSimplex_initial_add_one_le_resolution
    {cube : SpernerCube} {vertices : Fin (cube.n + 1) → cube.G}
    (hs : simplex cube cube.n vertices) (who : Fin cube.n) :
    (vertices 0 who).1 + 1 ≤ cube.p := by
  let raise := spernerChainRaiseIndex hs rfl who
  have hvalue := spernerChain_val_eq_of_raiseIndex_lt hs rfl who
    (i := raise.succ) (Nat.lt_succ_self raise.1)
  have hbound := (vertices raise.succ who).2
  omega

/-- The canonical fine lift of a coarse top simplex. -/
def kuhnFloorSimplexLift (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
    (vertices : Fin (coarse.n + 1) → coarse.G)
    (hs : simplex coarse coarse.n vertices) : Fin (fine.n + 1) → fine.G :=
  fun index who ↦
    let coarseIndex : Fin (coarse.n + 1) :=
      Fin.cast (congrArg (fun dimension ↦ dimension + 1) hn) index
    let coarseWho : Fin coarse.n := Fin.cast hn who
    let base := (vertices 0 coarseWho).1
    let raised := decide ((spernerChainRaiseIndex hs rfl coarseWho).1 < coarseIndex.1)
    Fin.cast (congrArg (fun resolution ↦ resolution + 1) hp).symm
      (kuhnLiftCoordinate coarse.p k base hk
        (spernerSimplex_initial_add_one_le_resolution hs coarseWho) raised)

/-- Flooring the canonical lift returns the literal coarse vertex tuple. -/
theorem kuhnFloorVertex_kuhnFloorSimplexLift
    (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
    (vertices : Fin (coarse.n + 1) → coarse.G)
    (hs : simplex coarse coarse.n vertices) (index : Fin (fine.n + 1)) :
    kuhnFloorVertex fine coarse k hn hp
      (kuhnFloorSimplexLift fine coarse k hn hp hk vertices hs index) =
        vertices (Fin.cast (congrArg (fun dimension ↦ dimension + 1) hn) index) := by
  funext who
  apply Fin.val_injective
  simp only [kuhnFloorVertex_val, kuhnFloorSimplexLift, Fin.val_cast]
  let coarseIndex := Fin.cast (congrArg (fun dimension ↦ dimension + 1) hn) index
  have hwho : Fin.cast hn (Fin.cast hn.symm who) = who := by simp
  simp only [hwho]
  by_cases hraised :
      (spernerChainRaiseIndex hs rfl who).1 < index.1
  · rw [show decide
        ((spernerChainRaiseIndex hs rfl who).1 < index.1) = true by simp [hraised]]
    have hfloor := congrArg Fin.val
      (kuhnFloorCoordinate_kuhnLiftCoordinate_true coarse.p k
        (vertices 0 who).1 hk
        (spernerSimplex_initial_add_one_le_resolution hs who))
    simp only [kuhnFloorCoordinate_val] at hfloor
    rw [hfloor]
    exact (spernerChain_val_eq_of_raiseIndex_lt hs rfl who
      (i := coarseIndex) (by simpa [coarseIndex] using hraised)).symm
  · have hle : coarseIndex.1 ≤ (spernerChainRaiseIndex hs rfl who).1 := by
      simp only [coarseIndex, Fin.val_cast]
      omega
    rw [show decide
        ((spernerChainRaiseIndex hs rfl who).1 < index.1) = false by simp [hraised]]
    have hfloor := congrArg Fin.val
      (kuhnFloorCoordinate_kuhnLiftCoordinate_false coarse.p k
        (vertices 0 who).1 hk
        (spernerSimplex_initial_add_one_le_resolution hs who))
    simp only [kuhnFloorCoordinate_val] at hfloor
    rw [hfloor]
    exact (spernerChain_val_eq_of_le_raiseIndex hs rfl who hle).symm

/-- The canonical lift is a literal fine-grid top simplex. -/
theorem simplex_kuhnFloorSimplexLift
    (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
    (vertices : Fin (coarse.n + 1) → coarse.G)
    (hs : simplex coarse coarse.n vertices) :
    simplex fine fine.n (kuhnFloorSimplexLift fine coarse k hn hp hk vertices hs) := by
  apply simplex_of_step_le
  · intro first second heq
    have hfloor := congrArg (kuhnFloorVertex fine coarse k hn hp) heq
    rw [kuhnFloorVertex_kuhnFloorSimplexLift fine coarse k hn hp hk vertices hs,
      kuhnFloorVertex_kuhnFloorSimplexLift fine coarse k hn hp hk vertices hs] at hfloor
    have hindex := hs.1 hfloor
    exact Fin.cast_injective _ hindex
  · intro step who
    simp only [kuhnFloorSimplexLift, Fin.val_cast, kuhnLiftCoordinate]
    by_cases hbefore :
        (spernerChainRaiseIndex hs rfl (Fin.cast hn who)).1 < step.1
    · have hafter :
          (spernerChainRaiseIndex hs rfl (Fin.cast hn who)).1 < step.1 + 1 := by omega
      simp [hbefore, hafter]
    · by_cases hafter :
          (spernerChainRaiseIndex hs rfl (Fin.cast hn who)).1 < step.1 + 1
      · simp [hbefore, hafter]
      · simp [hbefore, hafter]
  · intro who
    simp only [kuhnFloorSimplexLift, Fin.val_cast, kuhnLiftCoordinate]
    have hzero : ¬(spernerChainRaiseIndex hs rfl (Fin.cast hn who)).1 < 0 := by omega
    have hlast :
        (spernerChainRaiseIndex hs rfl (Fin.cast hn who)).1 < fine.n := by
      calc
        _ < coarse.n := (spernerChainRaiseIndex hs rfl (Fin.cast hn who)).2
        _ = fine.n := hn.symm
    simp [hzero, hlast]

variable {fine coarse : SpernerCube} {k m : ℕ}
  (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
  (vertices : Fin (m + 1) → fine.G) (hs : simplex fine m vertices)
  (hm : m = fine.n)
  (hinjective : Function.Injective (fun index ↦
    kuhnFloorVertex fine coarse k hn hp (vertices index)))

include hk hs hm hinjective

omit hk in
private theorem floor_step_changes (step : Fin m) :
    (vertices step.succ (spernerChainStep hs hm step)).1 / k ≠
      (vertices step.castSucc (spernerChainStep hs hm step)).1 / k := by
  intro heq
  apply (Fin.castSucc_lt_succ (i := step)).ne
  apply hinjective
  funext who
  apply Fin.val_injective
  simp only [kuhnFloorVertex_val]
  let fineWho : Fin fine.n := Fin.cast hn.symm who
  by_cases hwho : fineWho = spernerChainStep hs hm step
  · simpa [fineWho, hwho] using heq.symm
  · have hfixed := spernerChainStep_eq_of_ne hs hm step hwho
    simp [fineWho, hfixed]

/-- Every step of a noncollapsed rounded top simplex crosses exactly one
refinement boundary, at the coordinate raised by the fine simplex. -/
theorem kuhnFloorVertex_step_base_eq (step : Fin m) :
    (vertices step.castSucc (spernerChainStep hs hm step)).1 =
      k * ((vertices step.castSucc (spernerChainStep hs hm step)).1 / k + 1) - 1 := by
  have hsucc := spernerChainStep_val_succ hs hm step
  apply eq_mul_div_add_one_sub_one_of_succ_div_ne hk
  simpa [hsucc] using floor_step_changes hn hp vertices hs hm hinjective step

omit hm in
private theorem coarseSimplex :
    simplex coarse m (fun index ↦
      kuhnFloorVertex fine coarse k hn hp (vertices index)) :=
  simplex_kuhnFloorVertex_of_injective hn hp hk vertices hs hinjective

/-- The rounded simplex raises the same coordinate at every chronological
step as the fine simplex, modulo the dimension identification. -/
theorem kuhnFloorVertex_spernerChainStep_eq (step : Fin m) :
    spernerChainStep
        (simplex_kuhnFloorVertex_of_injective hn hp hk vertices hs hinjective)
        (hm.trans hn) step =
      Fin.cast hn (spernerChainStep hs hm step) := by
  let roundedSimplex := coarseSimplex hn hp hk vertices hs hinjective
  symm
  apply (mem_spernerChainStepSet_iff
    roundedSimplex (hm.trans hn) step _).1
  rw [mem_spernerChainStepSet]
  simp only [kuhnFloorVertex_val]
  have hsucc := spernerChainStep_val_succ hs hm step
  have hchange := floor_step_changes hn hp vertices hs hm hinjective step
  have hchange' :
      ((vertices step.castSucc (spernerChainStep hs hm step)).1 + 1) / k ≠
        (vertices step.castSucc (spernerChainStep hs hm step)).1 / k := by
    simpa [hsucc] using hchange
  have hcast : Fin.cast hn.symm (Fin.cast hn (spernerChainStep hs hm step)) =
      spernerChainStep hs hm step := by simp
  simp only [hcast]
  rw [hsucc]
  exact Nat.lt_of_le_of_ne (Nat.div_le_div_right (Nat.le_add_right _ _))
    (Ne.symm hchange')

/-- The initial fine coordinate over a coarse base coordinate `b` is forced
to be `k * (b + 1) - 1`. -/
theorem kuhnFloorVertex_initial_base_eq (who : Fin fine.n) :
    (vertices 0 who).1 =
      k * ((kuhnFloorVertex fine coarse k hn hp (vertices 0)
        (Fin.cast hn who)).1 + 1) - 1 := by
  let step := spernerChainRaiseIndex hs hm who
  have hbase := spernerChain_val_eq_of_le_raiseIndex hs hm who
    (i := step.castSucc) (le_refl _)
  have hcross := kuhnFloorVertex_step_base_eq
    hn hp hk vertices hs hm hinjective step
  simp only [kuhnFloorVertex_val]
  have hcast : Fin.cast hn.symm (Fin.cast hn who) = who := by simp
  simp only [hcast]
  have hstep : spernerChainStep hs hm step = who := by
    simp [step]
  rw [hstep] at hcross
  rw [hbase] at hcross
  exact hcross

omit hk hs hm hinjective in
/-- The canonical lift is the unique fine top simplex with the prescribed
literal rounded vertex tuple. -/
theorem eq_kuhnFloorSimplexLift_of_floor_eq
    (fine coarse : SpernerCube) (k : ℕ)
    (hn : fine.n = coarse.n) (hp : fine.p = coarse.p * k) (hk : 0 < k)
    (coarseVertices : Fin (coarse.n + 1) → coarse.G)
    (hcoarse : simplex coarse coarse.n coarseVertices)
    (fineVertices : Fin (fine.n + 1) → fine.G)
    (hfine : simplex fine fine.n fineVertices)
    (hfloor : ∀ index, kuhnFloorVertex fine coarse k hn hp (fineVertices index) =
      coarseVertices (Fin.cast (congrArg (fun dimension ↦ dimension + 1) hn) index)) :
    fineVertices = kuhnFloorSimplexLift fine coarse k hn hp hk coarseVertices hcoarse := by
  let lift := kuhnFloorSimplexLift fine coarse k hn hp hk coarseVertices hcoarse
  have hlift : simplex fine fine.n lift :=
    simplex_kuhnFloorSimplexLift fine coarse k hn hp hk coarseVertices hcoarse
  have hinjective : Function.Injective (fun index ↦
      kuhnFloorVertex fine coarse k hn hp (fineVertices index)) := by
    intro first second heq
    change kuhnFloorVertex fine coarse k hn hp (fineVertices first) =
      kuhnFloorVertex fine coarse k hn hp (fineVertices second) at heq
    rw [hfloor first, hfloor second] at heq
    exact Fin.cast_injective _ (hcoarse.1 heq)
  funext index who
  apply Fin.val_injective
  have hinitial := kuhnFloorVertex_initial_base_eq
    hn hp hk fineVertices hfine rfl hinjective who
  have hliftFloor := kuhnFloorVertex_kuhnFloorSimplexLift
    fine coarse k hn hp hk coarseVertices hcoarse
  have hinitialFloor := congrArg (fun vertex ↦ (vertex (Fin.cast hn who)).1) (hfloor 0)
  simp only [kuhnFloorVertex_val, Fin.cast_zero] at hinitialFloor
  have hliftInitial : (lift 0 who).1 = (fineVertices 0 who).1 := by
    simp only [lift, kuhnFloorSimplexLift, Fin.val_cast, kuhnLiftCoordinate]
    simp
    rw [← hinitialFloor]
    exact hinitial.symm
  have hfineLow : (fineVertices 0 who).1 ≤ (fineVertices index who).1 :=
    spernerSimplex_val_le_of_le hfine (Fin.zero_le _) who
  have hfineHigh : (fineVertices index who).1 ≤ (fineVertices 0 who).1 + 1 :=
    spernerSimplex_val_le_succ hfine index 0 who
  have hliftLow : (lift 0 who).1 ≤ (lift index who).1 :=
    spernerSimplex_val_le_of_le hlift (Fin.zero_le _) who
  have hliftHigh : (lift index who).1 ≤ (lift 0 who).1 + 1 :=
    spernerSimplex_val_le_succ hlift index 0 who
  have hsameFloor : (fineVertices index who).1 / k = (lift index who).1 / k := by
    have hc := congrArg (fun vertex ↦ (vertex (Fin.cast hn who)).1) (hfloor index)
    have hl := congrArg (fun vertex ↦ (vertex (Fin.cast hn who)).1) (hliftFloor index)
    simp only [kuhnFloorVertex_val] at hc hl
    have hcast : Fin.cast hn.symm (Fin.cast hn who) = who := by simp
    simp only [hcast] at hc hl
    exact hc.trans hl.symm
  have hcross : ((fineVertices 0 who).1 + 1) / k ≠
      (fineVertices 0 who).1 / k := by
    let step := spernerChainRaiseIndex hfine rfl who
    have hchange := floor_step_changes hn hp fineVertices hfine rfl hinjective step
    have hbase := spernerChain_val_eq_of_le_raiseIndex hfine rfl who
      (i := step.castSucc) (le_refl _)
    have hsucc := spernerChainStep_val_succ hfine rfl step
    have hstep : spernerChainStep hfine rfl step = who := by simp [step]
    rw [hstep, hbase] at hsucc hchange
    simpa [hsucc] using hchange
  have hfi : (fineVertices index who).1 = (fineVertices 0 who).1 ∨
      (fineVertices index who).1 = (fineVertices 0 who).1 + 1 := by omega
  have hli : (lift index who).1 = (lift 0 who).1 ∨
      (lift index who).1 = (lift 0 who).1 + 1 := by omega
  change (fineVertices index who).1 = (lift index who).1
  rcases hfi with hfi | hfi <;> rcases hli with hli | hli
  · rw [hfi, hli, hliftInitial]
  · exfalso
    apply hcross
    calc
      ((fineVertices 0 who).1 + 1) / k = (lift index who).1 / k := by
        rw [hli, hliftInitial]
      _ = (fineVertices index who).1 / k := hsameFloor.symm
      _ = (fineVertices 0 who).1 / k := by rw [hfi]
  · exfalso
    apply hcross
    calc
      ((fineVertices 0 who).1 + 1) / k = (fineVertices index who).1 / k := by rw [hfi]
      _ = (lift index who).1 / k := hsameFloor
      _ = (fineVertices 0 who).1 / k := by rw [hli, hliftInitial]
  · rw [hfi, hli, hliftInitial]

end Math
