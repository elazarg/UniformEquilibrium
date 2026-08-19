import Sorin1986

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

abbrev JointAction (G : FiniteStageGame) := ∀ who, G.Action who
abbrev PublicHistory (G : FiniteStageGame) (t : ℕ) := Fin t → JointAction G
abbrev History (G : FiniteStageGame) := Σ t, PublicHistory G t
abbrev UnitInterval := Set.Icc (0 : ℝ) 1

def emptyHistory (G : FiniteStageGame) : History G :=
  ⟨0, fun k => k.elim0⟩

def snocHistory {G : FiniteStageGame} (h : History G) (a : JointAction G) : History G :=
  ⟨h.1 + 1, Fin.snoc h.2 a⟩

abbrev RawRealizationPlan (G : FiniteStageGame) (who : G.Player) :=
  (History G → UnitInterval) ×
    (History G → G.Action who → UnitInterval)

def RawRealizationPlan.Valid {G : FiniteStageGame} {who : G.Player}
    (plan : RawRealizationPlan G who) : Prop :=
  (plan.1 (emptyHistory G) : ℝ) = 1 ∧
    (∀ h, ∑ a, (plan.2 h a : ℝ) = (plan.1 h : ℝ)) ∧
      ∀ h a, (plan.1 (snocHistory h a) : ℝ) =
        (plan.2 h (a who) : ℝ)

abbrev RealizationPlan (G : FiniteStageGame) (who : G.Player) :=
  {plan : RawRealizationPlan G who // plan.Valid}

private theorem validSet_isClosed (G : FiniteStageGame) (who : G.Player) :
    IsClosed {plan : RawRealizationPlan G who | plan.Valid} := by
  let root : Set (RawRealizationPlan G who) :=
    {plan | (plan.1 (emptyHistory G) : ℝ) = 1}
  let flow : Set (RawRealizationPlan G who) :=
    {plan | ∀ h, ∑ a, (plan.2 h a : ℝ) = (plan.1 h : ℝ)}
  let successor : Set (RawRealizationPlan G who) :=
    {plan | ∀ h a, (plan.1 (snocHistory h a) : ℝ) =
      (plan.2 h (a who) : ℝ)}
  have hroot : IsClosed root := by
    apply isClosed_eq
    · fun_prop
    · fun_prop
  have hflow : IsClosed flow := by
    rw [show flow = ⋂ h, {plan | ∑ a, (plan.2 h a : ℝ) =
        (plan.1 h : ℝ)} by
      ext plan
      simp [flow]]
    exact isClosed_iInter fun h => isClosed_eq (by fun_prop) (by fun_prop)
  have hsuccessor : IsClosed successor := by
    rw [show successor = ⋂ h, ⋂ a,
        {plan | (plan.1 (snocHistory h a) : ℝ) =
          (plan.2 h (a who) : ℝ)} by
      ext plan
      simp [successor]]
    exact isClosed_iInter fun h => isClosed_iInter fun a =>
      isClosed_eq (by fun_prop) (by fun_prop)
  have hset : {plan : RawRealizationPlan G who | plan.Valid} =
      root ∩ (flow ∩ successor) := by
    ext plan
    simp [RawRealizationPlan.Valid, root, flow, successor]
  rw [hset]
  exact hroot.inter (hflow.inter hsuccessor)

instance {G : FiniteStageGame} {who : G.Player} :
    CompactSpace (RealizationPlan G who) :=
  isCompact_iff_compactSpace.mp (validSet_isClosed G who).isCompact

def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

@[simp] theorem clamp01_zero : clamp01 0 = 0 := by simp [clamp01]
@[simp] theorem clamp01_one : clamp01 1 = 1 := by simp [clamp01]

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := by simp [clamp01]
theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := by simp [clamp01]

@[fun_prop] theorem continuous_clamp01 : Continuous clamp01 := by
  simpa [clamp01] using
    (continuous_const.max (continuous_const.min continuous_id) :
      Continuous fun t : ℝ => max 0 (min 1 t))

def intervalMix (t : ℝ) (x y : UnitInterval) : UnitInterval :=
  ⟨clamp01 t * x + (1 - clamp01 t) * y, by
    have hc0 : 0 ≤ clamp01 t := clamp01_nonneg t
    have hc1 : clamp01 t ≤ 1 := clamp01_le_one t
    constructor
    · exact add_nonneg (mul_nonneg hc0 x.2.1)
        (mul_nonneg (sub_nonneg.mpr hc1) y.2.1)
    · have hx := mul_le_mul_of_nonneg_left x.2.2 hc0
      have hy := mul_le_mul_of_nonneg_left y.2.2 (sub_nonneg.mpr hc1)
      nlinarith⟩

@[simp] theorem intervalMix_zero (x y : UnitInterval) :
    intervalMix 0 x y = y := by
  ext
  simp [intervalMix]

@[simp] theorem intervalMix_one (x y : UnitInterval) :
    intervalMix 1 x y = x := by
  ext
  simp [intervalMix]

@[fun_prop] theorem continuous_intervalMix :
    Continuous fun p : ℝ × (UnitInterval × UnitInterval) =>
      intervalMix p.1 p.2.1 p.2.2 := by
  apply Continuous.subtype_mk
  fun_prop

def RawRealizationPlan.mix {G : FiniteStageGame} {who : G.Player}
    (t : ℝ) (x y : RawRealizationPlan G who) : RawRealizationPlan G who :=
  (fun h => intervalMix t (x.1 h) (y.1 h),
    fun h a => intervalMix t (x.2 h a) (y.2 h a))

private theorem RawRealizationPlan.mix_valid
    {G : FiniteStageGame} {who : G.Player}
    (t : ℝ) {x y : RawRealizationPlan G who}
    (hx : x.Valid) (hy : y.Valid) :
    (x.mix t y).Valid := by
  constructor
  · simp [RawRealizationPlan.mix, intervalMix, hx.1, hy.1]
  constructor
  · intro h
    simp only [RawRealizationPlan.mix, intervalMix, Subtype.coe_mk]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hx.2.1 h, hy.2.1 h]
  · intro h a
    simp only [RawRealizationPlan.mix, intervalMix, Subtype.coe_mk]
    rw [hx.2.2 h a, hy.2.2 h a]

def RealizationPlan.mix {G : FiniteStageGame} {who : G.Player}
    (t : ℝ) (x y : RealizationPlan G who) : RealizationPlan G who :=
  ⟨x.1.mix t y.1, RawRealizationPlan.mix_valid t x.2 y.2⟩

@[simp] theorem RealizationPlan.mix_zero
    {G : FiniteStageGame} {who : G.Player}
    (x y : RealizationPlan G who) :
    RealizationPlan.mix 0 x y = y := by
  apply Subtype.ext
  apply Prod.ext <;> funext h
  · simp [RealizationPlan.mix, RawRealizationPlan.mix]
  · funext a
    simp [RealizationPlan.mix, RawRealizationPlan.mix]

@[simp] theorem RealizationPlan.mix_one
    {G : FiniteStageGame} {who : G.Player}
    (x y : RealizationPlan G who) :
    RealizationPlan.mix 1 x y = x := by
  apply Subtype.ext
  apply Prod.ext <;> funext h
  · simp [RealizationPlan.mix, RawRealizationPlan.mix]
  · funext a
    simp [RealizationPlan.mix, RawRealizationPlan.mix]

@[fun_prop] theorem RealizationPlan.mix_continuous
    (G : FiniteStageGame) (who : G.Player) :
    Continuous fun p : ℝ × (RealizationPlan G who × RealizationPlan G who) =>
      RealizationPlan.mix p.1 p.2.1 p.2.2 := by
  apply Continuous.subtype_mk
  apply Continuous.prod_mk
  · fun_prop
  · fun_prop

end SequenceForm

end Literature.Sorin1986
