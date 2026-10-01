import MathUE.Analysis.LowerBoxBoundarySmoothDrift
import UniformEquilibrium.Quitting.Projective.FullExactRootPotentialFaceDrift
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair

/-! # Every minimum of a full exact-root potential is above all own singletons

The exact root at an arbitrary minimizing annotation is produced by finite
Nash existence. One-sided minimum derivatives suffice even at upper box faces.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every exact root at a global boxed minimum has zero absorption. -/
theorem IsQuittingFullExactRootPotential.minimum_exactRoot_absorption_eq_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (point : Payoff ι) (hpoint : ∀ who, |point who| ≤ bound)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward point 0 root) :
    quittingRootAbsorptionMass root = 0 := by
  have hsuccessor : quittingRootSuccessorPayoff reward point root ∈
      Set.Icc (fun _ => -bound) (fun _ => bound) := by
    constructor <;> intro who
    · exact (abs_le.mp
        (abs_quittingRootSuccessorPayoff_le_bound reward point root who hreward hpoint)).1
    · exact (abs_le.mp
        (abs_quittingRootSuccessorPayoff_le_bound reward point root who hreward hpoint)).2
  have hminimum := hmin hsuccessor
  change potential point ≤ potential (quittingRootSuccessorPayoff reward point root)
    at hminimum
  have hdrift := hpotential point hpoint root hnash
  have hnonneg := quittingRootAbsorptionMass_nonneg root
  linarith

/-- Finite Nash existence and zero absorption localize every minimum weakly
above its own singleton rewards, with no differentiability assumption. -/
theorem IsQuittingFullExactRootPotential.minimum_singleton_le
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (point : Payoff ι) (hpoint : ∀ who, |point who| ≤ bound)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point) :
    ∀ who, quittingSoloReward reward who who ≤ point who := by
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) point
  have habsorption := hpotential.minimum_exactRoot_absorption_eq_zero
    hreward point hpoint hmin root hnash
  have hcontinue : quittingStationaryContinueMass root = 1 := by
    unfold quittingRootAbsorptionMass at habsorption
    linarith
  have hroot : root = quittingAllContinueRoot := by
    funext who
    exact eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who
  rw [hroot] at hnash
  intro who
  rw [quittingSoloReward_self]
  exact (isZeroQuittingRootNash_allContinue_iff_singleton_le reward point).mp hnash who

/-- Every given global boxed minimum is strictly above every own singleton.
Only a derivative at that minimum is needed; the minimum may be on upper faces. -/
theorem IsQuittingFullExactRootPotential.minimum_above_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (point : Payoff ι) (hpoint : ∀ who, |point who| ≤ bound)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    ∀ who, quittingSoloReward reward who who < point who := by
  have hrewardBox : ∀ terminal who, |reward terminal who| ≤ bound :=
    fun terminal who => (hreward terminal who).trans hbound.le
  have hlower := hpotential.minimum_singleton_le hrewardBox point hpoint hmin
  intro owner
  apply lt_of_le_of_ne (hlower owner)
  intro heq
  have hface := hpotential.singletonFace_drift hreward hbound point owner
    (fun who => ⟨hlower who, (le_abs_self _).trans (hpoint who)⟩)
    heq.symm derivative hdiff
  have hlocal : IsLocalMinOn potential
      (Set.Icc (fun _ => -bound) (fun _ => bound)) point :=
    Filter.mem_of_superset self_mem_nhdsWithin hmin
  have hsolo : quittingSoloReward reward owner ∈
      Set.Icc (fun _ => -bound) (fun _ => bound) := by
    constructor <;> intro who
    · exact (abs_le.mp (hrewardBox (quittingSingletonTerminal owner) who)).1
    · exact (abs_le.mp (hrewardBox (quittingSingletonTerminal owner) who)).2
  have hpointMem : point ∈ Set.Icc (fun _ => -bound) (fun _ => bound) := by
    exact ⟨fun who => (abs_le.mp (hpoint who)).1,
      fun who => (abs_le.mp (hpoint who)).2⟩
  have hnonneg : 0 ≤ derivative (quittingSoloReward reward owner - point) :=
    hlocal.hasFDerivWithinAt_nonneg hdiff.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset
        ((convex_Icc (fun _ : ι => -bound) (fun _ => bound)).segment_subset
          hpointMem hsolo))
  have hneg : derivative (quittingSoloReward reward owner - point) =
      -derivative (point - quittingSoloReward reward owner) := by
    rw [← map_neg, neg_sub]
  rw [hneg] at hnonneg
  linarith

/-- Regularity on the upper singleton rectangle is sufficient for the same
arbitrary-minimum location theorem. -/
theorem IsQuittingFullExactRootPotential.minimum_above_singleton_of_differentiable
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point)
    (point : Payoff ι) (hpoint : ∀ who, |point who| ≤ bound)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point) :
    ∀ who, quittingSoloReward reward who who < point who := by
  have hlower := hpotential.minimum_singleton_le
    (fun terminal who => (hreward terminal who).trans hbound.le) point hpoint hmin
  have hpointC : point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound) := ⟨hlower, fun who => (le_abs_self _).trans (hpoint who)⟩
  exact hpotential.minimum_above_singleton hreward hbound point hpoint hmin
    (fderiv ℝ potential point) (hdiff point hpointC).hasFDerivAt

/-- In nonempty finite dimension the least own-singleton gap of every minimum
is strictly positive. -/
theorem IsQuittingFullExactRootPotential.minimum_singletonGap_pos [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (point : Payoff ι) (hpoint : ∀ who, |point who| ≤ bound)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point)
    (derivative : Payoff ι →L[ℝ] ℝ)
    (hdiff : HasFDerivAt potential derivative point) :
    0 < Finset.univ.inf' Finset.univ_nonempty
      (fun who => point who - quittingSoloReward reward who who) := by
  apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
  intro who _
  exact sub_pos.mpr (hpotential.minimum_above_singleton
    hreward hbound point hpoint hmin derivative hdiff who)

/-- Continuity on the full box internally produces an attained minimum; the
location conclusion concerns its actual annotation for the same potential. -/
theorem IsQuittingFullExactRootPotential.exists_minimum_above_singleton
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point) :
    ∃ point, (∀ who, |point who| ≤ bound) ∧
      IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point ∧
      (∀ who, quittingSoloReward reward who who < point who) := by
  have hzero : (0 : Payoff ι) ∈ Set.Icc (fun _ => -bound) (fun _ => bound) := by
    have hboundNonneg : ∀ who : ι, 0 ≤ bound := fun who =>
      ((abs_nonneg (quittingSoloReward reward who who)).trans
        (hreward (quittingSingletonTerminal who) who)).trans hbound.le
    exact ⟨fun who => neg_nonpos.mpr (hboundNonneg who), hboundNonneg⟩
  obtain ⟨point, hpoint, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨0, hzero⟩ hcontinuous
  have hbox : ∀ who, |point who| ≤ bound :=
    fun who => abs_le.mpr ⟨hpoint.1 who, hpoint.2 who⟩
  exact ⟨point, hbox, hmin, hpotential.minimum_above_singleton_of_differentiable
    hreward hbound hdiff point hbox hmin⟩

/-- Every full-box minimum has value strictly below every point of the lower
singleton boundary. The compared point is arbitrary, not a chosen face minimum. -/
theorem IsQuittingFullExactRootPotential.minimum_lt_lowerBoxBoundary
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point)
    (point : Payoff ι)
    (hmin : IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point)
    (boundary : Payoff ι)
    (hboundary : boundary ∈ Math.lowerBoxBoundary
      (fun who => quittingSoloReward reward who who) (fun _ => bound)) :
    potential point < potential boundary := by
  have hboundaryBox : ∀ who, |boundary who| ≤ bound := by
    intro who
    apply abs_le.mpr
    exact ⟨(neg_le_of_abs_le ((hreward (quittingSingletonTerminal who) who).trans
      hbound.le)).trans (hboundary.1.1 who), hboundary.1.2 who⟩
  have hboundaryMem : boundary ∈ Set.Icc (fun _ => -bound) (fun _ => bound) :=
    ⟨fun who => (abs_le.mp (hboundaryBox who)).1,
      fun who => (abs_le.mp (hboundaryBox who)).2⟩
  apply lt_of_le_of_ne (hmin hboundaryMem)
  intro heq
  have hboundaryMin : IsMinOn potential
      (Set.Icc (fun _ => -bound) (fun _ => bound)) boundary := by
    intro target htarget
    rw [← heq]
    exact hmin htarget
  obtain ⟨owner, howner⟩ := hboundary.2
  have habove := hpotential.minimum_above_singleton_of_differentiable
    hreward hbound hdiff boundary hboundaryBox hboundaryMin owner
  rw [howner] at habove
  exact (lt_irrefl _) habove

/-- Both relevant minima are attained internally, with the full-box minimizer
also minimizing the upper singleton rectangle and strictly beating its boundary. -/
theorem IsQuittingFullExactRootPotential.exists_minima_strict_gap [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {M bound : ℝ} (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hbound : M < bound) {potential : Payoff ι → ℝ}
    (hpotential : IsQuittingFullExactRootPotential reward bound potential)
    (hcontinuous : ContinuousOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)))
    (hdiff : ∀ point ∈ Set.Icc (fun who => quittingSoloReward reward who who)
      (fun _ => bound), DifferentiableAt ℝ potential point) :
    ∃ point boundary,
      point ∈ Set.Icc (fun who => quittingSoloReward reward who who) (fun _ => bound) ∧
      boundary ∈ Math.lowerBoxBoundary
        (fun who => quittingSoloReward reward who who) (fun _ => bound) ∧
      IsMinOn potential (Set.Icc (fun _ => -bound) (fun _ => bound)) point ∧
      IsMinOn potential (Set.Icc (fun who => quittingSoloReward reward who who)
        (fun _ => bound)) point ∧
      IsMinOn potential (Math.lowerBoxBoundary
        (fun who => quittingSoloReward reward who who) (fun _ => bound)) boundary ∧
      potential point < potential boundary := by
  let lower : Payoff ι := fun who => quittingSoloReward reward who who
  let upper : Payoff ι := fun _ => bound
  have hlower : lower ≤ upper := fun who =>
    (le_abs_self _).trans ((hreward (quittingSingletonTerminal who) who).trans hbound.le)
  have hsubset : Set.Icc lower upper ⊆
      Set.Icc (fun _ => -bound) (fun _ => bound) := by
    intro point hpoint
    refine ⟨fun who => ?_, hpoint.2⟩
    exact (neg_le_of_abs_le ((hreward (quittingSingletonTerminal who) who).trans
      hbound.le)).trans (hpoint.1 who)
  obtain ⟨point, hpointBox, hmin, habove⟩ :=
    hpotential.exists_minimum_above_singleton hreward hbound hcontinuous hdiff
  have hpoint : point ∈ Set.Icc lower upper :=
    ⟨fun who => (habove who).le, fun who => (le_abs_self _).trans (hpointBox who)⟩
  obtain ⟨boundary, hboundary, hboundaryMin⟩ :=
    (Math.isCompact_lowerBoxBoundary lower upper).exists_isMinOn
      (Math.lowerBoxBoundary_nonempty lower upper hlower)
      (hcontinuous.mono (fun _ hmem => hsubset hmem.1))
  exact ⟨point, boundary, hpoint, hboundary, hmin,
    fun target htarget => hmin (hsubset htarget), hboundaryMin,
    hpotential.minimum_lt_lowerBoxBoundary hreward hbound hdiff point hmin
      boundary hboundary⟩

end GameTheory
