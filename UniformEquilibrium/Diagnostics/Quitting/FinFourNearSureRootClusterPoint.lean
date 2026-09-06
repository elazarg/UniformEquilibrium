import UniformEquilibrium.Diagnostics.Quitting.FinFourNearSureRootApproxSingletonBase

/-! # Universal cluster points of nearly-sure singleton-base roots -/

noncomputable section

namespace GameTheory

open Filter Math.ProbabilityMassFunction
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem continuous_rootFreeMixedPoint (free : Finset ι) :
    Continuous (fun simplex : QuittingRootSimplex ι ↦
      quittingRootFreeMixedPoint free (quittingRootOfSimplex simplex)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro who
  apply continuous_pi
  intro action
  have hcoordinate : Continuous (fun simplex : QuittingRootSimplex ι ↦
      simplex (who : ι) action) :=
    (continuous_apply action).comp
      (continuous_subtype_val.comp (continuous_apply (who : ι)))
  convert hcoordinate using 1
  funext simplex
  exact quittingRootOfSimplex_apply_toReal simplex (who : ι) action

/-- Any convergent subsequence of the finite forced free points has an exact
singleton-base Nash limit.  The finite points themselves retain only the
quantitative regret estimates from `finite_forceSureOwner_weighted_regrets`. -/
theorem FirstStationaryRootZeroBranch.clusterPoint_mem_singletonBaseNashSet
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {source : StationaryQuitNowCapPinSource reward}
    {root : ℕ → ι → PMF Bool} {minimum gap : ℝ}
    (branch : FirstStationaryRootZeroBranch source root minimum gap)
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (point : mixedPolytope
      (quittingBinaryForm (Finset.univ.erase branch.owner)).sig)
    (hpoint : Tendsto (fun rank ↦
      quittingRootFreeMixedPoint (Finset.univ.erase branch.owner)
        (Function.update (root (branch.select (subsequence rank)))
          branch.owner (PMF.pure true))) atTop (nhds point)) :
    point ∈ quittingPersistentBaseNashSet reward {branch.owner}
      (Finset.univ.erase branch.owner) := by
  let free := Finset.univ.erase branch.owner
  let limitPoint := quittingRootFreeMixedPoint free branch.rootLimit
  have hroot := branch.root_tendsto.comp hsubsequence.tendsto_atTop
  have hlimit : Tendsto (fun rank ↦
      quittingRootFreeMixedPoint free
        (root (branch.select (subsequence rank)))) atTop (nhds limitPoint) := by
    have h := (continuous_rootFreeMixedPoint free).tendsto
      (quittingSimplexOfRoot branch.rootLimit) |>.comp hroot
    simpa [Function.comp_def, limitPoint] using h
  have hforced : (fun rank ↦
      quittingRootFreeMixedPoint free
        (Function.update (root (branch.select (subsequence rank)))
          branch.owner (PMF.pure true))) =
      fun rank ↦ quittingRootFreeMixedPoint free
        (root (branch.select (subsequence rank))) := by
    funext rank
    apply Subtype.ext
    funext who action
    have hne : (who : ι) ≠ branch.owner := (Finset.mem_erase.mp who.property).1
    simp [quittingRootFreeMixedPoint, probs, Function.update_of_ne hne]
  have heq : point = limitPoint :=
    tendsto_nhds_unique hpoint (hforced.symm ▸ hlimit)
  rw [heq]
  exact branch.limit_freePoint_mem_singletonBaseNashSet

end GameTheory
