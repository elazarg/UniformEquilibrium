import MathUE.Probability.OverlappingFirstStopping

/-! # Relabeling exact first-stopping coalition laws -/

noncomputable section

namespace Math.Probability.DiscreteHazard.StoppingLaw

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Relabel one coalition through a finite player equivalence. -/
def relabelCoalition (equiv : ι ≃ κ)
    (coalition : {C : Finset ι // C.Nonempty}) :
    {C : Finset κ // C.Nonempty} :=
  ⟨coalition.1.map equiv.toEmbedding,
    coalition.2.map (f := equiv.toEmbedding)⟩

/-- Exact first-stopping coalition mass is invariant under simultaneous
relabeling of clocks and coalition coordinates. -/
theorem exactFiniteFirstStoppingCoalitionMass_relabel
    (laws : ι → PMF (Option ℕ)) (equiv : ι ≃ κ)
    (coalition : {C : Finset ι // C.Nonempty}) :
    exactFiniteFirstStoppingCoalitionMass (fun who => laws (equiv.symm who))
        (relabelCoalition equiv coalition) =
      exactFiniteFirstStoppingCoalitionMass laws coalition := by
  unfold exactFiniteFirstStoppingCoalitionMass
  apply tsum_congr
  intro time
  congr 1
  · simp [relabelCoalition, Finset.prod_map]
  · have hcompl : (coalition.1.map equiv.toEmbedding)ᶜ =
        coalition.1ᶜ.map equiv.toEmbedding := by
      ext who
      simp
    change (∏ who ∈ (coalition.1.map equiv.toEmbedding)ᶜ,
      survival (laws (equiv.symm who)) (time + 1)) = _
    rw [hcompl]
    simp [Finset.prod_map]

end Math.Probability.DiscreteHazard.StoppingLaw
