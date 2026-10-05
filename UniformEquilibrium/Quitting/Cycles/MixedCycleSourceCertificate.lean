import UniformEquilibrium.Quitting.Cycles.MixedCycleSoloMeshCertificate

/-! # Literal coarse sources for mixed-cycle refinement

The certificate records policy and pure Continue equalities separately. This
distinction matters for sure quitters in retained joint phases. Dummy owners
and masses on retained rows have no source restrictions.
-/

noncomputable section

namespace GameTheory.MixedCycleSoloMesh

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] {L m : ℕ}

def soloMass (solo : Fin L → Bool) (mass : Fin L → ℝ) (block : Fin L) : ℝ :=
  if solo block = true then mass block else 0

/-- Actual coarse product roots, with exact policy and all-player Continue.
Solo rows may be empty; only their aggregate masses must be proper. -/
structure SourceCertificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (root : Fin L → ι → PMF Bool) (value : Fin L → Payoff ι) : Prop where
  mass_nonneg : ∀ block, solo block = true → 0 ≤ mass block
  mass_lt_one : ∀ block, solo block = true → mass block < 1
  solo_root : ∀ block, (hsolo : solo block = true) →
    root block = quittingSoloStationaryRoot (owner block)
      (quittingHazardCoin (mass block) (mass_nonneg block hsolo)
        (mass_lt_one block hsolo).le)
  policy : ∀ block, value block = quittingRootSuccessorPayoff reward
    (value (finRotate L block)) (root block)
  continue_eq : ∀ block who,
    quittingRootContinuePayoff reward (value (finRotate L block)) (root block) who =
      value block who
  singleton_floor : ∀ block who, quittingSoloReward reward who who ≤ value block who
  retained_quit : ∀ block, solo block ≠ true → ∀ who,
    quittingRootQuitPayoff reward (value (finRotate L block)) (root block) who ≤
      value block who
  contracts : ∀ who,
    (∏ block : Fin L, quittingStationaryFixedOpponentsContinueMass (root block) who) < 1

namespace SourceCertificate

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {solo : Fin L → Bool} {owner : Fin L → ι} {mass : Fin L → ℝ}
variable {root : Fin L → ι → PMF Bool} {value : Fin L → Payoff ι}

theorem soloMass_nonneg (source : SourceCertificate reward solo owner mass root value)
    (block : Fin L) : 0 ≤ soloMass solo mass block := by
  by_cases hsolo : solo block = true
  · simpa [soloMass, hsolo] using source.mass_nonneg block hsolo
  · simp [soloMass, hsolo]

theorem soloMass_lt_one (source : SourceCertificate reward solo owner mass root value)
    (block : Fin L) : soloMass solo mass block < 1 := by
  by_cases hsolo : solo block = true
  · simpa [soloMass, hsolo] using source.mass_lt_one block hsolo
  · simp [soloMass, hsolo]

/-- The arc equation is derived from the literal source policy. -/
theorem solo_arc (source : SourceCertificate reward solo owner mass root value)
    (block : Fin L) (hsolo : solo block = true) :
    value block = quittingSingletonArcPayoff (soloMass solo mass block)
      (quittingSoloReward reward (owner block)) (value (finRotate L block)) := by
  rw [source.policy block, source.solo_root block hsolo,
    quittingRootSuccessorPayoff_solo]
  funext who
  simp [quittingSingletonArcPayoff, soloMass, hsolo]

/-- Exact Continue forces the owner anchor when the solo mass is positive;
an empty solo row does not imply or need that anchor. -/
theorem solo_active (source : SourceCertificate reward solo owner mass root value)
    (block : Fin L) (hsolo : solo block = true)
    (hpositive : 0 < soloMass solo mass block) :
    value block (owner block) = quittingSoloReward reward (owner block) (owner block) := by
  have hp : 0 < mass block := by simpa [soloMass, hsolo] using hpositive
  have hcontinue := source.continue_eq block (owner block)
  rw [source.solo_root block hsolo,
    quittingRootContinuePayoff_eq_fixedOpponents reward
      (fun _ => quittingSoloStationaryRoot (owner block)
        (quittingHazardCoin (mass block) (source.mass_nonneg block hsolo)
          (source.mass_lt_one block hsolo).le)) (owner block)
      (value (finRotate L block)) 0] at hcontinue
  change quittingStationaryFixedOpponentsContinueReward reward
      (quittingSoloStationaryRoot (owner block)
        (quittingHazardCoin (mass block) (source.mass_nonneg block hsolo)
          (source.mass_lt_one block hsolo).le)) (owner block) +
    quittingStationaryFixedOpponentsContinueMass
      (quittingSoloStationaryRoot (owner block)
        (quittingHazardCoin (mass block) (source.mass_nonneg block hsolo)
          (source.mass_lt_one block hsolo).le)) (owner block) *
      value (finRotate L block) (owner block) = value block (owner block) at hcontinue
  simp only [quittingStationaryFixedOpponentsContinueReward_solo_owner,
    quittingStationaryFixedOpponentsContinueMass_solo_owner, zero_add, one_mul] at hcontinue
  have harc := congrFun (source.solo_arc block hsolo) (owner block)
  simp only [quittingSingletonArcPayoff, soloMass, hsolo, ite_true] at harc
  nlinarith

end SourceCertificate

/-- Quiet padding contributes one to the deleted-player survival product. -/
theorem continueMass_allContinue (who : ι) :
    quittingStationaryFixedOpponentsContinueMass (quittingAllContinueRoot : ι → PMF Bool)
      who = 1 := by
  unfold quittingStationaryFixedOpponentsContinueMass quittingFixedOpponentsContinueMass
  have hupdate : Function.update (quittingAllContinueRoot : ι → PMF Bool) who
      (PMF.pure false) = quittingAllContinueRoot := by
    simp [quittingAllContinueRoot]
  rw [hupdate, quittingStationaryContinueMass_allContinueRoot]

/-- A retained block contains its original root exactly once, even for sure
hazards; quiet padding does not change its deleted-player survival factor. -/
theorem prod_continueMass_block_of_retained
    (solo : Fin L → Bool) (owner : Fin L → ι) (mass : Fin L → ℝ)
    (coarseRoot : Fin L → ι → PMF Bool) (hm : 0 < m)
    (hmass0 : ∀ block, 0 ≤ mass block) (hmass1 : ∀ block, mass block < 1)
    (block : Fin L) (who : ι) (hsolo : solo block ≠ true) :
    (∏ offset : Fin m, quittingStationaryFixedOpponentsContinueMass
      (refinedRoot solo owner mass coarseRoot m hmass0 hmass1
        (quittingSingletonMeshPhase block offset)) who) =
      quittingStationaryFixedOpponentsContinueMass (coarseRoot block) who := by
  classical
  rw [Finset.prod_eq_single (⟨0, hm⟩ : Fin m)]
  · simp [refinedRoot, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo]
  · intro offset _ hne
    have hoffset : offset.val ≠ 0 := by
      intro hzero
      apply hne
      exact Fin.ext hzero
    simp [refinedRoot, quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase, hsolo, hoffset, continueMass_allContinue]
  · simp

end GameTheory.MixedCycleSoloMesh
