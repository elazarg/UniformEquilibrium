import MathUE.Topology.AmbientDegreeUniqueFixedPointIndex
import UniformEquilibrium.Quitting.Classification.SignedPairCoreBadRoot
import UniformEquilibrium.Quitting.Root.NashExistence
import UniformEquilibrium.Quitting.Projective.SelectedSingletonSublevelReturnSmoothDrift

/-! # Selected exact return on a signed greatest pair core

The full ambient negative derivative produces a second fixed point. Literal
bad-root uniqueness then forces an exact root with a singleton sublevel.
The pure-pair alternative remains explicit; no universal return is asserted.
-/

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exactRoot_singletonSublevel_of_signed_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hbelow : ∃ player, tail player < reward (quittingSingletonTerminal player) player)
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first)
    (hnopure : ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true))) :
    ∃ root, IsεQuittingRootNash reward tail 0 root ∧
      ∃ player, quittingRootSuccessorPayoff reward tail root player ≤
        reward (quittingSingletonTerminal player) player := by
  classical
  by_contra hreturn
  have hbad : ∀ root, IsεQuittingRootNash reward tail 0 root →
      ∀ player, reward (quittingSingletonTerminal player) player <
        quittingRootSuccessorPayoff reward tail root player := by
    intro root hnash player
    by_contra hnot
    exact hreturn ⟨root, hnash, player, le_of_not_gt hnot⟩
  obtain ⟨root, hnash⟩ := exists_isZeroQuittingRootNash (reward := reward) tail
  obtain ⟨hdiff, hnegative, _⟩ := signed_pair_core_badRoot_hasFDerivAt_and_negative_det
    reward tail hne hcore hbelow hjoining hnopure root hnash (hbad root hnash)
  obtain ⟨hazard, hfixed, hneRoot⟩ :=
    Math.Topology.exists_fixedPoint_ne_of_negative_det_finite
      (quittingFullClippedEndpointMap reward tail)
      (continuous_quittingFullClippedEndpointMap reward tail)
      (quittingFullClippedEndpointMap_mem_unitCube reward tail) (hazardOfRoot root)
      ((quittingFullClippedEndpointMap_hazardOfRoot_eq_self_iff_isZeroNash
        reward tail root).mpr hnash) _ hdiff hnegative
  have hcube : hazard ∈ Set.Icc (fun _ => 0) (fun _ => 1) := by
    rw [← hfixed]
    exact quittingFullClippedEndpointMap_mem_unitCube reward tail hazard
  let other := rootOfHazard hazard hcube.1 hcube.2
  have hother : IsεQuittingRootNash reward tail 0 other :=
    (quittingFullClippedEndpointMap_eq_self_iff_isZeroNash_rootOfHazard
      reward tail hazard hcube.1 hcube.2).mp hfixed
  have hfirst : quittingPairJoiningGap reward first second ≠ 0 := by
    intro hzero
    simp only [hzero, zero_mul] at hjoining
    exact lt_irrefl _ hjoining
  have hsecond : quittingPairJoiningGap reward second first ≠ 0 := by
    intro hzero
    simp only [hzero, mul_zero] at hjoining
    exact lt_irrefl _ hjoining
  have hequal := exactRoot_bad_successor_unique_of_signed_pair_core reward tail hne
    hcore hbelow hfirst hsecond hnopure root other hnash hother
    (hbad root hnash) (hbad other hother)
  apply hneRoot
  have hhazard := congrArg hazardOfRoot hequal.symm
  simpa only [other, hazardOfRoot_rootOfHazard] using hhazard

theorem hasBoxedSelectedSingletonSublevelReturn_of_signed_pair_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {first second : ι} (hne : first ≠ second)
    (hcore : quittingPremiumCore reward = {first, second})
    (hjoining : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first)
    (hnopure : ∀ tail, ¬IsεQuittingRootNash reward tail 0
      (PairedCycle.root first second (PMF.pure true) (PMF.pure true)))
    (bound : ℝ) : HasBoxedSelectedSingletonSublevelReturn reward bound := by
  intro tail _ hbelow
  simpa only [quittingSoloReward, quittingSingletonTerminal] using
    exists_exactRoot_singletonSublevel_of_signed_pair_core reward tail hne hcore
      hbelow hjoining (hnopure tail)

end GameTheory
