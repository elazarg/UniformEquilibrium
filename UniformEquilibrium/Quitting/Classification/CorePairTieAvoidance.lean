import UniformEquilibrium.Quitting.Classification.SignedPairCoreBadRoot
import UniformEquilibrium.Quitting.Root.PairNashTieAvoidance

/-! # Computed-core pair tie avoidance and actual pair derivatives

Pair constraints include every inactive player, not only outsiders of the
greatest core. Actual source classes must supply the joining-product signs.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingCoreOrderedPairs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Finset (ι × ι) :=
  Finset.univ.filter (fun pair => pair.1 ∈ quittingPremiumCore reward ∧
    pair.2 ∈ quittingPremiumCore reward ∧ pair.1 ≠ pair.2)

theorem dense_quittingCorePairTieAvoidanceDomain_of_positive_pair_products
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hproduct : ∀ first ∈ quittingPremiumCore reward, ∀ second ∈ quittingPremiumCore reward,
      first ≠ second → 0 < quittingPairJoiningGap reward first second *
        quittingPairJoiningGap reward second first) :
    Dense (quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward)) := by
  apply dense_quittingPairTieAvoidanceDomain
  intro pair hpair
  obtain ⟨_, hfirst, hsecond, hne⟩ := Finset.mem_filter.mp hpair
  exact ne_of_gt (hproduct pair.1 hfirst pair.2 hsecond hne)

theorem proper_pairNash_hasFDerivAt_and_negative_det_of_core_tieAvoidance
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (hnash : IsεQuittingRootNash reward tail 0 root)
    (hsubset : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward)
    (hproper : ∀ player ∈ quittingPositiveHazardSupport root,
      (root player true).toReal ∈ Ioo (0 : ℝ) 1)
    {first second : ι} (hne : first ≠ second)
    (hsupport : quittingPositiveHazardSupport root = {first, second})
    (hproduct : 0 < quittingPairJoiningGap reward first second *
      quittingPairJoiningGap reward second first)
    (havoid : tail ∈ quittingPairTieAvoidanceDomain reward (quittingCoreOrderedPairs reward)) :
    ∃ derivative : (ι → ℝ) →L[ℝ] (ι → ℝ),
      HasFDerivAt (fun hazard => hazard - quittingFullClippedEndpointMap reward tail hazard)
        derivative (hazardOfRoot root) ∧
        (LinearMap.toMatrix' derivative.toLinearMap).det < 0 := by
  have hfirstCore : first ∈ quittingPremiumCore reward :=
    hsubset (by rw [hsupport]; simp)
  have hsecondCore : second ∈ quittingPremiumCore reward :=
    hsubset (by rw [hsupport]; simp)
  have hpairMember : (first, second) ∈ quittingCoreOrderedPairs reward :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirstCore, hsecondCore, hne⟩
  have hroot := quittingRoot_eq_pairedRoot_of_support_eq_pair root hne hsupport
  have hcertificate := pairNash_hasFDerivAt_and_negative_det_of_numerator_avoidance
    reward tail hne (root first) (root second)
    (hproper first (by rw [hsupport]; simp))
    (hproper second (by rw [hsupport]; simp)) (hroot ▸ hnash) hproduct
    (havoid (first, second) hpairMember)
  rw [← hroot] at hcertificate
  exact ⟨_, hcertificate.1, hcertificate.2.1⟩

end GameTheory
