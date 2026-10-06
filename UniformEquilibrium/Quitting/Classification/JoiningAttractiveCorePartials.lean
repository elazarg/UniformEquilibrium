import UniformEquilibrium.Quitting.Classification.JoiningAttractiveCoreSureCascade
import UniformEquilibrium.Quitting.Root.TripleFullClippedJacobian

/-! # Actual endpoint partials from joining-attractive core comparisons

The reward-only insertion tests produce the signed endpoint gaps used by the
canonical full ambient derivative. No participant-premium sign is assumed.
-/

noncomputable section

namespace GameTheory

open Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem quittingPairJoiningGap_pos_of_joiningAttractive_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    {first second : ι} (hne : first ≠ second)
    (hfirst : first ∈ quittingPremiumCore reward)
    (hsecond : second ∈ quittingPremiumCore reward) :
    0 < quittingPairJoiningGap reward first second := by
  have hcomparison := hattractive first hfirst {second} (Finset.singleton_nonempty second)
    (by simpa only [Finset.singleton_subset_iff, Finset.mem_erase] using
      And.intro hne.symm hsecond)
  simpa only [quittingPairJoiningGap, quittingSingletonTerminal] using
    sub_pos.mpr hcomparison

theorem quittingTripleJoiningGap_pos_of_joiningAttractive_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    {first second third : ι} (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hfirst : first ∈ quittingPremiumCore reward)
    (hsecond : second ∈ quittingPremiumCore reward)
    (hthird : third ∈ quittingPremiumCore reward) :
    0 < quittingTripleJoiningGap reward first second third := by
  have hsubset : ({second, third} : Finset ι) ⊆ (quittingPremiumCore reward).erase first := by
    intro player hplayer
    simp only [Finset.mem_insert, Finset.mem_singleton] at hplayer
    rcases hplayer with rfl | rfl
    · exact Finset.mem_erase.mpr ⟨hfirstSecond.symm, hsecond⟩
    · exact Finset.mem_erase.mpr ⟨hfirstThird.symm, hthird⟩
  have hcomparison := hattractive first hfirst {second, third}
    (Finset.insert_nonempty second {third}) hsubset
  exact sub_pos.mpr hcomparison

theorem quittingRealHazardEndpointPartial_pos_of_joiningAttractive_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (hattractive : HasStrictJoiningAttractivePremiumCore reward)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hcore : quittingPremiumCore reward = {first, second, third})
    (hsupport : quittingPositiveHazardSupport root ⊆ quittingPremiumCore reward)
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hfirst : (root first true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (root second true).toReal ∈ Ioo (0 : ℝ) 1)
    (hthird : (root third true).toReal < 1) :
    0 < quittingRealHazardEndpointPartial reward tail (hazardOfRoot root) first second := by
  have hfirstCore : first ∈ quittingPremiumCore reward := by rw [hcore]; simp
  have hsecondCore : second ∈ quittingPremiumCore reward := by rw [hcore]; simp
  have hthirdCore : third ∈ quittingPremiumCore reward := by rw [hcore]; simp
  apply quittingRealHazardEndpointPartial_pos_of_triple_joining reward tail root
    hfirstSecond hfirstThird hsecondThird (hcore ▸ hsupport) hnash hfirst hsecond hthird
  · exact quittingPairJoiningGap_pos_of_joiningAttractive_core reward hattractive
      hfirstSecond hfirstCore hsecondCore
  · exact (quittingTripleJoiningGap_pos_of_joiningAttractive_core reward hattractive
      hfirstSecond hfirstThird hfirstCore hsecondCore hthirdCore).le

end GameTheory
