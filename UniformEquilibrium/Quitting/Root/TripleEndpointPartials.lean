import UniformEquilibrium.Quitting.Root.PairFullClippedJacobian
import UniformEquilibrium.Quitting.Root.InteriorCoalitionOdds
import UniformEquilibrium.Quitting.Bellman.Finite.ActiveSetSupport

/-! # Actual proper-triple endpoint cross-partials

The existing four-atom paired opponent law gives an affine coordinate line.
Differentiation identifies the full ambient partial, and actual interior
indifference converts it to the signed coalition-odds formula. No signs or
local indices are supplied.
-/

noncomputable section

namespace GameTheory

open Set Filter Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def quittingTripleJoiningGap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (first second third : ι) : ℝ :=
  reward ⟨{first, second, third}, by simp⟩ first - reward ⟨{second, third}, by simp⟩ first

private def tripleGapConstant
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (first third : ι) : ℝ :=
  (1 - (root third true).toReal) *
      (reward (quittingSingletonTerminal first) first - tail first) +
    (root third true).toReal * quittingPairJoiningGap reward first third

private def tripleGapSlope
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (first second third : ι) : ℝ :=
  (1 - (root third true).toReal) * quittingPairJoiningGap reward first second +
    (root third true).toReal * quittingTripleJoiningGap reward first second third -
      tripleGapConstant reward tail root first third

private theorem triple_gap_update_second
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (rate : ℝ) (hzero : 0 ≤ rate) (hone : rate ≤ 1) :
    quittingRealHazardEndpointGap reward tail
        (Function.update (hazardOfRoot root) second rate) first =
      tripleGapConstant reward tail root first third +
        tripleGapSlope reward tail root first second third * rate := by
  let law := quittingHazardCoin rate hzero hone
  have hvector : hazardOfRoot (PairedCycle.root second third law (root third)) =
      Function.update (Function.update (hazardOfRoot root) second rate) first 0 := by
    funext player
    by_cases hfirst : player = first
    · subst player
      simp [hazardOfRoot, PairedCycle.root_outside hfirstSecond hfirstThird]
    · by_cases hsecond : player = second
      · subst player
        simp [hazardOfRoot, law, hsecondThird, hfirstSecond.symm]
      · by_cases hthird : player = third
        · subst player
          simp [hazardOfRoot, hfirstThird.symm, hsecondThird.symm]
        · have houtside : player ∉ quittingPositiveHazardSupport root := by
            intro hplayer
            have := hsupport hplayer
            simp [hfirst, hsecond, hthird] at this
          have hpure := quittingRoot_eq_pure_false_of_not_mem_positiveHazardSupport
            root houtside
          simp [hazardOfRoot, PairedCycle.root_outside hsecond hthird,
            hfirst, hsecond, hpure]
  rw [← quittingRealHazardEndpointGap_update_own reward tail
    (Function.update (hazardOfRoot root) second rate) first 0, ← hvector,
    quittingRealHazardEndpointGap_hazardOfRoot]
  unfold quittingRootEndpointDifference
  rw [PairedCycle.rootQuit_eq_bellman reward tail hsecondThird,
    PairedCycle.rootContinue_outside reward tail hsecondThird hfirstSecond hfirstThird]
  simp only [law, quittingHazardCoin_true_toReal]
  unfold tripleGapSlope tripleGapConstant quittingPairJoiningGap quittingTripleJoiningGap
    Math.PairedAffine.bellman Math.PairedAffine.contribution
  ring

theorem quittingRealHazardEndpointGap_triple_cross_partial
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (hsecond : (root second true).toReal ∈ Ioo (0 : ℝ) 1) :
    fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard first)
      (hazardOfRoot root) (Pi.single second 1) =
        (1 - (root third true).toReal) * quittingPairJoiningGap reward first second +
          (root third true).toReal * quittingTripleJoiningGap reward first second third -
            ((1 - (root third true).toReal) *
                (reward (quittingSingletonTerminal first) first - tail first) +
              (root third true).toReal * quittingPairJoiningGap reward first third) := by
  let point := hazardOfRoot root
  have hregular := contDiff_quittingRealHazardEndpointGap reward tail 1 first
  have hgap := (hregular.differentiable_one point).hasFDerivAt
  have hchain := hgap.comp_hasDerivAt_of_eq (point second)
    (hasDerivAt_update point second (point second)) (by simp)
  have hlinear := (hasDerivAt_const (point second)
    (tripleGapConstant reward tail root first third)).add
      ((hasDerivAt_id (point second)).const_mul
        (tripleGapSlope reward tail root first second third))
  simp only [mul_one, zero_add] at hlinear
  have hformula := hlinear.congr_of_eventuallyEq (f₁ := fun rate =>
    quittingRealHazardEndpointGap reward tail (Function.update point second rate) first) (by
      filter_upwards [isOpen_Ioo.mem_nhds hsecond] with rate hrate
      exact triple_gap_update_second reward tail root hfirstSecond hfirstThird hsecondThird
        hsupport rate hrate.1.le hrate.2.le)
  simpa only [tripleGapSlope, tripleGapConstant] using hchain.unique hformula

theorem quittingRealHazardEndpointGap_triple_cross_partial_of_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) {first second third : ι}
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hsupport : quittingPositiveHazardSupport root ⊆ {first, second, third})
    (hnash : IsεQuittingRootNash reward tail 0 root)
    (hfirst : (root first true).toReal ∈ Ioo (0 : ℝ) 1)
    (hsecond : (root second true).toReal ∈ Ioo (0 : ℝ) 1)
    (hthird : (root third true).toReal < 1) :
    fderiv ℝ (fun hazard => quittingRealHazardEndpointGap reward tail hazard first)
      (hazardOfRoot root) (Pi.single second 1) =
        (1 - (root third true).toReal) / (1 - (root second true).toReal) *
          (quittingPairJoiningGap reward first second +
            quittingRootOdds root third * quittingTripleJoiningGap reward first second third) := by
  have hfalseFirst : 0 < (root first false).toReal := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root first
    linarith [hfirst.2]
  have hgapZero := quittingRootEndpointDifference_eq_zero_of_both_probabilities_pos
    reward tail root first
      ((isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash reward tail root).mpr hnash)
      hfalseFirst hfirst.1
  have hline := triple_gap_update_second reward tail root hfirstSecond hfirstThird
    hsecondThird hsupport (root second true).toReal hsecond.1.le hsecond.2.le
  change quittingRealHazardEndpointGap reward tail
    (Function.update (hazardOfRoot root) second ((root second true).toReal)) first = _ at hline
  rw [show Function.update (hazardOfRoot root) second ((root second true).toReal) =
      hazardOfRoot root by apply Function.update_eq_self_iff.mpr; rfl,
    quittingRealHazardEndpointGap_hazardOfRoot, hgapZero] at hline
  rw [quittingRealHazardEndpointGap_triple_cross_partial reward tail root
    hfirstSecond hfirstThird hsecondThird hsupport hsecond]
  have hfalseThird : (root third false).toReal = 1 - (root third true).toReal := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root third
    linarith
  unfold quittingRootOdds
  rw [hfalseThird]
  have hsecondNe : 1 - (root second true).toReal ≠ 0 := by linarith [hsecond.2]
  have hthirdNe : 1 - (root third true).toReal ≠ 0 := by linarith
  dsimp only [tripleGapConstant, tripleGapSlope] at hline
  have hratio :
      (1 - (root third true).toReal) / (1 - (root second true).toReal) *
        (quittingPairJoiningGap reward first second +
          (root third true).toReal / (1 - (root third true).toReal) *
            quittingTripleJoiningGap reward first second third) =
      ((1 - (root third true).toReal) * quittingPairJoiningGap reward first second +
        (root third true).toReal * quittingTripleJoiningGap reward first second third) /
          (1 - (root second true).toReal) := by
    field_simp
  rw [hratio]
  apply (eq_div_iff hsecondNe).mpr
  nlinarith [hline]

end GameTheory
