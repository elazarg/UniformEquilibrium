import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.FiniteHorizonContinuation
import UniformEquilibrium.ProofView.Concepts.Stochastic.Transform.Payoff.DiscountedContinuation

/-!
# Actual supported discounted Nash continuations

Root Nash optimality implies Nash optimality of every actual positive-weight
continuation. The unilateral branch strategy is the existing finite-horizon
constructor, and its discounted gain is the checked actual replacement gain.
This is the continuation step used in Sorin (1986), Proposition 15.
-/

noncomputable section

namespace GameTheory.KernelGame

open _root_.Math.Probability
open scoped BigOperators

/-- Installing one full unilateral child deviation has exactly its actual
branch probability times its remaining discounted gain. The identity includes
depth zero, unreachable branches, and continuation discount zero. -/
theorem realizedAction_discountedPayoff_update_deviationAfterHistory
    {ι : Type} (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile) (who : ι)
    {prefixLength : ℕ} (base : G.realizedActionStochasticGame.Hist prefixLength)
    (deviation : G.realizedActionStochasticGame.BehaviorStrategy who)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    G.realizedActionStochasticGame.discountedPayoff β
        (Function.update profile who
          (G.realizedActionDeviationAfterHistory profile who base deviation))
        PUnit.unit who =
      G.realizedActionStochasticGame.discountedPayoff β profile PUnit.unit who +
        β ^ prefixLength *
          (G.realizedActionStochasticGame.histDist profile PUnit.unit prefixLength base).toReal *
          (G.realizedActionStochasticGame.discountedPayoff β
              (Function.update
                (G.realizedActionStochasticGame.afterHistoryProfile profile base)
                who deviation) base.2 who -
            G.realizedActionStochasticGame.discountedPayoff β
              (G.realizedActionStochasticGame.afterHistoryProfile profile base) base.2 who) := by
  classical
  let : Finite G.realizedActionStochasticGame.State :=
    inferInstanceAs (Finite PUnit)
  let (player : ι) : Finite (G.realizedActionStochasticGame.Act player) :=
    @Finite.of_fintype _ (inferInstanceAs (Fintype (G.Strategy player)))
  let rootDeviation := G.realizedActionDeviationAfterHistory profile who base deviation
  let deviated := Function.update profile who rootDeviation
  let replacement := Function.update
    (G.realizedActionStochasticGame.afterHistoryProfile profile base) who deviation
  let child := Function.update
    (G.realizedActionStochasticGame.afterHistoryProfile profile) base replacement
  have hagree := G.realizedAction_update_deviation_agreeBefore profile who base deviation
  have hprefix :
      (∑ time ∈ Finset.range prefixLength,
        β ^ time * G.realizedActionStochasticGame.expectedStagePayoff
          deviated PUnit.unit time who) =
      ∑ time ∈ Finset.range prefixLength,
        β ^ time * G.realizedActionStochasticGame.expectedStagePayoff
          profile PUnit.unit time who := by
    apply Finset.sum_congr rfl
    intro time htime
    rw [G.realizedAction_expectedStagePayoff_eq_of_agreeBefore hagree
      (Finset.mem_range.mp htime) who]
  have hchild (reached : G.realizedActionStochasticGame.Hist prefixLength) :
      G.realizedActionStochasticGame.afterHistoryProfile deviated reached = child reached := by
    dsimp only [deviated, rootDeviation]
    rw [G.realizedAction_afterHistoryProfile_update_deviation]
    by_cases hequal : reached = base
    · subst reached
      simp [child, replacement]
    · simp [child, hequal]
  have hnew := G.realizedActionStochasticGame.discountedPayoff_prefix_decomposition
    deviated PUnit.unit prefixLength who hβ0 hβ1
  rw [hprefix, G.realizedActionStochasticGame.histDist_eq_of_profilesAgreeBefore
    hagree prefixLength le_rfl] at hnew
  simp_rw [hchild] at hnew
  have hdispatch := G.realizedActionStochasticGame.discountedPayoff_terminalChildDispatcher
    profile PUnit.unit prefixLength child who hβ0 hβ1
  have hsame : G.realizedActionStochasticGame.discountedPayoff β deviated PUnit.unit who =
      G.realizedActionStochasticGame.discountedPayoff β
        (G.realizedActionStochasticGame.terminalChildDispatcher
          prefixLength profile child) PUnit.unit who := hnew.trans hdispatch.symm
  have hreplace : G.realizedActionStochasticGame.replaceContinuation profile base replacement =
      G.realizedActionStochasticGame.terminalChildDispatcher prefixLength profile child := by
    unfold StochasticGame.replaceContinuation
    congr 1
    funext reached
    by_cases hequal : reached = base
    · subst reached
      simp [child]
    · simp only [child, Function.update, hequal, ↓reduceDIte]
  have hgain := G.realizedActionStochasticGame.discountedPayoff_replaceContinuation
    profile PUnit.unit base replacement who hβ0 hβ1
  rw [hreplace, ← hsame] at hgain
  exact hgain

/-- Every actual reached positive-discount-weight continuation of a root
discounted Nash profile is Nash against every full unilateral behavioral
deviation. Discount zero is allowed only at depth zero. -/
theorem realizedAction_afterHistoryProfile_isDiscountedNash_of_mem_support
    {ι : Type} (G : KernelGame ι) [Fintype ι] [DecidableEq ι]
    [∀ player, Fintype (G.Strategy player)]
    (profile : G.realizedActionStochasticGame.BehaviorProfile)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {prefixLength : ℕ}
    (hdiscount : prefixLength = 0 ∨ 0 < β)
    (hnash : G.realizedActionStochasticGame.IsDiscountedεNash β PUnit.unit 0 profile)
    (base : G.realizedActionStochasticGame.Hist prefixLength)
    (hbase : base ∈
      (G.realizedActionStochasticGame.histDist profile PUnit.unit prefixLength).support) :
    G.realizedActionStochasticGame.IsDiscountedεNash β base.2 0
      (G.realizedActionStochasticGame.afterHistoryProfile profile base) := by
  intro who deviation
  simp only [add_zero]
  have hroot := hnash who (G.realizedActionDeviationAfterHistory profile who base deviation)
  simp only [add_zero] at hroot
  have hgain := G.realizedAction_discountedPayoff_update_deviationAfterHistory
    profile who base deviation hβ0 hβ1
  have hmass : 0 <
      (G.realizedActionStochasticGame.histDist profile PUnit.unit prefixLength base).toReal :=
    ENNReal.toReal_pos
      ((PMF.mem_support_iff _ base).mp hbase) (PMF.apply_ne_top _ base)
  have hpower : 0 < β ^ prefixLength := by
    rcases hdiscount with hzero | hpositive
    · simp [hzero]
    · exact pow_pos hpositive prefixLength
  have hcoefficient := mul_pos hpower hmass
  by_contra hnot
  have hstrict := mul_pos hcoefficient (sub_pos.mpr (lt_of_not_ge hnot))
  rw [hgain] at hroot
  linarith

end GameTheory.KernelGame
