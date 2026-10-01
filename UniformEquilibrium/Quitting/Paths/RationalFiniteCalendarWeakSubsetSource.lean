import UniformEquilibrium.Quitting.Paths.FiniteCalendarRawPredicates
import UniformEquilibrium.Quitting.Paths.ExecutableRationalSelectedOwnerStep

/-! # Exact rational word sources from raw weak-subset exclusion

Only prescribed payoff equality is used to transfer the raw exclusion.
Caps of each newly constructed source word remain its actual computed caps.
-/

namespace GameTheory

variable {players : ℕ}

/-- The actual raw predicate supplies both rational finite-word exclusion
and designated singleton signs. No selected word, cap or owner is input. -/
theorem rationalFiniteWordOwnerExclusion_and_signs_of_rawWeakSubsetExclusion
    (reward : RationalQuittingReward players) (owners : Finset (Fin players))
    (hraw : HasQuittingFiniteCalendarRawWeakSubsetExclusion
      (rationalQuittingRewardToReal reward) owners) :
    RationalQuittingFiniteWordOwnerExclusionOn reward owners ∧
      ∀ who ∈ owners, 0 ≤ reward (quittingSingletonTerminal who) who := by
  let calendar : MixedSimplex (Fin players)
      (fun _ => QuittingFiniteDeadlineTimingAction
        (Fintype.card (Fin players) * (Fintype.card (Fin players) + 1))) := fun _ =>
    Math.ProbabilityMassFunction.stdSimplexEquiv (PMF.pure none)
  obtain ⟨who, _, _⟩ := hraw.2 calendar
  let : Nonempty (Fin players) := ⟨who⟩
  have hactual := (hasQuittingFiniteCalendarRawWeakSubsetExclusion_iff_actual
    (rationalQuittingRewardToReal reward) owners).mp hraw
  refine ⟨?_, ?_⟩
  · intro roots
    obtain ⟨owner, howner, hpayoff⟩ := hactual.2
      (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
        (roots.map RationalQuittingRoot.toPMF)
        (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward)))
    refine ⟨owner, howner, ?_⟩
    have hpair := quittingTerminalSemanticPair_rationalFiniteWord_eq_cast reward roots
    have hcoordinate := congrFun (congrArg Prod.fst hpair) owner
    have hcoordinate' : quittingTerminalPayoff (rationalQuittingRewardToReal reward)
        (quittingLiteralRootStackProfile (rationalQuittingRewardToReal reward)
          (roots.map RationalQuittingRoot.toPMF)
          (quittingAlwaysContinueProfile (rationalQuittingRewardToReal reward))) owner =
        ((rationalQuittingFiniteWordSemanticPair reward roots).1 owner : ℝ) := by
      simpa only [quittingTerminalSemanticPair] using hcoordinate
    change _ ≤ (reward (quittingSingletonTerminal owner) owner : ℝ) at hpayoff
    have hreal := hcoordinate'.symm.trans_le hpayoff
    change ((rationalQuittingFiniteWordSemanticPair reward roots).1 owner : ℝ) ≤
      (reward (quittingSingletonTerminal owner) owner : ℝ) at hreal
    exact_mod_cast hreal
  · intro owner howner
    have hsign := hactual.1 owner howner
    change (0 : ℝ) ≤ (reward (quittingSingletonTerminal owner) owner : ℝ) at hsign
    exact_mod_cast hsign

end GameTheory
