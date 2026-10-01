import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalQuietFiniteWordAssembly
import UniformEquilibrium.Quitting.Classification.QuietExtension.RationalWithdrawalWeights
import UniformEquilibrium.Quitting.Classification.QuietExtension.CappedClockOriginalCoalitionRows

/-! # Rational arithmetic for literal quiet finite-word source adapters -/

noncomputable section

namespace GameTheory

open scoped BigOperators

theorem isRationalReal_quittingChildWithOutsiderReward_of_rationalReward
    {players : ℕ} (reward : RationalQuittingReward players)
    (deleted : Fin players → Prop) [DecidablePred deleted]
    (outside : {who : Fin players // deleted who})
    (terminal : {A : Finset (Option (QuittingChildPlayer deleted)) // A.Nonempty})
    (who : Option (QuittingChildPlayer deleted)) :
    Math.IsRationalReal (quittingChildWithOutsiderReward
      (rationalQuittingRewardToReal reward) deleted outside terminal who) := by
  rw [quittingChildWithOutsiderReward_apply_original]
  exact ⟨reward ⟨terminal.1.map
    (quittingChildWithOutsiderOriginalEmbedding deleted outside),
    Finset.map_nonempty.mpr terminal.2⟩
    (quittingChildWithOutsiderOriginalEmbedding deleted outside who), rfl⟩

/-- Rationality of the actual finite amplification, not a supplied numerical cap. -/
theorem isRationalReal_max_one_sup_sum
    {Outside Child : Type} [Fintype Outside] [Nonempty Outside] [Fintype Child]
    (weight : Outside → Child → ℝ)
    (hrational : ∀ outside child, Math.IsRationalReal (weight outside child)) :
    Math.IsRationalReal
      (max 1 (Finset.univ.sup' Finset.univ_nonempty
        (fun outside => ∑ child, weight outside child))) := by
  classical
  obtain ⟨outside, _, hsup⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun outside => ∑ child, weight outside child)
  rw [hsup]
  apply Math.IsRationalReal.one.max
  exact Math.IsRationalReal.sum Finset.univ (weight outside) (fun child _ => hrational _ child)

end GameTheory
