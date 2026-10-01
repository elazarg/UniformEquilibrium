import UniformEquilibrium.ProofView.Concepts.Existence.NashExistenceMixed

/-! # Joint continuity of actual finite-game Nash maps

The payoff table may vary with an arbitrary topological parameter. The map
is the existing Nash map on mixed simplices, not a new fixed-point engine.
The finite expectation expansion proves joint continuity directly and does
not assume a global bound on the varying payoff tables.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory.KernelGame

open _root_.Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Action : ι → Type} [∀ who, Fintype (Action who)]
variable {Parameter : Type*} [TopologicalSpace Parameter]

private theorem ofPureEU_mixedSimplex_eu_eq_sum
    (payoff : (∀ who, Action who) → Payoff ι)
    (simplex : MixedSimplex ι Action) (who : ι) :
    (ofPureEU Action payoff).mixedExtension.eu
        ((ofPureEU Action payoff).profileFromMixedSimplex simplex) who =
      ∑ choices : (∀ player, Action player),
        (∏ player, (simplex player).weights (choices player)) * payoff choices who := by
  classical
  let : Finite (ofPureEU Action payoff).Outcome := by
    change Finite (∀ who, Action who)
    infer_instance
  rw [(ofPureEU Action payoff).mixedExtension_eu, expect_eq_sum]
  apply Finset.sum_congr rfl
  intro choices _
  rw [eu_ofPureEU]
  congr 1
  simp [pmfPi_apply, profileFromMixedSimplex, profileFromWeights, realToPmf_toReal]

open Classical in
private theorem profileFromMixedSimplex_update_pure
    (game : KernelGame ι) [∀ who, Fintype (game.Strategy who)]
    (simplex : MixedSimplex ι (fun who => game.Strategy who))
    (who : ι) (action : game.Strategy who) :
    game.profileFromMixedSimplex
        (Function.update simplex who (Convexity.StdSimplex.pure action)) =
      Function.update (game.profileFromMixedSimplex simplex) who (PMF.pure action) := by
  classical
  funext player
  by_cases hplayer : player = who
  · subst player
    apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
    intro choice
    simp only [profileFromMixedSimplex, profileFromWeights, Function.update_self,
      realToPmf_toReal, PMF.pure_apply]
    change Finsupp.single action (1 : ℝ) choice =
      (if choice = action then (1 : ENNReal) else 0).toReal
    by_cases hchoice : choice = action
    · subst choice
      rw [Finsupp.single_eq_same, ite_eq_left rfl, ENNReal.toReal_one]
    · rw [Finsupp.single_eq_of_ne hchoice, ite_eq_right hchoice, ENNReal.toReal_zero]
  · simp only [profileFromMixedSimplex, profileFromWeights, Function.update_of_ne hplayer]

/-- Expected utility is jointly continuous for a continuous finite pure-payoff table family. -/
theorem continuous_ofPureEU_mixedSimplex_eu
    (payoff : Parameter → (∀ who, Action who) → Payoff ι)
    (hpayoff : ∀ choices who, Continuous (fun parameter => payoff parameter choices who))
    (who : ι) :
    Continuous (fun data : Parameter × MixedSimplex ι Action =>
      (ofPureEU Action (payoff data.1)).mixedExtension.eu
        ((ofPureEU Action (payoff data.1)).profileFromMixedSimplex data.2) who) := by
  classical
  simp_rw [ofPureEU_mixedSimplex_eu_eq_sum]
  apply continuous_finsetSum
  intro choices _
  apply Continuous.mul
  · apply continuous_finsetProd
    intro player _
    exact (Convexity.StdSimplex.continuous_weights_apply ℝ (choices player)).comp
      ((continuous_apply player).comp continuous_snd)
  · exact (hpayoff choices who).comp continuous_fst

/-- Joint continuity of the canonical Nash map for a varying finite payoff table.
No regularity or isolated-equilibrium hypothesis is imposed. -/
theorem continuous_ofPureEU_nashMapOnMixedSimplex
    (payoff : Parameter → (∀ who, Action who) → Payoff ι)
    (hpayoff : ∀ choices who, Continuous (fun parameter => payoff parameter choices who)) :
    Continuous (fun data : Parameter × MixedSimplex ι Action =>
      (show MixedSimplex ι Action from
        (ofPureEU Action (payoff data.1)).nashMapOnMixedSimplex data.2)) := by
  classical
  have hbase := continuous_ofPureEU_mixedSimplex_eu payoff hpayoff
  have hdev (who : ι) (action : Action who) :
      Continuous (fun data : Parameter × MixedSimplex ι Action =>
        (ofPureEU Action (payoff data.1)).mixedExtension.eu
          (Function.update
            ((ofPureEU Action (payoff data.1)).profileFromMixedSimplex data.2)
            who (PMF.pure action)) who) := by
    have h := (hbase who).comp
      (continuous_fst.prodMk
        (continuous_snd.update who
          (continuous_const : Continuous
            (fun _ : Parameter × MixedSimplex ι Action =>
              Convexity.StdSimplex.pure action))))
    exact h.congr fun data => congrArg
      (fun profile => (ofPureEU Action (payoff data.1)).mixedExtension.eu profile who)
      (profileFromMixedSimplex_update_pure
        (ofPureEU Action (payoff data.1)) data.2 who action)
  have hgain (who : ι) (action : Action who) :
      Continuous (fun data : Parameter × MixedSimplex ι Action =>
        (ofPureEU Action (payoff data.1)).mixedGainOnMixedSimplex data.2 who action) := by
    change Continuous (fun data : Parameter × MixedSimplex ι Action =>
      (ofPureEU Action (payoff data.1)).mixedExtension.eu
          (Function.update
            ((ofPureEU Action (payoff data.1)).profileFromMixedSimplex data.2)
            who (PMF.pure action)) who -
        (ofPureEU Action (payoff data.1)).mixedExtension.eu
          ((ofPureEU Action (payoff data.1)).profileFromMixedSimplex data.2) who)
    exact (hdev who action).sub (hbase who)
  have hsum (who : ι) :
      Continuous (fun data : Parameter × MixedSimplex ι Action =>
        (ofPureEU Action (payoff data.1)).gainSumOnMixedSimplex data.2 who) := by
    change Continuous (fun data : Parameter × MixedSimplex ι Action =>
      ∑ action : Action who,
        pospart ((ofPureEU Action (payoff data.1)).mixedGainOnMixedSimplex
          data.2 who action))
    exact continuous_finsetSum (s := Finset.univ)
      (fun action _ => continuous_pospart.comp (hgain who action))
  have hcoordinate (who : ι) (action : Action who) :
      Continuous (fun data : Parameter × MixedSimplex ι Action =>
        ((data.2 who).weights action +
          pospart ((ofPureEU Action (payoff data.1)).mixedGainOnMixedSimplex
            data.2 who action)) /
          (1 + (ofPureEU Action (payoff data.1)).gainSumOnMixedSimplex data.2 who)) := by
    have hweight : Continuous (fun data : Parameter × MixedSimplex ι Action =>
        (data.2 who).weights action) :=
      (Convexity.StdSimplex.continuous_weights_apply ℝ action).comp
        ((continuous_apply who).comp continuous_snd)
    exact (hweight.add (continuous_pospart.comp (hgain who action))).div
      (continuous_const.add (hsum who)) (fun data =>
        (add_pos_of_pos_of_nonneg zero_lt_one
          ((ofPureEU Action (payoff data.1)).gainSumOnMixedSimplex_nonneg
            data.2 who)).ne')
  apply continuous_pi
  intro who
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Action who)).continuous_iff.mpr
  change Continuous (fun data : Parameter × MixedSimplex ι Action =>
    fun action : Action who =>
      ((data.2 who).weights action +
        pospart ((ofPureEU Action (payoff data.1)).mixedGainOnMixedSimplex
          data.2 who action)) /
        (1 + (ofPureEU Action (payoff data.1)).gainSumOnMixedSimplex data.2 who))
  exact continuous_pi (fun action => hcoordinate who action)

end GameTheory.KernelGame
