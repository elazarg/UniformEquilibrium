/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.ProofView.Concepts.Stochastic.Equilibrium.Discounted.Fink

/-!
# Player-dependent discounted stationary equilibria

Fink's 1964 theorem allows each player to have a different discount factor.
The main `Fink.lean` interface uses one common factor because that is the
normalization used by the vanishing-discount development.  This file records
the finite-dimensional fixed-point argument with a factor `α i` in player
`i`'s auxiliary game.

No new analytic ingredient is needed.  Fink's compact strategy/value domain
is unchanged; only the scalar supplied to each state-player coordinate of the
gain-adjustment and value maps varies with the player.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability
open Math.ProbabilityMassFunction

variable {ι : Type}

/-- Statewise auxiliary Nash optimality with one discount factor per player. -/
def IsPlayerDiscountedAuxNash (G : StochasticGame ι) [Fintype ι]
    [DecidableEq ι] (α : ι → ℝ) (V : G.State → Payoff ι)
    (x : G.StationaryMixedProfile) : Prop :=
  ∀ (s : G.State) (who : ι) (d : PMF (G.Act who)),
    G.discountedAuxEU (α who) V s (Function.update (x s) who d) who ≤
      G.discountedAuxEU (α who) V s (x s) who

/-- Fink's stationary Bellman certificate with player-dependent discounts. -/
def IsPlayerDiscountedStationaryBellmanEq
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    (α : ι → ℝ) (x : G.StationaryMixedProfile)
    (V : G.State → Payoff ι) : Prop :=
  G.IsPlayerDiscountedAuxNash α V x ∧
    ∀ (s : G.State) (who : ι),
      G.discountedAuxEU (α who) V s (x s) who = V s who

/-- The auxiliary normal-form game whose player `i` uses discount `α i`. -/
def playerDiscountedAuxGame (G : StochasticGame ι) (α : ι → ℝ)
    (V : G.State → Payoff ι) (s : G.State) : KernelGame ι :=
  KernelGame.ofPureEU G.Act
    (fun a who => G.discountedAuxPayoff (α who) V s a who)

/-- The mixed extension of the player-dependent auxiliary game has the
expected payoff used in `IsPlayerDiscountedAuxNash`. -/
theorem mixedExtension_eu_playerDiscountedAuxGame
    (G : StochasticGame ι) [Fintype ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] (α : ι → ℝ)
    (V : G.State → Payoff ι) (s : G.State)
    (m : ∀ i, PMF (G.Act i)) (who : ι) :
    (G.playerDiscountedAuxGame α V s).mixedExtension.eu m who =
      G.discountedAuxEU (α who) V s m who := by
  haveI : Finite (G.playerDiscountedAuxGame α V s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  rw [KernelGame.mixedExtension_eu]
  simp [playerDiscountedAuxGame, discountedAuxEU, KernelGame.eu_ofPureEU]

/-- Fink's coordinate gain is the ordinary pure-deviation gain in the
player-dependent auxiliary game. -/
theorem finkGain_eq_playerMixedGain
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (α : ι → ℝ) {U : ℝ}
    (z : G.finkDomain U) (s : G.State) (who : ι) (d : G.Act who) :
    G.finkGain (α who) z s who d =
      (G.playerDiscountedAuxGame α (G.finkValue z) s).mixedGain
        (G.finkProfile z s) who d := by
  haveI : Finite (G.playerDiscountedAuxGame α (G.finkValue z) s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  unfold finkGain KernelGame.mixedGain
  rw [G.finkDeviationAuxEU_eq_discountedAuxEU,
    G.finkAuxEU_eq_discountedAuxEU]
  rw [← G.mixedExtension_eu_playerDiscountedAuxGame,
    ← G.mixedExtension_eu_playerDiscountedAuxGame]
  rfl

/-- Ambient-coordinate formula for the player-dependent Fink map. -/
def playerFinkAmbientUpdate (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] (α : ι → ℝ) {U : ℝ}
    (z : G.finkDomain U) : G.FinkAmbient :=
  (fun p d => G.finkStrategyWeightUpdate (α p.2) z p.1 p.2 d,
    fun s who => G.finkValueUpdate (α who) z s who)

theorem playerFinkAmbientUpdate_mem (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (α : ι → ℝ) (U : ℝ)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U) :
    G.playerFinkAmbientUpdate α z ∈ G.finkDomain U := by
  constructor
  · intro p hp
    exact (G.finkStrategyUpdate (α p.2) z p.1 p.2).property
  · constructor <;> intro s who
    · exact (abs_le.mp
        (G.abs_finkValueUpdate_le (α who) U (hα0 who) (hα1 who)
          hpay z s who)).1
    · exact (abs_le.mp
        (G.abs_finkValueUpdate_le (α who) U (hα0 who) (hα1 who)
          hpay z s who)).2

/-- Fink's continuous self-map with one discount factor per player. -/
def playerFinkMap (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (α : ι → ℝ) (U : ℝ)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    G.finkDomain U → G.finkDomain U :=
  fun z => ⟨G.playerFinkAmbientUpdate α z,
    G.playerFinkAmbientUpdate_mem α U hα0 hα1 hpay z⟩

theorem continuous_playerFinkMap (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (α : ι → ℝ) (U : ℝ)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    Continuous (G.playerFinkMap α U hα0 hα1 hpay) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact continuous_pi fun p => continuous_pi fun d =>
      G.continuous_finkStrategyWeightUpdate (α p.2) p.1 p.2 d
  · exact continuous_pi fun s => continuous_pi fun who =>
      G.continuous_finkAuxEU (α who) s who

/-- The value coordinate of a player-dependent Fink fixed point is its
auxiliary expected payoff. -/
theorem finkAuxEU_eq_finkValue_of_playerFinkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (α : ι → ℝ) (U : ℝ)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.playerFinkMap α U hα0 hα1 hpay z = z)
    (s : G.State) (who : ι) :
    G.finkAuxEU (α who) z s who = G.finkValue z s who := by
  have hcoord := congrArg (fun q : G.finkDomain U => q.1.2 s who) hfix
  simpa [playerFinkMap, playerFinkAmbientUpdate, finkValueUpdate, finkValue]
    using hcoord

/-- Brouwer supplies a fixed point of the player-dependent Fink map. -/
theorem exists_playerFinkMap_fixedPoint (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (α : ι → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ z : G.finkDomain U,
      G.playerFinkMap α U hα0 hα1 hpay z = z := by
  let f : C(G.finkDomain U, G.finkDomain U) :=
    ⟨G.playerFinkMap α U hα0 hα1 hpay,
      G.continuous_playerFinkMap α U hα0 hα1 hpay⟩
  exact _root_.brouwer_fixed_point (G.finkDomain U)
    (G.convex_finkDomain U) (G.isCompact_finkDomain U)
    (G.nonempty_finkDomain hU) f

/-- A fixed point of the player-dependent Fink map decodes to the
corresponding stationary Bellman equilibrium. -/
theorem isPlayerDiscountedStationaryBellmanEq_of_playerFinkMap_fixedPoint
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    (α : ι → ℝ) (U : ℝ)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain U)
    (hfix : G.playerFinkMap α U hα0 hα1 hpay z = z) :
    G.IsPlayerDiscountedStationaryBellmanEq α
      (G.finkProfile z) (G.finkValue z) := by
  constructor
  · intro s who dev
    let actFintype : ∀ i, Fintype (G.Act i) := inferInstance
    haveI : ∀ i,
        Fintype ((G.playerDiscountedAuxGame α (G.finkValue z) s).Strategy i) := by
      change ∀ i, Fintype (G.Act i)
      infer_instance
    haveI : Finite
        (G.playerDiscountedAuxGame α (G.finkValue z) s).Outcome :=
      inferInstanceAs (Finite G.JointAct)
    have hfp : ∀ (i : ι) (d : G.Act i),
        ((G.finkProfile z s i) d).toReal *
              (1 + (G.playerDiscountedAuxGame α (G.finkValue z) s).gainSum
                (G.finkProfile z s) i) =
          ((G.finkProfile z s i) d).toReal +
            KernelGame.pospart
              ((G.playerDiscountedAuxGame α (G.finkValue z) s).mixedGain
                (G.finkProfile z s) i d) := by
      intro i d
      have hcoord := congrArg
        (fun q : G.finkDomain U => q.1.1 (s, i) d) hfix
      have hden : 1 + G.finkGainSum (α i) z s i ≠ 0 := by
        linarith [G.finkGainSum_nonneg (α i) z s i]
      have hsum :
          (G.playerDiscountedAuxGame α (G.finkValue z) s).gainSum
              (G.finkProfile z s) i = G.finkGainSum (α i) z s i := by
        unfold KernelGame.gainSum finkGainSum
        apply Finset.sum_congr
        · ext x
          constructor
          · intro hx
            exact @Finset.mem_univ (G.Act i) (actFintype i) x
          · intro hx
            exact @Finset.mem_univ
              ((G.playerDiscountedAuxGame α (G.finkValue z) s).Strategy i)
              (inferInstance) x
        · intro x hx
          rw [← G.finkGain_eq_playerMixedGain α z s i x]
      have halg :
          z.1.1 (s, i) d * (1 + G.finkGainSum (α i) z s i) =
            z.1.1 (s, i) d +
              KernelGame.pospart (G.finkGain (α i) z s i d) := by
        have hdiv :
            (z.1.1 (s, i) d +
                KernelGame.pospart (G.finkGain (α i) z s i d)) /
                  (1 + G.finkGainSum (α i) z s i) =
              z.1.1 (s, i) d := by
          simpa [playerFinkMap, playerFinkAmbientUpdate,
            finkStrategyWeightUpdate] using hcoord
        exact ((div_eq_iff hden).mp hdiv).symm
      rw [hsum, ← G.finkGain_eq_playerMixedGain α z s i d,
        G.finkProfile_apply_toReal]
      exact halg
    have hN :=
      (G.playerDiscountedAuxGame α (G.finkValue z) s).nash_fp_is_nash
        (G.finkProfile z s) hfp
    have hdev := hN who dev
    rw [G.mixedExtension_eu_playerDiscountedAuxGame,
      G.mixedExtension_eu_playerDiscountedAuxGame] at hdev
    exact hdev
  · intro s who
    rw [← G.finkAuxEU_eq_discountedAuxEU]
    exact G.finkAuxEU_eq_finkValue_of_playerFinkMap_fixedPoint
      α U hα0 hα1 hpay z hfix s who

/-- Fink's theorem with player-dependent discount factors. -/
theorem exists_isPlayerDiscountedStationaryBellmanEq_bounded
    (G : StochasticGame ι)
    [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (α : ι → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (x : G.StationaryMixedProfile) (V : G.State → Payoff ι),
      G.IsPlayerDiscountedStationaryBellmanEq α x V ∧
        ∀ s who, |V s who| ≤ U := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  obtain ⟨z, hz⟩ :=
    G.exists_playerFinkMap_fixedPoint α U hU hα0 hα1 hpay
  exact ⟨G.finkProfile z, G.finkValue z,
    G.isPlayerDiscountedStationaryBellmanEq_of_playerFinkMap_fixedPoint
      α U hα0 hα1 hpay z hz,
    fun s who => G.abs_finkValue_le z s who⟩

/-- Certificate-only form of the player-dependent theorem. -/
theorem exists_isPlayerDiscountedStationaryBellmanEq
    (G : StochasticGame ι)
    [Finite G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (α : ι → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hα0 : ∀ who, 0 ≤ α who) (hα1 : ∀ who, α who ≤ 1)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U) :
    ∃ (x : G.StationaryMixedProfile) (V : G.State → Payoff ι),
      G.IsPlayerDiscountedStationaryBellmanEq α x V := by
  obtain ⟨x, V, hF, -⟩ :=
    G.exists_isPlayerDiscountedStationaryBellmanEq_bounded
      α U hU hα0 hα1 hpay
  exact ⟨x, V, hF⟩

end StochasticGame
end GameTheory
