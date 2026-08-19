import Sorin1986DiscountedScratch

noncomputable section

namespace Literature.Sorin1986

open GameTheory Set Filter
open scoped BigOperators Topology

namespace SequenceForm

/-- Nash equilibrium for one realization-plan payoff evaluator. -/
def IsNash {G : FiniteStageGame}
    (payoff : RealizationProfile G → Payoff G.Player)
    (profile : RealizationProfile G) : Prop :=
  ∀ who (deviation : RealizationPlan G who),
    payoff profile who ≥
      payoff (Function.update profile who deviation) who

/-- Compact continuous normal form of the positive finite repetition. -/
def finiteCompactGame (G : FiniteStageGame) (n : G.Horizon) :
    CompactContinuousGame where
  Player := G.Player
  Strategy := RealizationPlan G
  mix := fun _ => RealizationPlan.mix
  mixContinuous := RealizationPlan.mix_continuous G
  mix_zero := fun _ => RealizationPlan.mix_zero
  mix_one := fun _ => RealizationPlan.mix_one
  payoff := finiteRealizationPayoff G n.1
  payoffContinuous := continuous_finiteRealizationPayoff G n.1
  payoffAffine := fun profile who x y t observer ht0 ht1 =>
    finiteRealizationPayoff_update_mix G n.1 profile who x y t observer ht0 ht1

/-- Compact continuous normal form of the discounted repetition. -/
def discountedCompactGame (G : FiniteStageGame) (lam : G.DiscountRate) :
    CompactContinuousGame where
  Player := G.Player
  Strategy := RealizationPlan G
  mix := fun _ => RealizationPlan.mix
  mixContinuous := RealizationPlan.mix_continuous G
  mix_zero := fun _ => RealizationPlan.mix_zero
  mix_one := fun _ => RealizationPlan.mix_one
  payoff := discountedRealizationPayoff G lam
  payoffContinuous := continuous_discountedRealizationPayoff G lam
  payoffAffine := fun profile who x y t observer ht0 ht1 =>
    discountedRealizationPayoff_update_mix G lam profile who x y t observer ht0 ht1

/-- Feasible payoff set in sequence form. -/
def finiteFeasiblePayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  Set.range (finiteRealizationPayoff G n)

/-- Finite-horizon Nash payoff set in sequence form. -/
def finiteEquilibriumPayoffs (G : FiniteStageGame) (n : ℕ) :
    Set (Payoff G.Player) :=
  {value | ∃ profile : RealizationProfile G,
    IsNash (finiteRealizationPayoff G n) profile ∧
      finiteRealizationPayoff G n profile = value}

/-- Discounted feasible payoff set in sequence form. -/
def discountedFeasiblePayoffs (G : FiniteStageGame)
    (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  Set.range (discountedRealizationPayoff G lam)

/-- Discounted Nash payoff set in sequence form. -/
def discountedEquilibriumPayoffs (G : FiniteStageGame)
    (lam : G.DiscountRate) : Set (Payoff G.Player) :=
  {value | ∃ profile : RealizationProfile G,
    IsNash (discountedRealizationPayoff G lam) profile ∧
      discountedRealizationPayoff G lam profile = value}

@[simp] theorem finiteCompactGame_feasiblePayoffs
    (G : FiniteStageGame) (n : G.Horizon) :
    (finiteCompactGame G n).feasiblePayoffs =
      finiteFeasiblePayoffs G n.1 :=
  rfl

@[simp] theorem finiteCompactGame_equilibriumPayoffs
    (G : FiniteStageGame) (n : G.Horizon) :
    (finiteCompactGame G n).equilibriumPayoffs =
      finiteEquilibriumPayoffs G n.1 :=
  rfl

@[simp] theorem discountedCompactGame_feasiblePayoffs
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (discountedCompactGame G lam).feasiblePayoffs =
      discountedFeasiblePayoffs G lam :=
  rfl

@[simp] theorem discountedCompactGame_equilibriumPayoffs
    (G : FiniteStageGame) (lam : G.DiscountRate) :
    (discountedCompactGame G lam).equilibriumPayoffs =
      discountedEquilibriumPayoffs G lam :=
  rfl

end SequenceForm

end Literature.Sorin1986
