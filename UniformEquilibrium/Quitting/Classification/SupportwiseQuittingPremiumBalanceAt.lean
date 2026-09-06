import UniformEquilibrium.ProofView.Concepts.Stochastic.Models.Quitting.SimpleBranches
import Mathlib.Tactic.Positivity

/-! # Supportwise quitting-premium balance on one support -/

noncomputable section

namespace GameTheory

variable {ι : Type} [DecidableEq ι]

/-- One normalized nonnegative weight supported on `active` controls every
participant-only premium on its nonempty subcoalitions. -/
def HasSupportwiseQuittingPremiumBalanceAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) : Prop :=
  ∃ weight : ι → ℝ,
    (∀ player, 0 ≤ weight player) ∧
    (∀ player, player ∉ active → weight player = 0) ∧
    (∑ player ∈ active, weight player) = 1 ∧
    ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val ⊆ active →
      (∑ player ∈ terminal.val, weight player *
        (reward terminal player -
          reward (quittingSingletonTerminal player) player)) ≤ 0

/-- A player whose premium is nonpositive on every subcoalition containing
it supplies a point-mass supportwise certificate. -/
theorem hasSupportwiseQuittingPremiumBalanceAt_of_point
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (active : Finset ι) (chosen : ι) (hchosen : chosen ∈ active)
    (hlow : ∀ terminal : {S : Finset ι // S.Nonempty},
      terminal.val ⊆ active → chosen ∈ terminal.val →
        reward terminal chosen ≤
          reward (quittingSingletonTerminal chosen) chosen) :
    HasSupportwiseQuittingPremiumBalanceAt reward active := by
  let weight : ι → ℝ := fun player => if player = chosen then 1 else 0
  refine ⟨weight, ?_, ?_, ?_, ?_⟩
  · intro player
    dsimp only [weight]
    positivity
  · intro player hout
    by_cases h : player = chosen
    · subst player
      exact False.elim (hout hchosen)
    · simp [weight, h]
  · simp [weight, hchosen]
  · intro terminal _hsubset
    by_cases hmem : chosen ∈ terminal.val
    · calc
        _ = reward terminal chosen -
              reward (quittingSingletonTerminal chosen) chosen := by
          simp [weight, hmem]
        _ ≤ 0 := sub_nonpos.mpr (hlow terminal _hsubset hmem)
    · simp [weight, hmem]

end GameTheory
