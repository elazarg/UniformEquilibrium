/-
Uniform-radius reset-dispatch boundary for quitting games.

The fixed-law reset dispatch offers a dynamic alternative: either an absorbing
exact cap--Nash root strictly lowers the returned point's debt, or the cap
correspondence stalls on the all-Continue face.  The minimum-target boundary
records that a target no higher than a positive global-minimum source forces
the stall.  That boundary is not sharp in the target: it is uniform in a
quantitative neighborhood of the minimum, and the neighborhood depends on
nothing but the reward table and the minimum value.

The near-minimum cap--Nash radius supplies one positive `epsilon`, selected
from the explicit cap-freezing inequality, inside which every exact root
against the displayed behavioral cap of a carrier point is all-Continue.  A
returned point of any fixed-law dispatch is a carrier point, since the dispatch
retains the complete joint semantic/law datum.  So if its debt sits within
`epsilon` of the minimum, the dynamic branch's root is all-Continue and carries
no absorption, contradicting that branch's positive absorption clause.

Hence a single radius, uniform over every target, law, owner, opponent, and
returned point, separates the two dispatch outcomes: either the returned debt
strictly exceeds the minimum by more than `epsilon`, or the dispatch stalls.
-/
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Quitting.Debt.Dynamic.CyclePinnedDebt

noncomputable section

namespace GameTheory

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- **Uniform-radius reset-dispatch boundary.**  Let `source` be a global
minimizer of total terminal-semantic debt with positive value.  Then one
positive radius `epsilon`, depending only on the reward table and on the
minimum value, works simultaneously for every reset target, terminal law,
owner, opponent, and returned point: any fixed-law reset dispatch either
returns a point whose total debt strictly exceeds the minimum by more than
`epsilon`, or takes its all-Continue stall branch.

The stall branch is exactly the second arm of `dynamic_exit`: the all-Continue
root is an exact cap--Nash root against the returned behavioral cap, and
prefixing it fixes the returned point. -/
theorem fable_fixedLawResetDispatch_uniformRadius
    (source : QuittingTerminalSemanticPair ι)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hpositive : 0 < quittingTerminalSemanticDebtSum source) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (target : QuittingTerminalSemanticPair ι)
        (mass : QuittingTerminalOutcome ι → ℝ) (owner other : ι)
        (returned : QuittingTerminalSemanticPair ι),
        QuittingFixedLawResetDispatch (reward := reward) source target mass
            owner other returned →
          quittingTerminalSemanticDebtSum source + epsilon <
              quittingTerminalSemanticDebtSum returned ∨
            (IsεQuittingRootNash reward returned.2 0
                (quittingAllContinueRoot : ι → PMF Bool) ∧
              quittingTerminalSemanticPrefix reward quittingAllContinueRoot
                returned = returned) := by
  obtain ⟨epsilon, hepsilon, hradius⟩ :=
    exists_pos_nearMinimum_capNash_eq_allContinue_radius
      (reward := reward) (quittingTerminalSemanticDebtSum source)
        hpositive hminimum
  refine ⟨epsilon, hepsilon, ?_⟩
  intro target mass owner other returned dispatch
  rcases dispatch.dynamic_exit with hexit | hstall
  · left
    obtain ⟨root, hnash, habsorption, _hcontinue, _hstrict, _hjoint, _hreset,
      _hincidence⟩ := hexit
    by_contra hnot
    replace hnot : quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum source + epsilon := not_lt.mp hnot
    have hreturned : returned ∈ quittingTerminalSemanticCarrier reward :=
      terminalSemanticLawCarrier_fst_mem_carrier
        (point := (returned, mass)) dispatch.joint
    have hroot : root = (quittingAllContinueRoot : ι → PMF Bool) :=
      hradius returned hreturned hnot root hnash
    rw [hroot, quittingRootAbsorptionMass_allContinueRoot] at habsorption
    exact lt_irrefl 0 habsorption
  · exact Or.inr hstall

end GameTheory
